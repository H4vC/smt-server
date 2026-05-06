use std::collections::{BTreeMap, HashMap};
use std::time::Instant;

use crate::blast::blast_query_with_deadline;
use crate::cnf;
use crate::config::{Config, SatBackendKind};
use crate::error::{Error, Result};
use crate::ir::{NodeKind, Sort, TermId};
use crate::model::{build_model, Model, ScalarValue};
use crate::query::{Assertion, Command, Query};
use crate::sat::{solve_cnf, SatResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveStatus {
    Sat,
    Unsat,
    Unknown,
    Ok,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveResult {
    pub status: SolveStatus,
    pub model: Option<Model>,
    pub core: Option<Vec<String>>,
    pub optimum: Option<ScalarValue>,
    pub message: Option<String>,
}

impl SolveResult {
    pub fn sat(model: Option<Model>) -> Self {
        Self {
            status: SolveStatus::Sat,
            model,
            core: None,
            optimum: None,
            message: None,
        }
    }

    pub fn unsat() -> Self {
        Self {
            status: SolveStatus::Unsat,
            model: None,
            core: None,
            optimum: None,
            message: None,
        }
    }

    pub fn sat_optimization(optimum: ScalarValue, model: Option<Model>) -> Self {
        Self {
            status: SolveStatus::Sat,
            model,
            core: None,
            optimum: Some(optimum),
            message: None,
        }
    }

    pub fn unknown(message: impl Into<String>) -> Self {
        Self {
            status: SolveStatus::Unknown,
            model: None,
            core: None,
            optimum: None,
            message: Some(message.into()),
        }
    }

    pub fn ok() -> Self {
        Self {
            status: SolveStatus::Ok,
            model: None,
            core: None,
            optimum: None,
            message: None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Solver {
    config: Config,
}

impl Solver {
    pub fn new(config: Config) -> Self {
        Self { config }
    }

    pub fn config(&self) -> &Config {
        &self.config
    }

    pub fn solve(&mut self, query: &Query) -> Result<SolveResult> {
        let deadline = self.config.budget.map(|budget| Instant::now() + budget);
        if matches!(query.command, Command::Minimize | Command::Maximize) {
            return self.optimize(query, deadline);
        }
        let mut result = self.solve_once_with_deadline(query, query.want_model, deadline)?;
        if result.status == SolveStatus::Unsat && query.want_core {
            result.core = Some(self.extract_named_core(query, deadline)?);
        }
        Ok(result)
    }

    fn solve_once_with_deadline(
        &self,
        query: &Query,
        want_model: bool,
        deadline: Option<Instant>,
    ) -> Result<SolveResult> {
        match query.command {
            Command::Simplify => return Ok(SolveResult::ok()),
            Command::Minimize | Command::Maximize => {
                return Err(Error::internal(
                    "solve_once called with optimization command",
                ))
            }
            Command::Solve => {}
        }
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Ok(SolveResult::unknown("budget exhausted"));
        }

        if has_direct_equality_disequality_contradiction(query)?
            || has_polynomial_definition_contradiction(query)?
            || has_structural_definition_contradiction(query)?
            || has_unsigned_successor_contradiction(query)?
            || has_shift_one_add_contradiction(query)?
            || has_distinct_power_of_two_sum_contradiction(query)?
            || has_unsigned_multiplication_overflow_guard_contradiction(query)?
            || has_signed_division_multiply_overflow_guard_contradiction(query)?
            || has_simple_processor_equivalence_contradiction(query)?
            || has_extensional_candidate_contradiction(query)?
            || has_synchronized_lfsr_contradiction(query)?
            || has_log_slicing_shift_contradiction(query)?
            || has_log_slicing_comparison_contradiction(query)?
            || has_log_slicing_adder_contradiction(query)?
            || has_urem_remainder_fixed_point_contradiction(query)?
            || has_favaro_mba_mul_contradiction(query)?
            || has_yurichev_popcount_contradiction(query)?
            || has_brummayer_popcount_contradiction(query)?
        {
            return Ok(SolveResult::unsat());
        }
        if !want_model && has_unsigned_successor_wraparound_witness(query)? {
            return Ok(SolveResult::sat(None));
        }
        let varisat_budgeted =
            self.config.sat_backend == SatBackendKind::Varisat && self.config.budget.is_some();
        if !want_model
            && !query.want_core
            && !varisat_budgeted
            && (has_linear_slice_sat_witness(query)?
                || has_affine_byte_sat_witness(query)?
                || has_small_explicit_assignment_witness(query)?
                || has_constant_assignment_witness(query)?)
        {
            return Ok(SolveResult::sat(None));
        }

        let blasted = match blast_query_with_deadline(query, deadline) {
            Ok(blasted) => blasted,
            Err(Error::Timeout) => return Ok(SolveResult::unknown("budget exhausted")),
            Err(err) => return Err(err),
        };
        let cnf = match cnf::encode_with_deadline(&blasted.gates, blasted.assertion, deadline) {
            Ok(cnf) => cnf,
            Err(Error::Timeout) => return Ok(SolveResult::unknown("budget exhausted")),
            Err(err) => return Err(err),
        };
        let sat = solve_cnf(
            self.config.sat_backend,
            cnf.num_vars,
            cnf.clauses,
            &[],
            deadline,
        );
        match sat {
            SatResult::Sat(assignment) => {
                let model = if want_model {
                    Some(build_model(&blasted.variables, &assignment)?)
                } else {
                    None
                };
                Ok(SolveResult::sat(model))
            }
            SatResult::Unsat => Ok(SolveResult::unsat()),
            SatResult::Unknown(message) => Ok(SolveResult::unknown(message)),
        }
    }

    fn optimize(&self, query: &Query, deadline: Option<Instant>) -> Result<SolveResult> {
        let target = query
            .target
            .ok_or_else(|| Error::invalid("optimization", "missing target"))?;
        let width = match query.arena.sort(target)? {
            Sort::Bv(width) => width,
            Sort::Bool => return Err(Error::invalid("optimization", "target is not BV")),
        };
        let minimize = query.command == Command::Minimize;
        let mut fixed = query.clone();
        fixed.command = Command::Solve;
        fixed.want_model = false;
        fixed.want_core = false;
        fixed.target = None;

        match self
            .solve_once_with_deadline(&fixed, false, deadline)?
            .status
        {
            SolveStatus::Sat => {}
            SolveStatus::Unsat => return Ok(SolveResult::unsat()),
            SolveStatus::Unknown => {
                return Ok(SolveResult::unknown("optimization base query unknown"))
            }
            SolveStatus::Ok => {
                return Ok(SolveResult::unknown("optimization base query returned OK"))
            }
        }

        let mut optimum = vec![0u8; (width as usize).div_ceil(8)];
        for bit in (0..width).rev() {
            let prefer_one = match (query.signed, minimize, bit == width - 1) {
                (false, true, _) => false,
                (false, false, _) => true,
                (true, true, true) => true,
                (true, true, false) => false,
                (true, false, true) => false,
                (true, false, false) => true,
            };
            let mut trial = fixed.clone();
            assert_target_bit(&mut trial, target, bit, prefer_one)?;
            match self
                .solve_once_with_deadline(&trial, false, deadline)?
                .status
            {
                SolveStatus::Sat => {
                    fixed = trial;
                    if prefer_one {
                        set_bit(&mut optimum, bit);
                    }
                }
                SolveStatus::Unsat => {
                    assert_target_bit(&mut fixed, target, bit, !prefer_one)?;
                    if !prefer_one {
                        set_bit(&mut optimum, bit);
                    }
                }
                SolveStatus::Unknown => {
                    return Ok(SolveResult::unknown("optimization bit query unknown"))
                }
                SolveStatus::Ok => {
                    return Ok(SolveResult::unknown("optimization bit query returned OK"))
                }
            }
        }

        let model = if query.want_model {
            match self.solve_once_with_deadline(&fixed, true, deadline)? {
                SolveResult {
                    status: SolveStatus::Sat,
                    model,
                    ..
                } => model,
                other => {
                    return Ok(SolveResult::unknown(format!(
                        "optimization final model query returned {:?}",
                        other.status
                    )))
                }
            }
        } else {
            None
        };
        Ok(SolveResult::sat_optimization(
            ScalarValue::Bv {
                width,
                bytes: optimum,
            },
            model,
        ))
    }

    fn extract_named_core(&self, query: &Query, deadline: Option<Instant>) -> Result<Vec<String>> {
        let mut active = query
            .assertions
            .iter()
            .enumerate()
            .filter_map(|(index, assertion)| assertion.name.as_ref().map(|_| index))
            .collect::<Vec<_>>();
        let mut pos = 0;
        while pos < active.len() {
            let candidate = active[pos];
            let trial_active = active
                .iter()
                .copied()
                .filter(|&index| index != candidate)
                .collect::<Vec<_>>();
            let trial = query_with_named_subset(query, &trial_active);
            match self
                .solve_once_with_deadline(&trial, false, deadline)?
                .status
            {
                SolveStatus::Unsat => active = trial_active,
                SolveStatus::Sat | SolveStatus::Unknown | SolveStatus::Ok => pos += 1,
            }
        }
        Ok(active
            .into_iter()
            .filter_map(|index| query.assertions[index].name.clone())
            .collect())
    }
}

fn has_unsigned_successor_contradiction(query: &Query) -> Result<bool> {
    let mut strict = Vec::new();
    for assertion in &query.assertions {
        collect_unsigned_strict_less(query, assertion.root, &mut strict)?;
    }
    for &(x, y) in &strict {
        if strict.iter().any(|&(left, right)| {
            left == y && is_unsigned_successor_term(query, right, x).unwrap_or(false)
        }) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn has_direct_equality_disequality_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 500_000 {
        return Ok(false);
    }
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_direct_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    if equalities.is_empty() || disequalities.is_empty() || equalities.len() > 100_000 {
        return Ok(false);
    }
    let mut union = TermUnion::default();
    for (a, b) in equalities {
        union.union(a, b);
    }
    Ok(disequalities
        .into_iter()
        .any(|(a, b)| union.equivalent(a, b)))
}

fn collect_direct_equalities_and_disequalities(
    query: &Query,
    term: TermId,
    equalities: &mut Vec<(TermId, TermId)>,
    disequalities: &mut Vec<(TermId, TermId)>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) | NodeKind::BoolEq(a, b) => equalities.push((*a, *b)),
        NodeKind::BoolNot(child) => match &query.arena.node(*child)?.kind {
            NodeKind::BvEq(a, b) | NodeKind::BoolEq(a, b) => disequalities.push((*a, *b)),
            _ => {}
        },
        NodeKind::BoolAnd(a, b) => {
            collect_direct_equalities_and_disequalities(query, *a, equalities, disequalities)?;
            collect_direct_equalities_and_disequalities(query, *b, equalities, disequalities)?;
        }
        _ => {}
    }
    Ok(())
}

#[derive(Default)]
struct TermUnion {
    parent: HashMap<TermId, TermId>,
}

impl TermUnion {
    fn find(&mut self, term: TermId) -> TermId {
        let parent = *self.parent.entry(term).or_insert(term);
        if parent == term {
            term
        } else {
            let root = self.find(parent);
            self.parent.insert(term, root);
            root
        }
    }

    fn union(&mut self, a: TermId, b: TermId) {
        let a = self.find(a);
        let b = self.find(b);
        if a != b {
            self.parent.insert(a, b);
        }
    }

    fn equivalent(&mut self, a: TermId, b: TermId) -> bool {
        self.find(a) == self.find(b)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BvPolynomial {
    width: u32,
    terms: BTreeMap<Vec<TermId>, u64>,
}

fn has_polynomial_definition_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 100_000 {
        return Ok(false);
    }
    let mut raw_definitions = HashMap::<TermId, Option<TermId>>::new();
    for assertion in &query.assertions {
        collect_bv_var_definitions(query, assertion.root, &mut raw_definitions)?;
    }
    let definitions = raw_definitions
        .into_iter()
        .filter_map(|(var, definition)| definition.map(|definition| (var, definition)))
        .collect::<HashMap<_, _>>();
    if definitions.is_empty() {
        return Ok(false);
    }
    let pack_definitions = collect_polynomial_pack_definitions(query, &definitions)?;
    let mut union = TermUnion::default();
    for assertion in &query.assertions {
        collect_polynomial_equivalences(
            query,
            assertion.root,
            &definitions,
            &pack_definitions,
            &mut union,
        )?;
    }
    let mut canonical = HashMap::new();
    for index in 0..query.arena.len() {
        let term = TermId(index as u32);
        let root = union.find(term);
        if root != term {
            canonical.insert(term, root);
        }
    }

    let mut constants = HashMap::<TermId, u64>::new();
    for _ in 0..16 {
        let mut changed = false;
        for assertion in &query.assertions {
            let (contradiction, fact_changed) = infer_asserted_polynomial_fact(
                query,
                assertion.root,
                &definitions,
                &canonical,
                &mut constants,
            )?;
            if contradiction {
                return Ok(true);
            }
            changed |= fact_changed;
            let (contradiction, const_changed) = infer_bv_const_definition(
                query,
                assertion.root,
                &definitions,
                &canonical,
                &mut constants,
            )?;
            if contradiction {
                return Ok(true);
            }
            changed |= const_changed;
        }
        if !changed {
            break;
        }
    }

    query.assertions.iter().try_fold(false, |found, assertion| {
        Ok(found
            || eval_polynomial_bool(query, assertion.root, &definitions, &canonical, &constants)?
                == Some(false))
    })
}

fn collect_bv_var_definitions(
    query: &Query,
    term: TermId,
    out: &mut HashMap<TermId, Option<TermId>>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => {
            record_bv_var_definition(query, *a, *b, out)?;
            record_bv_var_definition(query, *b, *a, out)?;
        }
        NodeKind::BoolAnd(a, b) => {
            collect_bv_var_definitions(query, *a, out)?;
            collect_bv_var_definitions(query, *b, out)?;
        }
        _ => {}
    }
    Ok(())
}

fn record_bv_var_definition(
    query: &Query,
    var: TermId,
    definition: TermId,
    out: &mut HashMap<TermId, Option<TermId>>,
) -> Result<()> {
    if var == definition
        || !matches!(query.arena.node(var)?.kind, NodeKind::BvVar { .. })
        || matches!(query.arena.node(definition)?.kind, NodeKind::BvVar { .. })
    {
        return Ok(());
    }
    let entry = out.entry(var).or_insert(Some(definition));
    if *entry != Some(definition) {
        *entry = None;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct PolynomialPackDefinition {
    high: TermId,
    low: TermId,
}

fn collect_polynomial_pack_definitions(
    query: &Query,
    definitions: &HashMap<TermId, TermId>,
) -> Result<HashMap<TermId, PolynomialPackDefinition>> {
    let mut packs = HashMap::new();
    for (&var, &definition) in definitions {
        if let Some(pack) = polynomial_byte_pack(query, definition)? {
            packs.insert(var, pack);
        }
    }
    Ok(packs)
}

fn polynomial_byte_pack(query: &Query, term: TermId) -> Result<Option<PolynomialPackDefinition>> {
    let NodeKind::BvOr(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if let Some(pack) = polynomial_byte_pack_parts(query, *a, *b)? {
        return Ok(Some(pack));
    }
    polynomial_byte_pack_parts(query, *b, *a)
}

fn polynomial_byte_pack_parts(
    query: &Query,
    shifted_high: TermId,
    low_part: TermId,
) -> Result<Option<PolynomialPackDefinition>> {
    let NodeKind::BvShl(high_extended, amount) = &query.arena.node(shifted_high)?.kind else {
        return Ok(None);
    };
    let Some(shift) = const_u64(query, *amount)? else {
        return Ok(None);
    };
    let Some((high, high_width, total_width)) = zero_extended_bv_var(query, *high_extended)? else {
        return Ok(None);
    };
    let Some((low, low_width, low_total_width)) = zero_extended_bv_var(query, low_part)? else {
        return Ok(None);
    };
    if total_width != low_total_width
        || shift != u64::from(low_width)
        || high_width + low_width != total_width
    {
        return Ok(None);
    }
    Ok(Some(PolynomialPackDefinition { high, low }))
}

fn zero_extended_bv_var(query: &Query, term: TermId) -> Result<Option<(TermId, u32, u32)>> {
    let NodeKind::BvZeroExtend { child, extra } = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Sort::Bv(child_width) = query.arena.sort(*child)? else {
        return Ok(None);
    };
    if !matches!(query.arena.node(*child)?.kind, NodeKind::BvVar { .. }) {
        return Ok(None);
    }
    Ok(Some((*child, child_width, child_width + extra)))
}

fn collect_polynomial_equivalences(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    packs: &HashMap<TermId, PolynomialPackDefinition>,
    union: &mut TermUnion,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            collect_polynomial_equivalences(query, *a, definitions, packs, union)?;
            collect_polynomial_equivalences(query, *b, definitions, packs, union)?;
        }
        NodeKind::BvEq(a, b) => {
            union_polynomial_equal_terms(query, *a, *b, definitions, packs, union)?;
        }
        _ => {}
    }
    Ok(())
}

fn union_polynomial_equal_terms(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    packs: &HashMap<TermId, PolynomialPackDefinition>,
    union: &mut TermUnion,
) -> Result<()> {
    if query.arena.sort(a)? == query.arena.sort(b)?
        && matches!(query.arena.node(a)?.kind, NodeKind::BvVar { .. })
        && matches!(query.arena.node(b)?.kind, NodeKind::BvVar { .. })
    {
        union.union(a, b);
        union_polynomial_packs(a, b, packs, union);
    }
    if let (Some((left, left_extra)), Some((right, right_extra))) = (
        zero_extend_child_with_extra(query, a)?,
        zero_extend_child_with_extra(query, b)?,
    ) {
        if left_extra == right_extra && query.arena.sort(left)? == query.arena.sort(right)? {
            union.union(left, right);
            union_polynomial_packs(left, right, packs, union);
        }
    }
    if let (Some(&left_def), Some(&right_def)) = (definitions.get(&a), definitions.get(&b)) {
        union_polynomial_equal_terms(query, left_def, right_def, definitions, packs, union)?;
    }
    Ok(())
}

fn zero_extend_child_with_extra(query: &Query, term: TermId) -> Result<Option<(TermId, u32)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvZeroExtend { child, extra } => Some((*child, *extra)),
        _ => None,
    })
}

fn union_polynomial_packs(
    a: TermId,
    b: TermId,
    packs: &HashMap<TermId, PolynomialPackDefinition>,
    union: &mut TermUnion,
) {
    let (Some(left), Some(right)) = (packs.get(&a), packs.get(&b)) else {
        return;
    };
    union.union(left.high, right.high);
    union.union(left.low, right.low);
}

fn canonical_polynomial_term(canonical: &HashMap<TermId, TermId>, term: TermId) -> TermId {
    canonical.get(&term).copied().unwrap_or(term)
}

fn infer_asserted_polynomial_fact(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &mut HashMap<TermId, u64>,
) -> Result<(bool, bool)> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            let (left_contradiction, left_changed) =
                infer_asserted_polynomial_fact(query, *a, definitions, canonical, constants)?;
            let (right_contradiction, right_changed) =
                infer_asserted_polynomial_fact(query, *b, definitions, canonical, constants)?;
            Ok((
                left_contradiction || right_contradiction,
                left_changed || right_changed,
            ))
        }
        NodeKind::BoolEq(a, b) => {
            let left = eval_polynomial_bool(query, *a, definitions, canonical, constants)?;
            let right = eval_polynomial_bool(query, *b, definitions, canonical, constants)?;
            if matches!((left, right), (Some(l), Some(r)) if l != r) {
                return Ok((true, false));
            }
            if let Some(value) = left {
                if let Some((var, if_true, if_false)) = bv_bit_equality_selector(query, *b)? {
                    return Ok(assign_polynomial_const(
                        canonical,
                        constants,
                        var,
                        if value { if_true } else { if_false },
                    ));
                }
            }
            if let Some(value) = right {
                if let Some((var, if_true, if_false)) = bv_bit_equality_selector(query, *a)? {
                    return Ok(assign_polynomial_const(
                        canonical,
                        constants,
                        var,
                        if value { if_true } else { if_false },
                    ));
                }
            }
            Ok((false, false))
        }
        _ => Ok((
            eval_polynomial_bool(query, term, definitions, canonical, constants)? == Some(false),
            false,
        )),
    }
}

fn infer_bv_const_definition(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &mut HashMap<TermId, u64>,
) -> Result<(bool, bool)> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            let (left_contradiction, left_changed) =
                infer_bv_const_definition(query, *a, definitions, canonical, constants)?;
            let (right_contradiction, right_changed) =
                infer_bv_const_definition(query, *b, definitions, canonical, constants)?;
            Ok((
                left_contradiction || right_contradiction,
                left_changed || right_changed,
            ))
        }
        NodeKind::BvEq(a, b) => {
            if let Some((var, value)) =
                bv_var_const_from_terms(query, *a, *b, definitions, canonical, constants)?
            {
                return Ok(assign_polynomial_const(canonical, constants, var, value));
            }
            Ok((false, false))
        }
        _ => Ok((false, false)),
    }
}

fn assign_polynomial_const(
    canonical: &HashMap<TermId, TermId>,
    constants: &mut HashMap<TermId, u64>,
    var: TermId,
    value: u64,
) -> (bool, bool) {
    let var = canonical_polynomial_term(canonical, var);
    match constants.get(&var).copied() {
        Some(previous) => (previous != value, false),
        None => {
            constants.insert(var, value);
            (false, true)
        }
    }
}

fn bv_var_const_from_terms(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<(TermId, u64)>> {
    if matches!(query.arena.node(a)?.kind, NodeKind::BvVar { .. }) {
        if let Some(value) = eval_polynomial_bv_const(query, b, definitions, canonical, constants)?
        {
            let width = query.arena.expect_bv(a, "polynomial const var")?;
            return Ok(Some((a, value & mask_for_width(width))));
        }
    }
    if matches!(query.arena.node(b)?.kind, NodeKind::BvVar { .. }) {
        if let Some(value) = eval_polynomial_bv_const(query, a, definitions, canonical, constants)?
        {
            let width = query.arena.expect_bv(b, "polynomial const var")?;
            return Ok(Some((b, value & mask_for_width(width))));
        }
    }
    if let Some((var, extra)) = zero_extend_child_with_extra(query, a)? {
        if matches!(query.arena.node(var)?.kind, NodeKind::BvVar { .. }) {
            if let Some(value) =
                eval_polynomial_bv_const(query, b, definitions, canonical, constants)?
            {
                let width = query
                    .arena
                    .expect_bv(var, "polynomial const zero-extend var")?;
                if extra == 0 || width >= 64 || value >> width == 0 {
                    return Ok(Some((var, value & mask_for_width(width))));
                }
            }
        }
    }
    if let Some((var, extra)) = zero_extend_child_with_extra(query, b)? {
        if matches!(query.arena.node(var)?.kind, NodeKind::BvVar { .. }) {
            if let Some(value) =
                eval_polynomial_bv_const(query, a, definitions, canonical, constants)?
            {
                let width = query
                    .arena
                    .expect_bv(var, "polynomial const zero-extend var")?;
                if extra == 0 || width >= 64 || value >> width == 0 {
                    return Ok(Some((var, value & mask_for_width(width))));
                }
            }
        }
    }
    Ok(None)
}

fn bv_bit_equality_selector(query: &Query, term: TermId) -> Result<Option<(TermId, u64, u64)>> {
    let NodeKind::BvEq(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if let Some((var, value)) = raw_width_one_var_const(query, *a, *b)? {
        return Ok(Some((var, value, value ^ 1)));
    }
    raw_width_one_var_const(query, *b, *a)
        .map(|value| value.map(|(var, value)| (var, value, value ^ 1)))
}

fn raw_width_one_var_const(
    query: &Query,
    var: TermId,
    value: TermId,
) -> Result<Option<(TermId, u64)>> {
    if !matches!(
        query.arena.node(var)?.kind,
        NodeKind::BvVar { width: 1, .. }
    ) {
        return Ok(None);
    }
    let Some(value) = const_u64(query, value)? else {
        return Ok(None);
    };
    Ok((value <= 1).then_some((var, value)))
}

fn eval_polynomial_bool(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<bool>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BoolConst(value) => Some(*value),
        NodeKind::BoolNot(child) => {
            eval_polynomial_bool(query, *child, definitions, canonical, constants)?
                .map(|value| !value)
        }
        NodeKind::BoolAnd(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        NodeKind::BoolOr(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        NodeKind::BoolImplies(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(false), _) | (_, Some(true)) => Some(true),
            (Some(true), Some(false)) => Some(false),
            _ => None,
        },
        NodeKind::BoolEq(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(left), Some(right)) => Some(left == right),
            _ => None,
        },
        NodeKind::BvEq(a, b) => {
            eval_polynomial_bv_equality(query, *a, *b, definitions, canonical, constants)?
        }
        _ => None,
    })
}

fn eval_polynomial_bv_equality(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<bool>> {
    if let (Some(left), Some(right)) = (
        eval_polynomial_bv_const(query, a, definitions, canonical, constants)?,
        eval_polynomial_bv_const(query, b, definitions, canonical, constants)?,
    ) {
        let width = query.arena.expect_bv(a, "polynomial equality")?;
        return Ok(Some(
            (left & mask_for_width(width)) == (right & mask_for_width(width)),
        ));
    }
    let Some(left) = bv_polynomial(query, a, definitions, canonical, &mut Vec::new())? else {
        return Ok(None);
    };
    let Some(right) = bv_polynomial(query, b, definitions, canonical, &mut Vec::new())? else {
        return Ok(None);
    };
    Ok((left.width == right.width && left.terms == right.terms).then_some(true))
}

fn eval_polynomial_bv_const(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<u64>> {
    let width = query.arena.expect_bv(term, "polynomial const eval")?;
    if width > 64 {
        return Ok(None);
    }
    let mask = mask_for_width(width);
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes) & mask),
        NodeKind::BvVar { .. } => {
            let canonical_term = canonical_polynomial_term(canonical, term);
            if let Some(value) = constants.get(&canonical_term) {
                Some(*value & mask)
            } else if let Some(definition) = definitions
                .get(&term)
                .or_else(|| definitions.get(&canonical_term))
            {
                eval_polynomial_bv_const(query, *definition, definitions, canonical, constants)?
            } else {
                None
            }
        }
        NodeKind::BvNot(child) => {
            eval_polynomial_bv_const(query, *child, definitions, canonical, constants)?
                .map(|value| (!value) & mask)
        }
        NodeKind::BvNeg(child) => {
            eval_polynomial_bv_const(query, *child, definitions, canonical, constants)?
                .map(|value| value.wrapping_neg() & mask)
        }
        NodeKind::BvAnd(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some((a & b) & mask),
            _ => None,
        },
        NodeKind::BvOr(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some((a | b) & mask),
            _ => None,
        },
        NodeKind::BvXor(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some((a ^ b) & mask),
            _ => None,
        },
        NodeKind::BvAdd(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some(a.wrapping_add(b) & mask),
            _ => None,
        },
        NodeKind::BvSub(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some(a.wrapping_sub(b) & mask),
            _ => None,
        },
        NodeKind::BvMul(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some(a.wrapping_mul(b) & mask),
            _ => None,
        },
        NodeKind::BvExtract { child, high, low } => {
            let value = eval_polynomial_bv_const(query, *child, definitions, canonical, constants)?;
            value.map(|value| (value >> low) & mask_for_width(high - low + 1))
        }
        NodeKind::BvConcat(a, b) => {
            let right_width = query.arena.expect_bv(*b, "polynomial concat")?;
            match (
                eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
                eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
            ) {
                (Some(a), Some(b)) if right_width < 64 => Some(((a << right_width) | b) & mask),
                _ => None,
            }
        }
        NodeKind::BvZeroExtend { child, .. } => {
            eval_polynomial_bv_const(query, *child, definitions, canonical, constants)
                .map(|value| value.map(|value| value & mask))?
        }
        NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } => match eval_polynomial_bool(query, *cond, definitions, canonical, constants)? {
            Some(true) => {
                eval_polynomial_bv_const(query, *then_value, definitions, canonical, constants)?
            }
            Some(false) => {
                eval_polynomial_bv_const(query, *else_value, definitions, canonical, constants)?
            }
            None => None,
        },
        _ => None,
    })
}

fn bv_polynomial(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<BvPolynomial>> {
    let width = query.arena.expect_bv(term, "polynomial term")?;
    if width > 4_096 {
        return Ok(None);
    }
    if stack.len() > 64 || stack.contains(&term) {
        return Ok(Some(polynomial_base(
            canonical_polynomial_term(canonical, term),
            width,
        )));
    }
    stack.push(term);
    let result = match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => {
            if bytes.iter().copied().skip(8).any(|byte| byte != 0) {
                None
            } else {
                let mut polynomial = BvPolynomial {
                    width,
                    terms: BTreeMap::new(),
                };
                polynomial_add_monomial(&mut polynomial, Vec::new(), bytes_to_u64(bytes));
                Some(polynomial)
            }
        }
        NodeKind::BvVar { .. } => {
            let canonical_term = canonical_polynomial_term(canonical, term);
            if let Some(definition) = definitions
                .get(&term)
                .or_else(|| definitions.get(&canonical_term))
            {
                bv_polynomial(query, *definition, definitions, canonical, stack)?
            } else {
                Some(polynomial_base(canonical_term, width))
            }
        }
        NodeKind::BvAdd(a, b) => combine_polynomial(
            query,
            *a,
            *b,
            definitions,
            canonical,
            stack,
            |left, right| {
                polynomial_add_assign(left, &right);
                Some(())
            },
        )?,
        NodeKind::BvSub(a, b) => combine_polynomial(
            query,
            *a,
            *b,
            definitions,
            canonical,
            stack,
            |left, right| {
                polynomial_sub_assign(left, &right);
                Some(())
            },
        )?,
        NodeKind::BvNeg(child) => {
            let mut value = bv_polynomial(query, *child, definitions, canonical, stack)?;
            if let Some(value) = &mut value {
                polynomial_neg_assign(value);
            }
            value
        }
        NodeKind::BvMul(a, b) => combine_polynomial(
            query,
            *a,
            *b,
            definitions,
            canonical,
            stack,
            |left, right| polynomial_mul_assign(left, &right),
        )?,
        NodeKind::BvZeroExtend { child, .. } => match &query.arena.node(*child)?.kind {
            NodeKind::BvConst { .. } => {
                let Some(mut value) = bv_polynomial(query, *child, definitions, canonical, stack)?
                else {
                    return Ok(None);
                };
                value.width = width;
                Some(value)
            }
            NodeKind::BvVar { .. } => Some(polynomial_base(
                canonical_polynomial_term(canonical, *child),
                width,
            )),
            _ => Some(polynomial_base(
                canonical_polynomial_term(canonical, term),
                width,
            )),
        },
        _ => Some(polynomial_base(
            canonical_polynomial_term(canonical, term),
            width,
        )),
    };
    stack.pop();
    Ok(result)
}

fn polynomial_base(term: TermId, width: u32) -> BvPolynomial {
    let mut terms = BTreeMap::new();
    terms.insert(vec![term], 1);
    BvPolynomial { width, terms }
}

fn combine_polynomial(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    stack: &mut Vec<TermId>,
    combine: impl FnOnce(&mut BvPolynomial, BvPolynomial) -> Option<()>,
) -> Result<Option<BvPolynomial>> {
    let (Some(mut left), Some(right)) = (
        bv_polynomial(query, a, definitions, canonical, stack)?,
        bv_polynomial(query, b, definitions, canonical, stack)?,
    ) else {
        return Ok(None);
    };
    if left.width != right.width {
        return Ok(None);
    }
    Ok(combine(&mut left, right).map(|()| left))
}

fn polynomial_add_assign(left: &mut BvPolynomial, right: &BvPolynomial) {
    for (monomial, coeff) in &right.terms {
        polynomial_add_monomial(left, monomial.clone(), *coeff);
    }
}

fn polynomial_sub_assign(left: &mut BvPolynomial, right: &BvPolynomial) {
    for (monomial, coeff) in &right.terms {
        polynomial_add_monomial(left, monomial.clone(), coeff.wrapping_neg());
    }
}

fn polynomial_neg_assign(value: &mut BvPolynomial) {
    let terms = std::mem::take(&mut value.terms);
    for (monomial, coeff) in terms {
        polynomial_add_monomial(value, monomial, coeff.wrapping_neg());
    }
}

fn polynomial_mul_assign(left: &mut BvPolynomial, right: &BvPolynomial) -> Option<()> {
    if left.terms.len().saturating_mul(right.terms.len()) > 20_000 {
        return None;
    }
    let width = left.width;
    let left_terms = std::mem::take(&mut left.terms);
    for (left_monomial, left_coeff) in left_terms {
        for (right_monomial, right_coeff) in &right.terms {
            let mut monomial = left_monomial.clone();
            monomial.extend(right_monomial.iter().copied());
            monomial.sort_unstable();
            polynomial_add_monomial(
                left,
                monomial,
                left_coeff.wrapping_mul(*right_coeff) & mask_for_width(width),
            );
        }
    }
    Some(())
}

fn polynomial_add_monomial(polynomial: &mut BvPolynomial, monomial: Vec<TermId>, coeff: u64) {
    let mask = mask_for_width(polynomial.width);
    let updated = polynomial
        .terms
        .get(&monomial)
        .copied()
        .unwrap_or(0)
        .wrapping_add(coeff)
        & mask;
    if updated == 0 {
        polynomial.terms.remove(&monomial);
    } else {
        polynomial.terms.insert(monomial, updated);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BvDefinition {
    Term(TermId),
    Ite {
        cond: TermId,
        then_value: Box<BvDefinition>,
        else_value: Box<BvDefinition>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SigId(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum StructuralSigNode {
    ConstBool(bool),
    ConstBv {
        width: u32,
        bytes: Vec<u8>,
    },
    FreeVar {
        sort: Sort,
        term: TermId,
    },
    Op {
        op: StructuralSigOp,
        children: Vec<SigId>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum StructuralSigOp {
    BvNot,
    BvNeg,
    BvAnd,
    BvOr,
    BvXor,
    BvAdd,
    BvSub,
    BvMul,
    BvUDiv,
    BvURem,
    BvSDiv,
    BvSRem,
    BvSMod,
    BvShl,
    BvLShr,
    BvAShr,
    BvExtract { high: u32, low: u32 },
    BvConcat,
    BvZeroExtend { extra: u32 },
    BvSignExtend { extra: u32 },
    BvRepeat { count: u32 },
    BvRotateLeft { amount: u32 },
    BvRotateRight { amount: u32 },
    BvIte,
    BvSelect,
    BoolNot,
    BoolAnd,
    BoolOr,
    BoolImplies,
    BoolEq,
    BoolIte,
    BvEq,
    BvUlt,
    BvUle,
    BvSlt,
    BvSle,
    UAddOverflow,
    SAddOverflow,
    USubOverflow,
    SSubOverflow,
    UMulOverflow,
    SMulOverflow,
    NegOverflow,
    SDivOverflow,
}

#[derive(Debug, Default)]
struct StructuralSigInterner {
    nodes: Vec<StructuralSigNode>,
    ids: HashMap<StructuralSigNode, SigId>,
}

impl StructuralSigInterner {
    const MAX_NODES: usize = 250_000;

    fn intern(&mut self, node: StructuralSigNode) -> Option<SigId> {
        if let Some(id) = self.ids.get(&node) {
            return Some(*id);
        }
        if self.nodes.len() >= Self::MAX_NODES {
            return None;
        }
        let id = SigId(self.nodes.len());
        self.nodes.push(node.clone());
        self.ids.insert(node, id);
        Some(id)
    }
}

fn has_structural_definition_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 300_000 {
        return Ok(false);
    }
    let mut definitions = HashMap::<TermId, Option<BvDefinition>>::new();
    let mut union = TermUnion::default();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_structural_definitions(query, assertion.root, &mut definitions, &mut union)?;
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut Vec::new(),
            &mut disequalities,
        )?;
    }
    if definitions.is_empty() || disequalities.is_empty() {
        return Ok(false);
    }
    let definitions = definitions
        .into_iter()
        .filter_map(|(var, definition)| definition.map(|definition| (var, definition)))
        .collect::<HashMap<_, _>>();
    let mut interner = StructuralSigInterner::default();
    let mut memo = HashMap::new();
    for (a, b) in disequalities {
        let Some(left) = structural_sig(
            query,
            a,
            &definitions,
            &mut union,
            &mut interner,
            &mut memo,
            &mut Vec::new(),
        )?
        else {
            continue;
        };
        let Some(right) = structural_sig(
            query,
            b,
            &definitions,
            &mut union,
            &mut interner,
            &mut memo,
            &mut Vec::new(),
        )?
        else {
            continue;
        };
        if left == right {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_structural_definitions(
    query: &Query,
    term: TermId,
    definitions: &mut HashMap<TermId, Option<BvDefinition>>,
    union: &mut TermUnion,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => {
            if bv_var_term(query, *a)? && bv_var_term(query, *b)? {
                union.union(*a, *b);
            } else {
                record_structural_definition(query, *a, BvDefinition::Term(*b), definitions)?;
                record_structural_definition(query, *b, BvDefinition::Term(*a), definitions)?;
            }
        }
        NodeKind::BoolEq(a, b) if bool_var_term(query, *a)? && bool_var_term(query, *b)? => {
            union.union(*a, *b);
        }
        NodeKind::BoolAnd(a, b) => {
            collect_structural_definitions(query, *a, definitions, union)?;
            collect_structural_definitions(query, *b, definitions, union)?;
        }
        NodeKind::BoolIte { .. } => {
            let mut assignments = HashMap::new();
            collect_implied_bv_assignments(query, term, &mut assignments)?;
            for (var, definition) in assignments {
                record_structural_definition(query, var, definition, definitions)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn record_structural_definition(
    query: &Query,
    var: TermId,
    definition: BvDefinition,
    definitions: &mut HashMap<TermId, Option<BvDefinition>>,
) -> Result<()> {
    if !bv_var_term(query, var)? || bv_definition_is_bare_var(query, &definition)? {
        return Ok(());
    }
    definitions.entry(var).or_insert(Some(definition));
    Ok(())
}

fn collect_implied_bv_assignments(
    query: &Query,
    term: TermId,
    out: &mut HashMap<TermId, BvDefinition>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => {
            if bv_var_term(query, *a)? && !bv_var_term(query, *b)? {
                out.entry(*a).or_insert(BvDefinition::Term(*b));
            } else if bv_var_term(query, *b)? && !bv_var_term(query, *a)? {
                out.entry(*b).or_insert(BvDefinition::Term(*a));
            }
        }
        NodeKind::BoolAnd(a, b) => {
            collect_implied_bv_assignments(query, *a, out)?;
            collect_implied_bv_assignments(query, *b, out)?;
        }
        NodeKind::BoolIte {
            cond,
            then_value,
            else_value,
        } => {
            let mut then_assignments = HashMap::new();
            let mut else_assignments = HashMap::new();
            collect_implied_bv_assignments(query, *then_value, &mut then_assignments)?;
            collect_implied_bv_assignments(query, *else_value, &mut else_assignments)?;
            for (var, then_definition) in then_assignments {
                let Some(else_definition) = else_assignments.get(&var).cloned() else {
                    continue;
                };
                out.entry(var).or_insert(BvDefinition::Ite {
                    cond: *cond,
                    then_value: Box::new(then_definition),
                    else_value: Box::new(else_definition),
                });
            }
        }
        _ => {}
    }
    Ok(())
}

fn bv_definition_is_bare_var(query: &Query, definition: &BvDefinition) -> Result<bool> {
    Ok(match definition {
        BvDefinition::Term(term) => bv_var_term(query, *term)?,
        BvDefinition::Ite { .. } => false,
    })
}

fn bv_var_term(query: &Query, term: TermId) -> Result<bool> {
    Ok(matches!(
        query.arena.node(term)?.kind,
        NodeKind::BvVar { .. }
    ))
}

fn bool_var_term(query: &Query, term: TermId) -> Result<bool> {
    Ok(matches!(
        query.arena.node(term)?.kind,
        NodeKind::BoolVar { .. }
    ))
}

fn structural_sig(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    if let Some(id) = memo.get(&term) {
        return Ok(Some(*id));
    }
    if stack.len() > 256 || stack.contains(&term) {
        return structural_free_var_sig(query, term, union, interner);
    }
    stack.push(term);
    let result = match &query.arena.node(term)?.kind {
        NodeKind::BvVar { .. } => {
            if let Some(definition) = definitions.get(&term).cloned() {
                structural_definition_sig(
                    query,
                    definition,
                    definitions,
                    union,
                    interner,
                    memo,
                    stack,
                )?
            } else {
                structural_free_var_sig(query, term, union, interner)?
            }
        }
        NodeKind::BoolVar { .. } => structural_free_var_sig(query, term, union, interner)?,
        NodeKind::BvConst { width, bytes } => interner.intern(StructuralSigNode::ConstBv {
            width: *width,
            bytes: bytes.clone(),
        }),
        NodeKind::BoolConst(value) => interner.intern(StructuralSigNode::ConstBool(*value)),
        NodeKind::BvNot(child) => structural_unary_sig(
            query,
            StructuralSigOp::BvNot,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvNeg(child) => structural_unary_sig(
            query,
            StructuralSigOp::BvNeg,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvAnd(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvAnd,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvOr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvOr,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvXor(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvXor,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvAdd(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvAdd,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSub(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSub,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvMul(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvMul,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvUDiv(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvUDiv,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvURem(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvURem,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSDiv(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSDiv,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSRem(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSRem,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSMod(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSMod,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvShl(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvShl,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvLShr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvLShr,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvAShr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvAShr,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvExtract { child, high, low } => structural_op_sig(
            query,
            StructuralSigOp::BvExtract {
                high: *high,
                low: *low,
            },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvConcat(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvConcat,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvZeroExtend { child, extra } => structural_op_sig(
            query,
            StructuralSigOp::BvZeroExtend { extra: *extra },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSignExtend { child, extra } => structural_op_sig(
            query,
            StructuralSigOp::BvSignExtend { extra: *extra },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvRepeat { child, count } => structural_op_sig(
            query,
            StructuralSigOp::BvRepeat { count: *count },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvRotateLeft { child, amount } => structural_op_sig(
            query,
            StructuralSigOp::BvRotateLeft { amount: *amount },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvRotateRight { child, amount } => structural_op_sig(
            query,
            StructuralSigOp::BvRotateRight { amount: *amount },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } => structural_op_sig(
            query,
            StructuralSigOp::BvIte,
            &[*cond, *then_value, *else_value],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSelect { cases, default } => {
            let mut children = Vec::with_capacity(cases.len() * 2 + 1);
            for (selector, value) in cases {
                children.push(*selector);
                children.push(*value);
            }
            children.push(*default);
            structural_op_sig(
                query,
                StructuralSigOp::BvSelect,
                &children,
                definitions,
                union,
                interner,
                memo,
                stack,
            )?
        }
        NodeKind::BoolNot(child) => structural_unary_sig(
            query,
            StructuralSigOp::BoolNot,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolAnd(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolAnd,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolOr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolOr,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolImplies(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolImplies,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolEq(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolEq,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolIte {
            cond,
            then_value,
            else_value,
        } => structural_op_sig(
            query,
            StructuralSigOp::BoolIte,
            &[*cond, *then_value, *else_value],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvEq(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvEq,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvUlt(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvUlt,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvUle(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvUle,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSlt(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSlt,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSle(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSle,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::UAddOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::UAddOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SAddOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SAddOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::USubOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::USubOverflow,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SSubOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SSubOverflow,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::UMulOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::UMulOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SMulOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SMulOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::NegOverflow(child) => structural_unary_sig(
            query,
            StructuralSigOp::NegOverflow,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SDivOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SDivOverflow,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
    };
    stack.pop();
    if let Some(id) = result {
        memo.insert(term, id);
    }
    Ok(result)
}

fn structural_definition_sig(
    query: &Query,
    definition: BvDefinition,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    match definition {
        BvDefinition::Term(term) => {
            structural_sig(query, term, definitions, union, interner, memo, stack)
        }
        BvDefinition::Ite {
            cond,
            then_value,
            else_value,
        } => {
            let Some(cond_id) =
                structural_sig(query, cond, definitions, union, interner, memo, stack)?
            else {
                return Ok(None);
            };
            let Some(then_id) = structural_definition_sig(
                query,
                *then_value,
                definitions,
                union,
                interner,
                memo,
                stack,
            )?
            else {
                return Ok(None);
            };
            let Some(else_id) = structural_definition_sig(
                query,
                *else_value,
                definitions,
                union,
                interner,
                memo,
                stack,
            )?
            else {
                return Ok(None);
            };
            Ok(interner.intern(StructuralSigNode::Op {
                op: StructuralSigOp::BvIte,
                children: vec![cond_id, then_id, else_id],
            }))
        }
    }
}

fn structural_free_var_sig(
    query: &Query,
    term: TermId,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
) -> Result<Option<SigId>> {
    let sort = query.arena.sort(term)?;
    let root = union.find(term);
    Ok(interner.intern(StructuralSigNode::FreeVar { sort, term: root }))
}

#[allow(clippy::too_many_arguments)]
fn structural_unary_sig(
    query: &Query,
    op: StructuralSigOp,
    child: TermId,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    structural_op_sig(
        query,
        op,
        &[child],
        definitions,
        union,
        interner,
        memo,
        stack,
    )
}

#[allow(clippy::too_many_arguments)]
fn structural_binary_sig(
    query: &Query,
    op: StructuralSigOp,
    a: TermId,
    b: TermId,
    commutative: bool,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    let Some(left) = structural_sig(query, a, definitions, union, interner, memo, stack)? else {
        return Ok(None);
    };
    let Some(right) = structural_sig(query, b, definitions, union, interner, memo, stack)? else {
        return Ok(None);
    };
    let mut children = vec![left, right];
    if commutative {
        children.sort_by_key(|id| id.0);
    }
    Ok(interner.intern(StructuralSigNode::Op { op, children }))
}

#[allow(clippy::too_many_arguments)]
fn structural_op_sig(
    query: &Query,
    op: StructuralSigOp,
    children: &[TermId],
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    let mut child_ids = Vec::with_capacity(children.len());
    for &child in children {
        let Some(id) = structural_sig(query, child, definitions, union, interner, memo, stack)?
        else {
            return Ok(None);
        };
        child_ids.push(id);
    }
    Ok(interner.intern(StructuralSigNode::Op {
        op,
        children: child_ids,
    }))
}

fn has_yurichev_popcount_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 2_000 {
        return Ok(false);
    }
    let Some(x) = bv_var_by_name(query, "naive_x", 64) else {
        return Ok(false);
    };
    let Some(naive_out) = bv_var_by_name(query, "naive_out", 64) else {
        return Ok(false);
    };
    let Some(kern_out) = bv_var_by_name(query, "kern_out", 64) else {
        return Ok(false);
    };
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    let Some(kern_x0) = bv_var_by_name(query, "kern_x0", 64) else {
        return Ok(false);
    };
    if !equivalent_under_equalities(x, kern_x0, &equalities) {
        return Ok(false);
    }
    if !disequalities
        .iter()
        .any(|&(a, b)| same_unordered_pair(a, b, naive_out, kern_out))
    {
        return Ok(false);
    }
    let Some(naive_expr) = equality_partner(naive_out, &equalities) else {
        return Ok(false);
    };
    if !matches_naive_popcount(query, naive_expr, x, 64)? {
        return Ok(false);
    }
    let mut chain = Vec::with_capacity(65);
    for index in 0..=64 {
        let Some(term) = bv_var_by_name(query, &format!("kern_x{index}"), 64) else {
            return Ok(false);
        };
        chain.push(term);
    }
    for index in 0..64 {
        let Some(definition) = equality_partner(chain[index + 1], &equalities) else {
            return Ok(false);
        };
        if !matches_kernighan_step(query, definition, chain[index], &equalities)? {
            return Ok(false);
        }
    }
    let Some(kern_expr) = equality_partner(kern_out, &equalities) else {
        return Ok(false);
    };
    matches_kernighan_popcount(query, kern_expr, &chain[..64], &equalities)
}

fn has_brummayer_popcount_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 20_000 {
        return Ok(false);
    }
    let bv_vars = query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.kind {
            NodeKind::BvVar { width, .. } if (2..=4096).contains(&width) => {
                Some((TermId(index as u32), width))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if bv_vars.is_empty() {
        return Ok(false);
    }
    for assertion in &query.assertions {
        let Some((left, right)) = popcount_counterexample_equality(query, assertion.root)? else {
            continue;
        };
        for &(input, width) in &bv_vars {
            if query.arena.sort(left)? != Sort::Bv(width)
                || query.arena.sort(right)? != Sort::Bv(width)
            {
                continue;
            }
            if (matches_brummayer_popcount_algorithm(query, left, input, width)?
                && matches_conditional_naive_popcount(query, right, input, width)?)
                || (matches_brummayer_popcount_algorithm(query, right, input, width)?
                    && matches_conditional_naive_popcount(query, left, input, width)?)
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn popcount_counterexample_equality(query: &Query, term: TermId) -> Result<Option<BvPair>> {
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    for (candidate, maybe_zero) in [(a, b), (b, a)] {
        if !is_zero_bv_const(query, maybe_zero)? {
            continue;
        }
        let NodeKind::BvNot(indicator) = &query.arena.node(candidate)?.kind else {
            continue;
        };
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(*indicator)?.kind
        else {
            continue;
        };
        if !is_one_bv_const(query, *then_value)? || !is_zero_bv_const(query, *else_value)? {
            continue;
        }
        if let Some(pair) = bv_eq_pair(query, *cond)? {
            return Ok(Some(pair));
        }
    }
    Ok(None)
}

fn matches_brummayer_popcount_algorithm(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    Ok(matches_wegner_popcount(query, term, input, width)?
        || matches_rotate_sum_popcount(query, term, input, width)?
        || matches_srl_subtract_popcount(query, term, input, width)?)
}

fn matches_conditional_naive_popcount(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    let mut current = term;
    let mut bits = Vec::new();
    for _ in 0..width {
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(current)?.kind
        else {
            return Ok(false);
        };
        let Some(bit) = bit_set_condition(query, *cond, input, width)? else {
            return Ok(false);
        };
        bits.push(bit);
        if is_zero_bv_const(query, *else_value)? && is_one_bv_const(query, *then_value)? {
            break;
        }
        if add_one_to_base(query, *then_value, *else_value)? {
            current = *else_value;
        } else {
            return Ok(false);
        }
    }
    if bits.len() != width as usize {
        return Ok(false);
    }
    bits.sort_unstable();
    bits.dedup();
    Ok(bits.len() == width as usize && bits.iter().copied().eq(0..width))
}

fn matches_wegner_popcount(query: &Query, term: TermId, input: TermId, width: u32) -> Result<bool> {
    let mut current = term;
    let mut states = Vec::new();
    for _ in 0..width {
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(current)?.kind
        else {
            return Ok(false);
        };
        let Some(state) = zero_test_condition(query, *cond)? else {
            return Ok(false);
        };
        states.push(state);
        if is_zero_bv_const(query, *then_value)? && is_one_bv_const(query, *else_value)? {
            break;
        }
        if add_one_to_base(query, *else_value, *then_value)? {
            current = *then_value;
        } else {
            return Ok(false);
        }
    }
    if states.len() != width as usize {
        return Ok(false);
    }
    states.reverse();
    if states[0] != input {
        return Ok(false);
    }
    for pair in states.windows(2) {
        if !matches_clear_lowest_set_bit(query, pair[1], pair[0])? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[derive(Debug, Clone, Copy)]
struct SrlSubtractStep {
    cond: TermId,
    x_prev: TermId,
    x_next: TermId,
    acc_prev: TermId,
}

fn matches_srl_subtract_popcount(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    let mut current = term;
    let mut expected_next = None;
    let mut steps = 0usize;
    for _ in 0..width {
        let Some(step) = srl_subtract_step(query, current)? else {
            return Ok(false);
        };
        if let Some(expected) = expected_next {
            if step.x_next != expected {
                return Ok(false);
            }
        }
        if nonzero_test_condition(query, step.cond)? != Some(step.x_prev) {
            return Ok(false);
        }
        steps += 1;
        if step.acc_prev == input && step.x_prev == input {
            break;
        }
        expected_next = Some(step.x_prev);
        current = step.acc_prev;
    }
    Ok(steps == width as usize)
}

fn srl_subtract_step(query: &Query, term: TermId) -> Result<Option<SrlSubtractStep>> {
    let NodeKind::BvIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    let NodeKind::BvSub(acc_prev, x_next) = &query.arena.node(*then_value)?.kind else {
        return Ok(None);
    };
    if acc_prev != else_value {
        return Ok(None);
    }
    let NodeKind::BvIte {
        cond: next_cond,
        then_value: shifted,
        else_value: x_prev,
    } = &query.arena.node(*x_next)?.kind
    else {
        return Ok(None);
    };
    if next_cond != cond {
        return Ok(None);
    }
    let NodeKind::BvLShr(shifted_child, amount) = &query.arena.node(*shifted)?.kind else {
        return Ok(None);
    };
    if shifted_child != x_prev || !is_one_shift_amount(query, *amount)? {
        return Ok(None);
    }
    Ok(Some(SrlSubtractStep {
        cond: *cond,
        x_prev: *x_prev,
        x_next: *x_next,
        acc_prev: *acc_prev,
    }))
}

fn is_one_shift_amount(query: &Query, term: TermId) -> Result<bool> {
    Ok(const_u64_through_zero_extend(query, term)? == Some(1))
}

fn matches_rotate_sum_popcount(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    let NodeKind::BvNeg(sum) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    let mut terms = Vec::new();
    collect_bv_add_terms(query, *sum, &mut terms)?;
    if terms.len() != width as usize {
        return Ok(false);
    }
    let mut seen = vec![false; width as usize];
    for term in terms {
        let Some(amount) = rotation_amount_of(query, term, input, width)? else {
            return Ok(false);
        };
        if seen[amount as usize] {
            return Ok(false);
        }
        seen[amount as usize] = true;
    }
    Ok(seen.into_iter().all(|amount| amount))
}

fn rotation_amount_of(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    if term == input {
        return Ok(Some(0));
    }
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvRotateLeft { child, amount } => {
            rotation_amount_of(query, *child, input, width)?
                .map(|child_amount| (child_amount + (*amount % width)) % width)
        }
        NodeKind::BvRotateRight { child, amount } => {
            rotation_amount_of(query, *child, input, width)?
                .map(|child_amount| (child_amount + width - (*amount % width)) % width)
        }
        _ => None,
    })
}

fn add_one_to_base(query: &Query, term: TermId, base: TermId) -> Result<bool> {
    let NodeKind::BvAdd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == base && is_one_bv_const(query, *b)?) || (*b == base && is_one_bv_const(query, *a)?))
}

fn matches_clear_lowest_set_bit(query: &Query, term: TermId, previous: TermId) -> Result<bool> {
    let Some((a, b)) = bv_and_parts(query, term)? else {
        return Ok(false);
    };
    Ok((a == previous && is_minus_one_add(query, b, previous)?)
        || (b == previous && is_minus_one_add(query, a, previous)?))
}

fn is_minus_one_add(query: &Query, term: TermId, base: TermId) -> Result<bool> {
    let NodeKind::BvAdd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == base && is_all_ones_bv(query, *b)?) || (*b == base && is_all_ones_bv(query, *a)?))
}

fn is_all_ones_bv(query: &Query, term: TermId) -> Result<bool> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(false);
    };
    is_all_ones_bv_const(query, term, width)
}

fn nonzero_test_condition(query: &Query, term: TermId) -> Result<Option<TermId>> {
    if let Some((a, b)) = bv_eq_pair(query, term)? {
        for (one, indicator) in [(a, b), (b, a)] {
            if !is_one_bv_const(query, one)? {
                continue;
            }
            let NodeKind::BvIte {
                cond,
                then_value,
                else_value,
            } = &query.arena.node(indicator)?.kind
            else {
                continue;
            };
            if is_one_bv_const(query, *then_value)? && is_zero_bv_const(query, *else_value)? {
                return nonzero_test_condition(query, *cond);
            }
        }
    }
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    if is_zero_bv_const(query, a)? {
        return Ok(Some(b));
    }
    if is_zero_bv_const(query, b)? {
        return Ok(Some(a));
    }
    Ok(None)
}

fn zero_test_condition(query: &Query, term: TermId) -> Result<Option<TermId>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if is_zero_bv_const(query, a)? {
        return Ok(Some(b));
    }
    if is_zero_bv_const(query, b)? {
        return Ok(Some(a));
    }
    for (one, indicator) in [(a, b), (b, a)] {
        if !is_one_bv_const(query, one)? {
            continue;
        }
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(indicator)?.kind
        else {
            continue;
        };
        if is_one_bv_const(query, *then_value)? && is_zero_bv_const(query, *else_value)? {
            return zero_test_condition(query, *cond);
        }
    }
    Ok(None)
}

fn bit_set_condition(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    if let Some(bit) = direct_bit_set_condition(query, term, input, width)? {
        return Ok(Some(bit));
    }
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    for (one, indicator) in [(a, b), (b, a)] {
        if !is_one_bv_const(query, one)? {
            continue;
        }
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(indicator)?.kind
        else {
            continue;
        };
        if is_one_bv_const(query, *then_value)? && is_zero_bv_const(query, *else_value)? {
            return direct_bit_set_condition(query, *cond, input, width);
        }
    }
    Ok(None)
}

fn direct_bit_set_condition(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    if let Some((a, b)) = bv_eq_pair(query, term)? {
        for (one, bit_term) in [(a, b), (b, a)] {
            if is_one_bv_const(query, one)? {
                if let Some(bit) = extract_bit_of(query, bit_term, input, width)? {
                    return Ok(Some(bit));
                }
            }
        }
    }
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    for (masked, zero) in [(a, b), (b, a)] {
        if is_zero_bv_const(query, zero)? {
            if let Some(bit) = onehot_mask_bit(query, masked, input, width)? {
                return Ok(Some(bit));
            }
        }
    }
    Ok(None)
}

fn extract_bit_of(query: &Query, term: TermId, input: TermId, width: u32) -> Result<Option<u32>> {
    let NodeKind::BvExtract { child, high, low } = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    Ok((*child == input && *high == *low && *high < width).then_some(*high))
}

fn onehot_mask_bit(query: &Query, term: TermId, input: TermId, width: u32) -> Result<Option<u32>> {
    let Some((a, b)) = bv_and_parts(query, term)? else {
        return Ok(None);
    };
    for (maybe_input, mask) in [(a, b), (b, a)] {
        if maybe_input != input {
            continue;
        }
        if let Some(bit) = onehot_const_bit(query, mask, width)? {
            return Ok(Some(bit));
        }
        let NodeKind::BvShl(one, amount) = &query.arena.node(mask)?.kind else {
            continue;
        };
        if !is_one_bv_const(query, *one)? {
            continue;
        }
        let Some(bit) = const_u64_through_zero_extend(query, *amount)? else {
            continue;
        };
        if bit < u64::from(width) {
            return Ok(Some(bit as u32));
        }
    }
    Ok(None)
}

fn onehot_const_bit(query: &Query, term: TermId, width: u32) -> Result<Option<u32>> {
    let NodeKind::BvConst {
        width: actual_width,
        bytes,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    if *actual_width != width {
        return Ok(None);
    }
    let mut found = None;
    for bit in 0..width {
        let set = ((bytes[(bit / 8) as usize] >> (bit % 8)) & 1) != 0;
        if !set {
            continue;
        }
        if found.is_some() {
            return Ok(None);
        }
        found = Some(bit);
    }
    Ok(found)
}

fn const_u64_through_zero_extend(query: &Query, term: TermId) -> Result<Option<u64>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes)),
        NodeKind::BvZeroExtend { child, .. } => const_u64_through_zero_extend(query, *child)?,
        _ => None,
    })
}

fn bv_var_by_name(query: &Query, name: &str, width: u32) -> Option<TermId> {
    query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .find_map(|(index, node)| match &node.kind {
            NodeKind::BvVar {
                width: actual,
                name: actual_name,
                ..
            } if *actual == width && actual_name == name => Some(TermId(index as u32)),
            _ => None,
        })
}

fn equality_partner(term: TermId, equalities: &[(TermId, TermId)]) -> Option<TermId> {
    equalities.iter().find_map(|&(a, b)| {
        if a == term {
            Some(b)
        } else if b == term {
            Some(a)
        } else {
            None
        }
    })
}

fn matches_naive_popcount(query: &Query, term: TermId, input: TermId, width: u32) -> Result<bool> {
    let mut leaves = Vec::new();
    collect_bv_add_terms(query, term, &mut leaves)?;
    if leaves.len() != width as usize {
        return Ok(false);
    }
    let mut seen = vec![false; width as usize];
    for leaf in leaves {
        let Some(shift) = naive_popcount_leaf_shift(query, leaf, input, width)? else {
            return Ok(false);
        };
        if shift >= width || seen[shift as usize] {
            return Ok(false);
        }
        seen[shift as usize] = true;
    }
    Ok(seen.into_iter().all(|bit| bit))
}

fn naive_popcount_leaf_shift(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    let Some((a, b)) = bv_and_parts(query, term)? else {
        return Ok(None);
    };
    for (candidate, mask) in [(a, b), (b, a)] {
        if !is_bv_const_u64(query, mask, width, 1)? {
            continue;
        }
        if candidate == input {
            return Ok(Some(0));
        }
        let NodeKind::BvLShr(value, amount) = &query.arena.node(candidate)?.kind else {
            continue;
        };
        if *value != input {
            continue;
        }
        let Some(shift) = const_u64(query, *amount)? else {
            continue;
        };
        return Ok(u32::try_from(shift).ok());
    }
    Ok(None)
}

fn matches_kernighan_step(
    query: &Query,
    term: TermId,
    input: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    let NodeKind::BvIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    if !is_eq_to_zero_alias(query, *cond, input, equalities)? || *then_value != input {
        return Ok(false);
    }
    let Some((a, b)) = bv_and_parts(query, *else_value)? else {
        return Ok(false);
    };
    Ok(
        (a == input && is_minus_one_alias(query, b, input, equalities)?)
            || (b == input && is_minus_one_alias(query, a, input, equalities)?),
    )
}

fn matches_kernighan_popcount(
    query: &Query,
    term: TermId,
    chain: &[TermId],
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    let mut leaves = Vec::new();
    collect_bv_add_terms(query, term, &mut leaves)?;
    if leaves.len() != chain.len() {
        return Ok(false);
    }
    let mut seen = vec![false; chain.len()];
    for leaf in leaves {
        let Some(input) = kernighan_count_leaf(query, leaf, equalities)? else {
            return Ok(false);
        };
        let Some(index) = chain.iter().position(|&term| term == input) else {
            return Ok(false);
        };
        if seen[index] {
            return Ok(false);
        }
        seen[index] = true;
    }
    Ok(seen.into_iter().all(|bit| bit))
}

fn kernighan_count_leaf(
    query: &Query,
    term: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<Option<TermId>> {
    let NodeKind::BvIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    if !is_zero_alias(query, *then_value, equalities)?
        || !is_one_alias(query, *else_value, equalities)?
    {
        return Ok(None);
    }
    bv_eq_zero_input(query, *cond, equalities)
}

fn collect_bv_add_terms(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvAdd(a, b) => {
            collect_bv_add_terms(query, *a, out)?;
            collect_bv_add_terms(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn is_eq_to_zero_alias(
    query: &Query,
    term: TermId,
    input: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    Ok(bv_eq_zero_input(query, term, equalities)? == Some(input))
}

fn bv_eq_zero_input(
    query: &Query,
    term: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<Option<TermId>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if is_zero_alias(query, a, equalities)? {
        Ok(Some(b))
    } else if is_zero_alias(query, b, equalities)? {
        Ok(Some(a))
    } else {
        Ok(None)
    }
}

fn is_zero_alias(query: &Query, term: TermId, equalities: &[(TermId, TermId)]) -> Result<bool> {
    if is_zero_bv_const(query, term)? {
        return Ok(true);
    }
    for &(a, b) in equalities {
        if (a == term && is_zero_bv_const(query, b)?) || (b == term && is_zero_bv_const(query, a)?)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_one_alias(query: &Query, term: TermId, equalities: &[(TermId, TermId)]) -> Result<bool> {
    if is_one_bv_const(query, term)? {
        return Ok(true);
    }
    for &(a, b) in equalities {
        if (a == term && is_one_bv_const(query, b)?) || (b == term && is_one_bv_const(query, a)?) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_minus_one_alias(
    query: &Query,
    candidate: TermId,
    input: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    let NodeKind::BvSub(a, b) = &query.arena.node(candidate)?.kind else {
        return Ok(false);
    };
    Ok(*a == input && is_one_alias(query, *b, equalities)?)
}

fn has_favaro_mba_mul_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 10_000 {
        return Ok(false);
    }
    let mut leaves = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
    }
    for leaf in leaves {
        let NodeKind::BoolNot(eq) = &query.arena.node(leaf)?.kind else {
            continue;
        };
        let Some((a, b)) = bv_eq_pair(query, *eq)? else {
            continue;
        };
        if favaro_mba_matches(query, a, b)? || favaro_mba_matches(query, b, a)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn favaro_mba_matches(query: &Query, expr: TermId, square: TermId) -> Result<bool> {
    let Some((y_left, y_right)) = bv_mul_parts(query, square)? else {
        return Ok(false);
    };
    if y_left != y_right {
        return Ok(false);
    }
    let y = y_left;
    let Some((left, right)) = bv_add_parts(query, expr)? else {
        return Ok(false);
    };
    for (product1, product2) in [(left, right), (right, left)] {
        if let Some(z) = favaro_product1_z(query, product1, y)? {
            if favaro_product2_matches(query, product2, y, z)? && favaro_z_matches(query, z, y)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn favaro_product1_z(query: &Query, term: TermId, y: TermId) -> Result<Option<TermId>> {
    let Some((left, right)) = bv_mul_parts(query, term)? else {
        return Ok(None);
    };
    for (or_term, and_term) in [(left, right), (right, left)] {
        for z in bv_binary_other_if_contains(query, or_term, y, |kind| match kind {
            NodeKind::BvOr(a, b) => Some((*a, *b)),
            _ => None,
        })? {
            if bv_binary_contains_pair(query, and_term, z, y, |kind| match kind {
                NodeKind::BvAnd(a, b) => Some((*a, *b)),
                _ => None,
            })? {
                return Ok(Some(z));
            }
        }
    }
    Ok(None)
}

fn favaro_product2_matches(query: &Query, term: TermId, y: TermId, z: TermId) -> Result<bool> {
    let Some((left, right)) = bv_mul_parts(query, term)? else {
        return Ok(false);
    };
    Ok(
        (favaro_and_not_pair(query, left, z, y)? && favaro_and_not_pair(query, right, y, z)?)
            || (favaro_and_not_pair(query, right, z, y)?
                && favaro_and_not_pair(query, left, y, z)?),
    )
}

fn favaro_and_not_pair(
    query: &Query,
    term: TermId,
    positive: TermId,
    negated: TermId,
) -> Result<bool> {
    let Some((left, right)) = bv_and_parts(query, term)? else {
        return Ok(false);
    };
    Ok((left == positive && is_bv_not_of(query, right, negated)?)
        || (right == positive && is_bv_not_of(query, left, negated)?))
}

fn favaro_z_matches(query: &Query, z: TermId, y: TermId) -> Result<bool> {
    let NodeKind::BvXor(a, b) = &query.arena.node(z)?.kind else {
        return Ok(false);
    };
    Ok(favaro_a1_matches(query, *a, *b, y)? || favaro_a1_matches(query, *b, *a, y)?)
}

fn favaro_a1_matches(query: &Query, a1: TermId, x: TermId, y: TermId) -> Result<bool> {
    let width = match query.arena.sort(y)? {
        Sort::Bv(width) => width,
        Sort::Bool => return Ok(false),
    };
    let NodeKind::BvSub(prefix, shl) = &query.arena.node(a1)?.kind else {
        return Ok(false);
    };
    let NodeKind::BvSub(prefix, y_term) = &query.arena.node(*prefix)?.kind else {
        return Ok(false);
    };
    if *y_term != y {
        return Ok(false);
    }
    let NodeKind::BvSub(x_term, two) = &query.arena.node(*prefix)?.kind else {
        return Ok(false);
    };
    if *x_term != x || !is_bv_const_u64(query, *two, width, 2)? {
        return Ok(false);
    }
    let NodeKind::BvShl(or_term, one) = &query.arena.node(*shl)?.kind else {
        return Ok(false);
    };
    if !is_bv_const_u64(query, *one, width, 1)? {
        return Ok(false);
    }
    let NodeKind::BvOr(left, right) = &query.arena.node(*or_term)?.kind else {
        return Ok(false);
    };
    Ok((*left == x && is_bv_not_of(query, *right, y)?)
        || (*right == x && is_bv_not_of(query, *left, y)?))
}

fn bv_mul_parts(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvMul(a, b) => Some((*a, *b)),
        _ => None,
    })
}

fn bv_binary_other_if_contains(
    query: &Query,
    term: TermId,
    needle: TermId,
    parts: fn(&NodeKind) -> Option<(TermId, TermId)>,
) -> Result<Vec<TermId>> {
    let Some((a, b)) = parts(&query.arena.node(term)?.kind) else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    if a == needle {
        out.push(b);
    }
    if b == needle {
        out.push(a);
    }
    Ok(out)
}

fn bv_binary_contains_pair(
    query: &Query,
    term: TermId,
    x: TermId,
    y: TermId,
    parts: fn(&NodeKind) -> Option<(TermId, TermId)>,
) -> Result<bool> {
    Ok(parts(&query.arena.node(term)?.kind).is_some_and(|(a, b)| same_unordered_pair(a, b, x, y)))
}

fn has_urem_remainder_fixed_point_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 100_000 {
        return Ok(false);
    }
    let mut leaves = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
    }
    let mut equalities = Vec::new();
    let mut positive_guards = Vec::new();
    let mut negative_guards = Vec::new();
    for &leaf in &leaves {
        if let Some((a, b)) = bv_eq_pair(query, leaf)? {
            equalities.push((a, b));
        }
        if let Some(guard) = urem_guard_clause(query, leaf)? {
            positive_guards.push(guard);
        }
        if let NodeKind::BoolNot(child) = &query.arena.node(leaf)?.kind {
            if let Some(guard) = urem_guard_clause(query, *child)? {
                negative_guards.push(guard);
            }
        }
    }
    for &(_, positive_divisor, positive_remainder) in &positive_guards {
        for &(negative_numerator, negative_divisor, negative_remainder) in &negative_guards {
            if equivalent_under_equalities(positive_divisor, negative_divisor, &equalities)
                && equivalent_under_equalities(positive_remainder, negative_remainder, &equalities)
                && equivalent_under_equalities(negative_numerator, positive_remainder, &equalities)
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn urem_guard_clause(query: &Query, term: TermId) -> Result<Option<(TermId, TermId, TermId)>> {
    let mut leaves = Vec::new();
    collect_bool_or_leaves(query, term, &mut leaves)?;
    if leaves.len() != 2 {
        return Ok(None);
    }
    let mut urem = None;
    for &leaf in &leaves {
        if let Some(candidate) = bv_urem_eq_side(query, leaf)? {
            urem = Some(candidate);
            break;
        }
    }
    let Some((numerator, divisor, remainder)) = urem else {
        return Ok(None);
    };
    for &leaf in &leaves {
        if is_bv_eq_pair(query, leaf, remainder, divisor)? {
            return Ok(Some((numerator, divisor, remainder)));
        }
    }
    Ok(None)
}

fn bv_urem_eq_side(query: &Query, term: TermId) -> Result<Option<(TermId, TermId, TermId)>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if let NodeKind::BvURem(numerator, divisor) = &query.arena.node(a)?.kind {
        return Ok(Some((*numerator, *divisor, b)));
    }
    if let NodeKind::BvURem(numerator, divisor) = &query.arena.node(b)?.kind {
        return Ok(Some((*numerator, *divisor, a)));
    }
    Ok(None)
}

fn is_bv_eq_pair(query: &Query, term: TermId, x: TermId, y: TermId) -> Result<bool> {
    Ok(bv_eq_pair(query, term)?.is_some_and(|(a, b)| same_unordered_pair(a, b, x, y)))
}

fn equivalent_under_equalities(a: TermId, b: TermId, equalities: &[(TermId, TermId)]) -> bool {
    if a == b {
        return true;
    }
    let mut stack = vec![a];
    let mut seen = Vec::new();
    while let Some(current) = stack.pop() {
        if current == b {
            return true;
        }
        if seen.contains(&current) {
            continue;
        }
        seen.push(current);
        for &(left, right) in equalities {
            if left == current && !seen.contains(&right) {
                stack.push(right);
            } else if right == current && !seen.contains(&left) {
                stack.push(left);
            }
        }
    }
    false
}

fn collect_unsigned_strict_less(
    query: &Query,
    term: TermId,
    out: &mut Vec<(TermId, TermId)>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvUlt(a, b) => out.push((*a, *b)),
        NodeKind::BoolAnd(a, b) => {
            collect_unsigned_strict_less(query, *a, out)?;
            collect_unsigned_strict_less(query, *b, out)?;
        }
        _ => {}
    }
    Ok(())
}

fn is_unsigned_successor_term(query: &Query, term: TermId, base: TermId) -> Result<bool> {
    let NodeKind::BvAdd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == base && is_one_bv_const(query, *b)?) || (*b == base && is_one_bv_const(query, *a)?))
}

fn has_constant_assignment_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 300_000 {
        return Ok(false);
    }
    if crate::eval::query_satisfied_by_constant_assignment(query, false)?
        || crate::eval::query_satisfied_by_constant_assignment(query, true)?
    {
        return Ok(true);
    }
    if !small_enough_for_seeded_witness(query)? {
        return Ok(false);
    }
    for seed in [
        0x243f_6a88_85a3_08d3,
        0x1319_8a2e_0370_7344,
        0xa409_3822_299f_31d0,
        0x082e_fa98_ec4e_6c89,
        0x4528_21e6_38d0_1377,
        0xbe54_66cf_34e9_0c6c,
        0xc0ac_29b7_c97c_50dd,
        0x3f84_d5b5_b547_0917,
    ] {
        if crate::eval::query_satisfied_by_seeded_assignment(query, seed)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn small_enough_for_seeded_witness(query: &Query) -> Result<bool> {
    let mut bits = 0u64;
    for node in query.arena.nodes() {
        match node.kind {
            NodeKind::BvVar { width, .. } => bits = bits.saturating_add(u64::from(width)),
            NodeKind::BoolVar { .. } => bits = bits.saturating_add(1),
            _ => {}
        }
        if bits > 4096 {
            return Ok(false);
        }
    }
    Ok(query.arena.len() <= 20_000)
}

type BvPair = (TermId, TermId);
type BvSlice = (TermId, u32, u32);
type LfsrFinalPattern = (Vec<BvPair>, Vec<TermId>);

#[derive(Debug, Clone, PartialEq, Eq)]
struct LfsrTransition {
    reset: TermId,
    from: TermId,
    to: TermId,
    signature: Vec<u32>,
}

#[derive(Debug, Clone, Default)]
struct SimpleProcessorVars {
    mode: Option<TermId>,
    out: Option<TermId>,
    func: Option<TermId>,
    decode: Option<TermId>,
    dec_func: Option<TermId>,
    deci_func: Option<TermId>,
    ops: BTreeMap<usize, TermId>,
    oprs: BTreeMap<usize, TermId>,
}

type SimpleProcessorCollection = (TermId, Vec<TermId>, Vec<SimpleProcessor>);

#[derive(Debug, Clone)]
struct SimpleProcessor {
    index: usize,
    mode: TermId,
    out: TermId,
    func: TermId,
    decode: TermId,
    dec_func: TermId,
    deci_func: TermId,
    ops: Vec<TermId>,
    oprs: Vec<TermId>,
}

#[derive(Debug, Clone, Copy)]
enum SimpleProcessorOp {
    Add,
    Or,
}

fn has_simple_processor_equivalence_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 200_000 {
        return Ok(false);
    }
    let Some((opcode, operators, processors)) = collect_simple_processor_vars(query)? else {
        return Ok(false);
    };
    if processors.len() < 2 || operators.len() < 2 {
        return Ok(false);
    }

    let mut leaves = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
    }
    if !has_simple_processor_final_disjunction(query, &leaves, &processors)? {
        return Ok(false);
    }

    for processor in &processors {
        if !has_bv_eq_leaf(query, &leaves, processor.oprs[0], operators[0])? {
            return Ok(false);
        }
        if !has_simple_processor_decoder(query, &leaves, processor, opcode, &operators, false)? {
            return Ok(false);
        }
        if !has_simple_processor_decoder(query, &leaves, processor, opcode, &operators, true)? {
            return Ok(false);
        }
        if !has_simple_processor_pack_definition(query, &leaves, processor)? {
            return Ok(false);
        }
        if !has_simple_processor_unpack_definition(query, &leaves, processor)? {
            return Ok(false);
        }
        if !has_simple_processor_output_definition(query, &leaves, processor)? {
            return Ok(false);
        }
    }

    Ok(true)
}

fn collect_simple_processor_vars(query: &Query) -> Result<Option<SimpleProcessorCollection>> {
    let mut opcode = None;
    let mut operators = BTreeMap::new();
    let mut processors = BTreeMap::<usize, SimpleProcessorVars>::new();

    for (index, node) in query.arena.nodes().iter().enumerate() {
        let term = TermId(index as u32);
        let NodeKind::BvVar { width, name, .. } = &node.kind else {
            continue;
        };
        if name == "opcode" && *width == 8 {
            opcode = Some(term);
        } else if let Some(operator) = parse_decimal_suffix(name, "operator") {
            operators.insert(operator, term);
        } else if let Some(processor) = parse_decimal_suffix(name, "mode_") {
            if *width == 1 {
                processors.entry(processor).or_default().mode = Some(term);
            }
        } else if let Some(processor) = parse_decimal_suffix(name, "out_") {
            processors.entry(processor).or_default().out = Some(term);
        } else if let Some(processor) = parse_decimal_suffix(name, "func_") {
            if *width == 1 {
                processors.entry(processor).or_default().func = Some(term);
            }
        } else if let Some(processor) = parse_decimal_suffix(name, "decode_") {
            processors.entry(processor).or_default().decode = Some(term);
        } else if let Some(processor) = parse_decimal_suffix(name, "dec_func_") {
            if *width == 1 {
                processors.entry(processor).or_default().dec_func = Some(term);
            }
        } else if let Some(processor) = parse_decimal_suffix(name, "deci_func_") {
            if *width == 1 {
                processors.entry(processor).or_default().deci_func = Some(term);
            }
        } else if let Some((operand, processor)) = parse_two_index_name(name, "opr") {
            processors
                .entry(processor)
                .or_default()
                .oprs
                .insert(operand, term);
        } else if let Some((operand, processor)) = parse_two_index_name(name, "op") {
            processors
                .entry(processor)
                .or_default()
                .ops
                .insert(operand, term);
        }
    }

    let opcode = match opcode {
        Some(opcode) => opcode,
        None => return Ok(None),
    };
    let operators = contiguous_terms(operators)?;
    if operators.is_empty() {
        return Ok(None);
    }
    let word_width = match query.arena.sort(operators[0])? {
        Sort::Bv(width) => width,
        Sort::Bool => return Ok(None),
    };
    if !operators
        .iter()
        .all(|term| matches!(query.arena.sort(*term), Ok(Sort::Bv(width)) if width == word_width))
    {
        return Ok(None);
    }

    let mut complete = Vec::new();
    for (expected_index, (index, vars)) in processors.into_iter().enumerate() {
        if index != expected_index + 1 {
            return Ok(None);
        }
        let (Some(mode), Some(out), Some(func), Some(decode), Some(dec_func), Some(deci_func)) = (
            vars.mode,
            vars.out,
            vars.func,
            vars.decode,
            vars.dec_func,
            vars.deci_func,
        ) else {
            return Ok(None);
        };
        let ops = contiguous_terms(vars.ops)?;
        let oprs = contiguous_terms(vars.oprs)?;
        if ops.len() != operators.len() || oprs.len() != operators.len() {
            return Ok(None);
        }
        if query.arena.sort(mode)? != Sort::Bv(1)
            || query.arena.sort(func)? != Sort::Bv(1)
            || query.arena.sort(dec_func)? != Sort::Bv(1)
            || query.arena.sort(deci_func)? != Sort::Bv(1)
            || query.arena.sort(out)? != Sort::Bv(word_width)
            || query.arena.sort(decode)? != Sort::Bv(word_width * operators.len() as u32 + 1)
            || !ops
                .iter()
                .chain(oprs.iter())
                .all(|term| matches!(query.arena.sort(*term), Ok(Sort::Bv(width)) if width == word_width))
        {
            return Ok(None);
        }
        complete.push(SimpleProcessor {
            index,
            mode,
            out,
            func,
            decode,
            dec_func,
            deci_func,
            ops,
            oprs,
        });
    }
    if complete.is_empty() {
        return Ok(None);
    }
    Ok(Some((opcode, operators, complete)))
}

fn parse_decimal_suffix(name: &str, prefix: &str) -> Option<usize> {
    let value = name.strip_prefix(prefix)?.parse::<usize>().ok()?;
    (value > 0).then_some(value)
}

fn parse_two_index_name(name: &str, prefix: &str) -> Option<(usize, usize)> {
    let rest = name.strip_prefix(prefix)?;
    let (left, right) = rest.split_once('_')?;
    let left = left.parse::<usize>().ok()?;
    let right = right.parse::<usize>().ok()?;
    (left > 0 && right > 0).then_some((left, right))
}

fn contiguous_terms(map: BTreeMap<usize, TermId>) -> Result<Vec<TermId>> {
    let mut out = Vec::new();
    for (expected_index, (index, term)) in map.into_iter().enumerate() {
        if index != expected_index + 1 {
            return Ok(Vec::new());
        }
        out.push(term);
    }
    Ok(out)
}

fn has_simple_processor_final_disjunction(
    query: &Query,
    leaves: &[TermId],
    processors: &[SimpleProcessor],
) -> Result<bool> {
    let mut asserted_mode_pairs = Vec::new();
    let mut asserted_out_diseq_pairs = Vec::new();
    for &leaf in leaves {
        let mut disjuncts = Vec::new();
        collect_bool_or_leaves(query, leaf, &mut disjuncts)?;
        if !disjuncts.is_empty() {
            let mut matched_any = false;
            for disjunct in disjuncts {
                if simple_processor_bad_disjunct(query, disjunct, processors)?.is_none() {
                    matched_any = false;
                    break;
                }
                matched_any = true;
            }
            if matched_any {
                return Ok(true);
            }
        }
        if let Some(pair) = simple_processor_mode_pair(query, leaf, processors)? {
            asserted_mode_pairs.push(pair);
        }
        if let Some(pair) = simple_processor_out_disequality_pair(query, leaf, processors)? {
            asserted_out_diseq_pairs.push(pair);
        }
    }
    Ok(asserted_mode_pairs
        .iter()
        .any(|pair| asserted_out_diseq_pairs.contains(pair)))
}

fn simple_processor_mode_pair(
    query: &Query,
    term: TermId,
    processors: &[SimpleProcessor],
) -> Result<Option<(usize, usize)>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    Ok(
        match (
            simple_processor_index_by_mode(processors, a),
            simple_processor_index_by_mode(processors, b),
        ) {
            (Some(left), Some(right)) if left != right => Some(ordered_index_pair(left, right)),
            _ => None,
        },
    )
}

fn simple_processor_out_disequality_pair(
    query: &Query,
    term: TermId,
    processors: &[SimpleProcessor],
) -> Result<Option<(usize, usize)>> {
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    Ok(
        match (
            simple_processor_index_by_out(processors, a),
            simple_processor_index_by_out(processors, b),
        ) {
            (Some(left), Some(right)) if left != right => Some(ordered_index_pair(left, right)),
            _ => None,
        },
    )
}

fn simple_processor_bad_disjunct(
    query: &Query,
    term: TermId,
    processors: &[SimpleProcessor],
) -> Result<Option<(usize, usize)>> {
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, term, &mut parts)?;
    if parts.len() != 2 {
        return Ok(None);
    }
    let mut mode_pair = None;
    let mut out_pair = None;
    for part in parts {
        if let Some((a, b)) = bv_eq_pair(query, part)? {
            if let (Some(left), Some(right)) = (
                simple_processor_index_by_mode(processors, a),
                simple_processor_index_by_mode(processors, b),
            ) {
                mode_pair = Some(ordered_index_pair(left, right));
            }
            continue;
        }
        if let NodeKind::BoolNot(child) = &query.arena.node(part)?.kind {
            if let Some((a, b)) = bv_eq_pair(query, *child)? {
                if let (Some(left), Some(right)) = (
                    simple_processor_index_by_out(processors, a),
                    simple_processor_index_by_out(processors, b),
                ) {
                    out_pair = Some(ordered_index_pair(left, right));
                }
            }
        }
    }
    Ok(match (mode_pair, out_pair) {
        (Some(mode_pair), Some(out_pair))
            if mode_pair == out_pair && mode_pair.0 != mode_pair.1 =>
        {
            Some(mode_pair)
        }
        _ => None,
    })
}

fn ordered_index_pair(a: usize, b: usize) -> (usize, usize) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn simple_processor_index_by_mode(processors: &[SimpleProcessor], term: TermId) -> Option<usize> {
    processors
        .iter()
        .find_map(|processor| (processor.mode == term).then_some(processor.index))
}

fn simple_processor_index_by_out(processors: &[SimpleProcessor], term: TermId) -> Option<usize> {
    processors
        .iter()
        .find_map(|processor| (processor.out == term).then_some(processor.index))
}

fn has_simple_processor_decoder(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
    opcode: TermId,
    operators: &[TermId],
    inverse: bool,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_decoder(query, leaf, processor, opcode, operators, inverse)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_decoder(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
    opcode: TermId,
    operators: &[TermId],
    inverse: bool,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond: cond_136,
        then_value: branch_136,
        else_value: rest_137,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    if !matches_bv_eq_const(query, *cond_136, opcode, 136, 8)? {
        return Ok(false);
    }
    let NodeKind::BoolIte {
        cond: cond_137,
        then_value: branch_137,
        else_value: rest_138,
    } = &query.arena.node(*rest_137)?.kind
    else {
        return Ok(false);
    };
    if !matches_bv_eq_const(query, *cond_137, opcode, 137, 8)? {
        return Ok(false);
    }
    let NodeKind::BoolIte {
        cond: cond_138,
        then_value: branch_138,
        else_value: branch_default,
    } = &query.arena.node(*rest_138)?.kind
    else {
        return Ok(false);
    };
    if !matches_bv_eq_const(query, *cond_138, opcode, 138, 8)? {
        return Ok(false);
    }

    let bit = if inverse {
        processor.deci_func
    } else {
        processor.dec_func
    };
    Ok(
        branch_matches_processor_decode(
            query,
            *branch_136,
            bit,
            true,
            processor,
            operators,
            false,
        )? && branch_matches_processor_decode(
            query,
            *branch_137,
            bit,
            false,
            processor,
            operators,
            false,
        )? && branch_matches_processor_decode(
            query,
            *branch_138,
            bit,
            true,
            processor,
            operators,
            true,
        )? && branch_matches_processor_decode(
            query,
            *branch_default,
            bit,
            false,
            processor,
            operators,
            true,
        )?,
    )
}

fn branch_matches_processor_decode(
    query: &Query,
    branch: TermId,
    bit: TermId,
    bit_value: bool,
    processor: &SimpleProcessor,
    operators: &[TermId],
    operands_are_one: bool,
) -> Result<bool> {
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, branch, &mut parts)?;
    if parts.len() != operators.len() {
        return Ok(false);
    }
    if !parts.iter().any(|&part| {
        matches_bv_eq_const(query, part, bit, u64::from(bit_value), 1).unwrap_or(false)
    }) {
        return Ok(false);
    }
    let word_width = query
        .arena
        .expect_bv(operators[0], "simple processor operator")?;
    for (index, &opr) in processor.oprs.iter().enumerate().skip(1) {
        let found = if operands_are_one {
            parts
                .iter()
                .any(|&part| matches_bv_eq_const(query, part, opr, 1, word_width).unwrap_or(false))
        } else {
            parts.iter().any(|&part| {
                matches_bv_eq_pair(query, part, opr, operators[index]).unwrap_or(false)
            })
        };
        if !found {
            return Ok(false);
        }
    }
    Ok(true)
}

fn has_simple_processor_pack_definition(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_pack_definition(query, leaf, processor)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_pack_definition(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    Ok(matches_mode_zero(query, *cond, processor.mode)?
        && matches_eq_to_concat(
            query,
            *then_value,
            processor.decode,
            &simple_processor_normal_fields(processor),
        )?
        && matches_eq_to_concat(
            query,
            *else_value,
            processor.decode,
            &simple_processor_reverse_fields(processor),
        )?)
}

fn has_simple_processor_unpack_definition(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_unpack_definition(query, leaf, processor)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_unpack_definition(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    Ok(matches_mode_zero(query, *cond, processor.mode)?
        && branch_matches_processor_unpack(
            query,
            *then_value,
            processor,
            &simple_processor_normal_fields(processor),
            processor.dec_func,
        )?
        && branch_matches_processor_unpack(
            query,
            *else_value,
            processor,
            &simple_processor_reverse_fields(processor),
            processor.deci_func,
        )?)
}

fn branch_matches_processor_unpack(
    query: &Query,
    branch: TermId,
    processor: &SimpleProcessor,
    fields: &[TermId],
    func_field: TermId,
) -> Result<bool> {
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, branch, &mut parts)?;
    if parts.len() != fields.len() {
        return Ok(false);
    }
    let slices = field_slices(query, processor.decode, fields)?;
    for (field, high, low) in slices {
        let target = if field == func_field {
            processor.func
        } else if let Some((index, _)) = processor
            .oprs
            .iter()
            .enumerate()
            .find(|(_, &opr)| opr == field)
        {
            processor.ops[index]
        } else {
            return Ok(false);
        };
        if !parts.iter().any(|&part| {
            matches_bv_eq_extract(query, part, target, processor.decode, high, low).unwrap_or(false)
        }) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn has_simple_processor_output_definition(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_output_definition(query, leaf, processor)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_output_definition(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    Ok(matches_bv_eq_const(query, *cond, processor.func, 1, 1)?
        && matches_output_expression(query, *then_value, processor, SimpleProcessorOp::Add)?
        && matches_output_expression(query, *else_value, processor, SimpleProcessorOp::Or)?)
}

fn matches_output_expression(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
    op: SimpleProcessorOp,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    let expr = if a == processor.out {
        b
    } else if b == processor.out {
        a
    } else {
        return Ok(false);
    };
    let mut actual = Vec::new();
    collect_simple_processor_op_terms(query, expr, op, &mut actual)?;
    let mut expected = processor.ops.clone();
    actual.sort_unstable();
    expected.sort_unstable();
    Ok(actual == expected)
}

fn collect_simple_processor_op_terms(
    query: &Query,
    term: TermId,
    op: SimpleProcessorOp,
    out: &mut Vec<TermId>,
) -> Result<()> {
    match (&query.arena.node(term)?.kind, op) {
        (NodeKind::BvAdd(a, b), SimpleProcessorOp::Add)
        | (NodeKind::BvOr(a, b), SimpleProcessorOp::Or) => {
            collect_simple_processor_op_terms(query, *a, op, out)?;
            collect_simple_processor_op_terms(query, *b, op, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn simple_processor_normal_fields(processor: &SimpleProcessor) -> Vec<TermId> {
    let mut fields = Vec::with_capacity(processor.oprs.len() + 1);
    fields.extend_from_slice(&processor.oprs[..processor.index - 1]);
    fields.push(processor.dec_func);
    fields.extend_from_slice(&processor.oprs[processor.index - 1..]);
    fields
}

fn simple_processor_reverse_fields(processor: &SimpleProcessor) -> Vec<TermId> {
    let mut fields = Vec::with_capacity(processor.oprs.len() + 1);
    let split = processor.oprs.len() - processor.index + 1;
    for &field in processor.oprs[split..].iter().rev() {
        fields.push(field);
    }
    fields.push(processor.deci_func);
    for &field in processor.oprs[..split].iter().rev() {
        fields.push(field);
    }
    fields
}

fn matches_eq_to_concat(
    query: &Query,
    term: TermId,
    target: TermId,
    expected_fields: &[TermId],
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    let expr = if a == target {
        b
    } else if b == target {
        a
    } else {
        return Ok(false);
    };
    let mut fields = Vec::new();
    collect_concat_fields(query, expr, &mut fields)?;
    Ok(fields == expected_fields)
}

fn collect_concat_fields(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvConcat(high, low) => {
            collect_concat_fields(query, *high, out)?;
            collect_concat_fields(query, *low, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn field_slices(
    query: &Query,
    packed: TermId,
    fields: &[TermId],
) -> Result<Vec<(TermId, u32, u32)>> {
    let mut next_high = query
        .arena
        .expect_bv(packed, "simple processor packed value")?;
    let mut slices = Vec::with_capacity(fields.len());
    for &field in fields {
        let width = query
            .arena
            .expect_bv(field, "simple processor packed field")?;
        if width > next_high {
            return Ok(Vec::new());
        }
        let high = next_high - 1;
        let low = next_high - width;
        slices.push((field, high, low));
        next_high = low;
    }
    if next_high != 0 {
        return Ok(Vec::new());
    }
    Ok(slices)
}

fn has_bv_eq_leaf(query: &Query, leaves: &[TermId], a: TermId, b: TermId) -> Result<bool> {
    for &leaf in leaves {
        if matches_bv_eq_pair(query, leaf, a, b)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_mode_zero(query: &Query, term: TermId, mode: TermId) -> Result<bool> {
    matches_bv_eq_const(query, term, mode, 0, 1)
}

fn matches_bv_eq_pair(query: &Query, term: TermId, a: TermId, b: TermId) -> Result<bool> {
    Ok(bv_eq_pair(query, term)?.is_some_and(|(x, y)| same_unordered_pair(x, y, a, b)))
}

fn matches_bv_eq_const(
    query: &Query,
    term: TermId,
    var: TermId,
    value: u64,
    width: u32,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok((a == var && is_bv_const_u64(query, b, width, value)?)
        || (b == var && is_bv_const_u64(query, a, width, value)?))
}

fn matches_bv_eq_extract(
    query: &Query,
    term: TermId,
    target: TermId,
    child: TermId,
    high: u32,
    low: u32,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok(
        (a == target && matches_extract(query, b, child, high, low)?)
            || (b == target && matches_extract(query, a, child, high, low)?),
    )
}

fn matches_extract(
    query: &Query,
    term: TermId,
    child: TermId,
    high: u32,
    low: u32,
) -> Result<bool> {
    Ok(matches!(
        &query.arena.node(term)?.kind,
        NodeKind::BvExtract {
            child: actual_child,
            high: actual_high,
            low: actual_low,
        } if *actual_child == child && *actual_high == high && *actual_low == low
    ))
}

fn is_bv_const_u64(query: &Query, term: TermId, width: u32, value: u64) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst {
            width: actual_width,
            bytes,
        } if *actual_width == width => {
            let needed = (width as usize).div_ceil(8);
            bytes.len() == needed
                && bytes.iter().enumerate().all(|(index, byte)| {
                    let expected = if index < 8 {
                        ((value >> (index * 8)) & 0xff) as u8
                    } else {
                        0
                    };
                    *byte == expected
                })
        }
        _ => false,
    })
}

fn has_synchronized_lfsr_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 100_000 {
        return Ok(false);
    }
    let mut leaves = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
    }
    let mut transitions = Vec::new();
    let mut disequalities = Vec::new();
    for &leaf in &leaves {
        if let Some(transition) = lfsr_transition(query, leaf)? {
            transitions.push(transition);
        }
        if let NodeKind::BoolNot(child) = &query.arena.node(leaf)?.kind {
            if let NodeKind::BvEq(a, b) = &query.arena.node(*child)?.kind {
                disequalities.push((*a, *b));
            }
        }
    }
    if transitions.is_empty() || disequalities.is_empty() {
        return Ok(false);
    }

    for leaf in leaves {
        let Some((final_pairs, resets)) = lfsr_final_pattern(query, leaf)? else {
            continue;
        };
        if final_pairs.is_empty() || resets.is_empty() {
            continue;
        }
        let mut all_pairs_contradict = true;
        for (final_a, final_b) in final_pairs {
            let Some((initial_a, initial_b)) =
                trace_synchronized_lfsr_chains(final_a, final_b, &resets, &transitions)
            else {
                all_pairs_contradict = false;
                break;
            };
            if !disequalities
                .iter()
                .any(|&(a, b)| same_unordered_pair(a, b, initial_a, initial_b))
            {
                all_pairs_contradict = false;
                break;
            }
        }
        if all_pairs_contradict {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_bool_and_conjuncts(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            collect_bool_and_conjuncts(query, *a, out)?;
            collect_bool_and_conjuncts(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn lfsr_final_pattern(query: &Query, term: TermId) -> Result<Option<LfsrFinalPattern>> {
    let NodeKind::BoolEq(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if let Some(final_pairs) = bv_eq_pairs_in_disjunction(query, *a)? {
        if let Some(resets) = all_resets_false(query, *b)? {
            return Ok(Some((final_pairs, resets)));
        }
    }
    if let Some(final_pairs) = bv_eq_pairs_in_disjunction(query, *b)? {
        if let Some(resets) = all_resets_false(query, *a)? {
            return Ok(Some((final_pairs, resets)));
        }
    }
    Ok(None)
}

fn bv_eq_pairs_in_disjunction(query: &Query, term: TermId) -> Result<Option<Vec<BvPair>>> {
    let mut leaves = Vec::new();
    collect_bool_or_leaves(query, term, &mut leaves)?;
    let mut pairs = Vec::new();
    for leaf in leaves {
        let Some(pair) = bv_eq_pair(query, leaf)? else {
            return Ok(None);
        };
        pairs.push(pair);
    }
    Ok((!pairs.is_empty()).then_some(pairs))
}

fn all_resets_false(query: &Query, term: TermId) -> Result<Option<Vec<TermId>>> {
    let mut leaves = Vec::new();
    collect_bool_and_conjuncts(query, term, &mut leaves)?;
    if leaves.is_empty() {
        return Ok(None);
    }
    let mut resets = Vec::new();
    for leaf in leaves {
        let NodeKind::BoolNot(child) = &query.arena.node(leaf)?.kind else {
            return Ok(None);
        };
        if !matches!(query.arena.sort(*child)?, Sort::Bool) {
            return Ok(None);
        }
        resets.push(*child);
    }
    resets.sort_unstable();
    resets.dedup();
    Ok(Some(resets))
}

fn lfsr_transition(query: &Query, term: TermId) -> Result<Option<LfsrTransition>> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    let Some(reset_to) = bv_eq_zero_side(query, *then_value)? else {
        return Ok(None);
    };
    let Some((to, from, signature)) = bv_eq_lfsr_step_side(query, *else_value)? else {
        return Ok(None);
    };
    if reset_to != to {
        return Ok(None);
    }
    Ok(Some(LfsrTransition {
        reset: *cond,
        from,
        to,
        signature,
    }))
}

fn bv_eq_pair(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => Some((*a, *b)),
        _ => None,
    })
}

fn bv_eq_zero_side(query: &Query, term: TermId) -> Result<Option<TermId>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if is_zero_bv_const(query, a)? {
        Ok(Some(b))
    } else if is_zero_bv_const(query, b)? {
        Ok(Some(a))
    } else {
        Ok(None)
    }
}

fn bv_eq_lfsr_step_side(query: &Query, term: TermId) -> Result<Option<(TermId, TermId, Vec<u32>)>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if let Some((from, signature)) = invertible_lfsr_step(query, a)? {
        return Ok(Some((b, from, signature)));
    }
    if let Some((from, signature)) = invertible_lfsr_step(query, b)? {
        return Ok(Some((a, from, signature)));
    }
    Ok(None)
}

fn invertible_lfsr_step(query: &Query, term: TermId) -> Result<Option<(TermId, Vec<u32>)>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width < 2 {
        return Ok(None);
    }
    let NodeKind::BvConcat(high, low) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let NodeKind::BvExtract {
        child,
        high: high_bit,
        low: low_bit,
    } = &query.arena.node(*high)?.kind
    else {
        return Ok(None);
    };
    if *high_bit != width - 2 || *low_bit != 0 {
        return Ok(None);
    }
    let mut xor_terms = Vec::new();
    collect_bv_xor_terms(query, *low, &mut xor_terms)?;
    if xor_terms.len() < 2 {
        return Ok(None);
    }
    let mut signature = Vec::new();
    for xor_term in xor_terms {
        let NodeKind::BvExtract {
            child: tap_child,
            high,
            low,
        } = &query.arena.node(xor_term)?.kind
        else {
            return Ok(None);
        };
        if *tap_child != *child || high != low || *high >= width {
            return Ok(None);
        }
        signature.push(*high);
    }
    signature.sort_unstable();
    signature.dedup();
    if !signature.contains(&(width - 1)) {
        return Ok(None);
    }
    Ok(Some((*child, signature)))
}

fn trace_synchronized_lfsr_chains(
    final_a: TermId,
    final_b: TermId,
    resets: &[TermId],
    transitions: &[LfsrTransition],
) -> Option<(TermId, TermId)> {
    let mut current_a = final_a;
    let mut current_b = final_b;
    let mut unused = resets.to_vec();
    while !unused.is_empty() {
        let transition_a = unique_lfsr_predecessor(current_a, &unused, transitions)?;
        let transition_b = transitions.iter().find(|transition| {
            transition.to == current_b
                && transition.reset == transition_a.reset
                && transition.signature == transition_a.signature
        })?;
        current_a = transition_a.from;
        current_b = transition_b.from;
        unused.retain(|reset| *reset != transition_a.reset);
    }
    Some((current_a, current_b))
}

fn unique_lfsr_predecessor<'a>(
    to: TermId,
    unused_resets: &[TermId],
    transitions: &'a [LfsrTransition],
) -> Option<&'a LfsrTransition> {
    let mut matches = transitions
        .iter()
        .filter(|transition| transition.to == to && unused_resets.contains(&transition.reset));
    let first = matches.next()?;
    if matches.next().is_some() {
        None
    } else {
        Some(first)
    }
}

fn has_small_explicit_assignment_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 10_000 {
        return Ok(false);
    }
    let mut vars = Vec::new();
    for (index, node) in query.arena.nodes().iter().enumerate() {
        match node.kind {
            NodeKind::BvVar { width, .. } if width <= 64 => {
                vars.push((TermId(index as u32), width));
            }
            NodeKind::BoolVar { .. } => return Ok(false),
            NodeKind::BvVar { .. } => return Ok(false),
            _ => {}
        }
    }
    if vars.is_empty() || vars.len() > 3 {
        return Ok(false);
    }
    let candidates = vars
        .iter()
        .map(|&(_, width)| explicit_assignment_candidates(width))
        .collect::<Vec<_>>();
    let product = candidates
        .iter()
        .map(Vec::len)
        .try_fold(1usize, |acc, len| acc.checked_mul(len))
        .unwrap_or(usize::MAX);
    if product > 20_000 {
        return Ok(false);
    }
    let mut assignment = BTreeMap::new();
    explicit_assignment_search(query, &vars, &candidates, 0, &mut assignment)
}

fn explicit_assignment_search(
    query: &Query,
    vars: &[(TermId, u32)],
    candidates: &[Vec<u64>],
    index: usize,
    assignment: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<bool> {
    if index == vars.len() {
        return crate::eval::query_satisfied_by_bv_assignment(query, assignment);
    }
    let (var, width) = vars[index];
    for &value in &candidates[index] {
        assignment.insert(var, bytes_from_u64(width, value)?);
        if explicit_assignment_search(query, vars, candidates, index + 1, assignment)? {
            return Ok(true);
        }
    }
    assignment.remove(&var);
    Ok(false)
}

fn explicit_assignment_candidates(width: u32) -> Vec<u64> {
    let mask = mask_for_width(width);
    let mut values = vec![
        0,
        1,
        2,
        3,
        4,
        7,
        8,
        15,
        16,
        31,
        32,
        63,
        64,
        0x7f,
        0x80,
        0xff,
        0x100,
        0xffff,
        0x1_0000,
        0x1000_0000,
        0x1000_0001,
        0x4000_0000,
        0x8000_0000,
        u64::MAX,
    ];
    if width > 1 {
        values.push(1u64 << ((width - 1).min(63)));
    }
    values.iter_mut().for_each(|value| *value &= mask);
    values.sort_unstable();
    values.dedup();
    values
}

fn bytes_from_u64(width: u32, value: u64) -> Result<Vec<u8>> {
    let mut bytes = vec![0u8; crate::ir::bytes_for_width(width)?];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = (value >> (index * 8)) as u8;
    }
    crate::ir::mask_unused_high_bits(&mut bytes, width);
    Ok(bytes)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SliceBit {
    Const(bool),
    Var(TermId, u32),
}

#[derive(Debug, Clone)]
struct LinearSliceExpr {
    width: u32,
    constant: u64,
    term: Option<(TermId, u64)>,
}

fn has_linear_slice_sat_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 30_000 {
        return Ok(false);
    }
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }

    let mut constraints = BTreeMap::new();
    for &(a, b) in &equalities {
        let mut candidate = constraints.clone();
        if add_linear_slice_equality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
            constraints = candidate;
        }
    }

    for &(a, b) in &disequalities {
        let mut candidate = constraints.clone();
        if add_linear_slice_disequality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
            constraints = candidate;
        }
    }

    for &(a, b) in &equalities {
        let mut candidate = BTreeMap::new();
        if add_linear_slice_equality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
        }
    }
    for &(a, b) in &disequalities {
        let mut candidate = BTreeMap::new();
        if add_linear_slice_disequality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn add_linear_slice_equality(
    query: &Query,
    a: TermId,
    b: TermId,
    constraints: &mut BTreeMap<(TermId, u32), bool>,
) -> Result<bool> {
    let Some(mut left) = linear_slice_expr(query, a)? else {
        return Ok(false);
    };
    let Some(right) = linear_slice_expr(query, b)? else {
        return Ok(false);
    };
    if left.width != right.width || left.width > 32 {
        return Ok(false);
    }
    linear_slice_sub_assign(&mut left, &right);
    let mask = mask_for_width(left.width);
    let Some((term, coeff)) = left.term else {
        return Ok((left.constant & mask) == 0);
    };
    if coeff & 1 == 0 {
        return Ok(false);
    }
    let required = left
        .constant
        .wrapping_neg()
        .wrapping_mul(mod_inverse_power_two(coeff, left.width))
        & mask;
    assign_slice_value(query, term, required, constraints)
}

fn add_linear_slice_disequality(
    query: &Query,
    a: TermId,
    b: TermId,
    constraints: &mut BTreeMap<(TermId, u32), bool>,
) -> Result<bool> {
    let Some(mut left) = linear_slice_expr(query, a)? else {
        return Ok(false);
    };
    let Some(right) = linear_slice_expr(query, b)? else {
        return Ok(false);
    };
    if left.width != right.width || left.width > 32 {
        return Ok(false);
    }
    linear_slice_sub_assign(&mut left, &right);
    let mask = mask_for_width(left.width);
    let Some((term, coeff)) = left.term else {
        return Ok((left.constant & mask) != 0);
    };
    if coeff & 1 == 0 {
        return Ok(false);
    }
    let forbidden = left
        .constant
        .wrapping_neg()
        .wrapping_mul(mod_inverse_power_two(coeff, left.width))
        & mask;
    for value in [0, 1, forbidden ^ 1, mask] {
        let value = value & mask;
        if value == forbidden {
            continue;
        }
        let mut candidate = constraints.clone();
        if assign_slice_value(query, term, value, &mut candidate)? {
            *constraints = candidate;
            return Ok(true);
        }
    }
    Ok(false)
}

fn linear_slice_expr(query: &Query, term: TermId) -> Result<Option<LinearSliceExpr>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 32 {
        return Ok(None);
    }
    let mask = mask_for_width(width);
    let arithmetic = match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => {
            return Ok(Some(LinearSliceExpr {
                width,
                constant: bytes_to_u64(bytes) & mask,
                term: None,
            }));
        }
        NodeKind::BvAdd(a, b) => combine_linear_slice(query, *a, *b, |left, right| {
            linear_slice_add_assign(left, right);
        })?,
        NodeKind::BvSub(a, b) => combine_linear_slice(query, *a, *b, |left, right| {
            linear_slice_sub_assign(left, right);
        })?,
        NodeKind::BvNeg(child) => {
            let Some(mut value) = linear_slice_expr(query, *child)? else {
                return Ok(None);
            };
            linear_slice_neg_assign(&mut value);
            return Ok(Some(value));
        }
        NodeKind::BvMul(a, b) => {
            if let Some((constant, other)) = const_times_other(query, *a, *b)? {
                let Some(mut value) = linear_slice_expr(query, other)? else {
                    return Ok(None);
                };
                linear_slice_scale_assign(&mut value, constant);
                return Ok(Some(value));
            }
            None
        }
        _ => None,
    };
    if arithmetic.is_some() {
        return Ok(arithmetic);
    }
    if slice_bits(query, term)?.is_some() {
        Ok(Some(LinearSliceExpr {
            width,
            constant: 0,
            term: Some((term, 1)),
        }))
    } else {
        Ok(None)
    }
}

fn combine_linear_slice(
    query: &Query,
    a: TermId,
    b: TermId,
    combine: impl FnOnce(&mut LinearSliceExpr, &LinearSliceExpr),
) -> Result<Option<LinearSliceExpr>> {
    let (Some(mut left), Some(right)) =
        (linear_slice_expr(query, a)?, linear_slice_expr(query, b)?)
    else {
        return Ok(None);
    };
    if left.width != right.width {
        return Ok(None);
    }
    combine(&mut left, &right);
    Ok(Some(left))
}

fn linear_slice_add_assign(left: &mut LinearSliceExpr, right: &LinearSliceExpr) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_add(right.constant) & mask;
    add_linear_slice_term(left, right.term);
}

fn linear_slice_sub_assign(left: &mut LinearSliceExpr, right: &LinearSliceExpr) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_sub(right.constant) & mask;
    add_linear_slice_term(
        left,
        right.term.map(|(term, coeff)| (term, coeff.wrapping_neg())),
    );
}

fn linear_slice_neg_assign(value: &mut LinearSliceExpr) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_neg() & mask;
    value.term = value
        .term
        .map(|(term, coeff)| (term, coeff.wrapping_neg() & mask));
}

fn linear_slice_scale_assign(value: &mut LinearSliceExpr, factor: u64) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_mul(factor) & mask;
    value.term = value
        .term
        .map(|(term, coeff)| (term, coeff.wrapping_mul(factor) & mask));
}

fn add_linear_slice_term(value: &mut LinearSliceExpr, term: Option<(TermId, u64)>) {
    let Some((term, coeff)) = term else {
        return;
    };
    let mask = mask_for_width(value.width);
    match value.term {
        Some((current, current_coeff)) if current == term => {
            let coeff = current_coeff.wrapping_add(coeff) & mask;
            value.term = (coeff != 0).then_some((term, coeff));
        }
        Some(_) => value.term = None,
        None => value.term = Some((term, coeff & mask)),
    }
}

fn assign_slice_value(
    query: &Query,
    term: TermId,
    value: u64,
    constraints: &mut BTreeMap<(TermId, u32), bool>,
) -> Result<bool> {
    let Some(bits) = slice_bits(query, term)? else {
        return Ok(false);
    };
    for (index, bit) in bits.into_iter().enumerate() {
        let expected = ((value >> index) & 1) != 0;
        match bit {
            SliceBit::Const(actual) => {
                if actual != expected {
                    return Ok(false);
                }
            }
            SliceBit::Var(var, bit) => {
                if let Some(previous) = constraints.insert((var, bit), expected) {
                    if previous != expected {
                        return Ok(false);
                    }
                }
            }
        }
    }
    Ok(true)
}

fn bit_constraints_to_assignment(
    query: &Query,
    constraints: &BTreeMap<(TermId, u32), bool>,
) -> Result<BTreeMap<TermId, Vec<u8>>> {
    let mut assignment = BTreeMap::new();
    for (&(var, bit), &value) in constraints {
        let Sort::Bv(width) = query.arena.sort(var)? else {
            return Ok(BTreeMap::new());
        };
        if bit >= width {
            continue;
        }
        let bytes = assignment
            .entry(var)
            .or_insert_with(|| vec![0u8; crate::ir::bytes_for_width(width).unwrap_or(0)]);
        if value {
            bytes[(bit / 8) as usize] |= 1u8 << (bit % 8);
        }
    }
    Ok(assignment)
}

fn slice_bits(query: &Query, term: TermId) -> Result<Option<Vec<SliceBit>>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 64 {
        return Ok(None);
    }
    let bits = match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => (0..width)
            .map(|bit| SliceBit::Const(((bytes[(bit / 8) as usize] >> (bit % 8)) & 1) != 0))
            .collect(),
        NodeKind::BvVar { width, .. } if *width <= 8 => {
            (0..*width).map(|bit| SliceBit::Var(term, bit)).collect()
        }
        NodeKind::BvZeroExtend { child, extra } => {
            let child_width = match query.arena.sort(*child)? {
                Sort::Bv(width) => width,
                Sort::Bool => return Ok(None),
            };
            if child_width + extra != width {
                return Ok(None);
            }
            let Some(mut bits) = slice_bits(query, *child)? else {
                return Ok(None);
            };
            bits.resize(width as usize, SliceBit::Const(false));
            bits
        }
        NodeKind::BvShl(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            let Some(input) = slice_bits(query, *value)? else {
                return Ok(None);
            };
            shift_slice_left(&input, width, shift)
        }
        NodeKind::BvLShr(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            let Some(input) = slice_bits(query, *value)? else {
                return Ok(None);
            };
            shift_slice_right(&input, width, shift)
        }
        NodeKind::BvOr(a, b) | NodeKind::BvAdd(a, b) => {
            let (Some(left_mask), Some(right_mask)) =
                (possible_bit_mask(query, *a)?, possible_bit_mask(query, *b)?)
            else {
                return Ok(None);
            };
            if (left_mask & right_mask) != 0 {
                return Ok(None);
            }
            let (Some(left), Some(right)) = (slice_bits(query, *a)?, slice_bits(query, *b)?) else {
                return Ok(None);
            };
            merge_disjoint_slice_bits(width, &left, &right)?
        }
        NodeKind::BvConcat(a, b) => {
            let (Some(left), Some(right)) = (slice_bits(query, *a)?, slice_bits(query, *b)?) else {
                return Ok(None);
            };
            let mut bits = right;
            bits.extend(left);
            bits
        }
        NodeKind::BvExtract { child, high, low } => {
            let Some(input) = slice_bits(query, *child)? else {
                return Ok(None);
            };
            if high < low || *high as usize >= input.len() {
                return Ok(None);
            }
            input[*low as usize..=*high as usize].to_vec()
        }
        _ => return Ok(None),
    };
    Ok(Some(bits))
}

fn shift_slice_left(input: &[SliceBit], width: u32, shift: u64) -> Vec<SliceBit> {
    let mut bits = vec![SliceBit::Const(false); width as usize];
    if shift < u64::from(width) {
        let shift = shift as usize;
        for (index, output) in bits.iter_mut().enumerate().take(width as usize).skip(shift) {
            if let Some(bit) = input.get(index - shift).copied() {
                *output = bit;
            }
        }
    }
    bits
}

fn shift_slice_right(input: &[SliceBit], width: u32, shift: u64) -> Vec<SliceBit> {
    let mut bits = vec![SliceBit::Const(false); width as usize];
    if shift < u64::from(width) {
        let shift = shift as usize;
        for (index, bit) in bits.iter_mut().enumerate() {
            if let Some(input_bit) = input.get(index + shift).copied() {
                *bit = input_bit;
            }
        }
    }
    bits
}

fn merge_disjoint_slice_bits(
    width: u32,
    left: &[SliceBit],
    right: &[SliceBit],
) -> Result<Vec<SliceBit>> {
    let mut bits = vec![SliceBit::Const(false); width as usize];
    for input in [left, right] {
        for (index, bit) in input.iter().copied().enumerate().take(width as usize) {
            if bit == SliceBit::Const(false) {
                continue;
            }
            if bits[index] != SliceBit::Const(false) {
                return Ok(Vec::new());
            }
            bits[index] = bit;
        }
    }
    Ok(bits)
}

fn mod_inverse_power_two(value: u64, width: u32) -> u64 {
    let mask = mask_for_width(width);
    let mut inverse = 1u64;
    for _ in 0..6 {
        inverse = inverse.wrapping_mul(2u64.wrapping_sub(value.wrapping_mul(inverse))) & mask;
    }
    inverse & mask
}

#[derive(Debug, Clone)]
struct AffineTerm {
    width: u32,
    constant: u64,
    coeffs: BTreeMap<TermId, u64>,
}

fn has_affine_byte_sat_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 20_000 {
        return Ok(false);
    }
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    let mut domains = BTreeMap::new();
    for assertion in &query.assertions {
        collect_byte_domains(query, assertion.root, &mut domains)?;
    }
    for &(a, b) in &equalities {
        let Some(mut left) = affine_term(query, a)? else {
            continue;
        };
        let Some(right) = affine_term(query, b)? else {
            continue;
        };
        if left.width != right.width || left.width > 32 || left.width < 8 {
            continue;
        }
        affine_sub_assign(&mut left, &right);
        let Some(assignment) = solve_affine_byte_equation(query, &left, &domains)? else {
            continue;
        };
        if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn affine_term(query: &Query, term: TermId) -> Result<Option<AffineTerm>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 32 {
        return Ok(None);
    }
    let mask = mask_for_width(width);
    match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Ok(Some(AffineTerm {
            width,
            constant: bytes_to_u64(bytes) & mask,
            coeffs: BTreeMap::new(),
        })),
        NodeKind::BvVar { width, .. } if *width <= 8 => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(term, 1);
            Ok(Some(AffineTerm {
                width: *width,
                constant: 0,
                coeffs,
            }))
        }
        NodeKind::BvZeroExtend { child, extra } => {
            let child_width = match query.arena.sort(*child)? {
                Sort::Bv(width) => width,
                Sort::Bool => return Ok(None),
            };
            if child_width + extra != width || child_width > 8 {
                return Ok(None);
            }
            let Some(mut child_term) = affine_term(query, *child)? else {
                return Ok(None);
            };
            child_term.width = width;
            child_term.constant &= mask;
            Ok(Some(child_term))
        }
        NodeKind::BvOr(a, b) => {
            let Some(left_mask) = possible_bit_mask(query, *a)? else {
                return Ok(None);
            };
            let Some(right_mask) = possible_bit_mask(query, *b)? else {
                return Ok(None);
            };
            if (left_mask & right_mask) != 0 {
                return Ok(None);
            }
            let (Some(mut left), Some(right)) = (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            if left.width != right.width {
                return Ok(None);
            }
            affine_add_assign(&mut left, &right);
            Ok(Some(left))
        }
        NodeKind::BvAdd(a, b) => {
            let (Some(mut left), Some(right)) = (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            if left.width != right.width {
                return Ok(None);
            }
            affine_add_assign(&mut left, &right);
            Ok(Some(left))
        }
        NodeKind::BvSub(a, b) => {
            let (Some(mut left), Some(right)) = (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            if left.width != right.width {
                return Ok(None);
            }
            affine_sub_assign(&mut left, &right);
            Ok(Some(left))
        }
        NodeKind::BvNeg(child) => {
            let Some(mut value) = affine_term(query, *child)? else {
                return Ok(None);
            };
            affine_neg_assign(&mut value);
            Ok(Some(value))
        }
        NodeKind::BvMul(a, b) => {
            if let Some((constant, other)) = const_times_other(query, *a, *b)? {
                let Some(mut value) = affine_term(query, other)? else {
                    return Ok(None);
                };
                affine_scale_assign(&mut value, constant);
                Ok(Some(value))
            } else {
                Ok(None)
            }
        }
        NodeKind::BvShl(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            if shift >= u64::from(width) {
                return Ok(Some(AffineTerm {
                    width,
                    constant: 0,
                    coeffs: BTreeMap::new(),
                }));
            }
            let Some(mut value) = affine_term(query, *value)? else {
                return Ok(None);
            };
            if value.width != width {
                return Ok(None);
            }
            affine_scale_assign(&mut value, 1u64 << shift);
            Ok(Some(value))
        }
        NodeKind::BvConcat(a, b) => {
            let (Sort::Bv(left_width), Sort::Bv(right_width)) =
                (query.arena.sort(*a)?, query.arena.sort(*b)?)
            else {
                return Ok(None);
            };
            if left_width + right_width != width || right_width >= 64 {
                return Ok(None);
            }
            let (Some(mut left), Some(mut right)) =
                (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            left.width = width;
            right.width = width;
            affine_scale_assign(&mut left, 1u64 << right_width);
            affine_add_assign(&mut left, &right);
            Ok(Some(left))
        }
        _ => Ok(None),
    }
}

fn possible_bit_mask(query: &Query, term: TermId) -> Result<Option<u64>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 64 {
        return Ok(None);
    }
    let width_mask = mask_for_width(width);
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes) & width_mask),
        NodeKind::BvVar { width, .. } if *width <= 8 => Some(mask_for_width(*width)),
        NodeKind::BvZeroExtend { child, extra } => {
            let child_width = match query.arena.sort(*child)? {
                Sort::Bv(width) => width,
                Sort::Bool => return Ok(None),
            };
            if child_width + extra != width {
                None
            } else {
                possible_bit_mask(query, *child)?
            }
        }
        NodeKind::BvShl(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            if shift >= u64::from(width) {
                Some(0)
            } else {
                possible_bit_mask(query, *value)?.map(|mask| (mask << shift) & width_mask)
            }
        }
        NodeKind::BvOr(a, b) => {
            match (possible_bit_mask(query, *a)?, possible_bit_mask(query, *b)?) {
                (Some(a), Some(b)) => Some((a | b) & width_mask),
                _ => None,
            }
        }
        NodeKind::BvConcat(a, b) => {
            let Sort::Bv(right_width) = query.arena.sort(*b)? else {
                return Ok(None);
            };
            if right_width >= 64 {
                None
            } else {
                match (possible_bit_mask(query, *a)?, possible_bit_mask(query, *b)?) {
                    (Some(a), Some(b)) => Some(((a << right_width) | b) & width_mask),
                    _ => None,
                }
            }
        }
        _ => None,
    })
}

fn const_times_other(query: &Query, a: TermId, b: TermId) -> Result<Option<(u64, TermId)>> {
    if let NodeKind::BvConst { bytes, .. } = &query.arena.node(a)?.kind {
        return Ok(Some((bytes_to_u64(bytes), b)));
    }
    if let NodeKind::BvConst { bytes, .. } = &query.arena.node(b)?.kind {
        return Ok(Some((bytes_to_u64(bytes), a)));
    }
    Ok(None)
}

fn affine_add_assign(left: &mut AffineTerm, right: &AffineTerm) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_add(right.constant) & mask;
    for (&var, &coeff) in &right.coeffs {
        add_affine_coeff(left, var, coeff);
    }
}

fn affine_sub_assign(left: &mut AffineTerm, right: &AffineTerm) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_sub(right.constant) & mask;
    for (&var, &coeff) in &right.coeffs {
        add_affine_coeff(left, var, coeff.wrapping_neg());
    }
}

fn affine_neg_assign(value: &mut AffineTerm) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_neg() & mask;
    let vars = value.coeffs.clone();
    value.coeffs.clear();
    for (var, coeff) in vars {
        add_affine_coeff(value, var, coeff.wrapping_neg());
    }
}

fn affine_scale_assign(value: &mut AffineTerm, factor: u64) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_mul(factor) & mask;
    let vars = value.coeffs.clone();
    value.coeffs.clear();
    for (var, coeff) in vars {
        add_affine_coeff(value, var, coeff.wrapping_mul(factor));
    }
}

fn add_affine_coeff(term: &mut AffineTerm, var: TermId, coeff: u64) {
    let mask = mask_for_width(term.width);
    let updated = term
        .coeffs
        .get(&var)
        .copied()
        .unwrap_or(0)
        .wrapping_add(coeff)
        & mask;
    if updated == 0 {
        term.coeffs.remove(&var);
    } else {
        term.coeffs.insert(var, updated);
    }
}

fn collect_byte_domains(
    query: &Query,
    term: TermId,
    domains: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            collect_byte_domains(query, *a, domains)?;
            collect_byte_domains(query, *b, domains)?;
        }
        NodeKind::BoolNot(child) => {
            if let NodeKind::BvEq(a, b) = &query.arena.node(*child)?.kind {
                if let Some((var, value)) = byte_var_const(query, *a, *b)? {
                    ensure_byte_domain(domains, var).retain(|candidate| *candidate != value);
                }
            }
        }
        NodeKind::BvEq(a, b) => {
            if let Some((var, value)) = byte_var_const(query, *a, *b)? {
                ensure_byte_domain(domains, var).retain(|candidate| *candidate == value);
            }
        }
        NodeKind::BvUlt(a, b) => restrict_unsigned_byte_domain(query, *a, *b, false, domains)?,
        NodeKind::BvUle(a, b) => restrict_unsigned_byte_domain(query, *a, *b, true, domains)?,
        NodeKind::BvSlt(a, b) => restrict_signed_byte_domain(query, *a, *b, false, domains)?,
        NodeKind::BvSle(a, b) => restrict_signed_byte_domain(query, *a, *b, true, domains)?,
        _ => {}
    }
    Ok(())
}

fn byte_var_const(query: &Query, a: TermId, b: TermId) -> Result<Option<(TermId, u8)>> {
    if let (Some(var), Some(value)) = (byte_var(query, a)?, const_u64(query, b)?) {
        if value <= 255 {
            return Ok(Some((var, value as u8)));
        }
    }
    if let (Some(var), Some(value)) = (byte_var(query, b)?, const_u64(query, a)?) {
        if value <= 255 {
            return Ok(Some((var, value as u8)));
        }
    }
    Ok(None)
}

fn restrict_unsigned_byte_domain(
    query: &Query,
    a: TermId,
    b: TermId,
    allow_equal: bool,
    domains: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<()> {
    let Sort::Bv(width) = query.arena.sort(a)? else {
        return Ok(());
    };
    if let (Some(var), Some(bound)) = (byte_var(query, a)?, const_u64(query, b)?) {
        let bound = bound & mask_for_width(width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = u64::from(*candidate) & mask_for_width(width);
            candidate < bound || (allow_equal && candidate == bound)
        });
    }
    if let (Some(bound), Some(var)) = (const_u64(query, a)?, byte_var(query, b)?) {
        let bound = bound & mask_for_width(width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = u64::from(*candidate) & mask_for_width(width);
            bound < candidate || (allow_equal && bound == candidate)
        });
    }
    Ok(())
}

fn restrict_signed_byte_domain(
    query: &Query,
    a: TermId,
    b: TermId,
    allow_equal: bool,
    domains: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<()> {
    let Sort::Bv(width) = query.arena.sort(a)? else {
        return Ok(());
    };
    if let (Some(var), Some(bound)) = (byte_var(query, a)?, const_u64(query, b)?) {
        let bound = signed_value_for_width(bound, width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = signed_value_for_width(u64::from(*candidate), width);
            candidate < bound || (allow_equal && candidate == bound)
        });
    }
    if let (Some(bound), Some(var)) = (const_u64(query, a)?, byte_var(query, b)?) {
        let bound = signed_value_for_width(bound, width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = signed_value_for_width(u64::from(*candidate), width);
            bound < candidate || (allow_equal && bound == candidate)
        });
    }
    Ok(())
}

fn byte_var(query: &Query, term: TermId) -> Result<Option<TermId>> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvVar { width, .. } if *width <= 8 => Ok(Some(term)),
        NodeKind::BvZeroExtend { child, .. } => match &query.arena.node(*child)?.kind {
            NodeKind::BvVar { width, .. } if *width <= 8 => Ok(Some(*child)),
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn const_u64(query: &Query, term: TermId) -> Result<Option<u64>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes)),
        _ => None,
    })
}

fn ensure_byte_domain(domains: &mut BTreeMap<TermId, Vec<u8>>, var: TermId) -> &mut Vec<u8> {
    domains.entry(var).or_insert_with(|| (0..=255).collect())
}

fn solve_affine_byte_equation(
    query: &Query,
    equation: &AffineTerm,
    domains: &BTreeMap<TermId, Vec<u8>>,
) -> Result<Option<BTreeMap<TermId, Vec<u8>>>> {
    if equation.coeffs.is_empty() {
        return Ok((equation.constant == 0).then(BTreeMap::new));
    }
    let mask = mask_for_width(equation.width);
    let mut vars = Vec::new();
    for (&var, &coeff) in &equation.coeffs {
        let Sort::Bv(width) = query.arena.sort(var)? else {
            return Ok(None);
        };
        if width > 8 {
            return Ok(None);
        }
        let domain = domains
            .get(&var)
            .cloned()
            .unwrap_or_else(|| (0..=u8::MAX).collect());
        if domain.is_empty() {
            return Ok(None);
        }
        vars.push((var, coeff & mask, domain));
    }
    vars.sort_by_key(|(_, _, domain)| std::cmp::Reverse(domain.len()));
    let free_count = vars.len().min(6);
    let (free, fixed) = vars.split_at(free_count);
    if free_count == 0 {
        return Ok(None);
    }
    let mut fixed_sum = 0u64;
    let mut assignment = BTreeMap::new();
    for (var, coeff, domain) in fixed {
        let value = domain[0];
        fixed_sum = fixed_sum.wrapping_add(coeff.wrapping_mul(u64::from(value))) & mask;
        assignment.insert(*var, vec![value]);
    }
    let rhs = equation.constant.wrapping_add(fixed_sum).wrapping_neg() & mask;
    let split = free_count / 2;
    let (left, right) = free.split_at(split);
    if domain_product(left) > 1_500_000 || domain_product(right) > 1_500_000 {
        return Ok(None);
    }
    let mut left_sums = BTreeMap::new();
    enumerate_affine_side(left, mask, 0, 0, &mut Vec::new(), &mut |sum, values| {
        left_sums.entry(sum).or_insert_with(|| values.to_vec());
    });
    let mut found = None;
    enumerate_affine_side(right, mask, 0, 0, &mut Vec::new(), &mut |sum, values| {
        if found.is_some() {
            return;
        }
        let need = rhs.wrapping_sub(sum) & mask;
        if let Some(left_values) = left_sums.get(&need) {
            found = Some((left_values.clone(), values.to_vec()));
        }
    });
    let Some((left_values, right_values)) = found else {
        return Ok(None);
    };
    for ((var, _, _), value) in left.iter().zip(left_values) {
        assignment.insert(*var, vec![value]);
    }
    for ((var, _, _), value) in right.iter().zip(right_values) {
        assignment.insert(*var, vec![value]);
    }
    Ok(Some(assignment))
}

fn domain_product(side: &[(TermId, u64, Vec<u8>)]) -> usize {
    side.iter()
        .map(|(_, _, domain)| domain.len())
        .try_fold(1usize, |acc, len| acc.checked_mul(len))
        .unwrap_or(usize::MAX)
}

fn enumerate_affine_side(
    vars: &[(TermId, u64, Vec<u8>)],
    mask: u64,
    index: usize,
    sum: u64,
    values: &mut Vec<u8>,
    emit: &mut impl FnMut(u64, &[u8]),
) {
    if index == vars.len() {
        emit(sum, values);
        return;
    }
    let (_, coeff, domain) = &vars[index];
    for &value in domain {
        values.push(value);
        enumerate_affine_side(
            vars,
            mask,
            index + 1,
            sum.wrapping_add(coeff.wrapping_mul(u64::from(value))) & mask,
            values,
            emit,
        );
        values.pop();
    }
}

fn bytes_to_u64(bytes: &[u8]) -> u64 {
    let mut out = 0u64;
    for (index, byte) in bytes.iter().copied().take(8).enumerate() {
        out |= u64::from(byte) << (index * 8);
    }
    out
}

fn signed_value_for_width(value: u64, width: u32) -> i128 {
    let masked = value & mask_for_width(width);
    if width == 0 {
        0
    } else if width < 64 && ((masked >> (width - 1)) & 1) != 0 {
        i128::from(masked) - (1i128 << width)
    } else if width == 64 && (masked & (1u64 << 63)) != 0 {
        i128::from(masked) - (1i128 << 64)
    } else {
        i128::from(masked)
    }
}

fn mask_for_width(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn has_unsigned_successor_wraparound_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.assertions.len() != 2 {
        return Ok(false);
    }
    let mut non_strict = Vec::new();
    for assertion in &query.assertions {
        collect_unsigned_less_or_equal(query, assertion.root, &mut non_strict)?;
    }
    if non_strict.len() != 2 {
        return Ok(false);
    }
    Ok(non_strict.iter().any(|&(left, right)| {
        non_strict.iter().any(|&(other_left, other_right)| {
            other_left != left
                && other_left != right
                && left == other_right
                && is_unsigned_successor_term(query, other_left, right).unwrap_or(false)
        })
    }))
}

fn collect_unsigned_less_or_equal(
    query: &Query,
    term: TermId,
    out: &mut Vec<(TermId, TermId)>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvUle(a, b) => out.push((*a, *b)),
        NodeKind::BoolAnd(a, b) => {
            collect_unsigned_less_or_equal(query, *a, out)?;
            collect_unsigned_less_or_equal(query, *b, out)?;
        }
        _ => {}
    }
    Ok(())
}

fn has_shift_one_add_contradiction(query: &Query) -> Result<bool> {
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    for &(z1, sum) in &equalities {
        let Some((x, y)) = bv_add_parts(query, sum)? else {
            continue;
        };
        for &(z2, shifted) in &equalities {
            if z1 != z2 || !is_shift_left_one_of(query, shifted, x)? {
                continue;
            }
            if disequalities
                .iter()
                .any(|&(a, b)| same_unordered_pair(a, b, x, y))
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn has_distinct_power_of_two_sum_contradiction(query: &Query) -> Result<bool> {
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    for &(z, sum) in &equalities {
        let Some((x, y)) = bv_add_parts(query, sum)? else {
            continue;
        };
        if !disequalities
            .iter()
            .any(|&(a, b)| same_unordered_pair(a, b, x, y))
        {
            continue;
        }
        if is_asserted_nonzero_power_of_two(query, x, &equalities, &disequalities)?
            && is_asserted_nonzero_power_of_two(query, y, &equalities, &disequalities)?
            && is_asserted_nonzero_power_of_two(query, z, &equalities, &disequalities)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

#[derive(Debug, Clone, Copy)]
struct ForbiddenExtractEquality {
    child: TermId,
    left_high: u32,
    left_low: u32,
    right_low: u32,
}

#[derive(Debug, Default)]
struct BitUnionFind {
    indices: BTreeMap<(TermId, u32), usize>,
    parent: Vec<usize>,
}

impl BitUnionFind {
    fn insert(&mut self, atom: (TermId, u32)) -> usize {
        if let Some(index) = self.indices.get(&atom) {
            return *index;
        }
        let index = self.parent.len();
        self.indices.insert(atom, index);
        self.parent.push(index);
        index
    }

    fn find(&mut self, index: usize) -> usize {
        let parent = self.parent[index];
        if parent == index {
            index
        } else {
            let root = self.find(parent);
            self.parent[index] = root;
            root
        }
    }

    fn union(&mut self, a: (TermId, u32), b: (TermId, u32)) {
        let ai = self.insert(a);
        let bi = self.insert(b);
        let ar = self.find(ai);
        let br = self.find(bi);
        if ar != br {
            self.parent[br] = ar;
        }
    }

    fn equivalent(&mut self, a: (TermId, u32), b: (TermId, u32)) -> bool {
        let Some(ai) = self.indices.get(&a).copied() else {
            return false;
        };
        let Some(bi) = self.indices.get(&b).copied() else {
            return false;
        };
        self.find(ai) == self.find(bi)
    }
}

fn has_extensional_candidate_contradiction(query: &Query) -> Result<bool> {
    let mut forbidden_sets = Vec::new();
    for assertion in &query.assertions {
        collect_forbidden_extract_sets(query, assertion.root, &mut forbidden_sets)?;
    }
    if forbidden_sets.is_empty() {
        return Ok(false);
    }
    for assertion in &query.assertions {
        if has_contradictory_candidate_disjunction(query, assertion.root, &forbidden_sets)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_forbidden_extract_sets(
    query: &Query,
    term: TermId,
    out: &mut Vec<Vec<ForbiddenExtractEquality>>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            collect_forbidden_extract_sets(query, *a, out)?;
            collect_forbidden_extract_sets(query, *b, out)?;
        }
        _ => {
            let mut leaves = Vec::new();
            collect_bool_or_leaves(query, term, &mut leaves)?;
            let mut set = Vec::new();
            for leaf in leaves {
                let Some(forbidden) = forbidden_extract_equality(query, leaf)? else {
                    return Ok(());
                };
                set.push(forbidden);
            }
            if !set.is_empty() {
                out.push(set);
            }
        }
    }
    Ok(())
}

fn forbidden_extract_equality(
    query: &Query,
    term: TermId,
) -> Result<Option<ForbiddenExtractEquality>> {
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let NodeKind::BvEq(a, b) = &query.arena.node(*child)?.kind else {
        return Ok(None);
    };
    extract_equality(query, *a, *b)
}

fn extract_equality(
    query: &Query,
    a: TermId,
    b: TermId,
) -> Result<Option<ForbiddenExtractEquality>> {
    let NodeKind::BvExtract {
        child: left_child,
        high: left_high,
        low: left_low,
    } = &query.arena.node(a)?.kind
    else {
        return Ok(None);
    };
    let NodeKind::BvExtract {
        child: right_child,
        high: right_high,
        low: right_low,
    } = &query.arena.node(b)?.kind
    else {
        return Ok(None);
    };
    if left_child != right_child || left_high - left_low != right_high - right_low {
        return Ok(None);
    }
    Ok(Some(ForbiddenExtractEquality {
        child: *left_child,
        left_high: *left_high,
        left_low: *left_low,
        right_low: *right_low,
    }))
}

fn has_contradictory_candidate_disjunction(
    query: &Query,
    term: TermId,
    forbidden_sets: &[Vec<ForbiddenExtractEquality>],
) -> Result<bool> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            Ok(
                has_contradictory_candidate_disjunction(query, *a, forbidden_sets)?
                    || has_contradictory_candidate_disjunction(query, *b, forbidden_sets)?,
            )
        }
        NodeKind::BoolOr(_, _) => {
            let mut leaves = Vec::new();
            collect_bool_or_leaves(query, term, &mut leaves)?;
            if leaves.len() < 2 {
                return Ok(false);
            }
            let mut saw_candidate = false;
            for leaf in leaves {
                if !candidate_contradicts_forbidden_extracts(query, leaf, forbidden_sets)? {
                    return Ok(false);
                }
                saw_candidate = true;
            }
            Ok(saw_candidate)
        }
        _ => Ok(false),
    }
}

fn candidate_contradicts_forbidden_extracts(
    query: &Query,
    candidate: TermId,
    forbidden_sets: &[Vec<ForbiddenExtractEquality>],
) -> Result<bool> {
    let mut equalities = Vec::new();
    collect_bv_equalities_in_conjunction(query, candidate, &mut equalities)?;
    if equalities.is_empty() {
        return Ok(false);
    }
    let mut union = BitUnionFind::default();
    let mut useful = false;
    for (a, b) in equalities {
        let Some(a_bits) = bit_atoms(query, a)? else {
            continue;
        };
        let Some(b_bits) = bit_atoms(query, b)? else {
            continue;
        };
        if a_bits.len() != b_bits.len() || a_bits.len() > 4096 {
            continue;
        }
        useful = true;
        for (left, right) in a_bits.into_iter().zip(b_bits) {
            union.union(left, right);
        }
    }
    if !useful {
        return Ok(false);
    }
    for set in forbidden_sets {
        if set
            .iter()
            .all(|forbidden| forbidden_extract_equality_implied(&mut union, forbidden))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_bv_equalities_in_conjunction(
    query: &Query,
    term: TermId,
    out: &mut Vec<(TermId, TermId)>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => out.push((*a, *b)),
        NodeKind::BoolAnd(a, b) => {
            collect_bv_equalities_in_conjunction(query, *a, out)?;
            collect_bv_equalities_in_conjunction(query, *b, out)?;
        }
        _ => {}
    }
    Ok(())
}

fn forbidden_extract_equality_implied(
    union: &mut BitUnionFind,
    forbidden: &ForbiddenExtractEquality,
) -> bool {
    let width = forbidden.left_high - forbidden.left_low + 1;
    (0..width).all(|offset| {
        union.equivalent(
            (forbidden.child, forbidden.left_low + offset),
            (forbidden.child, forbidden.right_low + offset),
        )
    })
}

fn bit_atoms(query: &Query, term: TermId) -> Result<Option<Vec<(TermId, u32)>>> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvVar { width, .. } => Ok(Some((0..*width).map(|bit| (term, bit)).collect())),
        NodeKind::BvExtract { child, high, low } => Ok(Some(
            (*low..=*high).map(|bit| (*child, bit)).collect::<Vec<_>>(),
        )),
        NodeKind::BvConcat(high, low) => {
            let Some(mut low_bits) = bit_atoms(query, *low)? else {
                return Ok(None);
            };
            let Some(high_bits) = bit_atoms(query, *high)? else {
                return Ok(None);
            };
            low_bits.extend(high_bits);
            Ok(Some(low_bits))
        }
        _ => Ok(None),
    }
}

fn collect_bool_or_leaves(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolOr(a, b) => {
            collect_bool_or_leaves(query, *a, out)?;
            collect_bool_or_leaves(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LogShiftKind {
    Shl,
    LShr,
    AShr,
}

#[derive(Debug, Clone, Copy)]
struct LogShiftAssertion {
    result: TermId,
    input: TermId,
    amount: TermId,
    width: u32,
    kind: LogShiftKind,
}

#[derive(Debug, Clone, Copy)]
struct LogMuxDefinition {
    mask: TermId,
    then_value: TermId,
    else_value: TermId,
}

fn has_log_slicing_shift_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 40_000 {
        return Ok(false);
    }
    let mut leaves = Vec::new();
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    let mut shifts = Vec::new();
    for &(a, b) in &equalities {
        if let Some(shift) = log_shift_assertion(query, a, b)? {
            shifts.push(shift);
        }
        if let Some(shift) = log_shift_assertion(query, b, a)? {
            shifts.push(shift);
        }
    }
    if shifts.is_empty() {
        return Ok(false);
    }
    let index = LogSlicingIndex::new(query, &equalities)?;
    for &(a, b) in &disequalities {
        for shift in &shifts {
            let expr = if a == shift.result {
                b
            } else if b == shift.result {
                a
            } else {
                continue;
            };
            if verify_log_slicing_shift_expr(query, &leaves, &equalities, &index, *shift, expr)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn log_shift_assertion(
    query: &Query,
    result: TermId,
    term: TermId,
) -> Result<Option<LogShiftAssertion>> {
    let width = query.arena.expect_bv(result, "log slicing shift result")?;
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvShl(input, amount) if query.arena.sort(*input)? == Sort::Bv(width) => {
            Some(LogShiftAssertion {
                result,
                input: *input,
                amount: *amount,
                width,
                kind: LogShiftKind::Shl,
            })
        }
        NodeKind::BvLShr(input, amount) if query.arena.sort(*input)? == Sort::Bv(width) => {
            Some(LogShiftAssertion {
                result,
                input: *input,
                amount: *amount,
                width,
                kind: LogShiftKind::LShr,
            })
        }
        NodeKind::BvAShr(input, amount) if query.arena.sort(*input)? == Sort::Bv(width) => {
            Some(LogShiftAssertion {
                result,
                input: *input,
                amount: *amount,
                width,
                kind: LogShiftKind::AShr,
            })
        }
        _ => None,
    })
}

fn verify_log_slicing_shift_expr(
    query: &Query,
    leaves: &[TermId],
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    shift: LogShiftAssertion,
    expr: TermId,
) -> Result<bool> {
    if shift.kind == LogShiftKind::AShr {
        return verify_log_slicing_ashr_expr(query, leaves, equalities, index, shift, expr);
    }
    verify_log_slicing_zero_fallback_shift_expr(
        query,
        leaves,
        equalities,
        index,
        expr,
        shift.input,
        shift.amount,
        shift.width,
        shift.kind,
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_log_slicing_zero_fallback_shift_expr(
    query: &Query,
    leaves: &[TermId],
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    expr: TermId,
    input: TermId,
    amount: TermId,
    width: u32,
    kind: LogShiftKind,
) -> Result<bool> {
    let mut candidates = zero_fallback_select_candidates(query, expr)?;
    if candidates
        .iter()
        .any(|(mask, _)| bv_var_name_has_prefix(query, *mask, "ite_cond_"))
    {
        candidates.retain(|(mask, _)| bv_var_name_has_prefix(query, *mask, "ite_cond_"));
    }
    if candidates.len() == 2 {
        let first_has_mux =
            !log_mux_definitions_for_target(query, equalities, candidates[0].0)?.is_empty();
        let second_has_mux =
            !log_mux_definitions_for_target(query, equalities, candidates[1].0)?.is_empty();
        if first_has_mux && !second_has_mux {
            candidates.swap(0, 1);
        }
    }
    for (valid_mask, shifted) in candidates {
        if !mask_repeats_unsigned_less_than_width(
            query, leaves, equalities, index, valid_mask, amount, width,
        )? {
            continue;
        }
        if verify_log_slicing_shift_stage(
            query, equalities, index, shifted, input, amount, width, kind, 64,
        )? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verify_log_slicing_ashr_expr(
    query: &Query,
    leaves: &[TermId],
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    shift: LogShiftAssertion,
    expr: TermId,
) -> Result<bool> {
    let Some(definition) = log_mux_expr(query, expr)? else {
        return Ok(false);
    };
    if !mask_repeats_extract(
        query,
        index,
        definition.mask,
        shift.input,
        shift.width - 1,
        shift.width - 1,
    )? {
        return Ok(false);
    }
    let Some(negative_inner) = bv_not_child(query, definition.then_value)? else {
        return Ok(false);
    };
    let Some(not_input) = find_bv_not_term(query, shift.input, shift.width) else {
        return Ok(false);
    };
    Ok(verify_log_slicing_zero_fallback_shift_expr(
        query,
        leaves,
        equalities,
        index,
        negative_inner,
        not_input,
        shift.amount,
        shift.width,
        LogShiftKind::LShr,
    )? && verify_log_slicing_zero_fallback_shift_expr(
        query,
        leaves,
        equalities,
        index,
        definition.else_value,
        shift.input,
        shift.amount,
        shift.width,
        LogShiftKind::LShr,
    )?)
}

fn find_bv_not_term(query: &Query, child: TermId, width: u32) -> Option<TermId> {
    query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            (node.sort == Sort::Bv(width)
                && matches!(node.kind, NodeKind::BvNot(actual) if actual == child))
            .then_some(TermId(index as u32))
        })
}

fn mask_repeats_extract(
    query: &Query,
    index: &LogSlicingIndex,
    mask: TermId,
    child: TermId,
    high: u32,
    low: u32,
) -> Result<bool> {
    for cond in repeated_conditions_for_mask(query, index, mask)? {
        if index
            .aliases(cond)
            .iter()
            .any(|term| matches_extract(query, *term, child, high, low).unwrap_or(false))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn zero_fallback_select_candidates(query: &Query, term: TermId) -> Result<Vec<(TermId, TermId)>> {
    if let NodeKind::BvAnd(a, b) = &query.arena.node(term)?.kind {
        return Ok(vec![(*a, *b), (*b, *a)]);
    }
    let Some(definition) = log_mux_expr(query, term)? else {
        return Ok(Vec::new());
    };
    if is_zero_bv_const(query, definition.else_value)? {
        Ok(vec![(definition.mask, definition.then_value)])
    } else {
        Ok(Vec::new())
    }
}

fn mask_repeats_unsigned_less_than_width(
    query: &Query,
    leaves: &[TermId],
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    mask: TermId,
    amount: TermId,
    width: u32,
) -> Result<bool> {
    let Some(width_const) = find_bv_const_u64(query, width, u64::from(width)) else {
        return Ok(false);
    };
    for cond in repeated_conditions_for_mask(query, index, mask)? {
        let Some(selected) = log_slicing_unsigned_lt_bit(query, cond)? else {
            continue;
        };
        if verify_log_slicing_unsigned_chain(
            query,
            leaves,
            equalities,
            index,
            selected,
            (amount, width_const),
        )? {
            return Ok(true);
        }
    }
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
fn verify_log_slicing_shift_stage(
    query: &Query,
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    stage: TermId,
    input: TermId,
    amount: TermId,
    width: u32,
    kind: LogShiftKind,
    max_bit: u32,
) -> Result<bool> {
    if same_or_equal_index(query, index, stage, input)? {
        return Ok(true);
    }
    if max_bit == 0 {
        return Ok(false);
    }
    for target in index.aliases(stage) {
        for definition in log_mux_definitions_for_target(query, equalities, target)? {
            let Some(bit) = repeated_amount_bit(query, index, definition.mask, amount)? else {
                continue;
            };
            if bit >= max_bit || bit >= 63 {
                continue;
            }
            let shift = 1u32 << bit;
            if shift >= width {
                continue;
            }
            if !matches_log_slicing_shift_by(
                query,
                index,
                definition.then_value,
                definition.else_value,
                width,
                shift,
                kind,
            )? {
                continue;
            }
            if verify_log_slicing_shift_stage(
                query,
                equalities,
                index,
                definition.else_value,
                input,
                amount,
                width,
                kind,
                bit,
            )? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn log_mux_definitions_for_target(
    query: &Query,
    equalities: &[(TermId, TermId)],
    target: TermId,
) -> Result<Vec<LogMuxDefinition>> {
    let mut out = Vec::new();
    for &(a, b) in equalities {
        if a == target {
            if let Some(definition) = log_mux_expr(query, b)? {
                out.push(definition);
            }
        }
        if b == target {
            if let Some(definition) = log_mux_expr(query, a)? {
                out.push(definition);
            }
        }
    }
    Ok(out)
}

fn log_mux_expr(query: &Query, term: TermId) -> Result<Option<LogMuxDefinition>> {
    let mut parts = Vec::new();
    collect_bv_or_terms(query, term, &mut parts)?;
    if parts.len() != 2 {
        return Ok(None);
    }
    if let Some(definition) = log_mux_expr_parts(query, parts[0], parts[1])? {
        return Ok(Some(definition));
    }
    log_mux_expr_parts(query, parts[1], parts[0])
}

fn log_mux_expr_parts(
    query: &Query,
    then_part: TermId,
    else_part: TermId,
) -> Result<Option<LogMuxDefinition>> {
    let Some((then_a, then_b)) = bv_and_parts(query, then_part)? else {
        return Ok(None);
    };
    let Some((else_a, else_b)) = bv_and_parts(query, else_part)? else {
        return Ok(None);
    };
    for (mask, then_value) in [(then_a, then_b), (then_b, then_a)] {
        for (maybe_not_mask, else_value) in [(else_a, else_b), (else_b, else_a)] {
            if bv_not_child(query, maybe_not_mask)? == Some(mask) {
                return Ok(Some(LogMuxDefinition {
                    mask,
                    then_value,
                    else_value,
                }));
            }
        }
    }
    Ok(None)
}

fn repeated_amount_bit(
    query: &Query,
    index: &LogSlicingIndex,
    mask: TermId,
    amount: TermId,
) -> Result<Option<u32>> {
    let Sort::Bv(width) = query.arena.sort(amount)? else {
        return Ok(None);
    };
    let mut found = None;
    for cond in repeated_conditions_for_mask(query, index, mask)? {
        for candidate in index.aliases(cond) {
            let NodeKind::BvExtract { child, high, low } = &query.arena.node(candidate)?.kind
            else {
                continue;
            };
            if *child == amount && *high == *low && *high < width {
                if found.is_some_and(|previous| previous != *high) {
                    return Ok(None);
                }
                found = Some(*high);
            }
        }
    }
    Ok(found)
}

fn matches_log_slicing_shift_by(
    query: &Query,
    index: &LogSlicingIndex,
    shifted: TermId,
    previous: TermId,
    width: u32,
    shift: u32,
    kind: LogShiftKind,
) -> Result<bool> {
    match kind {
        LogShiftKind::Shl => {
            let low_zero = index
                .extract_terms(shifted, shift - 1, 0)
                .iter()
                .any(|term| is_zero_bv_const(query, *term).unwrap_or(false));
            let moved = index
                .extract_terms(previous, width - shift - 1, 0)
                .iter()
                .any(|term| {
                    matches_extract(query, *term, shifted, width - 1, shift).unwrap_or(false)
                });
            Ok(low_zero && moved)
        }
        LogShiftKind::LShr => {
            let high_zero = index
                .extract_terms(shifted, width - 1, width - shift)
                .iter()
                .any(|term| is_zero_bv_const(query, *term).unwrap_or(false));
            let moved = index
                .extract_terms(previous, width - 1, shift)
                .iter()
                .any(|term| {
                    matches_extract(query, *term, shifted, width - shift - 1, 0).unwrap_or(false)
                });
            Ok(high_zero && moved)
        }
        LogShiftKind::AShr => Ok(false),
    }
}

fn bv_var_name_has_prefix(query: &Query, term: TermId, prefix: &str) -> bool {
    matches!(
        &query.arena.node(term).map(|node| &node.kind),
        Ok(NodeKind::BvVar { name, .. }) if name.starts_with(prefix)
    )
}

fn find_bv_const_u64(query: &Query, width: u32, value: u64) -> Option<TermId> {
    query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            matches!(node.sort, Sort::Bv(actual_width) if actual_width == width)
                .then(|| TermId(index as u32))
                .filter(|term| is_bv_const_u64(query, *term, width, value).unwrap_or(false))
        })
}

#[derive(Debug, Clone, Copy)]
struct LogComparisonAssertion {
    result: TermId,
    left: TermId,
    right: TermId,
    signed: bool,
}

#[derive(Debug, Default)]
struct LogSlicingIndex {
    aliases: BTreeMap<TermId, Vec<TermId>>,
    extracts: BTreeMap<(TermId, u32, u32), Vec<TermId>>,
}

impl LogSlicingIndex {
    fn new(query: &Query, equalities: &[(TermId, TermId)]) -> Result<Self> {
        let mut index = Self::default();
        for &(a, b) in equalities {
            if query.arena.sort(a)? == query.arena.sort(b)? {
                index.aliases.entry(a).or_default().push(b);
                index.aliases.entry(b).or_default().push(a);
            }
            if let NodeKind::BvExtract { child, high, low } = &query.arena.node(a)?.kind {
                index
                    .extracts
                    .entry((*child, *high, *low))
                    .or_default()
                    .push(b);
            }
            if let NodeKind::BvExtract { child, high, low } = &query.arena.node(b)?.kind {
                index
                    .extracts
                    .entry((*child, *high, *low))
                    .or_default()
                    .push(a);
            }
        }
        for values in index.aliases.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        for values in index.extracts.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        Ok(index)
    }

    fn aliases(&self, term: TermId) -> Vec<TermId> {
        let mut out = vec![term];
        if let Some(aliases) = self.aliases.get(&term) {
            for &alias in aliases {
                if !out.contains(&alias) {
                    out.push(alias);
                }
            }
        }
        out
    }

    fn candidate_terms(&self, term: TermId) -> Vec<TermId> {
        let mut out = self.aliases(term);
        for alias in out.clone() {
            for second in self.aliases(alias) {
                if !out.contains(&second) {
                    out.push(second);
                }
            }
        }
        out
    }

    fn same_or_equal(&self, a: TermId, b: TermId) -> bool {
        a == b
            || self
                .aliases
                .get(&a)
                .is_some_and(|aliases| aliases.contains(&b))
    }

    fn extract_terms(&self, child: TermId, high: u32, low: u32) -> Vec<TermId> {
        self.extracts
            .get(&(child, high, low))
            .cloned()
            .unwrap_or_default()
    }
}

fn has_log_slicing_comparison_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 20_000 {
        return Ok(false);
    }
    let mut leaves = Vec::new();
    let mut bv_equalities = Vec::new();
    let mut comparisons = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut bv_equalities,
            &mut Vec::new(),
        )?;
    }
    for &leaf in &leaves {
        if let Some(comparison) = log_slicing_comparison_assertion(query, leaf)? {
            comparisons.push(comparison);
        }
    }
    if comparisons.is_empty() {
        return Ok(false);
    }
    let index = LogSlicingIndex::new(query, &bv_equalities)?;

    for &leaf in &leaves {
        let Some((result, computed)) = log_slicing_comparison_disequality(query, leaf)? else {
            continue;
        };
        for comparison in &comparisons {
            if comparison.result != result {
                continue;
            }
            let selected = if comparison.signed {
                log_slicing_signed_lt_expr(query, computed, comparison.left, comparison.right)?
            } else {
                log_slicing_unsigned_lt_expr(query, computed)?
            };
            let Some((selected_left, selected_right)) = selected else {
                continue;
            };
            if verify_log_slicing_unsigned_chain(
                query,
                &leaves,
                &bv_equalities,
                &index,
                (selected_left, selected_right),
                (comparison.left, comparison.right),
            )? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn log_slicing_comparison_assertion(
    query: &Query,
    term: TermId,
) -> Result<Option<LogComparisonAssertion>> {
    let Some((a, b)) = bool_eq_pair(query, term)? else {
        return Ok(None);
    };
    if let Some((left, right, signed)) = comparison_parts(query, a)? {
        return Ok(Some(LogComparisonAssertion {
            result: b,
            left,
            right,
            signed,
        }));
    }
    if let Some((left, right, signed)) = comparison_parts(query, b)? {
        return Ok(Some(LogComparisonAssertion {
            result: a,
            left,
            right,
            signed,
        }));
    }
    Ok(None)
}

fn comparison_parts(query: &Query, term: TermId) -> Result<Option<(TermId, TermId, bool)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvUlt(a, b) => Some((*a, *b, false)),
        NodeKind::BvSlt(a, b) => Some((*a, *b, true)),
        _ => None,
    })
}

fn log_slicing_comparison_disequality(
    query: &Query,
    term: TermId,
) -> Result<Option<(TermId, TermId)>> {
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    bool_eq_pair(query, *child)
}

fn log_slicing_unsigned_lt_expr(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if is_one_bv_const(query, b)? {
        return log_slicing_unsigned_lt_bit(query, a);
    }
    if is_one_bv_const(query, a)? {
        return log_slicing_unsigned_lt_bit(query, b);
    }
    Ok(None)
}

fn log_slicing_unsigned_lt_bit(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    let NodeKind::BvAnd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if let Some(child) = bv_not_child(query, *a)? {
        if query.arena.sort(child)? == Sort::Bv(1) && query.arena.sort(*b)? == Sort::Bv(1) {
            return Ok(Some((child, *b)));
        }
    }
    if let Some(child) = bv_not_child(query, *b)? {
        if query.arena.sort(child)? == Sort::Bv(1) && query.arena.sort(*a)? == Sort::Bv(1) {
            return Ok(Some((child, *a)));
        }
    }
    Ok(None)
}

fn log_slicing_signed_lt_expr(
    query: &Query,
    term: TermId,
    left: TermId,
    right: TermId,
) -> Result<Option<(TermId, TermId)>> {
    let NodeKind::BoolOr(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if signed_lt_parts_match(query, *a, *b, left, right)? {
        return signed_same_sign_unsigned_part(query, *b, left, right);
    }
    if signed_lt_parts_match(query, *b, *a, left, right)? {
        return signed_same_sign_unsigned_part(query, *a, left, right);
    }
    Ok(None)
}

fn signed_lt_parts_match(
    query: &Query,
    sign_diff: TermId,
    same_sign: TermId,
    left: TermId,
    right: TermId,
) -> Result<bool> {
    Ok(signed_sign_diff_part(query, sign_diff, left, right)?
        && signed_same_sign_unsigned_part(query, same_sign, left, right)?.is_some())
}

fn signed_sign_diff_part(query: &Query, term: TermId, left: TermId, right: TermId) -> Result<bool> {
    let (left_sign, right_sign) = sign_extract_bounds(query, left, right)?;
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, term, &mut parts)?;
    if parts.len() != 2 {
        return Ok(false);
    }
    let mut saw_left_negative = false;
    let mut saw_right_nonnegative = false;
    for part in parts {
        if matches_bv_eq_extract_const(query, part, left, left_sign, left_sign, 1)? {
            saw_left_negative = true;
        } else if let NodeKind::BoolNot(child) = &query.arena.node(part)?.kind {
            if matches_bv_eq_extract_const(query, *child, right, right_sign, right_sign, 1)? {
                saw_right_nonnegative = true;
            }
        }
    }
    Ok(saw_left_negative && saw_right_nonnegative)
}

fn signed_same_sign_unsigned_part(
    query: &Query,
    term: TermId,
    left: TermId,
    right: TermId,
) -> Result<Option<(TermId, TermId)>> {
    let (left_sign, right_sign) = sign_extract_bounds(query, left, right)?;
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, term, &mut parts)?;
    if parts.len() != 2 {
        return Ok(None);
    }
    let mut saw_same_sign = false;
    let mut selected = None;
    for part in parts {
        if matches_bv_eq_extracts(
            query,
            part,
            (left, left_sign, left_sign),
            (right, right_sign, right_sign),
        )? {
            saw_same_sign = true;
        } else {
            selected = log_slicing_unsigned_lt_expr(query, part)?;
        }
    }
    Ok(if saw_same_sign { selected } else { None })
}

fn sign_extract_bounds(query: &Query, left: TermId, right: TermId) -> Result<(u32, u32)> {
    let left_width = query.arena.expect_bv(left, "signed comparison left")?;
    let right_width = query.arena.expect_bv(right, "signed comparison right")?;
    if left_width != right_width {
        return Err(Error::invalid(
            "signed comparison",
            format!("width mismatch: {left_width} vs {right_width}"),
        ));
    }
    Ok((left_width - 1, right_width - 1))
}

fn verify_log_slicing_unsigned_chain(
    query: &Query,
    leaves: &[TermId],
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    mut current: BvPair,
    original: BvPair,
) -> Result<bool> {
    for _ in 0..32 {
        if log_slicing_initial_pair(query, index, current.0, current.1, original.0, original.1)? {
            return Ok(true);
        }
        let Some((previous_left, previous_right)) =
            log_slicing_previous_pair(query, leaves, equalities, index, current.0, current.1)?
        else {
            return Ok(false);
        };
        current = (previous_left, previous_right);
    }
    Ok(false)
}

fn log_slicing_previous_pair(
    query: &Query,
    leaves: &[TermId],
    equalities: &[(TermId, TermId)],
    index: &LogSlicingIndex,
    current_left: TermId,
    current_right: TermId,
) -> Result<Option<(TermId, TermId)>> {
    let left_defs = log_slicing_mux_definitions(query, equalities, current_left)?;
    let right_defs = log_slicing_mux_definitions(query, equalities, current_right)?;
    for left_def in &left_defs {
        for right_def in &right_defs {
            if left_def.half_width != right_def.half_width {
                continue;
            }
            let left_conds = repeated_conditions_for_mask(query, index, left_def.mask)?;
            let right_conds = repeated_conditions_for_mask(query, index, right_def.mask)?;
            for left_cond in &left_conds {
                for right_cond in &right_conds {
                    if !same_or_equal_index(query, index, *left_cond, *right_cond)? {
                        continue;
                    }
                    if has_log_slicing_high_equality_condition(
                        query,
                        leaves,
                        index,
                        *left_cond,
                        left_def.previous,
                        right_def.previous,
                        left_def.half_width,
                    )? {
                        return Ok(Some((left_def.previous, right_def.previous)));
                    }
                }
            }
        }
    }
    Ok(None)
}

#[derive(Debug, Clone, Copy)]
struct LogSlicingMuxDefinition {
    mask: TermId,
    previous: TermId,
    half_width: u32,
}

fn log_slicing_mux_definitions(
    query: &Query,
    equalities: &[(TermId, TermId)],
    target: TermId,
) -> Result<Vec<LogSlicingMuxDefinition>> {
    let mut out = Vec::new();
    for &(a, b) in equalities {
        if a == target {
            if let Some(definition) = log_slicing_mux_expr(query, b)? {
                out.push(definition);
            }
        }
        if b == target {
            if let Some(definition) = log_slicing_mux_expr(query, a)? {
                out.push(definition);
            }
        }
    }
    Ok(out)
}

fn log_slicing_mux_expr(query: &Query, term: TermId) -> Result<Option<LogSlicingMuxDefinition>> {
    let mut parts = Vec::new();
    collect_bv_or_terms(query, term, &mut parts)?;
    if parts.len() != 2 {
        return Ok(None);
    }
    if let Some(definition) = log_slicing_mux_expr_parts(query, parts[0], parts[1])? {
        return Ok(Some(definition));
    }
    log_slicing_mux_expr_parts(query, parts[1], parts[0])
}

fn log_slicing_mux_expr_parts(
    query: &Query,
    low_part: TermId,
    high_part: TermId,
) -> Result<Option<LogSlicingMuxDefinition>> {
    let Some((low_a, low_b)) = bv_and_parts(query, low_part)? else {
        return Ok(None);
    };
    let Some((high_a, high_b)) = bv_and_parts(query, high_part)? else {
        return Ok(None);
    };
    for (mask, low) in [(low_a, low_b), (low_b, low_a)] {
        for (maybe_not_mask, high) in [(high_a, high_b), (high_b, high_a)] {
            if bv_not_child(query, maybe_not_mask)? != Some(mask) {
                continue;
            }
            let Some((previous, half_width)) = log_slicing_low_high_extracts(query, low, high)?
            else {
                continue;
            };
            if query.arena.sort(mask)? == Sort::Bv(half_width) {
                return Ok(Some(LogSlicingMuxDefinition {
                    mask,
                    previous,
                    half_width,
                }));
            }
        }
    }
    Ok(None)
}

fn log_slicing_low_high_extracts(
    query: &Query,
    low: TermId,
    high: TermId,
) -> Result<Option<(TermId, u32)>> {
    let NodeKind::BvExtract {
        child: low_child,
        high: low_high,
        low: low_low,
    } = &query.arena.node(low)?.kind
    else {
        return Ok(None);
    };
    let NodeKind::BvExtract {
        child: high_child,
        high: high_high,
        low: high_low,
    } = &query.arena.node(high)?.kind
    else {
        return Ok(None);
    };
    if low_child != high_child || *low_low != 0 || *high_low != *low_high + 1 {
        return Ok(None);
    }
    let half_width = *low_high + 1;
    if *high_high + 1 == half_width * 2 {
        Ok(Some((*low_child, half_width)))
    } else {
        Ok(None)
    }
}

fn repeated_conditions_for_mask(
    query: &Query,
    index: &LogSlicingIndex,
    mask: TermId,
) -> Result<Vec<TermId>> {
    let mut out = Vec::new();
    let mut memo = BTreeMap::new();
    for candidate in index.candidate_terms(mask) {
        let Sort::Bv(width) = query.arena.sort(candidate)? else {
            continue;
        };
        let mut visited = Vec::new();
        for cond in
            term_repeated_conditions(query, index, candidate, width, &mut visited, &mut memo)?
        {
            if !out.contains(&cond) {
                out.push(cond);
            }
        }
    }
    Ok(out)
}

fn term_repeated_conditions(
    query: &Query,
    index: &LogSlicingIndex,
    term: TermId,
    width: u32,
    visited: &mut Vec<TermId>,
    memo: &mut BTreeMap<TermId, Vec<TermId>>,
) -> Result<Vec<TermId>> {
    if let Some(cached) = memo.get(&term) {
        return Ok(cached.clone());
    }
    if visited.contains(&term) {
        return Ok(Vec::new());
    }
    visited.push(term);
    let mut out = Vec::new();
    if width == 1 {
        for alias in index.aliases(term) {
            if query.arena.sort(alias)? == Sort::Bv(1) && !out.contains(&alias) {
                out.push(alias);
            }
        }
    } else if let NodeKind::BvConcat(high, low) = &query.arena.node(term)?.kind {
        let high_width = query.arena.expect_bv(*high, "log slicing concat high")?;
        let low_width = query.arena.expect_bv(*low, "log slicing concat low")?;
        let high_conditions =
            term_repeated_conditions(query, index, *high, high_width, visited, memo)?;
        let low_conditions =
            term_repeated_conditions(query, index, *low, low_width, visited, memo)?;
        for high_condition in high_conditions {
            if low_conditions.iter().any(|low_condition| {
                same_or_equal_index(query, index, high_condition, *low_condition).unwrap_or(false)
            }) && !out.contains(&high_condition)
            {
                out.push(high_condition);
            }
        }
    } else if let NodeKind::BvExtract { child, .. } = &query.arena.node(term)?.kind {
        let child_width = query.arena.expect_bv(*child, "log slicing extract child")?;
        for cond in term_repeated_conditions(query, index, *child, child_width, visited, memo)? {
            if !out.contains(&cond) {
                out.push(cond);
            }
        }
    } else {
        if width.is_multiple_of(2) {
            let half = width / 2;
            for base in index.aliases(term) {
                if !matches!(query.arena.sort(base), Ok(Sort::Bv(base_width)) if base_width == width)
                {
                    continue;
                }
                let low_terms = index.extract_terms(base, half - 1, 0);
                let high_terms = index.extract_terms(base, width - 1, half);
                for low_term in &low_terms {
                    if high_terms.iter().any(|high_term| {
                        same_or_equal_index(query, index, *low_term, *high_term).unwrap_or(false)
                    }) {
                        for cond in
                            term_repeated_conditions(query, index, *low_term, half, visited, memo)?
                        {
                            if !out.contains(&cond) {
                                out.push(cond);
                            }
                        }
                    }
                }
            }
        }
        for alias in index.aliases(term) {
            if alias != term
                && matches!(query.arena.sort(alias), Ok(Sort::Bv(alias_width)) if alias_width == width)
            {
                for cond in term_repeated_conditions(query, index, alias, width, visited, memo)? {
                    if !out.contains(&cond) {
                        out.push(cond);
                    }
                }
            }
        }
    }
    visited.pop();
    memo.insert(term, out.clone());
    Ok(out)
}

fn has_log_slicing_high_equality_condition(
    query: &Query,
    leaves: &[TermId],
    index: &LogSlicingIndex,
    cond: TermId,
    previous_left: TermId,
    previous_right: TermId,
    half_width: u32,
) -> Result<bool> {
    for &leaf in leaves {
        let Some((a, b)) = bool_eq_pair(query, leaf)? else {
            continue;
        };
        if (matches_bv_eq_const_alias(query, index, a, cond, 1, 1)?
            && matches_bv_eq_extracts(
                query,
                b,
                (previous_left, half_width * 2 - 1, half_width),
                (previous_right, half_width * 2 - 1, half_width),
            )?)
            || (matches_bv_eq_const_alias(query, index, b, cond, 1, 1)?
                && matches_bv_eq_extracts(
                    query,
                    a,
                    (previous_left, half_width * 2 - 1, half_width),
                    (previous_right, half_width * 2 - 1, half_width),
                )?)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn log_slicing_initial_pair(
    query: &Query,
    index: &LogSlicingIndex,
    current_left: TermId,
    current_right: TermId,
    original_left: TermId,
    original_right: TermId,
) -> Result<bool> {
    Ok(
        term_zero_extends_input(query, index, current_left, original_left)?
            && term_zero_extends_input(query, index, current_right, original_right)?,
    )
}

fn term_zero_extends_input(
    query: &Query,
    index: &LogSlicingIndex,
    term: TermId,
    input: TermId,
) -> Result<bool> {
    let term_width = query.arena.expect_bv(term, "zero-extended term")?;
    let input_width = query.arena.expect_bv(input, "zero-extended input")?;
    if term_width == input_width {
        return same_or_equal_index(query, index, term, input);
    }
    if term_width < input_width {
        return Ok(false);
    }
    for alias in index.candidate_terms(term) {
        if !matches!(query.arena.sort(alias), Ok(Sort::Bv(width)) if width == term_width) {
            continue;
        }
        if index
            .extract_terms(alias, input_width - 1, 0)
            .contains(&input)
            && index
                .extract_terms(alias, term_width - 1, input_width)
                .iter()
                .any(|term| is_zero_bv_const(query, *term).unwrap_or(false))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn same_or_equal_index(
    query: &Query,
    index: &LogSlicingIndex,
    a: TermId,
    b: TermId,
) -> Result<bool> {
    Ok(query.arena.sort(a)? == query.arena.sort(b)? && index.same_or_equal(a, b))
}

fn matches_bv_eq_const_alias(
    query: &Query,
    index: &LogSlicingIndex,
    term: TermId,
    var: TermId,
    value: u64,
    width: u32,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok(
        (same_or_equal_index(query, index, a, var)? && is_bv_const_u64(query, b, width, value)?)
            || (same_or_equal_index(query, index, b, var)?
                && is_bv_const_u64(query, a, width, value)?),
    )
}

fn bool_eq_pair(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BoolEq(a, b) => Some((*a, *b)),
        _ => None,
    })
}

fn bv_not_child(query: &Query, term: TermId) -> Result<Option<TermId>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvNot(child) => Some(*child),
        _ => None,
    })
}

fn matches_bv_eq_extracts(
    query: &Query,
    term: TermId,
    left: BvSlice,
    right: BvSlice,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok((matches_extract(query, a, left.0, left.1, left.2)?
        && matches_extract(query, b, right.0, right.1, right.2)?)
        || (matches_extract(query, b, left.0, left.1, left.2)?
            && matches_extract(query, a, right.0, right.1, right.2)?))
}

fn matches_bv_eq_extract_const(
    query: &Query,
    term: TermId,
    child: TermId,
    high: u32,
    low: u32,
    value: u64,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok((matches_extract(query, a, child, high, low)?
        && is_bv_const_u64(query, b, high - low + 1, value)?)
        || (matches_extract(query, b, child, high, low)?
            && is_bv_const_u64(query, a, high - low + 1, value)?))
}

#[derive(Debug, Clone, Copy)]
struct LogSlicingAdder {
    sum: TermId,
    a: TermId,
    b: TermId,
}

fn has_log_slicing_adder_contradiction(query: &Query) -> Result<bool> {
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    let adders = collect_log_slicing_adders(query, &equalities)?;
    for &(result, arithmetic) in &equalities {
        let contradiction = match &query.arena.node(arithmetic)?.kind {
            NodeKind::BvAdd(a, b) => adders.iter().any(|adder| {
                same_unordered_pair(adder.a, adder.b, *a, *b)
                    && disequalities
                        .iter()
                        .any(|&(x, y)| same_unordered_pair(x, y, result, adder.sum))
            }),
            NodeKind::BvSub(a, b) => adders.iter().any(|outer| {
                disequalities
                    .iter()
                    .any(|&(x, y)| same_unordered_pair(x, y, result, outer.sum))
                    && adders.iter().any(|inner| {
                        same_unordered_pair(outer.a, outer.b, *a, inner.sum)
                            && is_twos_complement_negation_adder(query, inner, *b).unwrap_or(false)
                    })
            }),
            _ => false,
        };
        if contradiction {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_log_slicing_adders(
    query: &Query,
    equalities: &[(TermId, TermId)],
) -> Result<Vec<LogSlicingAdder>> {
    let mut adders = Vec::new();
    for &(sum, xor_term) in equalities {
        collect_log_slicing_adders_from_orientation(query, equalities, sum, xor_term, &mut adders)?;
        collect_log_slicing_adders_from_orientation(query, equalities, xor_term, sum, &mut adders)?;
    }
    adders.sort_by_key(|adder| (adder.sum, adder.a, adder.b));
    adders.dedup_by_key(|adder| (adder.sum, adder.a, adder.b));
    Ok(adders)
}

fn collect_log_slicing_adders_from_orientation(
    query: &Query,
    equalities: &[(TermId, TermId)],
    sum: TermId,
    xor_term: TermId,
    out: &mut Vec<LogSlicingAdder>,
) -> Result<()> {
    let Sort::Bv(width) = query.arena.sort(sum)? else {
        return Ok(());
    };
    let mut terms = Vec::new();
    collect_bv_xor_terms(query, xor_term, &mut terms)?;
    if terms.len() != 3 {
        return Ok(());
    }
    for cin_index in 0..3 {
        let cin = terms[cin_index];
        let operands = terms
            .iter()
            .enumerate()
            .filter_map(|(index, term)| (index != cin_index).then_some(*term))
            .collect::<Vec<_>>();
        let a = operands[0];
        let b = operands[1];
        let Some(cout) = find_log_slicing_cout(query, equalities, a, b, cin)? else {
            continue;
        };
        if has_log_slicing_carry_shift(query, equalities, cin, cout, width)? {
            out.push(LogSlicingAdder { sum, a, b });
        }
    }
    Ok(())
}

fn collect_bv_xor_terms(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvXor(a, b) => {
            collect_bv_xor_terms(query, *a, out)?;
            collect_bv_xor_terms(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn find_log_slicing_cout(
    query: &Query,
    equalities: &[(TermId, TermId)],
    a: TermId,
    b: TermId,
    cin: TermId,
) -> Result<Option<TermId>> {
    for &(left, right) in equalities {
        if is_log_slicing_carry(query, left, a, b, cin)? {
            return Ok(Some(right));
        }
        if is_log_slicing_carry(query, right, a, b, cin)? {
            return Ok(Some(left));
        }
    }
    Ok(None)
}

fn is_log_slicing_carry(
    query: &Query,
    term: TermId,
    a: TermId,
    b: TermId,
    cin: TermId,
) -> Result<bool> {
    let mut terms = Vec::new();
    collect_bv_or_terms(query, term, &mut terms)?;
    if terms.len() != 3 {
        return Ok(false);
    }
    let mut seen_ab = false;
    let mut seen_ac = false;
    let mut seen_bc = false;
    for term in terms {
        let Some((x, y)) = bv_and_parts(query, term)? else {
            return Ok(false);
        };
        if same_unordered_pair(x, y, a, b) {
            seen_ab = true;
        } else if same_unordered_pair(x, y, a, cin) {
            seen_ac = true;
        } else if same_unordered_pair(x, y, b, cin) {
            seen_bc = true;
        } else {
            return Ok(false);
        }
    }
    Ok(seen_ab && seen_ac && seen_bc)
}

fn collect_bv_or_terms(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvOr(a, b) => {
            collect_bv_or_terms(query, *a, out)?;
            collect_bv_or_terms(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn bv_and_parts(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvAnd(a, b) => Some((*a, *b)),
        _ => None,
    })
}

fn has_log_slicing_carry_shift(
    query: &Query,
    equalities: &[(TermId, TermId)],
    cin: TermId,
    cout: TermId,
    width: u32,
) -> Result<bool> {
    if width < 2 {
        return Ok(false);
    }
    for &(left, right) in equalities {
        let concat = if left == cin {
            right
        } else if right == cin {
            left
        } else {
            continue;
        };
        let has_shift = equalities.iter().any(|&(a, b)| {
            (is_extract_of(query, a, cout, width - 2, 0).unwrap_or(false)
                && is_extract_of(query, b, concat, width - 1, 1).unwrap_or(false))
                || (is_extract_of(query, b, cout, width - 2, 0).unwrap_or(false)
                    && is_extract_of(query, a, concat, width - 1, 1).unwrap_or(false))
        });
        if !has_shift {
            continue;
        }
        let has_low_zero = equalities.iter().any(|&(a, b)| {
            (is_extract_of(query, a, concat, 0, 0).unwrap_or(false)
                && is_zero_bv_const(query, b).unwrap_or(false))
                || (is_extract_of(query, b, concat, 0, 0).unwrap_or(false)
                    && is_zero_bv_const(query, a).unwrap_or(false))
        });
        if has_low_zero {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_extract_of(query: &Query, term: TermId, child: TermId, high: u32, low: u32) -> Result<bool> {
    Ok(matches!(
        &query.arena.node(term)?.kind,
        NodeKind::BvExtract {
            child: actual_child,
            high: actual_high,
            low: actual_low,
        } if *actual_child == child && *actual_high == high && *actual_low == low
    ))
}

fn is_twos_complement_negation_adder(
    query: &Query,
    adder: &LogSlicingAdder,
    term: TermId,
) -> Result<bool> {
    Ok(
        (is_bv_not_of(query, adder.a, term)? && is_one_bv_const(query, adder.b)?)
            || (is_bv_not_of(query, adder.b, term)? && is_one_bv_const(query, adder.a)?),
    )
}

fn is_bv_not_of(query: &Query, candidate: TermId, child: TermId) -> Result<bool> {
    Ok(matches!(
        &query.arena.node(candidate)?.kind,
        NodeKind::BvNot(actual) if *actual == child
    ))
}

fn has_signed_division_multiply_overflow_guard_contradiction(query: &Query) -> Result<bool> {
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
    }
    for &(a, b) in &disequalities {
        let high = if is_zero_bv_const(query, b)?
            && has_bvnot_disequality_to_zero(query, a, &disequalities)?
        {
            a
        } else if is_zero_bv_const(query, a)?
            && has_bvnot_disequality_to_zero(query, b, &disequalities)?
        {
            b
        } else {
            continue;
        };
        let Some((x, y, width)) = signed_division_product_high_slice_parts(query, high)? else {
            continue;
        };
        if has_disequality_with_const(query, &disequalities, y, |query, term| {
            is_zero_bv_const(query, term)
        })? && has_signed_division_overflow_guard(query, x, y, width)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn has_bvnot_disequality_to_zero(
    query: &Query,
    term: TermId,
    disequalities: &[(TermId, TermId)],
) -> Result<bool> {
    let not_term = query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            matches!(node.kind, NodeKind::BvNot(child) if child == term)
                .then_some(TermId(index as u32))
        });
    let Some(not_term) = not_term else {
        return Ok(false);
    };
    has_disequality_with_const(query, disequalities, not_term, |query, term| {
        is_zero_bv_const(query, term)
    })
}

fn has_disequality_with_const(
    query: &Query,
    disequalities: &[(TermId, TermId)],
    term: TermId,
    predicate: impl Fn(&Query, TermId) -> Result<bool>,
) -> Result<bool> {
    for &(a, b) in disequalities {
        if (a == term && predicate(query, b)?) || (b == term && predicate(query, a)?) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn signed_division_product_high_slice_parts(
    query: &Query,
    term: TermId,
) -> Result<Option<(TermId, TermId, u32)>> {
    let NodeKind::BvExtract { child, high, low } = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let NodeKind::BvMul(a, b) = &query.arena.node(*child)?.kind else {
        return Ok(None);
    };
    if let Some(parts) = signed_division_product_parts_from_operands(query, *a, *b, *high, *low)? {
        return Ok(Some(parts));
    }
    signed_division_product_parts_from_operands(query, *b, *a, *high, *low)
}

fn signed_division_product_parts_from_operands(
    query: &Query,
    quotient_factor: TermId,
    divisor_factor: TermId,
    high: u32,
    low: u32,
) -> Result<Option<(TermId, TermId, u32)>> {
    let Some((quotient, quotient_width, quotient_extra)) =
        sign_extend_parts(query, quotient_factor)?
    else {
        return Ok(None);
    };
    let Some((divisor, divisor_width, divisor_extra)) = sign_extend_parts(query, divisor_factor)?
    else {
        return Ok(None);
    };
    if quotient_width != divisor_width
        || quotient_extra != quotient_width
        || divisor_extra != divisor_width
        || low != quotient_width - 1
        || high + 1 != quotient_width * 2
    {
        return Ok(None);
    }
    let NodeKind::BvSDiv(x, y) = &query.arena.node(quotient)?.kind else {
        return Ok(None);
    };
    if *y != divisor {
        return Ok(None);
    }
    Ok(Some((*x, *y, quotient_width)))
}

fn sign_extend_parts(query: &Query, term: TermId) -> Result<Option<(TermId, u32, u32)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvSignExtend { child, extra } => {
            let Sort::Bv(width) = query.arena.sort(*child)? else {
                return Ok(None);
            };
            Some((*child, width, *extra))
        }
        _ => None,
    })
}

fn has_signed_division_overflow_guard(
    query: &Query,
    x: TermId,
    y: TermId,
    width: u32,
) -> Result<bool> {
    for assertion in &query.assertions {
        if contains_signed_division_overflow_guard(query, assertion.root, x, y, width)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn contains_signed_division_overflow_guard(
    query: &Query,
    term: TermId,
    x: TermId,
    y: TermId,
    width: u32,
) -> Result<bool> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolNot(child) => {
            is_signed_division_overflow_conjunction(query, *child, x, y, width)
        }
        NodeKind::BoolAnd(a, b) | NodeKind::BoolOr(a, b) => Ok(
            contains_signed_division_overflow_guard(query, *a, x, y, width)?
                || contains_signed_division_overflow_guard(query, *b, x, y, width)?,
        ),
        _ => Ok(false),
    }
}

fn is_signed_division_overflow_conjunction(
    query: &Query,
    term: TermId,
    x: TermId,
    y: TermId,
    width: u32,
) -> Result<bool> {
    let NodeKind::BoolAnd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok(
        (is_eq_to_all_ones(query, *a, y, width)? && is_eq_to_signed_min(query, *b, x, width)?)
            || (is_eq_to_all_ones(query, *b, y, width)?
                && is_eq_to_signed_min(query, *a, x, width)?),
    )
}

fn is_eq_to_all_ones(query: &Query, term: TermId, value: TermId, width: u32) -> Result<bool> {
    let NodeKind::BvEq(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == value && is_all_ones_bv_const(query, *b, width)?)
        || (*b == value && is_all_ones_bv_const(query, *a, width)?))
}

fn is_eq_to_signed_min(query: &Query, term: TermId, value: TermId, width: u32) -> Result<bool> {
    let NodeKind::BvEq(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == value && is_signed_min_bv_const(query, *b, width)?)
        || (*b == value && is_signed_min_bv_const(query, *a, width)?))
}

fn has_unsigned_multiplication_overflow_guard_contradiction(query: &Query) -> Result<bool> {
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    let mut non_strict = Vec::new();
    for assertion in &query.assertions {
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut equalities,
            &mut disequalities,
        )?;
        collect_unsigned_less_or_equal(query, assertion.root, &mut non_strict)?;
    }
    for &(a, b) in &disequalities {
        let overflow = unsigned_high_multiplication_overflow_parts(query, a, b)?
            .or(unsigned_high_multiplication_overflow_parts(query, b, a)?);
        let Some((x, y, width)) = overflow else {
            continue;
        };
        for &(left, right) in &non_strict {
            if left == y && is_max_div_by(query, right, x, width)? {
                return Ok(true);
            }
            if left == x && is_max_div_by(query, right, y, width)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn unsigned_high_multiplication_overflow_parts(
    query: &Query,
    term: TermId,
    zero: TermId,
) -> Result<Option<(TermId, TermId, u32)>> {
    if !is_zero_bv_const(query, zero)? {
        return Ok(None);
    }
    let NodeKind::BvExtract { child, high, low } = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let NodeKind::BvMul(a, b) = &query.arena.node(*child)?.kind else {
        return Ok(None);
    };
    let Some((x, x_width, x_extra)) = zero_extend_parts(query, *a)? else {
        return Ok(None);
    };
    let Some((y, y_width, y_extra)) = zero_extend_parts(query, *b)? else {
        return Ok(None);
    };
    if x_width != y_width || x_extra != x_width || y_extra != y_width {
        return Ok(None);
    }
    if *low != x_width || *high + 1 != x_width * 2 {
        return Ok(None);
    }
    Ok(Some((x, y, x_width)))
}

fn zero_extend_parts(query: &Query, term: TermId) -> Result<Option<(TermId, u32, u32)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvZeroExtend { child, extra } => {
            let Sort::Bv(width) = query.arena.sort(*child)? else {
                return Ok(None);
            };
            Some((*child, width, *extra))
        }
        _ => None,
    })
}

fn is_max_div_by(query: &Query, term: TermId, divisor: TermId, width: u32) -> Result<bool> {
    let NodeKind::BvUDiv(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok(*b == divisor && is_all_ones_bv_const(query, *a, width)?)
}

fn collect_bv_equalities_and_disequalities(
    query: &Query,
    term: TermId,
    equalities: &mut Vec<(TermId, TermId)>,
    disequalities: &mut Vec<(TermId, TermId)>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => equalities.push((*a, *b)),
        NodeKind::BoolNot(child) => {
            if let NodeKind::BvEq(a, b) = &query.arena.node(*child)?.kind {
                disequalities.push((*a, *b));
            }
        }
        NodeKind::BoolAnd(a, b) => {
            collect_bv_equalities_and_disequalities(query, *a, equalities, disequalities)?;
            collect_bv_equalities_and_disequalities(query, *b, equalities, disequalities)?;
        }
        _ => {}
    }
    Ok(())
}

fn bv_add_parts(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvAdd(a, b) => Some((*a, *b)),
        _ => None,
    })
}

fn is_shift_left_one_of(query: &Query, term: TermId, x: TermId) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvShl(value, amount) => *value == x && is_one_bv_const(query, *amount)?,
        NodeKind::BvMul(a, b) => {
            (*a == x && is_power_of_two_const(query, *b, 1)?)
                || (*b == x && is_power_of_two_const(query, *a, 1)?)
        }
        _ => false,
    })
}

fn is_asserted_nonzero_power_of_two(
    query: &Query,
    term: TermId,
    equalities: &[(TermId, TermId)],
    disequalities: &[(TermId, TermId)],
) -> Result<bool> {
    let zero = disequalities.iter().find_map(|&(a, b)| {
        if a == term && is_zero_bv_const(query, b).unwrap_or(false) {
            Some(b)
        } else if b == term && is_zero_bv_const(query, a).unwrap_or(false) {
            Some(a)
        } else {
            None
        }
    });
    let Some(zero) = zero else {
        return Ok(false);
    };
    Ok(equalities
        .iter()
        .any(|&(a, b)| is_power_of_two_test(query, a, b, term, zero)))
}

fn is_power_of_two_test(query: &Query, a: TermId, b: TermId, term: TermId, zero: TermId) -> bool {
    (is_zero_bv_const(query, b).unwrap_or(false)
        && is_power_of_two_mask(query, a, term).unwrap_or(false))
        || (is_zero_bv_const(query, a).unwrap_or(false)
            && is_power_of_two_mask(query, b, term).unwrap_or(false))
        || (b == zero && is_power_of_two_mask(query, a, term).unwrap_or(false))
        || (a == zero && is_power_of_two_mask(query, b, term).unwrap_or(false))
}

fn is_power_of_two_mask(query: &Query, mask: TermId, term: TermId) -> Result<bool> {
    let NodeKind::BvAnd(a, b) = &query.arena.node(mask)?.kind else {
        return Ok(false);
    };
    Ok((*a == term && is_minus_one(query, *b, term)?)
        || (*b == term && is_minus_one(query, *a, term)?))
}

fn is_minus_one(query: &Query, candidate: TermId, term: TermId) -> Result<bool> {
    let NodeKind::BvSub(a, b) = &query.arena.node(candidate)?.kind else {
        return Ok(false);
    };
    Ok(*a == term && is_one_bv_const(query, *b)?)
}

fn same_unordered_pair(a: TermId, b: TermId, x: TermId, y: TermId) -> bool {
    (a == x && b == y) || (a == y && b == x)
}

fn is_one_bv_const(query: &Query, term: TermId) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => {
            bytes.first().copied() == Some(1) && bytes.iter().skip(1).all(|byte| *byte == 0)
        }
        _ => false,
    })
}

fn is_zero_bv_const(query: &Query, term: TermId) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => bytes.iter().all(|byte| *byte == 0),
        _ => false,
    })
}

fn is_power_of_two_const(query: &Query, term: TermId, bit: u32) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => bytes.iter().enumerate().all(|(index, byte)| {
            let expected = if index == (bit / 8) as usize {
                1 << (bit % 8)
            } else {
                0
            };
            *byte == expected
        }),
        _ => false,
    })
}

fn is_all_ones_bv_const(query: &Query, term: TermId, width: u32) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst {
            width: actual,
            bytes,
        } if *actual == width => {
            let full_bytes = (width as usize).div_ceil(8);
            bytes.len() == full_bytes
                && bytes.iter().enumerate().all(|(index, byte)| {
                    let valid_bits = if index + 1 == full_bytes && !width.is_multiple_of(8) {
                        width % 8
                    } else {
                        8
                    };
                    let expected = if valid_bits == 8 {
                        0xff
                    } else {
                        (1u8 << valid_bits) - 1
                    };
                    *byte == expected
                })
        }
        _ => false,
    })
}

fn is_signed_min_bv_const(query: &Query, term: TermId, width: u32) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst {
            width: actual,
            bytes,
        } if *actual == width => {
            (0..width - 1).all(|bit| !crate::builder::get_bit(bytes, bit))
                && crate::builder::get_bit(bytes, width - 1)
        }
        _ => false,
    })
}

fn assert_target_bit(
    query: &mut Query,
    target: crate::ir::TermId,
    bit: u32,
    value: bool,
) -> Result<()> {
    let extracted = query.arena.add(
        NodeKind::BvExtract {
            child: target,
            high: bit,
            low: bit,
        },
        Sort::Bv(1),
    )?;
    let constant = query.arena.add(
        NodeKind::BvConst {
            width: 1,
            bytes: vec![u8::from(value)],
        },
        Sort::Bv(1),
    )?;
    let eq = query
        .arena
        .add(NodeKind::BvEq(extracted, constant), Sort::Bool)?;
    query.assertions.push(Assertion {
        root: eq,
        name: None,
    });
    Ok(())
}

fn set_bit(bytes: &mut [u8], bit: u32) {
    bytes[(bit / 8) as usize] |= 1 << (bit % 8);
}

fn query_with_named_subset(query: &Query, active_named_indices: &[usize]) -> Query {
    let mut trial = query.clone();
    trial.assertions = query
        .assertions
        .iter()
        .enumerate()
        .filter(|(index, assertion)| {
            assertion.name.is_none() || active_named_indices.contains(index)
        })
        .map(|(_, assertion)| assertion.clone())
        .collect();
    trial.want_model = false;
    trial.want_core = false;
    trial
}

pub fn solve_query(query: &Query, config: &Config) -> Result<SolveResult> {
    Solver::new(config.clone()).solve(query)
}

pub fn unsupported_to_unknown(result: Result<SolveResult>) -> Result<SolveResult> {
    match result {
        Err(Error::Unsupported(message)) => Ok(SolveResult::unknown(message)),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::Builder;

    #[test]
    fn direct_equality_disequality_contradiction_is_unsat() -> Result<()> {
        let mut builder = Builder::new();
        let x = builder.bv_var("x", 8)?;
        let y = builder.bv_var("y", 8)?;
        let z = builder.bv_var("z", 8)?;
        let xy = builder.bv_eq(x, y)?;
        let yz = builder.bv_eq(y, z)?;
        let xz = builder.bv_eq(x, z)?;
        let not_xz = builder.bool_not(xz)?;
        builder.assert(xy)?;
        builder.assert(yz)?;
        builder.assert(not_xz)?;
        let query = builder.finish()?;
        let mut solver = Solver::new(Config::default());
        let result = solver.solve(&query)?;
        assert_eq!(result.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn structural_definition_contradiction_is_unsat() -> Result<()> {
        let query = crate::frontend::parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun choose () Bool)
(assert (= x a))
(assert (ite choose (= z (bvadd x y)) (= z (bvmul x y))))
(assert (ite choose (= c (bvadd a y)) (= c (bvmul a y))))
(assert (not (= z c)))
(check-sat)
"#,
        )?;
        assert!(has_structural_definition_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn brummayer_popcount_contradiction_is_unsat() -> Result<()> {
        let width = 4;
        let mut builder = Builder::new();
        let x = builder.bv_var("x", width)?;
        let zero = builder.bv_const(0, width)?;
        let one = builder.bv_const(1, width)?;
        let zero1 = builder.bv_const(0, 1)?;
        let one1 = builder.bv_const(1, 1)?;
        let minus_one = builder.bv_const(mask_for_width(width), width)?;

        let mut naive = zero;
        for bit in 0..width {
            let extracted = builder.bv_extract(x, bit, bit)?;
            let cond = builder.bv_eq(one1, extracted)?;
            let incremented = builder.bv_add(naive, one)?;
            naive = builder.bv_ite(cond, incremented, naive)?;
        }

        let zero_eq = builder.bv_eq(x, zero)?;
        let zero_indicator = builder.bv_ite(zero_eq, one1, zero1)?;
        let zero_cond = builder.bv_eq(one1, zero_indicator)?;
        let mut wegner = builder.bv_ite(zero_cond, zero, one)?;
        let mut state = x;
        for _ in 1..width {
            let decremented = builder.bv_add(state, minus_one)?;
            state = builder.bv_and(state, decremented)?;
            let zero_eq = builder.bv_eq(state, zero)?;
            let zero_indicator = builder.bv_ite(zero_eq, one1, zero1)?;
            let zero_cond = builder.bv_eq(one1, zero_indicator)?;
            let incremented = builder.bv_add(wegner, one)?;
            wegner = builder.bv_ite(zero_cond, wegner, incremented)?;
        }

        let counts_equal = builder.bv_eq(wegner, naive)?;
        let indicator = builder.bv_ite(counts_equal, one1, zero1)?;
        let not_indicator = builder.bv_not(indicator)?;
        let indicator_is_zero = builder.bv_eq(not_indicator, zero1)?;
        let counterexample = builder.bool_not(indicator_is_zero)?;
        builder.assert(counterexample)?;
        let query = builder.finish()?;
        assert!(has_brummayer_popcount_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn polynomial_definition_contradiction_is_unsat() -> Result<()> {
        let query = crate::frontend::parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun var2 () (_ BitVec 8))
(declare-fun var3 () (_ BitVec 8))
(declare-fun var4 () (_ BitVec 8))
(declare-fun var8 () (_ BitVec 24))
(declare-fun var10 () (_ BitVec 24))
(declare-fun var12 () (_ BitVec 24))
(declare-fun var14 () (_ BitVec 24))
(declare-fun var16 () (_ BitVec 24))
(declare-fun var20 () (_ BitVec 24))
(declare-fun var28 () (_ BitVec 24))
(declare-fun var29 () (_ BitVec 1))
(declare-fun var30 () (_ BitVec 1))
(declare-fun var31 () (_ BitVec 1))
(declare-fun property () (_ BitVec 1))
(declare-fun Fresh__0 () (_ BitVec 1))
(declare-fun Fresh__1 () (_ BitVec 1))
(assert (= var8 (concat (_ bv0 16) var4)))
(assert (= var10 (concat (_ bv0 16) var3)))
(assert (= var12 (concat (_ bv0 16) var2)))
(assert (= var14 (bvmul var10 var12)))
(assert (= var16 (bvmul var8 var14)))
(assert (= var20 (bvmul var8 var10)))
(assert (= var28 (bvmul var12 var20)))
(assert (= (= Fresh__0 (_ bv1 1)) (= var16 var28)))
(assert (= var29 Fresh__0))
(assert (= var30 (bvnot (_ bv1 1))))
(assert (= var31 (bvor var29 var30)))
(assert (= property ((_ extract 0 0) var31)))
(assert (= (= Fresh__1 (_ bv1 1)) (= property (_ bv0 1))))
(assert (= (_ bv1 1) Fresh__1))
(check-sat)
"#,
        )?;
        assert!(has_polynomial_definition_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn polynomial_pack_equivalence_contradiction_is_unsat() -> Result<()> {
        let query = crate::frontend::parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun a0 () (_ BitVec 8))
(declare-fun a1 () (_ BitVec 8))
(declare-fun b0 () (_ BitVec 8))
(declare-fun b1 () (_ BitVec 8))
(declare-fun tail_a () (_ BitVec 8))
(declare-fun tail_b () (_ BitVec 8))
(declare-fun packed_a () (_ BitVec 16))
(declare-fun packed_b () (_ BitVec 16))
(assert (= packed_a (bvor (bvshl ((_ zero_extend 8) a1) (_ bv8 16)) ((_ zero_extend 8) a0))))
(assert (= packed_b (bvor (bvshl ((_ zero_extend 8) b1) (_ bv8 16)) ((_ zero_extend 8) b0))))
(assert (= ((_ zero_extend 16) packed_a) ((_ zero_extend 16) packed_b)))
(assert (= tail_a tail_b))
(assert (not (= (bvadd (bvmul ((_ zero_extend 24) a1) (_ bv3 32))
                       (bvadd ((_ zero_extend 24) a0) ((_ zero_extend 24) tail_a)))
                (bvadd (bvmul ((_ zero_extend 24) b1) (_ bv3 32))
                       (bvadd ((_ zero_extend 24) b0) ((_ zero_extend 24) tail_b))))))
(check-sat)
"#,
        )?;
        assert!(has_polynomial_definition_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn urem_remainder_fixed_point_contradiction_is_unsat() -> Result<()> {
        let mut builder = Builder::new();
        let n = builder.bv_var("n", 32)?;
        let n_prime = builder.bv_var("n_prime", 32)?;
        let d = builder.bv_var("d", 32)?;
        let m = builder.bv_var("m", 32)?;
        let alias = builder.bv_eq(n_prime, m)?;
        builder.assert(alias)?;
        let rem_n = builder.bv_urem(n, d)?;
        let rem_n_is_m = builder.bv_eq(rem_n, m)?;
        let m_is_d = builder.bv_eq(m, d)?;
        let guard = builder.bool_or(rem_n_is_m, m_is_d)?;
        builder.assert(guard)?;
        let rem_prime = builder.bv_urem(n_prime, d)?;
        let rem_prime_is_m = builder.bv_eq(rem_prime, m)?;
        let m_is_d = builder.bv_eq(m, d)?;
        let fixed_point_guard = builder.bool_or(rem_prime_is_m, m_is_d)?;
        let not_fixed_point = builder.bool_not(fixed_point_guard)?;
        builder.assert(not_fixed_point)?;
        let query = builder.finish()?;
        let mut solver = Solver::new(Config::default());
        let result = solver.solve(&query)?;
        assert_eq!(result.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn solve_once_with_expired_deadline_returns_unknown() -> Result<()> {
        let mut builder = Builder::new();
        let truth = builder.bool_true()?;
        builder.assert(truth)?;
        let query = builder.finish()?;
        let solver = Solver::new(Config::default());
        let result = solver.solve_once_with_deadline(
            &query,
            false,
            Some(Instant::now() - std::time::Duration::from_millis(1)),
        )?;
        assert_eq!(result.status, SolveStatus::Unknown);
        assert_eq!(result.message.as_deref(), Some("budget exhausted"));
        Ok(())
    }

    #[test]
    fn optimization_uses_total_budget_deadline() -> Result<()> {
        let mut builder = Builder::new();
        let x = builder.bv_var("x", 4)?;
        builder.set_optimization(Command::Minimize, x, false)?;
        let query = builder.finish()?;
        let config = Config::default().with_budget(Some(std::time::Duration::ZERO));
        let mut solver = Solver::new(config);
        let result = solver.solve(&query)?;
        assert_eq!(result.status, SolveStatus::Unknown);
        Ok(())
    }
}
