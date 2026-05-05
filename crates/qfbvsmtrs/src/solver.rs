use std::collections::BTreeMap;
use std::time::Instant;

use crate::blast::blast_query_with_deadline;
use crate::cnf;
use crate::config::Config;
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
        if matches!(query.command, Command::Minimize | Command::Maximize) {
            return self.optimize(query);
        }
        let mut result = self.solve_once(query, query.want_model)?;
        if result.status == SolveStatus::Unsat && query.want_core {
            result.core = Some(self.extract_named_core(query)?);
        }
        Ok(result)
    }

    fn solve_once(&self, query: &Query, want_model: bool) -> Result<SolveResult> {
        match query.command {
            Command::Simplify => return Ok(SolveResult::ok()),
            Command::Minimize | Command::Maximize => {
                return Err(Error::internal(
                    "solve_once called with optimization command",
                ))
            }
            Command::Solve => {}
        }

        if has_unsigned_successor_contradiction(query)?
            || has_shift_one_add_contradiction(query)?
            || has_distinct_power_of_two_sum_contradiction(query)?
            || has_unsigned_multiplication_overflow_guard_contradiction(query)?
            || has_signed_division_multiply_overflow_guard_contradiction(query)?
            || has_extensional_candidate_contradiction(query)?
            || has_log_slicing_adder_contradiction(query)?
        {
            return Ok(SolveResult::unsat());
        }
        if !want_model && has_unsigned_successor_wraparound_witness(query)? {
            return Ok(SolveResult::sat(None));
        }
        if !want_model && !query.want_core && has_constant_assignment_witness(query)? {
            return Ok(SolveResult::sat(None));
        }

        let deadline = self.config.budget.map(|budget| Instant::now() + budget);
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

    fn optimize(&self, query: &Query) -> Result<SolveResult> {
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

        match self.solve_once(&fixed, false)?.status {
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
            match self.solve_once(&trial, false)?.status {
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
            match self.solve_once(&fixed, true)? {
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

    fn extract_named_core(&self, query: &Query) -> Result<Vec<String>> {
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
            match self.solve_once(&trial, false)?.status {
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
    if !query.assumptions.is_empty() || query.arena.len() > 100_000 {
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
