use std::collections::BTreeMap;

use crate::error::{Error, Result};
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{
    bv_eq_pair, collect_bool_and_conjuncts, collect_bv_equalities_and_disequalities,
    is_bv_const_u64, is_one_bv_const, is_zero_bv_const, matches_extract, same_unordered_pair,
    BvPair, BvSlice,
};

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

pub(in crate::solver) fn has_log_slicing_shift_contradiction(query: &Query) -> Result<bool> {
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

pub(in crate::solver) fn has_log_slicing_comparison_contradiction(query: &Query) -> Result<bool> {
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

pub(in crate::solver) fn has_log_slicing_adder_contradiction(query: &Query) -> Result<bool> {
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

pub(super) fn collect_bv_xor_terms(
    query: &Query,
    term: TermId,
    out: &mut Vec<TermId>,
) -> Result<()> {
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

pub(super) fn bv_and_parts(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
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

pub(super) fn is_bv_not_of(query: &Query, candidate: TermId, child: TermId) -> Result<bool> {
    Ok(matches!(
        &query.arena.node(candidate)?.kind,
        NodeKind::BvNot(actual) if *actual == child
    ))
}
