use std::collections::BTreeMap;

use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::is_one_bv_const;

pub(in crate::solver) fn has_unsigned_successor_contradiction(query: &Query) -> Result<bool> {
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

pub(in crate::solver) fn has_unsigned_successor_wraparound_witness(
    query: &Query,
    validate: bool,
) -> Result<bool> {
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
    for &(left, right) in &non_strict {
        for &(other_left, other_right) in &non_strict {
            if other_left != left
                && other_left != right
                && left == other_right
                && is_unsigned_successor_term(query, other_left, right)?
            {
                return if validate {
                    validate_unsigned_successor_wraparound_witness(query, left, right)
                } else {
                    Ok(true)
                };
            }
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

fn validate_unsigned_successor_wraparound_witness(
    query: &Query,
    left: TermId,
    right: TermId,
) -> Result<bool> {
    let width = match (query.arena.sort(left)?, query.arena.sort(right)?) {
        (Sort::Bv(left_width), Sort::Bv(right_width)) if left_width == right_width => left_width,
        _ => return Ok(false),
    };
    if !matches!(query.arena.node(left)?.kind, NodeKind::BvVar { .. })
        || !matches!(query.arena.node(right)?.kind, NodeKind::BvVar { .. })
    {
        return Ok(false);
    }
    let mut assignment = BTreeMap::new();
    assignment.insert(left, vec![0u8; crate::ir::bytes_for_width(width)?]);
    let mut max = vec![0xffu8; crate::ir::bytes_for_width(width)?];
    crate::ir::mask_unused_high_bits(&mut max, width);
    assignment.insert(right, max);
    crate::eval::query_satisfied_by_bv_assignment(query, &assignment)
}

pub(super) fn collect_unsigned_less_or_equal(
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
