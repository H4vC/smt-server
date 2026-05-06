use crate::error::Result;
use crate::ir::{NodeKind, TermId};
use crate::query::Query;

use super::{bv_eq_pair, collect_bool_and_conjuncts, collect_bool_or_leaves, same_unordered_pair};

pub(in crate::solver) fn has_urem_remainder_fixed_point_contradiction(
    query: &Query,
) -> Result<bool> {
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
