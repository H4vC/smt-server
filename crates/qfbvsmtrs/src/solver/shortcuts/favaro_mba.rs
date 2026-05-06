use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{
    bv_add_parts, bv_and_parts, bv_eq_pair, collect_bool_and_conjuncts, is_bv_const_u64,
    is_bv_not_of, same_unordered_pair,
};

pub(in crate::solver) fn has_favaro_mba_mul_contradiction(query: &Query) -> Result<bool> {
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
