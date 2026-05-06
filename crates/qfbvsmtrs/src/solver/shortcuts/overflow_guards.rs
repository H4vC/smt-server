use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{
    collect_bv_equalities_and_disequalities, collect_unsigned_less_or_equal, is_all_ones_bv_const,
    is_signed_min_bv_const, is_zero_bv_const,
};

pub(in crate::solver) fn has_signed_division_multiply_overflow_guard_contradiction(
    query: &Query,
) -> Result<bool> {
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

pub(in crate::solver) fn has_unsigned_multiplication_overflow_guard_contradiction(
    query: &Query,
) -> Result<bool> {
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
