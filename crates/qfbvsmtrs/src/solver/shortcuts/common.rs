use std::collections::HashMap;

use crate::error::Result;
use crate::ir::{NodeKind, TermId};
use crate::query::Query;

#[derive(Default)]
pub(in crate::solver) struct TermUnion {
    parent: HashMap<TermId, TermId>,
}

impl TermUnion {
    pub(in crate::solver) fn find(&mut self, term: TermId) -> TermId {
        let parent = *self.parent.entry(term).or_insert(term);
        if parent == term {
            term
        } else {
            let root = self.find(parent);
            self.parent.insert(term, root);
            root
        }
    }

    pub(in crate::solver) fn union(&mut self, a: TermId, b: TermId) {
        let a = self.find(a);
        let b = self.find(b);
        if a != b {
            self.parent.insert(a, b);
        }
    }

    pub(in crate::solver) fn equivalent(&mut self, a: TermId, b: TermId) -> bool {
        self.find(a) == self.find(b)
    }
}

pub(in crate::solver) fn equivalent_under_equalities(
    a: TermId,
    b: TermId,
    equalities: &[(TermId, TermId)],
) -> bool {
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

pub(in crate::solver) type BvPair = (TermId, TermId);
pub(in crate::solver) type BvSlice = (TermId, u32, u32);
pub(in crate::solver) fn collect_bool_or_leaves(
    query: &Query,
    term: TermId,
    out: &mut Vec<TermId>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolOr(a, b) => {
            collect_bool_or_leaves(query, *a, out)?;
            collect_bool_or_leaves(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

pub(in crate::solver) fn collect_bv_equalities_and_disequalities(
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

pub(in crate::solver) fn bv_add_parts(
    query: &Query,
    term: TermId,
) -> Result<Option<(TermId, TermId)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvAdd(a, b) => Some((*a, *b)),
        _ => None,
    })
}

pub(in crate::solver) fn is_shift_left_one_of(
    query: &Query,
    term: TermId,
    x: TermId,
) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvShl(value, amount) => *value == x && is_one_bv_const(query, *amount)?,
        NodeKind::BvMul(a, b) => {
            (*a == x && is_power_of_two_const(query, *b, 1)?)
                || (*b == x && is_power_of_two_const(query, *a, 1)?)
        }
        _ => false,
    })
}

pub(in crate::solver) fn is_asserted_nonzero_power_of_two(
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

pub(in crate::solver) fn same_unordered_pair(a: TermId, b: TermId, x: TermId, y: TermId) -> bool {
    (a == x && b == y) || (a == y && b == x)
}

pub(in crate::solver) fn is_one_bv_const(query: &Query, term: TermId) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => {
            bytes.first().copied() == Some(1) && bytes.iter().skip(1).all(|byte| *byte == 0)
        }
        _ => false,
    })
}

pub(in crate::solver) fn is_zero_bv_const(query: &Query, term: TermId) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => bytes.iter().all(|byte| *byte == 0),
        _ => false,
    })
}

pub(in crate::solver) fn is_power_of_two_const(
    query: &Query,
    term: TermId,
    bit: u32,
) -> Result<bool> {
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

pub(in crate::solver) fn is_all_ones_bv_const(
    query: &Query,
    term: TermId,
    width: u32,
) -> Result<bool> {
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

pub(in crate::solver) fn is_signed_min_bv_const(
    query: &Query,
    term: TermId,
    width: u32,
) -> Result<bool> {
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
