use std::collections::BTreeMap;

use crate::error::Result;
use crate::ir::{NodeKind, TermId};
use crate::query::Query;

use super::collect_bool_or_leaves;

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

pub(in crate::solver) fn has_extensional_candidate_contradiction(query: &Query) -> Result<bool> {
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
