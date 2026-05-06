use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{
    collect_bool_or_leaves, collect_bv_xor_terms, is_zero_bv_const, same_unordered_pair, BvPair,
};

type LfsrFinalPattern = (Vec<BvPair>, Vec<TermId>);

#[derive(Debug, Clone, PartialEq, Eq)]
struct LfsrTransition {
    reset: TermId,
    from: TermId,
    to: TermId,
    signature: Vec<u32>,
}

pub(in crate::solver) fn has_synchronized_lfsr_contradiction(query: &Query) -> Result<bool> {
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

pub(super) fn collect_bool_and_conjuncts(
    query: &Query,
    term: TermId,
    out: &mut Vec<TermId>,
) -> Result<()> {
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

pub(super) fn bv_eq_pair(query: &Query, term: TermId) -> Result<Option<(TermId, TermId)>> {
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
