use crate::error::Result;
use crate::ir::{NodeKind, TermId};
use crate::query::Query;

use super::TermUnion;

pub(super) fn has_direct_equality_disequality_contradiction(query: &Query) -> Result<bool> {
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
