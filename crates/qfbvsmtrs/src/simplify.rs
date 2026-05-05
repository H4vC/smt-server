use crate::query::Query;

/// Runs the current word-level simplification pass.
///
/// Most cheap rewrites are applied eagerly by `Builder` while terms are
/// constructed: constant folding for common BV/Bool operations, identity and
/// annihilator rules, double negation, and trivial ITE reduction. This function
/// is intentionally cheap today and exists as the stable hook for future
/// whole-query/worklist rewrites such as extract/concat merging.
pub fn simplify(query: Query) -> Query {
    query
}
