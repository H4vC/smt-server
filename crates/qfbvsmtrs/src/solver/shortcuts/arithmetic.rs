use crate::error::Result;
use crate::query::Query;

use super::{
    bv_add_parts, collect_bv_equalities_and_disequalities, is_asserted_nonzero_power_of_two,
    is_shift_left_one_of, same_unordered_pair,
};

pub(in crate::solver) fn has_shift_one_add_contradiction(query: &Query) -> Result<bool> {
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
    for &(z1, sum) in &equalities {
        let Some((x, y)) = bv_add_parts(query, sum)? else {
            continue;
        };
        for &(z2, shifted) in &equalities {
            if z1 != z2 || !is_shift_left_one_of(query, shifted, x)? {
                continue;
            }
            if disequalities
                .iter()
                .any(|&(a, b)| same_unordered_pair(a, b, x, y))
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

pub(in crate::solver) fn has_distinct_power_of_two_sum_contradiction(
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
    for &(z, sum) in &equalities {
        let Some((x, y)) = bv_add_parts(query, sum)? else {
            continue;
        };
        if !disequalities
            .iter()
            .any(|&(a, b)| same_unordered_pair(a, b, x, y))
        {
            continue;
        }
        if is_asserted_nonzero_power_of_two(query, x, &equalities, &disequalities)?
            && is_asserted_nonzero_power_of_two(query, y, &equalities, &disequalities)?
            && is_asserted_nonzero_power_of_two(query, z, &equalities, &disequalities)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}
