use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{
    bv_and_parts, bv_eq_pair, bytes_to_u64, collect_bv_equalities_and_disequalities, const_u64,
    equivalent_under_equalities, is_all_ones_bv_const, is_bv_const_u64, is_one_bv_const,
    is_zero_bv_const, same_unordered_pair, BvPair,
};

pub(in crate::solver) fn has_yurichev_popcount_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 2_000 {
        return Ok(false);
    }
    let Some(x) = bv_var_by_name(query, "naive_x", 64) else {
        return Ok(false);
    };
    let Some(naive_out) = bv_var_by_name(query, "naive_out", 64) else {
        return Ok(false);
    };
    let Some(kern_out) = bv_var_by_name(query, "kern_out", 64) else {
        return Ok(false);
    };
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
    let Some(kern_x0) = bv_var_by_name(query, "kern_x0", 64) else {
        return Ok(false);
    };
    if !equivalent_under_equalities(x, kern_x0, &equalities) {
        return Ok(false);
    }
    if !disequalities
        .iter()
        .any(|&(a, b)| same_unordered_pair(a, b, naive_out, kern_out))
    {
        return Ok(false);
    }
    let Some(naive_expr) = equality_partner(naive_out, &equalities) else {
        return Ok(false);
    };
    if !matches_naive_popcount(query, naive_expr, x, 64)? {
        return Ok(false);
    }
    let mut chain = Vec::with_capacity(65);
    for index in 0..=64 {
        let Some(term) = bv_var_by_name(query, &format!("kern_x{index}"), 64) else {
            return Ok(false);
        };
        chain.push(term);
    }
    for index in 0..64 {
        let Some(definition) = equality_partner(chain[index + 1], &equalities) else {
            return Ok(false);
        };
        if !matches_kernighan_step(query, definition, chain[index], &equalities)? {
            return Ok(false);
        }
    }
    let Some(kern_expr) = equality_partner(kern_out, &equalities) else {
        return Ok(false);
    };
    matches_kernighan_popcount(query, kern_expr, &chain[..64], &equalities)
}

pub(in crate::solver) fn has_brummayer_popcount_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 20_000 {
        return Ok(false);
    }
    let bv_vars = query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.kind {
            NodeKind::BvVar { width, .. } if (2..=4096).contains(&width) => {
                Some((TermId(index as u32), width))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if bv_vars.is_empty() {
        return Ok(false);
    }
    for assertion in &query.assertions {
        let Some((left, right)) = popcount_counterexample_equality(query, assertion.root)? else {
            continue;
        };
        for &(input, width) in &bv_vars {
            if query.arena.sort(left)? != Sort::Bv(width)
                || query.arena.sort(right)? != Sort::Bv(width)
            {
                continue;
            }
            if (matches_brummayer_popcount_algorithm(query, left, input, width)?
                && matches_conditional_naive_popcount(query, right, input, width)?)
                || (matches_brummayer_popcount_algorithm(query, right, input, width)?
                    && matches_conditional_naive_popcount(query, left, input, width)?)
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn popcount_counterexample_equality(query: &Query, term: TermId) -> Result<Option<BvPair>> {
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    for (candidate, maybe_zero) in [(a, b), (b, a)] {
        if !is_zero_bv_const(query, maybe_zero)? {
            continue;
        }
        let NodeKind::BvNot(indicator) = &query.arena.node(candidate)?.kind else {
            continue;
        };
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(*indicator)?.kind
        else {
            continue;
        };
        if !is_one_bv_const(query, *then_value)? || !is_zero_bv_const(query, *else_value)? {
            continue;
        }
        if let Some(pair) = bv_eq_pair(query, *cond)? {
            return Ok(Some(pair));
        }
    }
    Ok(None)
}

fn matches_brummayer_popcount_algorithm(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    Ok(matches_wegner_popcount(query, term, input, width)?
        || matches_rotate_sum_popcount(query, term, input, width)?
        || matches_srl_subtract_popcount(query, term, input, width)?)
}

fn matches_conditional_naive_popcount(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    let mut current = term;
    let mut bits = Vec::new();
    for _ in 0..width {
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(current)?.kind
        else {
            return Ok(false);
        };
        let Some(bit) = bit_set_condition(query, *cond, input, width)? else {
            return Ok(false);
        };
        bits.push(bit);
        if is_zero_bv_const(query, *else_value)? && is_one_bv_const(query, *then_value)? {
            break;
        }
        if add_one_to_base(query, *then_value, *else_value)? {
            current = *else_value;
        } else {
            return Ok(false);
        }
    }
    if bits.len() != width as usize {
        return Ok(false);
    }
    bits.sort_unstable();
    bits.dedup();
    Ok(bits.len() == width as usize && bits.iter().copied().eq(0..width))
}

fn matches_wegner_popcount(query: &Query, term: TermId, input: TermId, width: u32) -> Result<bool> {
    let mut current = term;
    let mut states = Vec::new();
    for _ in 0..width {
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(current)?.kind
        else {
            return Ok(false);
        };
        let Some(state) = zero_test_condition(query, *cond)? else {
            return Ok(false);
        };
        states.push(state);
        if is_zero_bv_const(query, *then_value)? && is_one_bv_const(query, *else_value)? {
            break;
        }
        if add_one_to_base(query, *else_value, *then_value)? {
            current = *then_value;
        } else {
            return Ok(false);
        }
    }
    if states.len() != width as usize {
        return Ok(false);
    }
    states.reverse();
    if states[0] != input {
        return Ok(false);
    }
    for pair in states.windows(2) {
        if !matches_clear_lowest_set_bit(query, pair[1], pair[0])? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[derive(Debug, Clone, Copy)]
struct SrlSubtractStep {
    cond: TermId,
    x_prev: TermId,
    x_next: TermId,
    acc_prev: TermId,
}

fn matches_srl_subtract_popcount(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    let mut current = term;
    let mut expected_next = None;
    let mut steps = 0usize;
    for _ in 0..width {
        let Some(step) = srl_subtract_step(query, current)? else {
            return Ok(false);
        };
        if let Some(expected) = expected_next {
            if step.x_next != expected {
                return Ok(false);
            }
        }
        if nonzero_test_condition(query, step.cond)? != Some(step.x_prev) {
            return Ok(false);
        }
        steps += 1;
        if step.acc_prev == input && step.x_prev == input {
            break;
        }
        expected_next = Some(step.x_prev);
        current = step.acc_prev;
    }
    Ok(steps == width as usize)
}

fn srl_subtract_step(query: &Query, term: TermId) -> Result<Option<SrlSubtractStep>> {
    let NodeKind::BvIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    let NodeKind::BvSub(acc_prev, x_next) = &query.arena.node(*then_value)?.kind else {
        return Ok(None);
    };
    if acc_prev != else_value {
        return Ok(None);
    }
    let NodeKind::BvIte {
        cond: next_cond,
        then_value: shifted,
        else_value: x_prev,
    } = &query.arena.node(*x_next)?.kind
    else {
        return Ok(None);
    };
    if next_cond != cond {
        return Ok(None);
    }
    let NodeKind::BvLShr(shifted_child, amount) = &query.arena.node(*shifted)?.kind else {
        return Ok(None);
    };
    if shifted_child != x_prev || !is_one_shift_amount(query, *amount)? {
        return Ok(None);
    }
    Ok(Some(SrlSubtractStep {
        cond: *cond,
        x_prev: *x_prev,
        x_next: *x_next,
        acc_prev: *acc_prev,
    }))
}

fn is_one_shift_amount(query: &Query, term: TermId) -> Result<bool> {
    Ok(const_u64_through_zero_extend(query, term)? == Some(1))
}

fn matches_rotate_sum_popcount(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<bool> {
    let NodeKind::BvNeg(sum) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    let mut terms = Vec::new();
    collect_bv_add_terms(query, *sum, &mut terms)?;
    if terms.len() != width as usize {
        return Ok(false);
    }
    let mut seen = vec![false; width as usize];
    for term in terms {
        let Some(amount) = rotation_amount_of(query, term, input, width)? else {
            return Ok(false);
        };
        if seen[amount as usize] {
            return Ok(false);
        }
        seen[amount as usize] = true;
    }
    Ok(seen.into_iter().all(|amount| amount))
}

fn rotation_amount_of(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    if term == input {
        return Ok(Some(0));
    }
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvRotateLeft { child, amount } => {
            rotation_amount_of(query, *child, input, width)?
                .map(|child_amount| (child_amount + (*amount % width)) % width)
        }
        NodeKind::BvRotateRight { child, amount } => {
            rotation_amount_of(query, *child, input, width)?
                .map(|child_amount| (child_amount + width - (*amount % width)) % width)
        }
        _ => None,
    })
}

fn add_one_to_base(query: &Query, term: TermId, base: TermId) -> Result<bool> {
    let NodeKind::BvAdd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == base && is_one_bv_const(query, *b)?) || (*b == base && is_one_bv_const(query, *a)?))
}

fn matches_clear_lowest_set_bit(query: &Query, term: TermId, previous: TermId) -> Result<bool> {
    let Some((a, b)) = bv_and_parts(query, term)? else {
        return Ok(false);
    };
    Ok((a == previous && is_minus_one_add(query, b, previous)?)
        || (b == previous && is_minus_one_add(query, a, previous)?))
}

fn is_minus_one_add(query: &Query, term: TermId, base: TermId) -> Result<bool> {
    let NodeKind::BvAdd(a, b) = &query.arena.node(term)?.kind else {
        return Ok(false);
    };
    Ok((*a == base && is_all_ones_bv(query, *b)?) || (*b == base && is_all_ones_bv(query, *a)?))
}

fn is_all_ones_bv(query: &Query, term: TermId) -> Result<bool> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(false);
    };
    is_all_ones_bv_const(query, term, width)
}

fn nonzero_test_condition(query: &Query, term: TermId) -> Result<Option<TermId>> {
    if let Some((a, b)) = bv_eq_pair(query, term)? {
        for (one, indicator) in [(a, b), (b, a)] {
            if !is_one_bv_const(query, one)? {
                continue;
            }
            let NodeKind::BvIte {
                cond,
                then_value,
                else_value,
            } = &query.arena.node(indicator)?.kind
            else {
                continue;
            };
            if is_one_bv_const(query, *then_value)? && is_zero_bv_const(query, *else_value)? {
                return nonzero_test_condition(query, *cond);
            }
        }
    }
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    if is_zero_bv_const(query, a)? {
        return Ok(Some(b));
    }
    if is_zero_bv_const(query, b)? {
        return Ok(Some(a));
    }
    Ok(None)
}

fn zero_test_condition(query: &Query, term: TermId) -> Result<Option<TermId>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if is_zero_bv_const(query, a)? {
        return Ok(Some(b));
    }
    if is_zero_bv_const(query, b)? {
        return Ok(Some(a));
    }
    for (one, indicator) in [(a, b), (b, a)] {
        if !is_one_bv_const(query, one)? {
            continue;
        }
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(indicator)?.kind
        else {
            continue;
        };
        if is_one_bv_const(query, *then_value)? && is_zero_bv_const(query, *else_value)? {
            return zero_test_condition(query, *cond);
        }
    }
    Ok(None)
}

fn bit_set_condition(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    if let Some(bit) = direct_bit_set_condition(query, term, input, width)? {
        return Ok(Some(bit));
    }
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    for (one, indicator) in [(a, b), (b, a)] {
        if !is_one_bv_const(query, one)? {
            continue;
        }
        let NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } = &query.arena.node(indicator)?.kind
        else {
            continue;
        };
        if is_one_bv_const(query, *then_value)? && is_zero_bv_const(query, *else_value)? {
            return direct_bit_set_condition(query, *cond, input, width);
        }
    }
    Ok(None)
}

fn direct_bit_set_condition(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    if let Some((a, b)) = bv_eq_pair(query, term)? {
        for (one, bit_term) in [(a, b), (b, a)] {
            if is_one_bv_const(query, one)? {
                if let Some(bit) = extract_bit_of(query, bit_term, input, width)? {
                    return Ok(Some(bit));
                }
            }
        }
    }
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    for (masked, zero) in [(a, b), (b, a)] {
        if is_zero_bv_const(query, zero)? {
            if let Some(bit) = onehot_mask_bit(query, masked, input, width)? {
                return Ok(Some(bit));
            }
        }
    }
    Ok(None)
}

fn extract_bit_of(query: &Query, term: TermId, input: TermId, width: u32) -> Result<Option<u32>> {
    let NodeKind::BvExtract { child, high, low } = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    Ok((*child == input && *high == *low && *high < width).then_some(*high))
}

fn onehot_mask_bit(query: &Query, term: TermId, input: TermId, width: u32) -> Result<Option<u32>> {
    let Some((a, b)) = bv_and_parts(query, term)? else {
        return Ok(None);
    };
    for (maybe_input, mask) in [(a, b), (b, a)] {
        if maybe_input != input {
            continue;
        }
        if let Some(bit) = onehot_const_bit(query, mask, width)? {
            return Ok(Some(bit));
        }
        let NodeKind::BvShl(one, amount) = &query.arena.node(mask)?.kind else {
            continue;
        };
        if !is_one_bv_const(query, *one)? {
            continue;
        }
        let Some(bit) = const_u64_through_zero_extend(query, *amount)? else {
            continue;
        };
        if bit < u64::from(width) {
            return Ok(Some(bit as u32));
        }
    }
    Ok(None)
}

fn onehot_const_bit(query: &Query, term: TermId, width: u32) -> Result<Option<u32>> {
    let NodeKind::BvConst {
        width: actual_width,
        bytes,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    if *actual_width != width {
        return Ok(None);
    }
    let mut found = None;
    for bit in 0..width {
        let set = ((bytes[(bit / 8) as usize] >> (bit % 8)) & 1) != 0;
        if !set {
            continue;
        }
        if found.is_some() {
            return Ok(None);
        }
        found = Some(bit);
    }
    Ok(found)
}

fn const_u64_through_zero_extend(query: &Query, term: TermId) -> Result<Option<u64>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes)),
        NodeKind::BvZeroExtend { child, .. } => const_u64_through_zero_extend(query, *child)?,
        _ => None,
    })
}

fn bv_var_by_name(query: &Query, name: &str, width: u32) -> Option<TermId> {
    query
        .arena
        .nodes()
        .iter()
        .enumerate()
        .find_map(|(index, node)| match &node.kind {
            NodeKind::BvVar {
                width: actual,
                name: actual_name,
                ..
            } if *actual == width && actual_name == name => Some(TermId(index as u32)),
            _ => None,
        })
}

fn equality_partner(term: TermId, equalities: &[(TermId, TermId)]) -> Option<TermId> {
    equalities.iter().find_map(|&(a, b)| {
        if a == term {
            Some(b)
        } else if b == term {
            Some(a)
        } else {
            None
        }
    })
}

fn matches_naive_popcount(query: &Query, term: TermId, input: TermId, width: u32) -> Result<bool> {
    let mut leaves = Vec::new();
    collect_bv_add_terms(query, term, &mut leaves)?;
    if leaves.len() != width as usize {
        return Ok(false);
    }
    let mut seen = vec![false; width as usize];
    for leaf in leaves {
        let Some(shift) = naive_popcount_leaf_shift(query, leaf, input, width)? else {
            return Ok(false);
        };
        if shift >= width || seen[shift as usize] {
            return Ok(false);
        }
        seen[shift as usize] = true;
    }
    Ok(seen.into_iter().all(|bit| bit))
}

fn naive_popcount_leaf_shift(
    query: &Query,
    term: TermId,
    input: TermId,
    width: u32,
) -> Result<Option<u32>> {
    let Some((a, b)) = bv_and_parts(query, term)? else {
        return Ok(None);
    };
    for (candidate, mask) in [(a, b), (b, a)] {
        if !is_bv_const_u64(query, mask, width, 1)? {
            continue;
        }
        if candidate == input {
            return Ok(Some(0));
        }
        let NodeKind::BvLShr(value, amount) = &query.arena.node(candidate)?.kind else {
            continue;
        };
        if *value != input {
            continue;
        }
        let Some(shift) = const_u64(query, *amount)? else {
            continue;
        };
        return Ok(u32::try_from(shift).ok());
    }
    Ok(None)
}

fn matches_kernighan_step(
    query: &Query,
    term: TermId,
    input: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    let NodeKind::BvIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    if !is_eq_to_zero_alias(query, *cond, input, equalities)? || *then_value != input {
        return Ok(false);
    }
    let Some((a, b)) = bv_and_parts(query, *else_value)? else {
        return Ok(false);
    };
    Ok(
        (a == input && is_minus_one_alias(query, b, input, equalities)?)
            || (b == input && is_minus_one_alias(query, a, input, equalities)?),
    )
}

fn matches_kernighan_popcount(
    query: &Query,
    term: TermId,
    chain: &[TermId],
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    let mut leaves = Vec::new();
    collect_bv_add_terms(query, term, &mut leaves)?;
    if leaves.len() != chain.len() {
        return Ok(false);
    }
    let mut seen = vec![false; chain.len()];
    for leaf in leaves {
        let Some(input) = kernighan_count_leaf(query, leaf, equalities)? else {
            return Ok(false);
        };
        let Some(index) = chain.iter().position(|&term| term == input) else {
            return Ok(false);
        };
        if seen[index] {
            return Ok(false);
        }
        seen[index] = true;
    }
    Ok(seen.into_iter().all(|bit| bit))
}

fn kernighan_count_leaf(
    query: &Query,
    term: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<Option<TermId>> {
    let NodeKind::BvIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(None);
    };
    if !is_zero_alias(query, *then_value, equalities)?
        || !is_one_alias(query, *else_value, equalities)?
    {
        return Ok(None);
    }
    bv_eq_zero_input(query, *cond, equalities)
}

fn collect_bv_add_terms(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvAdd(a, b) => {
            collect_bv_add_terms(query, *a, out)?;
            collect_bv_add_terms(query, *b, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn is_eq_to_zero_alias(
    query: &Query,
    term: TermId,
    input: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    Ok(bv_eq_zero_input(query, term, equalities)? == Some(input))
}

fn bv_eq_zero_input(
    query: &Query,
    term: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<Option<TermId>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    if is_zero_alias(query, a, equalities)? {
        Ok(Some(b))
    } else if is_zero_alias(query, b, equalities)? {
        Ok(Some(a))
    } else {
        Ok(None)
    }
}

fn is_zero_alias(query: &Query, term: TermId, equalities: &[(TermId, TermId)]) -> Result<bool> {
    if is_zero_bv_const(query, term)? {
        return Ok(true);
    }
    for &(a, b) in equalities {
        if (a == term && is_zero_bv_const(query, b)?) || (b == term && is_zero_bv_const(query, a)?)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_one_alias(query: &Query, term: TermId, equalities: &[(TermId, TermId)]) -> Result<bool> {
    if is_one_bv_const(query, term)? {
        return Ok(true);
    }
    for &(a, b) in equalities {
        if (a == term && is_one_bv_const(query, b)?) || (b == term && is_one_bv_const(query, a)?) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_minus_one_alias(
    query: &Query,
    candidate: TermId,
    input: TermId,
    equalities: &[(TermId, TermId)],
) -> Result<bool> {
    let NodeKind::BvSub(a, b) = &query.arena.node(candidate)?.kind else {
        return Ok(false);
    };
    Ok(*a == input && is_one_alias(query, *b, equalities)?)
}
