use std::collections::{BTreeMap, HashMap};

use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{bytes_to_u64, const_u64, mask_for_width, TermUnion};

#[derive(Debug, Clone, PartialEq, Eq)]
struct BvPolynomial {
    width: u32,
    terms: BTreeMap<Vec<TermId>, u64>,
}

pub(in crate::solver) fn has_polynomial_definition_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 100_000 {
        return Ok(false);
    }
    let mut raw_definitions = HashMap::<TermId, Option<TermId>>::new();
    for assertion in &query.assertions {
        collect_bv_var_definitions(query, assertion.root, &mut raw_definitions)?;
    }
    let definitions = raw_definitions
        .into_iter()
        .filter_map(|(var, definition)| definition.map(|definition| (var, definition)))
        .collect::<HashMap<_, _>>();
    if definitions.is_empty() {
        return Ok(false);
    }
    let pack_definitions = collect_polynomial_pack_definitions(query, &definitions)?;
    let mut union = TermUnion::default();
    for assertion in &query.assertions {
        collect_polynomial_equivalences(
            query,
            assertion.root,
            &definitions,
            &pack_definitions,
            &mut union,
        )?;
    }
    let mut canonical = HashMap::new();
    for index in 0..query.arena.len() {
        let term = TermId(index as u32);
        let root = union.find(term);
        if root != term {
            canonical.insert(term, root);
        }
    }

    let mut constants = HashMap::<TermId, u64>::new();
    for _ in 0..16 {
        let mut changed = false;
        for assertion in &query.assertions {
            let (contradiction, fact_changed) = infer_asserted_polynomial_fact(
                query,
                assertion.root,
                &definitions,
                &canonical,
                &mut constants,
            )?;
            if contradiction {
                return Ok(true);
            }
            changed |= fact_changed;
            let (contradiction, const_changed) = infer_bv_const_definition(
                query,
                assertion.root,
                &definitions,
                &canonical,
                &mut constants,
            )?;
            if contradiction {
                return Ok(true);
            }
            changed |= const_changed;
        }
        if !changed {
            break;
        }
    }

    query.assertions.iter().try_fold(false, |found, assertion| {
        Ok(found
            || eval_polynomial_bool(query, assertion.root, &definitions, &canonical, &constants)?
                == Some(false))
    })
}

fn collect_bv_var_definitions(
    query: &Query,
    term: TermId,
    out: &mut HashMap<TermId, Option<TermId>>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => {
            record_bv_var_definition(query, *a, *b, out)?;
            record_bv_var_definition(query, *b, *a, out)?;
        }
        NodeKind::BoolAnd(a, b) => {
            collect_bv_var_definitions(query, *a, out)?;
            collect_bv_var_definitions(query, *b, out)?;
        }
        _ => {}
    }
    Ok(())
}

fn record_bv_var_definition(
    query: &Query,
    var: TermId,
    definition: TermId,
    out: &mut HashMap<TermId, Option<TermId>>,
) -> Result<()> {
    if var == definition
        || !matches!(query.arena.node(var)?.kind, NodeKind::BvVar { .. })
        || matches!(query.arena.node(definition)?.kind, NodeKind::BvVar { .. })
    {
        return Ok(());
    }
    let entry = out.entry(var).or_insert(Some(definition));
    if *entry != Some(definition) {
        *entry = None;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct PolynomialPackDefinition {
    high: TermId,
    low: TermId,
}

fn collect_polynomial_pack_definitions(
    query: &Query,
    definitions: &HashMap<TermId, TermId>,
) -> Result<HashMap<TermId, PolynomialPackDefinition>> {
    let mut packs = HashMap::new();
    for (&var, &definition) in definitions {
        if let Some(pack) = polynomial_byte_pack(query, definition)? {
            packs.insert(var, pack);
        }
    }
    Ok(packs)
}

fn polynomial_byte_pack(query: &Query, term: TermId) -> Result<Option<PolynomialPackDefinition>> {
    let NodeKind::BvOr(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if let Some(pack) = polynomial_byte_pack_parts(query, *a, *b)? {
        return Ok(Some(pack));
    }
    polynomial_byte_pack_parts(query, *b, *a)
}

fn polynomial_byte_pack_parts(
    query: &Query,
    shifted_high: TermId,
    low_part: TermId,
) -> Result<Option<PolynomialPackDefinition>> {
    let NodeKind::BvShl(high_extended, amount) = &query.arena.node(shifted_high)?.kind else {
        return Ok(None);
    };
    let Some(shift) = const_u64(query, *amount)? else {
        return Ok(None);
    };
    let Some((high, high_width, total_width)) = zero_extended_bv_var(query, *high_extended)? else {
        return Ok(None);
    };
    let Some((low, low_width, low_total_width)) = zero_extended_bv_var(query, low_part)? else {
        return Ok(None);
    };
    if total_width != low_total_width
        || shift != u64::from(low_width)
        || high_width + low_width != total_width
    {
        return Ok(None);
    }
    Ok(Some(PolynomialPackDefinition { high, low }))
}

fn zero_extended_bv_var(query: &Query, term: TermId) -> Result<Option<(TermId, u32, u32)>> {
    let NodeKind::BvZeroExtend { child, extra } = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Sort::Bv(child_width) = query.arena.sort(*child)? else {
        return Ok(None);
    };
    if !matches!(query.arena.node(*child)?.kind, NodeKind::BvVar { .. }) {
        return Ok(None);
    }
    Ok(Some((*child, child_width, child_width + extra)))
}

fn collect_polynomial_equivalences(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    packs: &HashMap<TermId, PolynomialPackDefinition>,
    union: &mut TermUnion,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            collect_polynomial_equivalences(query, *a, definitions, packs, union)?;
            collect_polynomial_equivalences(query, *b, definitions, packs, union)?;
        }
        NodeKind::BvEq(a, b) => {
            union_polynomial_equal_terms(query, *a, *b, definitions, packs, union)?;
        }
        _ => {}
    }
    Ok(())
}

fn union_polynomial_equal_terms(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    packs: &HashMap<TermId, PolynomialPackDefinition>,
    union: &mut TermUnion,
) -> Result<()> {
    if query.arena.sort(a)? == query.arena.sort(b)?
        && matches!(query.arena.node(a)?.kind, NodeKind::BvVar { .. })
        && matches!(query.arena.node(b)?.kind, NodeKind::BvVar { .. })
    {
        union.union(a, b);
        union_polynomial_packs(a, b, packs, union);
    }
    if let (Some((left, left_extra)), Some((right, right_extra))) = (
        zero_extend_child_with_extra(query, a)?,
        zero_extend_child_with_extra(query, b)?,
    ) {
        if left_extra == right_extra && query.arena.sort(left)? == query.arena.sort(right)? {
            union.union(left, right);
            union_polynomial_packs(left, right, packs, union);
        }
    }
    if let (Some(&left_def), Some(&right_def)) = (definitions.get(&a), definitions.get(&b)) {
        union_polynomial_equal_terms(query, left_def, right_def, definitions, packs, union)?;
    }
    Ok(())
}

fn zero_extend_child_with_extra(query: &Query, term: TermId) -> Result<Option<(TermId, u32)>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvZeroExtend { child, extra } => Some((*child, *extra)),
        _ => None,
    })
}

fn union_polynomial_packs(
    a: TermId,
    b: TermId,
    packs: &HashMap<TermId, PolynomialPackDefinition>,
    union: &mut TermUnion,
) {
    let (Some(left), Some(right)) = (packs.get(&a), packs.get(&b)) else {
        return;
    };
    union.union(left.high, right.high);
    union.union(left.low, right.low);
}

fn canonical_polynomial_term(canonical: &HashMap<TermId, TermId>, term: TermId) -> TermId {
    canonical.get(&term).copied().unwrap_or(term)
}

fn infer_asserted_polynomial_fact(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &mut HashMap<TermId, u64>,
) -> Result<(bool, bool)> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            let (left_contradiction, left_changed) =
                infer_asserted_polynomial_fact(query, *a, definitions, canonical, constants)?;
            let (right_contradiction, right_changed) =
                infer_asserted_polynomial_fact(query, *b, definitions, canonical, constants)?;
            Ok((
                left_contradiction || right_contradiction,
                left_changed || right_changed,
            ))
        }
        NodeKind::BoolEq(a, b) => {
            let left = eval_polynomial_bool(query, *a, definitions, canonical, constants)?;
            let right = eval_polynomial_bool(query, *b, definitions, canonical, constants)?;
            if matches!((left, right), (Some(l), Some(r)) if l != r) {
                return Ok((true, false));
            }
            if let Some(value) = left {
                if let Some((var, if_true, if_false)) = bv_bit_equality_selector(query, *b)? {
                    return Ok(assign_polynomial_const(
                        canonical,
                        constants,
                        var,
                        if value { if_true } else { if_false },
                    ));
                }
            }
            if let Some(value) = right {
                if let Some((var, if_true, if_false)) = bv_bit_equality_selector(query, *a)? {
                    return Ok(assign_polynomial_const(
                        canonical,
                        constants,
                        var,
                        if value { if_true } else { if_false },
                    ));
                }
            }
            Ok((false, false))
        }
        _ => Ok((
            eval_polynomial_bool(query, term, definitions, canonical, constants)? == Some(false),
            false,
        )),
    }
}

fn infer_bv_const_definition(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &mut HashMap<TermId, u64>,
) -> Result<(bool, bool)> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            let (left_contradiction, left_changed) =
                infer_bv_const_definition(query, *a, definitions, canonical, constants)?;
            let (right_contradiction, right_changed) =
                infer_bv_const_definition(query, *b, definitions, canonical, constants)?;
            Ok((
                left_contradiction || right_contradiction,
                left_changed || right_changed,
            ))
        }
        NodeKind::BvEq(a, b) => {
            if let Some((var, value)) =
                bv_var_const_from_terms(query, *a, *b, definitions, canonical, constants)?
            {
                return Ok(assign_polynomial_const(canonical, constants, var, value));
            }
            Ok((false, false))
        }
        _ => Ok((false, false)),
    }
}

fn assign_polynomial_const(
    canonical: &HashMap<TermId, TermId>,
    constants: &mut HashMap<TermId, u64>,
    var: TermId,
    value: u64,
) -> (bool, bool) {
    let var = canonical_polynomial_term(canonical, var);
    match constants.get(&var).copied() {
        Some(previous) => (previous != value, false),
        None => {
            constants.insert(var, value);
            (false, true)
        }
    }
}

fn bv_var_const_from_terms(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<(TermId, u64)>> {
    if matches!(query.arena.node(a)?.kind, NodeKind::BvVar { .. }) {
        if let Some(value) = eval_polynomial_bv_const(query, b, definitions, canonical, constants)?
        {
            let width = query.arena.expect_bv(a, "polynomial const var")?;
            return Ok(Some((a, value & mask_for_width(width))));
        }
    }
    if matches!(query.arena.node(b)?.kind, NodeKind::BvVar { .. }) {
        if let Some(value) = eval_polynomial_bv_const(query, a, definitions, canonical, constants)?
        {
            let width = query.arena.expect_bv(b, "polynomial const var")?;
            return Ok(Some((b, value & mask_for_width(width))));
        }
    }
    if let Some((var, extra)) = zero_extend_child_with_extra(query, a)? {
        if matches!(query.arena.node(var)?.kind, NodeKind::BvVar { .. }) {
            if let Some(value) =
                eval_polynomial_bv_const(query, b, definitions, canonical, constants)?
            {
                let width = query
                    .arena
                    .expect_bv(var, "polynomial const zero-extend var")?;
                if extra == 0 || width >= 64 || value >> width == 0 {
                    return Ok(Some((var, value & mask_for_width(width))));
                }
            }
        }
    }
    if let Some((var, extra)) = zero_extend_child_with_extra(query, b)? {
        if matches!(query.arena.node(var)?.kind, NodeKind::BvVar { .. }) {
            if let Some(value) =
                eval_polynomial_bv_const(query, a, definitions, canonical, constants)?
            {
                let width = query
                    .arena
                    .expect_bv(var, "polynomial const zero-extend var")?;
                if extra == 0 || width >= 64 || value >> width == 0 {
                    return Ok(Some((var, value & mask_for_width(width))));
                }
            }
        }
    }
    Ok(None)
}

fn bv_bit_equality_selector(query: &Query, term: TermId) -> Result<Option<(TermId, u64, u64)>> {
    let NodeKind::BvEq(a, b) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    if let Some((var, value)) = raw_width_one_var_const(query, *a, *b)? {
        return Ok(Some((var, value, value ^ 1)));
    }
    raw_width_one_var_const(query, *b, *a)
        .map(|value| value.map(|(var, value)| (var, value, value ^ 1)))
}

fn raw_width_one_var_const(
    query: &Query,
    var: TermId,
    value: TermId,
) -> Result<Option<(TermId, u64)>> {
    if !matches!(
        query.arena.node(var)?.kind,
        NodeKind::BvVar { width: 1, .. }
    ) {
        return Ok(None);
    }
    let Some(value) = const_u64(query, value)? else {
        return Ok(None);
    };
    Ok((value <= 1).then_some((var, value)))
}

fn eval_polynomial_bool(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<bool>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BoolConst(value) => Some(*value),
        NodeKind::BoolNot(child) => {
            eval_polynomial_bool(query, *child, definitions, canonical, constants)?
                .map(|value| !value)
        }
        NodeKind::BoolAnd(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        NodeKind::BoolOr(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        NodeKind::BoolImplies(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(false), _) | (_, Some(true)) => Some(true),
            (Some(true), Some(false)) => Some(false),
            _ => None,
        },
        NodeKind::BoolEq(a, b) => match (
            eval_polynomial_bool(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bool(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(left), Some(right)) => Some(left == right),
            _ => None,
        },
        NodeKind::BvEq(a, b) => {
            eval_polynomial_bv_equality(query, *a, *b, definitions, canonical, constants)?
        }
        _ => None,
    })
}

fn eval_polynomial_bv_equality(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<bool>> {
    if let (Some(left), Some(right)) = (
        eval_polynomial_bv_const(query, a, definitions, canonical, constants)?,
        eval_polynomial_bv_const(query, b, definitions, canonical, constants)?,
    ) {
        let width = query.arena.expect_bv(a, "polynomial equality")?;
        return Ok(Some(
            (left & mask_for_width(width)) == (right & mask_for_width(width)),
        ));
    }
    let Some(left) = bv_polynomial(query, a, definitions, canonical, &mut Vec::new())? else {
        return Ok(None);
    };
    let Some(right) = bv_polynomial(query, b, definitions, canonical, &mut Vec::new())? else {
        return Ok(None);
    };
    Ok((left.width == right.width && left.terms == right.terms).then_some(true))
}

fn eval_polynomial_bv_const(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    constants: &HashMap<TermId, u64>,
) -> Result<Option<u64>> {
    let width = query.arena.expect_bv(term, "polynomial const eval")?;
    if width > 64 {
        return Ok(None);
    }
    let mask = mask_for_width(width);
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes) & mask),
        NodeKind::BvVar { .. } => {
            let canonical_term = canonical_polynomial_term(canonical, term);
            if let Some(value) = constants.get(&canonical_term) {
                Some(*value & mask)
            } else if let Some(definition) = definitions
                .get(&term)
                .or_else(|| definitions.get(&canonical_term))
            {
                eval_polynomial_bv_const(query, *definition, definitions, canonical, constants)?
            } else {
                None
            }
        }
        NodeKind::BvNot(child) => {
            eval_polynomial_bv_const(query, *child, definitions, canonical, constants)?
                .map(|value| (!value) & mask)
        }
        NodeKind::BvNeg(child) => {
            eval_polynomial_bv_const(query, *child, definitions, canonical, constants)?
                .map(|value| value.wrapping_neg() & mask)
        }
        NodeKind::BvAnd(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some((a & b) & mask),
            _ => None,
        },
        NodeKind::BvOr(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some((a | b) & mask),
            _ => None,
        },
        NodeKind::BvXor(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some((a ^ b) & mask),
            _ => None,
        },
        NodeKind::BvAdd(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some(a.wrapping_add(b) & mask),
            _ => None,
        },
        NodeKind::BvSub(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some(a.wrapping_sub(b) & mask),
            _ => None,
        },
        NodeKind::BvMul(a, b) => match (
            eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
            eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
        ) {
            (Some(a), Some(b)) => Some(a.wrapping_mul(b) & mask),
            _ => None,
        },
        NodeKind::BvExtract { child, high, low } => {
            let value = eval_polynomial_bv_const(query, *child, definitions, canonical, constants)?;
            value.map(|value| (value >> low) & mask_for_width(high - low + 1))
        }
        NodeKind::BvConcat(a, b) => {
            let right_width = query.arena.expect_bv(*b, "polynomial concat")?;
            match (
                eval_polynomial_bv_const(query, *a, definitions, canonical, constants)?,
                eval_polynomial_bv_const(query, *b, definitions, canonical, constants)?,
            ) {
                (Some(a), Some(b)) if right_width < 64 => Some(((a << right_width) | b) & mask),
                _ => None,
            }
        }
        NodeKind::BvZeroExtend { child, .. } => {
            eval_polynomial_bv_const(query, *child, definitions, canonical, constants)
                .map(|value| value.map(|value| value & mask))?
        }
        NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } => match eval_polynomial_bool(query, *cond, definitions, canonical, constants)? {
            Some(true) => {
                eval_polynomial_bv_const(query, *then_value, definitions, canonical, constants)?
            }
            Some(false) => {
                eval_polynomial_bv_const(query, *else_value, definitions, canonical, constants)?
            }
            None => None,
        },
        _ => None,
    })
}

fn bv_polynomial(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<BvPolynomial>> {
    let width = query.arena.expect_bv(term, "polynomial term")?;
    if width > 4_096 {
        return Ok(None);
    }
    if stack.len() > 64 || stack.contains(&term) {
        return Ok(Some(polynomial_base(
            canonical_polynomial_term(canonical, term),
            width,
        )));
    }
    stack.push(term);
    let result = match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => {
            if bytes.iter().copied().skip(8).any(|byte| byte != 0) {
                None
            } else {
                let mut polynomial = BvPolynomial {
                    width,
                    terms: BTreeMap::new(),
                };
                polynomial_add_monomial(&mut polynomial, Vec::new(), bytes_to_u64(bytes));
                Some(polynomial)
            }
        }
        NodeKind::BvVar { .. } => {
            let canonical_term = canonical_polynomial_term(canonical, term);
            if let Some(definition) = definitions
                .get(&term)
                .or_else(|| definitions.get(&canonical_term))
            {
                bv_polynomial(query, *definition, definitions, canonical, stack)?
            } else {
                Some(polynomial_base(canonical_term, width))
            }
        }
        NodeKind::BvAdd(a, b) => combine_polynomial(
            query,
            *a,
            *b,
            definitions,
            canonical,
            stack,
            |left, right| {
                polynomial_add_assign(left, &right);
                Some(())
            },
        )?,
        NodeKind::BvSub(a, b) => combine_polynomial(
            query,
            *a,
            *b,
            definitions,
            canonical,
            stack,
            |left, right| {
                polynomial_sub_assign(left, &right);
                Some(())
            },
        )?,
        NodeKind::BvNeg(child) => {
            let mut value = bv_polynomial(query, *child, definitions, canonical, stack)?;
            if let Some(value) = &mut value {
                polynomial_neg_assign(value);
            }
            value
        }
        NodeKind::BvMul(a, b) => combine_polynomial(
            query,
            *a,
            *b,
            definitions,
            canonical,
            stack,
            |left, right| polynomial_mul_assign(left, &right),
        )?,
        NodeKind::BvZeroExtend { child, .. } => match &query.arena.node(*child)?.kind {
            NodeKind::BvConst { .. } => {
                let Some(mut value) = bv_polynomial(query, *child, definitions, canonical, stack)?
                else {
                    return Ok(None);
                };
                value.width = width;
                Some(value)
            }
            NodeKind::BvVar { .. } => Some(polynomial_base(
                canonical_polynomial_term(canonical, *child),
                width,
            )),
            _ => Some(polynomial_base(
                canonical_polynomial_term(canonical, term),
                width,
            )),
        },
        _ => Some(polynomial_base(
            canonical_polynomial_term(canonical, term),
            width,
        )),
    };
    stack.pop();
    Ok(result)
}

fn polynomial_base(term: TermId, width: u32) -> BvPolynomial {
    let mut terms = BTreeMap::new();
    terms.insert(vec![term], 1);
    BvPolynomial { width, terms }
}

fn combine_polynomial(
    query: &Query,
    a: TermId,
    b: TermId,
    definitions: &HashMap<TermId, TermId>,
    canonical: &HashMap<TermId, TermId>,
    stack: &mut Vec<TermId>,
    combine: impl FnOnce(&mut BvPolynomial, BvPolynomial) -> Option<()>,
) -> Result<Option<BvPolynomial>> {
    let (Some(mut left), Some(right)) = (
        bv_polynomial(query, a, definitions, canonical, stack)?,
        bv_polynomial(query, b, definitions, canonical, stack)?,
    ) else {
        return Ok(None);
    };
    if left.width != right.width {
        return Ok(None);
    }
    Ok(combine(&mut left, right).map(|()| left))
}

fn polynomial_add_assign(left: &mut BvPolynomial, right: &BvPolynomial) {
    for (monomial, coeff) in &right.terms {
        polynomial_add_monomial(left, monomial.clone(), *coeff);
    }
}

fn polynomial_sub_assign(left: &mut BvPolynomial, right: &BvPolynomial) {
    for (monomial, coeff) in &right.terms {
        polynomial_add_monomial(left, monomial.clone(), coeff.wrapping_neg());
    }
}

fn polynomial_neg_assign(value: &mut BvPolynomial) {
    let terms = std::mem::take(&mut value.terms);
    for (monomial, coeff) in terms {
        polynomial_add_monomial(value, monomial, coeff.wrapping_neg());
    }
}

fn polynomial_mul_assign(left: &mut BvPolynomial, right: &BvPolynomial) -> Option<()> {
    if left.terms.len().saturating_mul(right.terms.len()) > 20_000 {
        return None;
    }
    let width = left.width;
    let left_terms = std::mem::take(&mut left.terms);
    for (left_monomial, left_coeff) in left_terms {
        for (right_monomial, right_coeff) in &right.terms {
            let mut monomial = left_monomial.clone();
            monomial.extend(right_monomial.iter().copied());
            monomial.sort_unstable();
            polynomial_add_monomial(
                left,
                monomial,
                left_coeff.wrapping_mul(*right_coeff) & mask_for_width(width),
            );
        }
    }
    Some(())
}

fn polynomial_add_monomial(polynomial: &mut BvPolynomial, monomial: Vec<TermId>, coeff: u64) {
    let mask = mask_for_width(polynomial.width);
    let updated = polynomial
        .terms
        .get(&monomial)
        .copied()
        .unwrap_or(0)
        .wrapping_add(coeff)
        & mask;
    if updated == 0 {
        polynomial.terms.remove(&monomial);
    } else {
        polynomial.terms.insert(monomial, updated);
    }
}
