use std::collections::BTreeMap;

use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::collect_bv_equalities_and_disequalities;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SliceBit {
    Const(bool),
    Var(TermId, u32),
}

#[derive(Debug, Clone)]
struct LinearSliceExpr {
    width: u32,
    constant: u64,
    term: Option<(TermId, u64)>,
}

pub(in crate::solver) fn has_linear_slice_sat_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 30_000 {
        return Ok(false);
    }
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

    let mut constraints = BTreeMap::new();
    for &(a, b) in &equalities {
        let mut candidate = constraints.clone();
        if add_linear_slice_equality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
            constraints = candidate;
        }
    }

    for &(a, b) in &disequalities {
        let mut candidate = constraints.clone();
        if add_linear_slice_disequality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
            constraints = candidate;
        }
    }

    for &(a, b) in &equalities {
        let mut candidate = BTreeMap::new();
        if add_linear_slice_equality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
        }
    }
    for &(a, b) in &disequalities {
        let mut candidate = BTreeMap::new();
        if add_linear_slice_disequality(query, a, b, &mut candidate)? {
            let assignment = bit_constraints_to_assignment(query, &candidate)?;
            if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn add_linear_slice_equality(
    query: &Query,
    a: TermId,
    b: TermId,
    constraints: &mut BTreeMap<(TermId, u32), bool>,
) -> Result<bool> {
    let Some(mut left) = linear_slice_expr(query, a)? else {
        return Ok(false);
    };
    let Some(right) = linear_slice_expr(query, b)? else {
        return Ok(false);
    };
    if left.width != right.width || left.width > 32 {
        return Ok(false);
    }
    linear_slice_sub_assign(&mut left, &right);
    let mask = mask_for_width(left.width);
    let Some((term, coeff)) = left.term else {
        return Ok((left.constant & mask) == 0);
    };
    if coeff & 1 == 0 {
        return Ok(false);
    }
    let required = left
        .constant
        .wrapping_neg()
        .wrapping_mul(mod_inverse_power_two(coeff, left.width))
        & mask;
    assign_slice_value(query, term, required, constraints)
}

fn add_linear_slice_disequality(
    query: &Query,
    a: TermId,
    b: TermId,
    constraints: &mut BTreeMap<(TermId, u32), bool>,
) -> Result<bool> {
    let Some(mut left) = linear_slice_expr(query, a)? else {
        return Ok(false);
    };
    let Some(right) = linear_slice_expr(query, b)? else {
        return Ok(false);
    };
    if left.width != right.width || left.width > 32 {
        return Ok(false);
    }
    linear_slice_sub_assign(&mut left, &right);
    let mask = mask_for_width(left.width);
    let Some((term, coeff)) = left.term else {
        return Ok((left.constant & mask) != 0);
    };
    if coeff & 1 == 0 {
        return Ok(false);
    }
    let forbidden = left
        .constant
        .wrapping_neg()
        .wrapping_mul(mod_inverse_power_two(coeff, left.width))
        & mask;
    for value in [0, 1, forbidden ^ 1, mask] {
        let value = value & mask;
        if value == forbidden {
            continue;
        }
        let mut candidate = constraints.clone();
        if assign_slice_value(query, term, value, &mut candidate)? {
            *constraints = candidate;
            return Ok(true);
        }
    }
    Ok(false)
}

fn linear_slice_expr(query: &Query, term: TermId) -> Result<Option<LinearSliceExpr>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 32 {
        return Ok(None);
    }
    let mask = mask_for_width(width);
    let arithmetic = match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => {
            return Ok(Some(LinearSliceExpr {
                width,
                constant: bytes_to_u64(bytes) & mask,
                term: None,
            }));
        }
        NodeKind::BvAdd(a, b) => combine_linear_slice(query, *a, *b, |left, right| {
            linear_slice_add_assign(left, right);
        })?,
        NodeKind::BvSub(a, b) => combine_linear_slice(query, *a, *b, |left, right| {
            linear_slice_sub_assign(left, right);
        })?,
        NodeKind::BvNeg(child) => {
            let Some(mut value) = linear_slice_expr(query, *child)? else {
                return Ok(None);
            };
            linear_slice_neg_assign(&mut value);
            return Ok(Some(value));
        }
        NodeKind::BvMul(a, b) => {
            if let Some((constant, other)) = const_times_other(query, *a, *b)? {
                let Some(mut value) = linear_slice_expr(query, other)? else {
                    return Ok(None);
                };
                linear_slice_scale_assign(&mut value, constant);
                return Ok(Some(value));
            }
            None
        }
        _ => None,
    };
    if arithmetic.is_some() {
        return Ok(arithmetic);
    }
    if slice_bits(query, term)?.is_some() {
        Ok(Some(LinearSliceExpr {
            width,
            constant: 0,
            term: Some((term, 1)),
        }))
    } else {
        Ok(None)
    }
}

fn combine_linear_slice(
    query: &Query,
    a: TermId,
    b: TermId,
    combine: impl FnOnce(&mut LinearSliceExpr, &LinearSliceExpr),
) -> Result<Option<LinearSliceExpr>> {
    let (Some(mut left), Some(right)) =
        (linear_slice_expr(query, a)?, linear_slice_expr(query, b)?)
    else {
        return Ok(None);
    };
    if left.width != right.width {
        return Ok(None);
    }
    combine(&mut left, &right);
    Ok(Some(left))
}

fn linear_slice_add_assign(left: &mut LinearSliceExpr, right: &LinearSliceExpr) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_add(right.constant) & mask;
    add_linear_slice_term(left, right.term);
}

fn linear_slice_sub_assign(left: &mut LinearSliceExpr, right: &LinearSliceExpr) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_sub(right.constant) & mask;
    add_linear_slice_term(
        left,
        right.term.map(|(term, coeff)| (term, coeff.wrapping_neg())),
    );
}

fn linear_slice_neg_assign(value: &mut LinearSliceExpr) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_neg() & mask;
    value.term = value
        .term
        .map(|(term, coeff)| (term, coeff.wrapping_neg() & mask));
}

fn linear_slice_scale_assign(value: &mut LinearSliceExpr, factor: u64) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_mul(factor) & mask;
    value.term = value
        .term
        .map(|(term, coeff)| (term, coeff.wrapping_mul(factor) & mask));
}

fn add_linear_slice_term(value: &mut LinearSliceExpr, term: Option<(TermId, u64)>) {
    let Some((term, coeff)) = term else {
        return;
    };
    let mask = mask_for_width(value.width);
    match value.term {
        Some((current, current_coeff)) if current == term => {
            let coeff = current_coeff.wrapping_add(coeff) & mask;
            value.term = (coeff != 0).then_some((term, coeff));
        }
        Some(_) => value.term = None,
        None => value.term = Some((term, coeff & mask)),
    }
}

fn assign_slice_value(
    query: &Query,
    term: TermId,
    value: u64,
    constraints: &mut BTreeMap<(TermId, u32), bool>,
) -> Result<bool> {
    let Some(bits) = slice_bits(query, term)? else {
        return Ok(false);
    };
    for (index, bit) in bits.into_iter().enumerate() {
        let expected = ((value >> index) & 1) != 0;
        match bit {
            SliceBit::Const(actual) => {
                if actual != expected {
                    return Ok(false);
                }
            }
            SliceBit::Var(var, bit) => {
                if let Some(previous) = constraints.insert((var, bit), expected) {
                    if previous != expected {
                        return Ok(false);
                    }
                }
            }
        }
    }
    Ok(true)
}

fn bit_constraints_to_assignment(
    query: &Query,
    constraints: &BTreeMap<(TermId, u32), bool>,
) -> Result<BTreeMap<TermId, Vec<u8>>> {
    let mut assignment = BTreeMap::new();
    for (&(var, bit), &value) in constraints {
        let Sort::Bv(width) = query.arena.sort(var)? else {
            return Ok(BTreeMap::new());
        };
        if bit >= width {
            continue;
        }
        let bytes = assignment
            .entry(var)
            .or_insert_with(|| vec![0u8; crate::ir::bytes_for_width(width).unwrap_or(0)]);
        if value {
            bytes[(bit / 8) as usize] |= 1u8 << (bit % 8);
        }
    }
    Ok(assignment)
}

fn slice_bits(query: &Query, term: TermId) -> Result<Option<Vec<SliceBit>>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 64 {
        return Ok(None);
    }
    let bits = match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => (0..width)
            .map(|bit| SliceBit::Const(((bytes[(bit / 8) as usize] >> (bit % 8)) & 1) != 0))
            .collect(),
        NodeKind::BvVar { width, .. } if *width <= 8 => {
            (0..*width).map(|bit| SliceBit::Var(term, bit)).collect()
        }
        NodeKind::BvZeroExtend { child, extra } => {
            let child_width = match query.arena.sort(*child)? {
                Sort::Bv(width) => width,
                Sort::Bool => return Ok(None),
            };
            if child_width + extra != width {
                return Ok(None);
            }
            let Some(mut bits) = slice_bits(query, *child)? else {
                return Ok(None);
            };
            bits.resize(width as usize, SliceBit::Const(false));
            bits
        }
        NodeKind::BvShl(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            let Some(input) = slice_bits(query, *value)? else {
                return Ok(None);
            };
            shift_slice_left(&input, width, shift)
        }
        NodeKind::BvLShr(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            let Some(input) = slice_bits(query, *value)? else {
                return Ok(None);
            };
            shift_slice_right(&input, width, shift)
        }
        NodeKind::BvOr(a, b) | NodeKind::BvAdd(a, b) => {
            let (Some(left_mask), Some(right_mask)) =
                (possible_bit_mask(query, *a)?, possible_bit_mask(query, *b)?)
            else {
                return Ok(None);
            };
            if (left_mask & right_mask) != 0 {
                return Ok(None);
            }
            let (Some(left), Some(right)) = (slice_bits(query, *a)?, slice_bits(query, *b)?) else {
                return Ok(None);
            };
            merge_disjoint_slice_bits(width, &left, &right)?
        }
        NodeKind::BvConcat(a, b) => {
            let (Some(left), Some(right)) = (slice_bits(query, *a)?, slice_bits(query, *b)?) else {
                return Ok(None);
            };
            let mut bits = right;
            bits.extend(left);
            bits
        }
        NodeKind::BvExtract { child, high, low } => {
            let Some(input) = slice_bits(query, *child)? else {
                return Ok(None);
            };
            if high < low || *high as usize >= input.len() {
                return Ok(None);
            }
            input[*low as usize..=*high as usize].to_vec()
        }
        _ => return Ok(None),
    };
    Ok(Some(bits))
}

fn shift_slice_left(input: &[SliceBit], width: u32, shift: u64) -> Vec<SliceBit> {
    let mut bits = vec![SliceBit::Const(false); width as usize];
    if shift < u64::from(width) {
        let shift = shift as usize;
        for (index, output) in bits.iter_mut().enumerate().take(width as usize).skip(shift) {
            if let Some(bit) = input.get(index - shift).copied() {
                *output = bit;
            }
        }
    }
    bits
}

fn shift_slice_right(input: &[SliceBit], width: u32, shift: u64) -> Vec<SliceBit> {
    let mut bits = vec![SliceBit::Const(false); width as usize];
    if shift < u64::from(width) {
        let shift = shift as usize;
        for (index, bit) in bits.iter_mut().enumerate() {
            if let Some(input_bit) = input.get(index + shift).copied() {
                *bit = input_bit;
            }
        }
    }
    bits
}

fn merge_disjoint_slice_bits(
    width: u32,
    left: &[SliceBit],
    right: &[SliceBit],
) -> Result<Vec<SliceBit>> {
    let mut bits = vec![SliceBit::Const(false); width as usize];
    for input in [left, right] {
        for (index, bit) in input.iter().copied().enumerate().take(width as usize) {
            if bit == SliceBit::Const(false) {
                continue;
            }
            if bits[index] != SliceBit::Const(false) {
                return Ok(Vec::new());
            }
            bits[index] = bit;
        }
    }
    Ok(bits)
}

fn mod_inverse_power_two(value: u64, width: u32) -> u64 {
    let mask = mask_for_width(width);
    let mut inverse = 1u64;
    for _ in 0..6 {
        inverse = inverse.wrapping_mul(2u64.wrapping_sub(value.wrapping_mul(inverse))) & mask;
    }
    inverse & mask
}

#[derive(Debug, Clone)]
struct AffineTerm {
    width: u32,
    constant: u64,
    coeffs: BTreeMap<TermId, u64>,
}

pub(in crate::solver) fn has_affine_byte_sat_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 20_000 {
        return Ok(false);
    }
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
    let mut domains = BTreeMap::new();
    for assertion in &query.assertions {
        collect_byte_domains(query, assertion.root, &mut domains)?;
    }
    for &(a, b) in &equalities {
        let Some(mut left) = affine_term(query, a)? else {
            continue;
        };
        let Some(right) = affine_term(query, b)? else {
            continue;
        };
        if left.width != right.width || left.width > 32 || left.width < 8 {
            continue;
        }
        affine_sub_assign(&mut left, &right);
        let Some(assignment) = solve_affine_byte_equation(query, &left, &domains)? else {
            continue;
        };
        if crate::eval::query_satisfied_by_bv_assignment(query, &assignment)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn affine_term(query: &Query, term: TermId) -> Result<Option<AffineTerm>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 32 {
        return Ok(None);
    }
    let mask = mask_for_width(width);
    match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Ok(Some(AffineTerm {
            width,
            constant: bytes_to_u64(bytes) & mask,
            coeffs: BTreeMap::new(),
        })),
        NodeKind::BvVar { width, .. } if *width <= 8 => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(term, 1);
            Ok(Some(AffineTerm {
                width: *width,
                constant: 0,
                coeffs,
            }))
        }
        NodeKind::BvZeroExtend { child, extra } => {
            let child_width = match query.arena.sort(*child)? {
                Sort::Bv(width) => width,
                Sort::Bool => return Ok(None),
            };
            if child_width + extra != width || child_width > 8 {
                return Ok(None);
            }
            let Some(mut child_term) = affine_term(query, *child)? else {
                return Ok(None);
            };
            child_term.width = width;
            child_term.constant &= mask;
            Ok(Some(child_term))
        }
        NodeKind::BvOr(a, b) => {
            let Some(left_mask) = possible_bit_mask(query, *a)? else {
                return Ok(None);
            };
            let Some(right_mask) = possible_bit_mask(query, *b)? else {
                return Ok(None);
            };
            if (left_mask & right_mask) != 0 {
                return Ok(None);
            }
            let (Some(mut left), Some(right)) = (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            if left.width != right.width {
                return Ok(None);
            }
            affine_add_assign(&mut left, &right);
            Ok(Some(left))
        }
        NodeKind::BvAdd(a, b) => {
            let (Some(mut left), Some(right)) = (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            if left.width != right.width {
                return Ok(None);
            }
            affine_add_assign(&mut left, &right);
            Ok(Some(left))
        }
        NodeKind::BvSub(a, b) => {
            let (Some(mut left), Some(right)) = (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            if left.width != right.width {
                return Ok(None);
            }
            affine_sub_assign(&mut left, &right);
            Ok(Some(left))
        }
        NodeKind::BvNeg(child) => {
            let Some(mut value) = affine_term(query, *child)? else {
                return Ok(None);
            };
            affine_neg_assign(&mut value);
            Ok(Some(value))
        }
        NodeKind::BvMul(a, b) => {
            if let Some((constant, other)) = const_times_other(query, *a, *b)? {
                let Some(mut value) = affine_term(query, other)? else {
                    return Ok(None);
                };
                affine_scale_assign(&mut value, constant);
                Ok(Some(value))
            } else {
                Ok(None)
            }
        }
        NodeKind::BvShl(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            if shift >= u64::from(width) {
                return Ok(Some(AffineTerm {
                    width,
                    constant: 0,
                    coeffs: BTreeMap::new(),
                }));
            }
            let Some(mut value) = affine_term(query, *value)? else {
                return Ok(None);
            };
            if value.width != width {
                return Ok(None);
            }
            affine_scale_assign(&mut value, 1u64 << shift);
            Ok(Some(value))
        }
        NodeKind::BvConcat(a, b) => {
            let (Sort::Bv(left_width), Sort::Bv(right_width)) =
                (query.arena.sort(*a)?, query.arena.sort(*b)?)
            else {
                return Ok(None);
            };
            if left_width + right_width != width || right_width >= 64 {
                return Ok(None);
            }
            let (Some(mut left), Some(mut right)) =
                (affine_term(query, *a)?, affine_term(query, *b)?)
            else {
                return Ok(None);
            };
            left.width = width;
            right.width = width;
            affine_scale_assign(&mut left, 1u64 << right_width);
            affine_add_assign(&mut left, &right);
            Ok(Some(left))
        }
        _ => Ok(None),
    }
}

fn possible_bit_mask(query: &Query, term: TermId) -> Result<Option<u64>> {
    let Sort::Bv(width) = query.arena.sort(term)? else {
        return Ok(None);
    };
    if width > 64 {
        return Ok(None);
    }
    let width_mask = mask_for_width(width);
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes) & width_mask),
        NodeKind::BvVar { width, .. } if *width <= 8 => Some(mask_for_width(*width)),
        NodeKind::BvZeroExtend { child, extra } => {
            let child_width = match query.arena.sort(*child)? {
                Sort::Bv(width) => width,
                Sort::Bool => return Ok(None),
            };
            if child_width + extra != width {
                None
            } else {
                possible_bit_mask(query, *child)?
            }
        }
        NodeKind::BvShl(value, amount) => {
            let Some(shift) = const_u64(query, *amount)? else {
                return Ok(None);
            };
            if shift >= u64::from(width) {
                Some(0)
            } else {
                possible_bit_mask(query, *value)?.map(|mask| (mask << shift) & width_mask)
            }
        }
        NodeKind::BvOr(a, b) => {
            match (possible_bit_mask(query, *a)?, possible_bit_mask(query, *b)?) {
                (Some(a), Some(b)) => Some((a | b) & width_mask),
                _ => None,
            }
        }
        NodeKind::BvConcat(a, b) => {
            let Sort::Bv(right_width) = query.arena.sort(*b)? else {
                return Ok(None);
            };
            if right_width >= 64 {
                None
            } else {
                match (possible_bit_mask(query, *a)?, possible_bit_mask(query, *b)?) {
                    (Some(a), Some(b)) => Some(((a << right_width) | b) & width_mask),
                    _ => None,
                }
            }
        }
        _ => None,
    })
}

fn const_times_other(query: &Query, a: TermId, b: TermId) -> Result<Option<(u64, TermId)>> {
    if let NodeKind::BvConst { bytes, .. } = &query.arena.node(a)?.kind {
        return Ok(Some((bytes_to_u64(bytes), b)));
    }
    if let NodeKind::BvConst { bytes, .. } = &query.arena.node(b)?.kind {
        return Ok(Some((bytes_to_u64(bytes), a)));
    }
    Ok(None)
}

fn affine_add_assign(left: &mut AffineTerm, right: &AffineTerm) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_add(right.constant) & mask;
    for (&var, &coeff) in &right.coeffs {
        add_affine_coeff(left, var, coeff);
    }
}

fn affine_sub_assign(left: &mut AffineTerm, right: &AffineTerm) {
    let mask = mask_for_width(left.width);
    left.constant = left.constant.wrapping_sub(right.constant) & mask;
    for (&var, &coeff) in &right.coeffs {
        add_affine_coeff(left, var, coeff.wrapping_neg());
    }
}

fn affine_neg_assign(value: &mut AffineTerm) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_neg() & mask;
    let vars = value.coeffs.clone();
    value.coeffs.clear();
    for (var, coeff) in vars {
        add_affine_coeff(value, var, coeff.wrapping_neg());
    }
}

fn affine_scale_assign(value: &mut AffineTerm, factor: u64) {
    let mask = mask_for_width(value.width);
    value.constant = value.constant.wrapping_mul(factor) & mask;
    let vars = value.coeffs.clone();
    value.coeffs.clear();
    for (var, coeff) in vars {
        add_affine_coeff(value, var, coeff.wrapping_mul(factor));
    }
}

fn add_affine_coeff(term: &mut AffineTerm, var: TermId, coeff: u64) {
    let mask = mask_for_width(term.width);
    let updated = term
        .coeffs
        .get(&var)
        .copied()
        .unwrap_or(0)
        .wrapping_add(coeff)
        & mask;
    if updated == 0 {
        term.coeffs.remove(&var);
    } else {
        term.coeffs.insert(var, updated);
    }
}

fn collect_byte_domains(
    query: &Query,
    term: TermId,
    domains: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BoolAnd(a, b) => {
            collect_byte_domains(query, *a, domains)?;
            collect_byte_domains(query, *b, domains)?;
        }
        NodeKind::BoolNot(child) => {
            if let NodeKind::BvEq(a, b) = &query.arena.node(*child)?.kind {
                if let Some((var, value)) = byte_var_const(query, *a, *b)? {
                    ensure_byte_domain(domains, var).retain(|candidate| *candidate != value);
                }
            }
        }
        NodeKind::BvEq(a, b) => {
            if let Some((var, value)) = byte_var_const(query, *a, *b)? {
                ensure_byte_domain(domains, var).retain(|candidate| *candidate == value);
            }
        }
        NodeKind::BvUlt(a, b) => restrict_unsigned_byte_domain(query, *a, *b, false, domains)?,
        NodeKind::BvUle(a, b) => restrict_unsigned_byte_domain(query, *a, *b, true, domains)?,
        NodeKind::BvSlt(a, b) => restrict_signed_byte_domain(query, *a, *b, false, domains)?,
        NodeKind::BvSle(a, b) => restrict_signed_byte_domain(query, *a, *b, true, domains)?,
        _ => {}
    }
    Ok(())
}

fn byte_var_const(query: &Query, a: TermId, b: TermId) -> Result<Option<(TermId, u8)>> {
    if let (Some(var), Some(value)) = (byte_var(query, a)?, const_u64(query, b)?) {
        if value <= 255 {
            return Ok(Some((var, value as u8)));
        }
    }
    if let (Some(var), Some(value)) = (byte_var(query, b)?, const_u64(query, a)?) {
        if value <= 255 {
            return Ok(Some((var, value as u8)));
        }
    }
    Ok(None)
}

fn restrict_unsigned_byte_domain(
    query: &Query,
    a: TermId,
    b: TermId,
    allow_equal: bool,
    domains: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<()> {
    let Sort::Bv(width) = query.arena.sort(a)? else {
        return Ok(());
    };
    if let (Some(var), Some(bound)) = (byte_var(query, a)?, const_u64(query, b)?) {
        let bound = bound & mask_for_width(width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = u64::from(*candidate) & mask_for_width(width);
            candidate < bound || (allow_equal && candidate == bound)
        });
    }
    if let (Some(bound), Some(var)) = (const_u64(query, a)?, byte_var(query, b)?) {
        let bound = bound & mask_for_width(width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = u64::from(*candidate) & mask_for_width(width);
            bound < candidate || (allow_equal && bound == candidate)
        });
    }
    Ok(())
}

fn restrict_signed_byte_domain(
    query: &Query,
    a: TermId,
    b: TermId,
    allow_equal: bool,
    domains: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<()> {
    let Sort::Bv(width) = query.arena.sort(a)? else {
        return Ok(());
    };
    if let (Some(var), Some(bound)) = (byte_var(query, a)?, const_u64(query, b)?) {
        let bound = signed_value_for_width(bound, width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = signed_value_for_width(u64::from(*candidate), width);
            candidate < bound || (allow_equal && candidate == bound)
        });
    }
    if let (Some(bound), Some(var)) = (const_u64(query, a)?, byte_var(query, b)?) {
        let bound = signed_value_for_width(bound, width);
        ensure_byte_domain(domains, var).retain(|candidate| {
            let candidate = signed_value_for_width(u64::from(*candidate), width);
            bound < candidate || (allow_equal && bound == candidate)
        });
    }
    Ok(())
}

fn byte_var(query: &Query, term: TermId) -> Result<Option<TermId>> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvVar { width, .. } if *width <= 8 => Ok(Some(term)),
        NodeKind::BvZeroExtend { child, .. } => match &query.arena.node(*child)?.kind {
            NodeKind::BvVar { width, .. } if *width <= 8 => Ok(Some(*child)),
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

pub(super) fn const_u64(query: &Query, term: TermId) -> Result<Option<u64>> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst { bytes, .. } => Some(bytes_to_u64(bytes)),
        _ => None,
    })
}

fn ensure_byte_domain(domains: &mut BTreeMap<TermId, Vec<u8>>, var: TermId) -> &mut Vec<u8> {
    domains.entry(var).or_insert_with(|| (0..=255).collect())
}

fn solve_affine_byte_equation(
    query: &Query,
    equation: &AffineTerm,
    domains: &BTreeMap<TermId, Vec<u8>>,
) -> Result<Option<BTreeMap<TermId, Vec<u8>>>> {
    if equation.coeffs.is_empty() {
        return Ok((equation.constant == 0).then(BTreeMap::new));
    }
    let mask = mask_for_width(equation.width);
    let mut vars = Vec::new();
    for (&var, &coeff) in &equation.coeffs {
        let Sort::Bv(width) = query.arena.sort(var)? else {
            return Ok(None);
        };
        if width > 8 {
            return Ok(None);
        }
        let domain = domains
            .get(&var)
            .cloned()
            .unwrap_or_else(|| (0..=u8::MAX).collect());
        if domain.is_empty() {
            return Ok(None);
        }
        vars.push((var, coeff & mask, domain));
    }
    vars.sort_by_key(|(_, _, domain)| std::cmp::Reverse(domain.len()));
    let free_count = vars.len().min(6);
    let (free, fixed) = vars.split_at(free_count);
    if free_count == 0 {
        return Ok(None);
    }
    let mut fixed_sum = 0u64;
    let mut assignment = BTreeMap::new();
    for (var, coeff, domain) in fixed {
        let value = domain[0];
        fixed_sum = fixed_sum.wrapping_add(coeff.wrapping_mul(u64::from(value))) & mask;
        assignment.insert(*var, vec![value]);
    }
    let rhs = equation.constant.wrapping_add(fixed_sum).wrapping_neg() & mask;
    let split = free_count / 2;
    let (left, right) = free.split_at(split);
    if domain_product(left) > 1_500_000 || domain_product(right) > 1_500_000 {
        return Ok(None);
    }
    let mut left_sums = BTreeMap::new();
    enumerate_affine_side(left, mask, 0, 0, &mut Vec::new(), &mut |sum, values| {
        left_sums.entry(sum).or_insert_with(|| values.to_vec());
    });
    let mut found = None;
    enumerate_affine_side(right, mask, 0, 0, &mut Vec::new(), &mut |sum, values| {
        if found.is_some() {
            return;
        }
        let need = rhs.wrapping_sub(sum) & mask;
        if let Some(left_values) = left_sums.get(&need) {
            found = Some((left_values.clone(), values.to_vec()));
        }
    });
    let Some((left_values, right_values)) = found else {
        return Ok(None);
    };
    for ((var, _, _), value) in left.iter().zip(left_values) {
        assignment.insert(*var, vec![value]);
    }
    for ((var, _, _), value) in right.iter().zip(right_values) {
        assignment.insert(*var, vec![value]);
    }
    Ok(Some(assignment))
}

fn domain_product(side: &[(TermId, u64, Vec<u8>)]) -> usize {
    side.iter()
        .map(|(_, _, domain)| domain.len())
        .try_fold(1usize, |acc, len| acc.checked_mul(len))
        .unwrap_or(usize::MAX)
}

fn enumerate_affine_side(
    vars: &[(TermId, u64, Vec<u8>)],
    mask: u64,
    index: usize,
    sum: u64,
    values: &mut Vec<u8>,
    emit: &mut impl FnMut(u64, &[u8]),
) {
    if index == vars.len() {
        emit(sum, values);
        return;
    }
    let (_, coeff, domain) = &vars[index];
    for &value in domain {
        values.push(value);
        enumerate_affine_side(
            vars,
            mask,
            index + 1,
            sum.wrapping_add(coeff.wrapping_mul(u64::from(value))) & mask,
            values,
            emit,
        );
        values.pop();
    }
}

pub(super) fn bytes_to_u64(bytes: &[u8]) -> u64 {
    let mut out = 0u64;
    for (index, byte) in bytes.iter().copied().take(8).enumerate() {
        out |= u64::from(byte) << (index * 8);
    }
    out
}

fn signed_value_for_width(value: u64, width: u32) -> i128 {
    let masked = value & mask_for_width(width);
    if width == 0 {
        0
    } else if width < 64 && ((masked >> (width - 1)) & 1) != 0 {
        i128::from(masked) - (1i128 << width)
    } else if width == 64 && (masked & (1u64 << 63)) != 0 {
        i128::from(masked) - (1i128 << 64)
    } else {
        i128::from(masked)
    }
}

pub(in crate::solver) fn mask_for_width(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}
