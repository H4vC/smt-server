use std::cmp::Ordering;

use crate::builder::{
    add_bytes, ashr_bytes, bytes_to_bounded_usize, cmp_unsigned_bytes, concat_bytes, extract_bytes,
    get_bit, lshr_bytes, mul_bytes, neg_bytes, repeat_bytes, rotate_left_bytes, rotate_right_bytes,
    sext_bytes, shl_bytes, signed_less_than, sub_bytes,
};
use crate::error::{Error, Result};
use crate::ir::{bytes_for_width, mask_unused_high_bits, NodeKind, Sort};
use crate::query::Query;

#[derive(Debug, Clone)]
enum Value {
    Bool(bool),
    Bv { width: u32, bytes: Vec<u8> },
}

impl Value {
    fn bool(&self) -> Result<bool> {
        match self {
            Value::Bool(value) => Ok(*value),
            Value::Bv { .. } => Err(Error::internal("expected Bool value during evaluation")),
        }
    }

    fn bv(&self) -> Result<(u32, &[u8])> {
        match self {
            Value::Bv { width, bytes } => Ok((*width, bytes)),
            Value::Bool(_) => Err(Error::internal("expected BV value during evaluation")),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum EvalAssignment {
    Constant(bool),
    Seed(u64),
}

pub(crate) fn query_satisfied_by_constant_assignment(query: &Query, ones: bool) -> Result<bool> {
    let values = evaluate(query, EvalAssignment::Constant(ones))?;
    for assertion in &query.assertions {
        if !values[assertion.root.index()].bool()? {
            return Ok(false);
        }
    }
    for assumption in &query.assumptions {
        if !values[assumption.index()].bool()? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) fn query_satisfied_by_seeded_assignment(query: &Query, seed: u64) -> Result<bool> {
    let values = evaluate(query, EvalAssignment::Seed(seed))?;
    for assertion in &query.assertions {
        if !values[assertion.root.index()].bool()? {
            return Ok(false);
        }
    }
    for assumption in &query.assumptions {
        if !values[assumption.index()].bool()? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn evaluate(query: &Query, assignment: EvalAssignment) -> Result<Vec<Value>> {
    let mut values: Vec<Value> = Vec::with_capacity(query.arena.len());
    for (index, node) in query.arena.nodes().iter().enumerate() {
        let value = match &node.kind {
            NodeKind::BoolConst(value) => Value::Bool(*value),
            NodeKind::BoolVar { name, external } => Value::Bool(match assignment {
                EvalAssignment::Constant(value) => value,
                EvalAssignment::Seed(seed) => seeded_bool(seed, index, name, *external),
            }),
            NodeKind::BvConst { width, bytes } => Value::Bv {
                width: *width,
                bytes: bytes.clone(),
            },
            NodeKind::BvVar {
                width,
                name,
                external,
            } => Value::Bv {
                width: *width,
                bytes: match assignment {
                    EvalAssignment::Constant(value) => constant_bytes(*width, value)?,
                    EvalAssignment::Seed(seed) => {
                        seeded_bytes(*width, seed, index, name, *external)?
                    }
                },
            },

            NodeKind::BvNot(x) => {
                let (width, bytes) = values[x.index()].bv()?;
                let mut out = bytes.iter().map(|byte| !byte).collect::<Vec<_>>();
                mask_unused_high_bits(&mut out, width);
                Value::Bv { width, bytes: out }
            }
            NodeKind::BvNeg(x) => unary_bv(&values, *x, neg_bytes)?,
            NodeKind::BvAnd(a, b) => bitwise_bv(&values, *a, *b, |x, y| x & y)?,
            NodeKind::BvOr(a, b) => bitwise_bv(&values, *a, *b, |x, y| x | y)?,
            NodeKind::BvXor(a, b) => bitwise_bv(&values, *a, *b, |x, y| x ^ y)?,
            NodeKind::BvAdd(a, b) => binary_bv(&values, *a, *b, add_bytes)?,
            NodeKind::BvSub(a, b) => binary_bv(&values, *a, *b, sub_bytes)?,
            NodeKind::BvMul(a, b) => binary_bv(&values, *a, *b, mul_bytes)?,
            NodeKind::BvUDiv(a, b) => {
                let (quotient, _) = udiv_urem_value(&values, *a, *b)?;
                quotient
            }
            NodeKind::BvURem(a, b) => {
                let (_, remainder) = udiv_urem_value(&values, *a, *b)?;
                remainder
            }
            NodeKind::BvSDiv(a, b) => signed_div_rem_value(&values, *a, *b, SignedDivKind::Div)?,
            NodeKind::BvSRem(a, b) => signed_div_rem_value(&values, *a, *b, SignedDivKind::Rem)?,
            NodeKind::BvSMod(a, b) => signed_div_rem_value(&values, *a, *b, SignedDivKind::Mod)?,
            NodeKind::BvShl(a, b) => shift_value(&values, *a, *b, shl_bytes)?,
            NodeKind::BvLShr(a, b) => shift_value(&values, *a, *b, lshr_bytes)?,
            NodeKind::BvAShr(a, b) => shift_value(&values, *a, *b, ashr_bytes)?,
            NodeKind::BvExtract { child, high, low } => {
                let (_, bytes) = values[child.index()].bv()?;
                let width = high - low + 1;
                Value::Bv {
                    width,
                    bytes: extract_bytes(bytes, *low, width),
                }
            }
            NodeKind::BvConcat(high, low) => {
                let (high_width, high_bytes) = values[high.index()].bv()?;
                let (low_width, low_bytes) = values[low.index()].bv()?;
                Value::Bv {
                    width: high_width + low_width,
                    bytes: concat_bytes(high_bytes, high_width, low_bytes, low_width),
                }
            }
            NodeKind::BvZeroExtend { child, extra } => {
                let (child_width, child_bytes) = values[child.index()].bv()?;
                let width = child_width + extra;
                let mut bytes = child_bytes.to_vec();
                bytes.resize(bytes_for_width(width)?, 0);
                mask_unused_high_bits(&mut bytes, width);
                Value::Bv { width, bytes }
            }
            NodeKind::BvSignExtend { child, extra } => {
                let (child_width, child_bytes) = values[child.index()].bv()?;
                Value::Bv {
                    width: child_width + extra,
                    bytes: sext_bytes(child_bytes, child_width, *extra),
                }
            }
            NodeKind::BvRepeat { child, count } => {
                let (child_width, child_bytes) = values[child.index()].bv()?;
                Value::Bv {
                    width: child_width * count,
                    bytes: repeat_bytes(child_bytes, child_width, *count),
                }
            }
            NodeKind::BvRotateLeft { child, amount } => {
                let (width, bytes) = values[child.index()].bv()?;
                Value::Bv {
                    width,
                    bytes: rotate_left_bytes(bytes, width, *amount % width),
                }
            }
            NodeKind::BvRotateRight { child, amount } => {
                let (width, bytes) = values[child.index()].bv()?;
                Value::Bv {
                    width,
                    bytes: rotate_right_bytes(bytes, width, *amount % width),
                }
            }
            NodeKind::BvIte {
                cond,
                then_value,
                else_value,
            } => {
                if values[cond.index()].bool()? {
                    values[then_value.index()].clone()
                } else {
                    values[else_value.index()].clone()
                }
            }
            NodeKind::BvSelect { cases, default } => {
                let mut selected = *default;
                for (selector, value) in cases {
                    if values[selector.index()].bool()? {
                        selected = *value;
                        break;
                    }
                }
                values[selected.index()].clone()
            }

            NodeKind::BoolNot(x) => Value::Bool(!values[x.index()].bool()?),
            NodeKind::BoolAnd(a, b) => {
                Value::Bool(values[a.index()].bool()? && values[b.index()].bool()?)
            }
            NodeKind::BoolOr(a, b) => {
                Value::Bool(values[a.index()].bool()? || values[b.index()].bool()?)
            }
            NodeKind::BoolImplies(a, b) => {
                Value::Bool(!values[a.index()].bool()? || values[b.index()].bool()?)
            }
            NodeKind::BoolEq(a, b) => {
                Value::Bool(values[a.index()].bool()? == values[b.index()].bool()?)
            }
            NodeKind::BoolIte {
                cond,
                then_value,
                else_value,
            } => {
                if values[cond.index()].bool()? {
                    values[then_value.index()].clone()
                } else {
                    values[else_value.index()].clone()
                }
            }

            NodeKind::BvEq(a, b) => {
                let (_, av) = values[a.index()].bv()?;
                let (_, bv) = values[b.index()].bv()?;
                Value::Bool(av == bv)
            }
            NodeKind::BvUlt(a, b) => unsigned_cmp_value(&values, *a, *b, true)?,
            NodeKind::BvUle(a, b) => unsigned_cmp_value(&values, *a, *b, false)?,
            NodeKind::BvSlt(a, b) => signed_cmp_value(&values, *a, *b, true)?,
            NodeKind::BvSle(a, b) => signed_cmp_value(&values, *a, *b, false)?,

            NodeKind::UAddOverflow(a, b) => unsigned_add_overflow_value(&values, *a, *b)?,
            NodeKind::SAddOverflow(a, b) => signed_add_overflow_value(&values, *a, *b)?,
            NodeKind::USubOverflow(a, b) => unsigned_cmp_value(&values, *a, *b, true)?,
            NodeKind::SSubOverflow(a, b) => signed_sub_overflow_value(&values, *a, *b)?,
            NodeKind::UMulOverflow(a, b) => unsigned_mul_overflow_value(&values, *a, *b)?,
            NodeKind::SMulOverflow(a, b) => signed_mul_overflow_value(&values, *a, *b)?,
            NodeKind::NegOverflow(x) => neg_overflow_value(&values, *x)?,
            NodeKind::SDivOverflow(a, b) => signed_div_overflow_value(&values, *a, *b)?,
        };
        debug_assert_eq!(sort_of_value(&value), node.sort);
        values.push(value);
    }
    Ok(values)
}

fn sort_of_value(value: &Value) -> Sort {
    match value {
        Value::Bool(_) => Sort::Bool,
        Value::Bv { width, .. } => Sort::Bv(*width),
    }
}

fn constant_bytes(width: u32, ones: bool) -> Result<Vec<u8>> {
    let mut bytes = vec![if ones { 0xff } else { 0 }; bytes_for_width(width)?];
    mask_unused_high_bits(&mut bytes, width);
    Ok(bytes)
}

fn seeded_bool(seed: u64, index: usize, name: &str, external: Option<u32>) -> bool {
    (seeded_word(seed, index, name, external, 0) & 1) != 0
}

fn seeded_bytes(
    width: u32,
    seed: u64,
    index: usize,
    name: &str,
    external: Option<u32>,
) -> Result<Vec<u8>> {
    let mut bytes = vec![0u8; bytes_for_width(width)?];
    for (chunk, slot) in bytes.chunks_mut(8).enumerate() {
        let word = seeded_word(seed, index, name, external, chunk as u64).to_le_bytes();
        let count = slot.len();
        slot.copy_from_slice(&word[..count]);
    }
    mask_unused_high_bits(&mut bytes, width);
    Ok(bytes)
}

fn seeded_word(seed: u64, index: usize, name: &str, external: Option<u32>, chunk: u64) -> u64 {
    let mut state = seed
        ^ ((index as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15))
        ^ ((u64::from(external.unwrap_or(u32::MAX))) << 32)
        ^ chunk.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    for byte in name.bytes() {
        state ^= u64::from(byte);
        state = state.wrapping_mul(0x1000_0000_01b3);
        state ^= state >> 32;
    }
    splitmix64(state)
}

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn unary_bv(values: &[Value], x: crate::ir::TermId, f: fn(&[u8], u32) -> Vec<u8>) -> Result<Value> {
    let (width, bytes) = values[x.index()].bv()?;
    Ok(Value::Bv {
        width,
        bytes: f(bytes, width),
    })
}

fn binary_bv(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
    f: fn(&[u8], &[u8], u32) -> Vec<u8>,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    Ok(Value::Bv {
        width,
        bytes: f(av, bv, width),
    })
}

fn bitwise_bv(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
    f: fn(u8, u8) -> u8,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    Ok(Value::Bv {
        width,
        bytes: av.iter().zip(bv).map(|(&x, &y)| f(x, y)).collect(),
    })
}

fn shift_value(
    values: &[Value],
    value: crate::ir::TermId,
    amount: crate::ir::TermId,
    f: fn(&[u8], u32, usize) -> Vec<u8>,
) -> Result<Value> {
    let (width, bytes) = values[value.index()].bv()?;
    let (_, amount_bytes) = values[amount.index()].bv()?;
    let amount = bytes_to_bounded_usize(amount_bytes, width as usize);
    Ok(Value::Bv {
        width,
        bytes: f(bytes, width, amount),
    })
}

fn unsigned_cmp_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
    strict: bool,
) -> Result<Value> {
    let (_, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let ordering = cmp_unsigned_bytes(av, bv);
    Ok(Value::Bool(if strict {
        ordering == Ordering::Less
    } else {
        ordering != Ordering::Greater
    }))
}

fn signed_cmp_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
    strict: bool,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    Ok(Value::Bool(if strict {
        signed_less_than(av, bv, width)
    } else {
        !signed_less_than(bv, av, width)
    }))
}

fn udiv_urem_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<(Value, Value)> {
    let (width, dividend) = values[a.index()].bv()?;
    let (_, divisor) = values[b.index()].bv()?;
    let (quotient, remainder) = udiv_urem_bytes(dividend, divisor, width)?;
    Ok((
        Value::Bv {
            width,
            bytes: quotient,
        },
        Value::Bv {
            width,
            bytes: remainder,
        },
    ))
}

fn udiv_urem_bytes(dividend: &[u8], divisor: &[u8], width: u32) -> Result<(Vec<u8>, Vec<u8>)> {
    if divisor.iter().all(|byte| *byte == 0) {
        return Ok((constant_bytes(width, true)?, dividend.to_vec()));
    }
    let mut quotient = constant_bytes(width, false)?;
    let mut remainder = constant_bytes(width, false)?;
    for bit in (0..width).rev() {
        remainder = shl_bytes(&remainder, width, 1);
        if get_bit(dividend, bit) {
            crate::builder::set_bit(&mut remainder, 0);
        }
        if cmp_unsigned_bytes(&remainder, divisor) != Ordering::Less {
            remainder = sub_bytes(&remainder, divisor, width);
            crate::builder::set_bit(&mut quotient, bit);
        }
    }
    Ok((quotient, remainder))
}

#[derive(Debug, Clone, Copy)]
enum SignedDivKind {
    Div,
    Rem,
    Mod,
}

fn signed_div_rem_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
    kind: SignedDivKind,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let sign_a = get_bit(av, width - 1);
    let sign_b = get_bit(bv, width - 1);
    let abs_a = if sign_a {
        neg_bytes(av, width)
    } else {
        av.to_vec()
    };
    let abs_b = if sign_b {
        neg_bytes(bv, width)
    } else {
        bv.to_vec()
    };
    let (mut q, mut r) = udiv_urem_bytes(&abs_a, &abs_b, width)?;
    match kind {
        SignedDivKind::Div => {
            if sign_a ^ sign_b {
                q = neg_bytes(&q, width);
            }
            Ok(Value::Bv { width, bytes: q })
        }
        SignedDivKind::Rem => {
            if sign_a {
                r = neg_bytes(&r, width);
            }
            Ok(Value::Bv { width, bytes: r })
        }
        SignedDivKind::Mod => {
            let u_zero = r.iter().all(|byte| *byte == 0);
            let out = if u_zero {
                r
            } else {
                match (sign_a, sign_b) {
                    (false, false) => r,
                    (true, false) => sub_bytes(bv, &r, width),
                    (false, true) => add_bytes(bv, &r, width),
                    (true, true) => neg_bytes(&r, width),
                }
            };
            Ok(Value::Bv { width, bytes: out })
        }
    }
}

fn unsigned_add_overflow_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let sum = add_bytes(av, bv, width);
    Ok(Value::Bool(cmp_unsigned_bytes(&sum, av) == Ordering::Less))
}

fn signed_add_overflow_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let sum = add_bytes(av, bv, width);
    let sa = get_bit(av, width - 1);
    let sb = get_bit(bv, width - 1);
    let ss = get_bit(&sum, width - 1);
    Ok(Value::Bool(sa == sb && sa != ss))
}

fn signed_sub_overflow_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let diff = sub_bytes(av, bv, width);
    let sa = get_bit(av, width - 1);
    let sb = get_bit(bv, width - 1);
    let sd = get_bit(&diff, width - 1);
    Ok(Value::Bool(sa != sb && sa != sd))
}

fn unsigned_mul_overflow_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let mut aw = av.to_vec();
    let mut bw = bv.to_vec();
    aw.resize(bytes_for_width(width * 2)?, 0);
    bw.resize(bytes_for_width(width * 2)?, 0);
    let product = mul_bytes(&aw, &bw, width * 2);
    Ok(Value::Bool(
        (width..(width * 2)).any(|bit| get_bit(&product, bit)),
    ))
}

fn signed_mul_overflow_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let aw = sext_bytes(av, width, width);
    let bw = sext_bytes(bv, width, width);
    let product = mul_bytes(&aw, &bw, width * 2);
    let low = extract_bytes(&product, 0, width);
    let sign_extended_low = sext_bytes(&low, width, width);
    Ok(Value::Bool(product != sign_extended_low))
}

fn neg_overflow_value(values: &[Value], x: crate::ir::TermId) -> Result<Value> {
    let (width, bytes) = values[x.index()].bv()?;
    Ok(Value::Bool(
        get_bit(bytes, width - 1) && (0..(width - 1)).all(|bit| !get_bit(bytes, bit)),
    ))
}

fn signed_div_overflow_value(
    values: &[Value],
    a: crate::ir::TermId,
    b: crate::ir::TermId,
) -> Result<Value> {
    let (width, av) = values[a.index()].bv()?;
    let (_, bv) = values[b.index()].bv()?;
    let a_min = get_bit(av, width - 1) && (0..(width - 1)).all(|bit| !get_bit(av, bit));
    let b_minus_one = bv == constant_bytes(width, true)?.as_slice();
    Ok(Value::Bool(a_min && b_minus_one))
}
