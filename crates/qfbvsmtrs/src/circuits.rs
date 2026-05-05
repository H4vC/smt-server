use crate::gates::{GateArena, GateId};

pub type Bits = Vec<GateId>; // LSB first

pub fn zero(width: usize, gates: &GateArena) -> Bits {
    vec![gates.false_gate(); width]
}

pub fn ones(width: usize, gates: &GateArena) -> Bits {
    vec![gates.true_gate(); width]
}

pub fn bitwise_not(gates: &mut GateArena, x: &[GateId]) -> Bits {
    x.iter().map(|&b| gates.not(b)).collect()
}

pub fn bitwise_binary(
    gates: &mut GateArena,
    a: &[GateId],
    b: &[GateId],
    f: fn(&mut GateArena, GateId, GateId) -> GateId,
) -> Bits {
    a.iter().zip(b).map(|(&x, &y)| f(gates, x, y)).collect()
}

pub fn bv_and(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    bitwise_binary(gates, a, b, GateArena::and)
}

pub fn bv_or(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    bitwise_binary(gates, a, b, GateArena::or)
}

pub fn bv_xor(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    bitwise_binary(gates, a, b, GateArena::xor)
}

pub fn add(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    let carry_in = gates.false_gate();
    add_with_carry(gates, a, b, carry_in).0
}

pub fn add_with_carry(
    gates: &mut GateArena,
    a: &[GateId],
    b: &[GateId],
    carry_in: GateId,
) -> (Bits, GateId) {
    let mut carry = carry_in;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let axb = gates.xor(x, y);
        let sum = gates.xor(axb, carry);
        let xy = gates.and(x, y);
        let c_and_axb = gates.and(carry, axb);
        carry = gates.or(xy, c_and_axb);
        out.push(sum);
    }
    (out, carry)
}

pub fn sub(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    let not_b = bitwise_not(gates, b);
    let carry_in = gates.true_gate();
    add_with_carry(gates, a, &not_b, carry_in).0
}

pub fn neg(gates: &mut GateArena, x: &[GateId]) -> Bits {
    let zeros = zero(x.len(), gates);
    sub(gates, &zeros, x)
}

pub fn mul(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    mul_width(gates, a, b, a.len())
}

pub fn mul_const(gates: &mut GateArena, value: &[GateId], constant: &[u8]) -> Bits {
    let width = value.len();
    if const_is_zero(constant, width) {
        return zero(width, gates);
    }
    if const_is_one(constant, width) {
        return value.to_vec();
    }
    if const_is_all_ones(constant, width) {
        return neg(gates, value);
    }

    let mut acc: Option<Bits> = None;
    for shift in 0..width {
        if !const_bit(constant, shift) {
            continue;
        }
        let mut partial = zero(width, gates);
        if shift < width {
            partial[shift..width].copy_from_slice(&value[..(width - shift)]);
        }
        acc = Some(match acc {
            Some(current) => add(gates, &current, &partial),
            None => partial,
        });
    }
    acc.unwrap_or_else(|| zero(width, gates))
}

pub fn mul_width(gates: &mut GateArena, a: &[GateId], b: &[GateId], width: usize) -> Bits {
    let mut acc = zero(width, gates);
    for (shift, &sel) in b.iter().enumerate() {
        let mut partial = zero(width, gates);
        for (i, &abit) in a.iter().enumerate() {
            let out_index = i + shift;
            if out_index < width {
                partial[out_index] = gates.and(abit, sel);
            }
        }
        acc = add(gates, &acc, &partial);
    }
    acc
}

fn const_bit(bytes: &[u8], bit: usize) -> bool {
    bytes
        .get(bit / 8)
        .is_some_and(|byte| ((byte >> (bit % 8)) & 1) != 0)
}

fn const_is_zero(bytes: &[u8], width: usize) -> bool {
    (0..width).all(|bit| !const_bit(bytes, bit))
}

fn const_is_one(bytes: &[u8], width: usize) -> bool {
    const_bit(bytes, 0) && (1..width).all(|bit| !const_bit(bytes, bit))
}

fn const_is_all_ones(bytes: &[u8], width: usize) -> bool {
    (0..width).all(|bit| const_bit(bytes, bit))
}

pub fn eq_bits(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let xnor = a
        .iter()
        .zip(b)
        .map(|(&x, &y)| gates.xnor(x, y))
        .collect::<Vec<_>>();
    gates.and_many(xnor)
}

pub fn is_zero(gates: &mut GateArena, x: &[GateId]) -> GateId {
    let any = gates.or_many(x.iter().copied());
    gates.not(any)
}

pub fn ult(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let mut lt = gates.false_gate();
    let mut eq = gates.true_gate();
    for (&x, &y) in a.iter().zip(b).rev() {
        let not_x = gates.not(x);
        let x_lt_y = gates.and(not_x, y);
        let eq_and_lt = gates.and(eq, x_lt_y);
        lt = gates.or(lt, eq_and_lt);
        let same = gates.xnor(x, y);
        eq = gates.and(eq, same);
    }
    lt
}

pub fn ule(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let b_lt_a = ult(gates, b, a);
    gates.not(b_lt_a)
}

pub fn slt(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let sign_a = *a.last().expect("non-empty bv");
    let sign_b = *b.last().expect("non-empty bv");
    let signs_differ = gates.xor(sign_a, sign_b);
    let unsigned_lt = ult(gates, a, b);
    gates.mux(signs_differ, sign_a, unsigned_lt)
}

pub fn sle(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let b_lt_a = slt(gates, b, a);
    gates.not(b_lt_a)
}

pub fn shl(gates: &mut GateArena, value: &[GateId], amount: &[GateId]) -> Bits {
    let n = value.len();
    let mut out = value.to_vec();
    for (stage, &sel) in amount.iter().enumerate() {
        let shift = 1usize.checked_shl(stage as u32).unwrap_or(usize::MAX);
        let mut shifted = vec![gates.false_gate(); n];
        if shift < n {
            shifted[shift..n].copy_from_slice(&out[..(n - shift)]);
        }
        out = mux_bits(gates, sel, &shifted, &out);
    }
    out
}

pub fn lshr(gates: &mut GateArena, value: &[GateId], amount: &[GateId]) -> Bits {
    let n = value.len();
    let mut out = value.to_vec();
    for (stage, &sel) in amount.iter().enumerate() {
        let shift = 1usize.checked_shl(stage as u32).unwrap_or(usize::MAX);
        let mut shifted = vec![gates.false_gate(); n];
        if shift < n {
            shifted[..(n - shift)].copy_from_slice(&out[shift..n]);
        }
        out = mux_bits(gates, sel, &shifted, &out);
    }
    out
}

pub fn ashr(gates: &mut GateArena, value: &[GateId], amount: &[GateId]) -> Bits {
    let n = value.len();
    let mut out = value.to_vec();
    for (stage, &sel) in amount.iter().enumerate() {
        let shift = 1usize.checked_shl(stage as u32).unwrap_or(usize::MAX);
        let sign = *out.last().expect("non-empty bv");
        let mut shifted = vec![sign; n];
        if shift < n {
            shifted[..(n - shift)].copy_from_slice(&out[shift..n]);
        }
        out = mux_bits(gates, sel, &shifted, &out);
    }
    out
}

pub fn concat(high: &[GateId], low: &[GateId]) -> Bits {
    let mut out = Vec::with_capacity(high.len() + low.len());
    out.extend_from_slice(low);
    out.extend_from_slice(high);
    out
}

pub fn extract(value: &[GateId], high: u32, low: u32) -> Bits {
    value[low as usize..=high as usize].to_vec()
}

pub fn zext(gates: &GateArena, value: &[GateId], extra: u32) -> Bits {
    let mut out = value.to_vec();
    out.extend(std::iter::repeat_n(gates.false_gate(), extra as usize));
    out
}

pub fn sext(value: &[GateId], extra: u32) -> Bits {
    let mut out = value.to_vec();
    let sign = *value.last().expect("non-empty bv");
    out.extend(std::iter::repeat_n(sign, extra as usize));
    out
}

pub fn repeat(value: &[GateId], count: u32) -> Bits {
    let mut out = Vec::with_capacity(value.len() * count as usize);
    for _ in 0..count {
        out.extend_from_slice(value);
    }
    out
}

pub fn rotate_left(value: &[GateId], amount: u32) -> Bits {
    let n = value.len();
    let amount = amount as usize % n;
    (0..n).map(|i| value[(i + n - amount) % n]).collect()
}

pub fn rotate_right(value: &[GateId], amount: u32) -> Bits {
    let n = value.len();
    let amount = amount as usize % n;
    (0..n).map(|i| value[(i + amount) % n]).collect()
}

pub fn mux_bits(gates: &mut GateArena, sel: GateId, t: &[GateId], f: &[GateId]) -> Bits {
    t.iter()
        .zip(f)
        .map(|(&tb, &fb)| gates.mux(sel, tb, fb))
        .collect()
}

pub fn udiv_urem(gates: &mut GateArena, dividend: &[GateId], divisor: &[GateId]) -> (Bits, Bits) {
    let n = dividend.len();
    let mut rem = zero(n, gates);
    let mut quo = zero(n, gates);
    for i in (0..n).rev() {
        let mut shifted = vec![gates.false_gate(); n];
        shifted[0] = dividend[i];
        if n > 1 {
            shifted[1..n].copy_from_slice(&rem[..(n - 1)]);
        }
        rem = shifted;
        let ge = ule(gates, divisor, &rem);
        let rem_minus_divisor = sub(gates, &rem, divisor);
        rem = mux_bits(gates, ge, &rem_minus_divisor, &rem);
        quo[i] = ge;
    }

    let divisor_zero = is_zero(gates, divisor);
    let all_ones = ones(n, gates);
    let quotient = mux_bits(gates, divisor_zero, &all_ones, &quo);
    let remainder = mux_bits(gates, divisor_zero, dividend, &rem);
    (quotient, remainder)
}

pub fn sdiv(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    let sign_a = *a.last().expect("non-empty bv");
    let sign_b = *b.last().expect("non-empty bv");
    let abs_a = abs_bits(gates, a);
    let abs_b = abs_bits(gates, b);
    let (q, _) = udiv_urem(gates, &abs_a, &abs_b);
    let neg_q = neg(gates, &q);
    let signs_differ = gates.xor(sign_a, sign_b);
    mux_bits(gates, signs_differ, &neg_q, &q)
}

pub fn srem(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    let sign_a = *a.last().expect("non-empty bv");
    let abs_a = abs_bits(gates, a);
    let abs_b = abs_bits(gates, b);
    let (_, r) = udiv_urem(gates, &abs_a, &abs_b);
    let neg_r = neg(gates, &r);
    mux_bits(gates, sign_a, &neg_r, &r)
}

pub fn smod(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> Bits {
    let sign_a = *a.last().expect("non-empty bv");
    let sign_b = *b.last().expect("non-empty bv");
    let abs_a = abs_bits(gates, a);
    let abs_b = abs_bits(gates, b);
    let (_, u) = udiv_urem(gates, &abs_a, &abs_b);
    let u_zero = is_zero(gates, &u);
    let neg_u = neg(gates, &u);
    let b_minus_u = sub(gates, b, &u);
    let b_plus_u = add(gates, b, &u);

    // SMT-LIB bvsmod definition:
    // if u = 0 -> u
    // else if a>=0 && b>=0 -> u
    // else if a<0 && b>=0 -> b - u
    // else if a>=0 && b<0 -> b + u
    // else -u
    let pos_pos = u.clone();
    let neg_pos = b_minus_u;
    let pos_neg = b_plus_u;
    let neg_neg = neg_u;
    let when_b_nonneg = mux_bits(gates, sign_a, &neg_pos, &pos_pos);
    let when_b_neg = mux_bits(gates, sign_a, &neg_neg, &pos_neg);
    let nonzero_result = mux_bits(gates, sign_b, &when_b_neg, &when_b_nonneg);
    mux_bits(gates, u_zero, &u, &nonzero_result)
}

pub fn uadd_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let carry_in = gates.false_gate();
    add_with_carry(gates, a, b, carry_in).1
}

pub fn usub_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    ult(gates, a, b)
}

pub fn sadd_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let sum = add(gates, a, b);
    let sa = *a.last().expect("non-empty bv");
    let sb = *b.last().expect("non-empty bv");
    let ss = *sum.last().expect("non-empty bv");
    let same_ab = gates.xnor(sa, sb);
    let diff_sum = gates.xor(sa, ss);
    gates.and(same_ab, diff_sum)
}

pub fn ssub_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let diff = sub(gates, a, b);
    let sa = *a.last().expect("non-empty bv");
    let sb = *b.last().expect("non-empty bv");
    let sd = *diff.last().expect("non-empty bv");
    let diff_ab = gates.xor(sa, sb);
    let diff_res = gates.xor(sa, sd);
    gates.and(diff_ab, diff_res)
}

pub fn umul_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let n = a.len();
    let mut aw = a.to_vec();
    aw.extend(std::iter::repeat_n(gates.false_gate(), n));
    let mut bw = b.to_vec();
    bw.extend(std::iter::repeat_n(gates.false_gate(), n));
    let product = mul_width(gates, &aw, &bw, n * 2);
    gates.or_many(product[n..].iter().copied())
}

pub fn smul_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let n = a.len();
    let aw = sext(a, n as u32);
    let bw = sext(b, n as u32);
    let product = mul_width(gates, &aw, &bw, n * 2);
    let low = product[..n].to_vec();
    let sign_extended_low = sext(&low, n as u32);
    let equal = eq_bits(gates, &product, &sign_extended_low);
    gates.not(equal)
}

pub fn neg_overflow(gates: &mut GateArena, x: &[GateId]) -> GateId {
    let n = x.len();
    let mut min = vec![gates.false_gate(); n];
    min[n - 1] = gates.true_gate();
    eq_bits(gates, x, &min)
}

pub fn sdiv_overflow(gates: &mut GateArena, a: &[GateId], b: &[GateId]) -> GateId {
    let n = a.len();
    let mut min = vec![gates.false_gate(); n];
    min[n - 1] = gates.true_gate();
    let minus_one = vec![gates.true_gate(); n];
    let a_min = eq_bits(gates, a, &min);
    let b_minus_one = eq_bits(gates, b, &minus_one);
    gates.and(a_min, b_minus_one)
}

fn abs_bits(gates: &mut GateArena, x: &[GateId]) -> Bits {
    let sign = *x.last().expect("non-empty bv");
    let neg_x = neg(gates, x);
    mux_bits(gates, sign, &neg_x, x)
}
