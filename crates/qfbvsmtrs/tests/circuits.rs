use qfbvsmtrs::circuits;
use qfbvsmtrs::gates::{GateArena, GateKind};

fn const_bits(gates: &GateArena, value: u64, width: usize) -> Vec<qfbvsmtrs::gates::GateId> {
    (0..width)
        .map(|bit| gates.const_gate(((value >> bit) & 1) != 0))
        .collect()
}

fn eval_bits(gates: &GateArena, bits: &[qfbvsmtrs::gates::GateId]) -> u64 {
    let mut values: Vec<bool> = Vec::with_capacity(gates.gates().len());
    for gate in gates.gates() {
        let value = match *gate {
            GateKind::Const(value) => value,
            GateKind::Input(_) => false,
            GateKind::Not(a) => !values[a.index()],
            GateKind::And(a, b) => values[a.index()] & values[b.index()],
            GateKind::Or(a, b) => values[a.index()] | values[b.index()],
            GateKind::Xor(a, b) => values[a.index()] ^ values[b.index()],
            GateKind::Mux { sel, t, f } => {
                if values[sel.index()] {
                    values[t.index()]
                } else {
                    values[f.index()]
                }
            }
        };
        values.push(value);
    }
    bits.iter().enumerate().fold(0u64, |acc, (bit, gate)| {
        if values[gate.index()] {
            acc | (1 << bit)
        } else {
            acc
        }
    })
}

fn eval_bool(gates: &GateArena, gate: qfbvsmtrs::gates::GateId) -> bool {
    eval_bits(gates, &[gate]) != 0
}

#[test]
fn exhaustive_4bit_arithmetic_circuits() {
    const W: usize = 4;
    let mask = (1u64 << W) - 1;
    for a in 0..=mask {
        for b in 0..=mask {
            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::add(&mut gates, &ab, &bb);
            assert_eq!(eval_bits(&gates, &out), (a + b) & mask, "add {a} {b}");

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::sub(&mut gates, &ab, &bb);
            assert_eq!(
                eval_bits(&gates, &out),
                a.wrapping_sub(b) & mask,
                "sub {a} {b}"
            );

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::mul(&mut gates, &ab, &bb);
            assert_eq!(eval_bits(&gates, &out), (a * b) & mask, "mul {a} {b}");
        }
    }
}

#[test]
fn exhaustive_4bit_comparison_circuits() {
    const W: usize = 4;
    let mask = (1u64 << W) - 1;
    for a in 0..=mask {
        for b in 0..=mask {
            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::ult(&mut gates, &ab, &bb);
            assert_eq!(eval_bool(&gates, out), a < b);

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::ule(&mut gates, &ab, &bb);
            assert_eq!(eval_bool(&gates, out), a <= b);

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::slt(&mut gates, &ab, &bb);
            assert_eq!(eval_bool(&gates, out), signed(a, W) < signed(b, W));

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::sle(&mut gates, &ab, &bb);
            assert_eq!(eval_bool(&gates, out), signed(a, W) <= signed(b, W));
        }
    }
}

#[test]
fn exhaustive_4bit_shift_and_division_circuits() {
    const W: usize = 4;
    let mask = (1u64 << W) - 1;
    for a in 0..=mask {
        for b in 0..=mask {
            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::shl(&mut gates, &ab, &bb);
            assert_eq!(
                eval_bits(&gates, &out),
                if b >= W as u64 { 0 } else { (a << b) & mask }
            );

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::lshr(&mut gates, &ab, &bb);
            assert_eq!(
                eval_bits(&gates, &out),
                if b >= W as u64 { 0 } else { a >> b }
            );

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::ashr(&mut gates, &ab, &bb);
            assert_eq!(eval_bits(&gates, &out), native_ashr(a, b, W));

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let (q, r) = circuits::udiv_urem(&mut gates, &ab, &bb);
            assert_eq!(eval_bits(&gates, &q), udiv(a, b, W), "udiv {a} {b}");
            assert_eq!(eval_bits(&gates, &r), urem(a, b, W), "urem {a} {b}");
        }
    }
}

#[test]
fn exhaustive_4bit_signed_division_circuits() {
    const W: usize = 4;
    let mask = (1u64 << W) - 1;
    for a in 0..=mask {
        for b in 0..=mask {
            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::sdiv(&mut gates, &ab, &bb);
            assert_eq!(
                eval_bits(&gates, &out),
                native_sdiv(a, b, W),
                "sdiv {a} {b}"
            );

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::srem(&mut gates, &ab, &bb);
            assert_eq!(
                eval_bits(&gates, &out),
                native_srem(a, b, W),
                "srem {a} {b}"
            );

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, W);
            let bb = const_bits(&gates, b, W);
            let out = circuits::smod(&mut gates, &ab, &bb);
            assert_eq!(
                eval_bits(&gates, &out),
                native_smod(a, b, W),
                "smod {a} {b}"
            );
        }
    }
}

fn signed(value: u64, width: usize) -> i64 {
    let sign = 1u64 << (width - 1);
    if (value & sign) == 0 {
        value as i64
    } else {
        value as i64 - (1i64 << width)
    }
}

fn mask(width: usize) -> u64 {
    (1u64 << width) - 1
}

fn bvneg(value: u64, width: usize) -> u64 {
    value.wrapping_neg() & mask(width)
}

fn sign(value: u64, width: usize) -> bool {
    ((value >> (width - 1)) & 1) != 0
}

fn udiv(a: u64, b: u64, width: usize) -> u64 {
    a.checked_div(b).unwrap_or_else(|| mask(width))
}

fn urem(a: u64, b: u64, _width: usize) -> u64 {
    a.checked_rem(b).unwrap_or(a)
}

fn native_sdiv(a: u64, b: u64, width: usize) -> u64 {
    match (sign(a, width), sign(b, width)) {
        (false, false) => udiv(a, b, width),
        (false, true) => bvneg(udiv(a, bvneg(b, width), width), width),
        (true, false) => bvneg(udiv(bvneg(a, width), b, width), width),
        (true, true) => udiv(bvneg(a, width), bvneg(b, width), width),
    }
}

fn native_srem(a: u64, b: u64, width: usize) -> u64 {
    match (sign(a, width), sign(b, width)) {
        (false, false) => urem(a, b, width),
        (false, true) => urem(a, bvneg(b, width), width),
        (true, false) => bvneg(urem(bvneg(a, width), b, width), width),
        (true, true) => bvneg(urem(bvneg(a, width), bvneg(b, width), width), width),
    }
}

fn native_smod(a: u64, b: u64, width: usize) -> u64 {
    let abs_a = if sign(a, width) { bvneg(a, width) } else { a };
    let abs_b = if sign(b, width) { bvneg(b, width) } else { b };
    let u = urem(abs_a, abs_b, width);
    if u == 0 {
        0
    } else {
        match (sign(a, width), sign(b, width)) {
            (false, false) => u,
            (true, false) => (b.wrapping_sub(u)) & mask(width),
            (false, true) => (b + u) & mask(width),
            (true, true) => bvneg(u, width),
        }
    }
}

fn native_ashr(a: u64, b: u64, width: usize) -> u64 {
    if b >= width as u64 {
        if sign(a, width) {
            mask(width)
        } else {
            0
        }
    } else if sign(a, width) {
        let fill = mask(width) << (width - b as usize);
        ((a >> b) | fill) & mask(width)
    } else {
        a >> b
    }
}
