use qfbvsmtrs::circuits;
use qfbvsmtrs::gates::{GateArena, GateId, GateKind};

fn const_bits(gates: &GateArena, value: u64, width: usize) -> Vec<GateId> {
    (0..width)
        .map(|bit| gates.const_gate(((value >> bit) & 1) != 0))
        .collect()
}

fn eval_bits(gates: &GateArena, bits: &[GateId]) -> u64 {
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

fn eval_bool(gates: &GateArena, gate: GateId) -> bool {
    eval_bits(gates, &[gate]) != 0
}

#[derive(Clone)]
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

#[test]
fn randomized_wide_circuit_identities() {
    run_randomized_wide_circuit_identities(512);
}

#[test]
fn randomized_wide_circuit_identities_production_when_enabled() {
    if std::env::var("QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES")
        .ok()
        .as_deref()
        != Some("10000")
    {
        eprintln!("skipping 10k-sample circuit test; set QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES=10000");
        return;
    }
    run_randomized_wide_circuit_identities(10_000);
}

fn run_randomized_wide_circuit_identities(samples: usize) {
    let mut rng = Rng::new(0x5146_4256_534d_5452);
    for width in [16usize, 32, 64] {
        let mask = mask(width);
        for _ in 0..samples {
            let a = rng.next() & mask;
            let b = rng.next() & mask;

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, width);
            let zero = const_bits(&gates, 0, width);
            let out = circuits::add(&mut gates, &ab, &zero);
            assert_eq!(eval_bits(&gates, &out), a, "add identity width={width}");

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, width);
            let bb = const_bits(&gates, b, width);
            let sum = circuits::add(&mut gates, &ab, &bb);
            let out = circuits::sub(&mut gates, &sum, &bb);
            assert_eq!(eval_bits(&gates, &out), a, "add/sub inverse width={width}");

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, width);
            let neg = circuits::neg(&mut gates, &ab);
            let out = circuits::add(&mut gates, &ab, &neg);
            assert_eq!(eval_bits(&gates, &out), 0, "neg inverse width={width}");

            let mut gates = GateArena::new();
            let ab = const_bits(&gates, a, width);
            let bb = const_bits(&gates, b, width);
            let and = circuits::bv_and(&mut gates, &ab, &bb);
            let lhs = circuits::bitwise_not(&mut gates, &and);
            let nota = circuits::bitwise_not(&mut gates, &ab);
            let notb = circuits::bitwise_not(&mut gates, &bb);
            let rhs = circuits::bv_or(&mut gates, &nota, &notb);
            let eq = circuits::eq_bits(&mut gates, &lhs, &rhs);
            assert!(eval_bool(&gates, eq), "DeMorgan width={width}");

            if b != 0 {
                let mut gates = GateArena::new();
                let ab = const_bits(&gates, a, width);
                let bb = const_bits(&gates, b, width);
                let (q, r) = circuits::udiv_urem(&mut gates, &ab, &bb);
                let qb = circuits::mul(&mut gates, &q, &bb);
                let recomposed = circuits::add(&mut gates, &qb, &r);
                assert_eq!(
                    eval_bits(&gates, &recomposed),
                    a,
                    "division identity width={width} a={a} b={b}"
                );
            }
        }
    }
}

fn mask(width: usize) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}
