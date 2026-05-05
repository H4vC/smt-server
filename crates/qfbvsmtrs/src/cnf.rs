use std::time::Instant;

use crate::error::{Error, Result};
use crate::gates::{GateArena, GateId, GateKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CnfVar(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit(pub i32);

impl Lit {
    pub fn positive(var: CnfVar) -> Self {
        Self(var.0 as i32)
    }

    pub fn negative(var: CnfVar) -> Self {
        Self(-(var.0 as i32))
    }

    pub fn raw(self) -> i32 {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<i32>>,
}

pub fn encode(gates: &GateArena, assertion: GateId) -> Cnf {
    encode_with_deadline(gates, assertion, None)
        .expect("CNF encoding without deadline cannot time out")
}

pub fn encode_with_deadline(
    gates: &GateArena,
    assertion: GateId,
    deadline: Option<Instant>,
) -> Result<Cnf> {
    let num_vars = gates.gates().len();
    let mut clauses = Vec::new();
    for (index, gate) in gates.gates().iter().enumerate() {
        if index % 4096 == 0 && deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(Error::Timeout);
        }
        let g = (index + 1) as i32;
        match *gate {
            GateKind::Const(value) => {
                push_clause(&mut clauses, vec![if value { g } else { -g }]);
            }
            GateKind::Input(_) => {}
            GateKind::Not(a) => {
                let a = lit(a);
                push_clause(&mut clauses, vec![g, a]);
                push_clause(&mut clauses, vec![-g, -a]);
            }
            GateKind::And(a, b) => {
                let a = lit(a);
                let b = lit(b);
                push_clause(&mut clauses, vec![-g, a]);
                push_clause(&mut clauses, vec![-g, b]);
                push_clause(&mut clauses, vec![g, -a, -b]);
            }
            GateKind::Or(a, b) => {
                let a = lit(a);
                let b = lit(b);
                push_clause(&mut clauses, vec![g, -a]);
                push_clause(&mut clauses, vec![g, -b]);
                push_clause(&mut clauses, vec![-g, a, b]);
            }
            GateKind::Xor(a, b) => {
                let a = lit(a);
                let b = lit(b);
                push_clause(&mut clauses, vec![-a, -b, -g]);
                push_clause(&mut clauses, vec![-a, b, g]);
                push_clause(&mut clauses, vec![a, -b, g]);
                push_clause(&mut clauses, vec![a, b, -g]);
            }
            GateKind::Mux { sel, t, f } => {
                let s = lit(sel);
                let t = lit(t);
                let f_lit = lit(f);
                push_clause(&mut clauses, vec![-s, -t, g]);
                push_clause(&mut clauses, vec![-s, t, -g]);
                push_clause(&mut clauses, vec![s, -f_lit, g]);
                push_clause(&mut clauses, vec![s, f_lit, -g]);
            }
        }
    }
    push_clause(&mut clauses, vec![lit(assertion)]);
    Ok(Cnf { num_vars, clauses })
}

fn push_clause(clauses: &mut Vec<Vec<i32>>, mut clause: Vec<i32>) {
    clause.sort_unstable_by_key(|lit| lit.abs());
    clause.dedup();
    for pair in clause.windows(2) {
        if pair[0].abs() == pair[1].abs() && pair[0] == -pair[1] {
            return;
        }
    }
    clauses.push(clause);
}

pub fn lit(gate: GateId) -> i32 {
    gate.index() as i32 + 1
}
