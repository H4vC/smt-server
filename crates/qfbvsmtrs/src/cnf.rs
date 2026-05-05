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
    let num_vars = gates.gates().len();
    let mut clauses = Vec::new();
    for (index, gate) in gates.gates().iter().enumerate() {
        let g = (index + 1) as i32;
        match *gate {
            GateKind::Const(value) => {
                clauses.push(vec![if value { g } else { -g }]);
            }
            GateKind::Input(_) => {}
            GateKind::Not(a) => {
                let a = lit(a);
                clauses.push(vec![g, a]);
                clauses.push(vec![-g, -a]);
            }
            GateKind::And(a, b) => {
                let a = lit(a);
                let b = lit(b);
                clauses.push(vec![-g, a]);
                clauses.push(vec![-g, b]);
                clauses.push(vec![g, -a, -b]);
            }
            GateKind::Or(a, b) => {
                let a = lit(a);
                let b = lit(b);
                clauses.push(vec![g, -a]);
                clauses.push(vec![g, -b]);
                clauses.push(vec![-g, a, b]);
            }
            GateKind::Xor(a, b) => {
                let a = lit(a);
                let b = lit(b);
                clauses.push(vec![-a, -b, -g]);
                clauses.push(vec![-a, b, g]);
                clauses.push(vec![a, -b, g]);
                clauses.push(vec![a, b, -g]);
            }
            GateKind::Mux { sel, t, f } => {
                let s = lit(sel);
                let t = lit(t);
                let f_lit = lit(f);
                clauses.push(vec![-s, -t, g]);
                clauses.push(vec![-s, t, -g]);
                clauses.push(vec![s, -f_lit, g]);
                clauses.push(vec![s, f_lit, -g]);
            }
        }
    }
    clauses.push(vec![lit(assertion)]);
    Cnf { num_vars, clauses }
}

pub fn lit(gate: GateId) -> i32 {
    gate.index() as i32 + 1
}
