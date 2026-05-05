use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GateId(pub(crate) u32);

impl GateId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub const fn raw(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GateKind {
    Const(bool),
    Input(u32),
    Not(GateId),
    And(GateId, GateId),
    Or(GateId, GateId),
    Xor(GateId, GateId),
    Mux { sel: GateId, t: GateId, f: GateId },
}

#[derive(Debug, Clone)]
pub struct GateArena {
    gates: Vec<GateKind>,
    ids: HashMap<GateKind, GateId>,
    false_id: GateId,
    true_id: GateId,
    input_count: u32,
}

impl Default for GateArena {
    fn default() -> Self {
        Self::new()
    }
}

impl GateArena {
    pub fn new() -> Self {
        let mut arena = Self {
            gates: Vec::new(),
            ids: HashMap::new(),
            false_id: GateId(0),
            true_id: GateId(1),
            input_count: 0,
        };
        let f = arena.add_raw(GateKind::Const(false));
        let t = arena.add_raw(GateKind::Const(true));
        arena.false_id = f;
        arena.true_id = t;
        arena
    }

    pub fn gates(&self) -> &[GateKind] {
        &self.gates
    }

    pub const fn false_gate(&self) -> GateId {
        self.false_id
    }

    pub const fn true_gate(&self) -> GateId {
        self.true_id
    }

    pub fn input_count(&self) -> u32 {
        self.input_count
    }

    pub fn input(&mut self) -> GateId {
        let id = self.input_count;
        self.input_count += 1;
        self.add_raw(GateKind::Input(id))
    }

    pub fn const_gate(&self, value: bool) -> GateId {
        if value {
            self.true_id
        } else {
            self.false_id
        }
    }

    pub fn not(&mut self, x: GateId) -> GateId {
        if x == self.false_id {
            return self.true_id;
        }
        if x == self.true_id {
            return self.false_id;
        }
        if let GateKind::Not(inner) = self.gates[x.index()] {
            return inner;
        }
        self.add_raw(GateKind::Not(x))
    }

    pub fn and(&mut self, a: GateId, b: GateId) -> GateId {
        let (a, b) = order_pair(a, b);
        if a == self.false_id || b == self.false_id {
            return self.false_id;
        }
        if a == self.true_id {
            return b;
        }
        if b == self.true_id || a == b {
            return a;
        }
        if self.is_negation_pair(a, b) {
            return self.false_id;
        }
        self.add_raw(GateKind::And(a, b))
    }

    pub fn or(&mut self, a: GateId, b: GateId) -> GateId {
        let (a, b) = order_pair(a, b);
        if a == self.true_id || b == self.true_id {
            return self.true_id;
        }
        if a == self.false_id {
            return b;
        }
        if b == self.false_id || a == b {
            return a;
        }
        if self.is_negation_pair(a, b) {
            return self.true_id;
        }
        self.add_raw(GateKind::Or(a, b))
    }

    pub fn xor(&mut self, a: GateId, b: GateId) -> GateId {
        let (a, b) = order_pair(a, b);
        if a == self.false_id {
            return b;
        }
        if b == self.false_id {
            return a;
        }
        if a == b {
            return self.false_id;
        }
        if a == self.true_id {
            return self.not(b);
        }
        if b == self.true_id {
            return self.not(a);
        }
        self.add_raw(GateKind::Xor(a, b))
    }

    pub fn xnor(&mut self, a: GateId, b: GateId) -> GateId {
        let xor = self.xor(a, b);
        self.not(xor)
    }

    pub fn mux(&mut self, sel: GateId, t: GateId, f: GateId) -> GateId {
        if sel == self.true_id {
            return t;
        }
        if sel == self.false_id {
            return f;
        }
        if t == f {
            return t;
        }
        if t == self.true_id && f == self.false_id {
            return sel;
        }
        if t == self.false_id && f == self.true_id {
            return self.not(sel);
        }
        self.add_raw(GateKind::Mux { sel, t, f })
    }

    pub fn implies(&mut self, a: GateId, b: GateId) -> GateId {
        let not_a = self.not(a);
        self.or(not_a, b)
    }

    pub fn and_many<I>(&mut self, iter: I) -> GateId
    where
        I: IntoIterator<Item = GateId>,
    {
        let mut out = self.true_id;
        for gate in iter {
            out = self.and(out, gate);
            if out == self.false_id {
                break;
            }
        }
        out
    }

    pub fn or_many<I>(&mut self, iter: I) -> GateId
    where
        I: IntoIterator<Item = GateId>,
    {
        let mut out = self.false_id;
        for gate in iter {
            out = self.or(out, gate);
            if out == self.true_id {
                break;
            }
        }
        out
    }

    fn add_raw(&mut self, kind: GateKind) -> GateId {
        if let Some(existing) = self.ids.get(&kind) {
            return *existing;
        }
        let id = GateId(self.gates.len() as u32);
        self.gates.push(kind.clone());
        self.ids.insert(kind, id);
        id
    }

    fn is_negation_pair(&self, a: GateId, b: GateId) -> bool {
        matches!(self.gates[a.index()], GateKind::Not(x) if x == b)
            || matches!(self.gates[b.index()], GateKind::Not(x) if x == a)
    }
}

fn order_pair(a: GateId, b: GateId) -> (GateId, GateId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}
