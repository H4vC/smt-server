use crate::ir::{Arena, TermId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Command {
    Solve,
    Simplify,
    Minimize,
    Maximize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    pub root: TermId,
    pub name: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Query {
    pub arena: Arena,
    pub assertions: Vec<Assertion>,
    pub assumptions: Vec<TermId>,
    pub command: Command,
    pub target: Option<TermId>,
    pub signed: bool,
    pub want_model: bool,
    pub want_core: bool,
    pub get_values: Vec<String>,
}

impl Query {
    pub fn assertions_and_assumptions(&self) -> impl Iterator<Item = TermId> + '_ {
        self.assertions
            .iter()
            .map(|assertion| assertion.root)
            .chain(self.assumptions.iter().copied())
    }
}
