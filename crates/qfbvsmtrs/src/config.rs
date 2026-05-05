use std::time::Duration;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatBackendKind {
    Splr,
    Varisat,
    Dpll,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub sat_backend: SatBackendKind,
    pub budget: Option<Duration>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            sat_backend: SatBackendKind::Splr,
            budget: None,
        }
    }
}

impl Config {
    pub fn with_budget(mut self, budget: Option<Duration>) -> Self {
        self.budget = budget;
        self
    }

    pub fn with_sat_backend(mut self, sat_backend: SatBackendKind) -> Self {
        self.sat_backend = sat_backend;
        self
    }
}
