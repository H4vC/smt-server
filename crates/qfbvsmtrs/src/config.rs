use std::time::Duration;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatBackendKind {
    Splr,
    Varisat,
    Dpll,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShortcutMode {
    /// Preserve the existing fast path: conclusive shortcuts may answer before bit-blasting.
    Enabled,
    /// Bypass all shortcuts and use only the bit-blast/CNF/SAT core path.
    Disabled,
    /// Use shortcuts, but require SAT existence shortcuts to validate a witness where available.
    ValidateSatWitnesses,
    /// Run shortcuts, then compare conclusive shortcut answers with the core path when budget allows.
    Audit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub sat_backend: SatBackendKind,
    pub budget: Option<Duration>,
    pub shortcut_mode: ShortcutMode,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            sat_backend: SatBackendKind::Splr,
            budget: None,
            shortcut_mode: ShortcutMode::Enabled,
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

    pub fn with_shortcut_mode(mut self, shortcut_mode: ShortcutMode) -> Self {
        self.shortcut_mode = shortcut_mode;
        self
    }
}
