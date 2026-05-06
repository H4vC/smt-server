use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
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

/// Cooperative cancellation token for qfbvsmtrs solve pipelines.
#[derive(Debug, Clone)]
pub struct CancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl CancellationToken {
    pub fn new() -> Self {
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }
}

impl Default for CancellationToken {
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for CancellationToken {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.cancelled, &other.cancelled)
    }
}

impl Eq for CancellationToken {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub sat_backend: SatBackendKind,
    pub budget: Option<Duration>,
    pub shortcut_mode: ShortcutMode,
    pub cancellation_token: Option<CancellationToken>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            sat_backend: SatBackendKind::Splr,
            budget: None,
            shortcut_mode: ShortcutMode::Enabled,
            cancellation_token: None,
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

    pub fn with_cancellation_token(
        mut self,
        cancellation_token: Option<CancellationToken>,
    ) -> Self {
        self.cancellation_token = cancellation_token;
        self
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancellation_token
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
    }
}
