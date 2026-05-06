//! Standalone pure-Rust QF_BV SMT solver via bit-blasting.

/// Stack reserved for qfbvsmtrs worker threads.
///
/// Large SMT-LIB generated formulas can be deeply nested enough to overflow
/// Rust's default thread stack during frontend/simplification traversals. The
/// standalone CLI and smt-server adapter use this stack size for qfbvsmtrs
/// worker threads so those cases degrade to `unknown`/timeout instead of
/// aborting the process.
pub const DEFAULT_WORKER_STACK_BYTES: usize = 512 * 1024 * 1024;

pub mod blast;
pub mod builder;
pub mod circuits;
pub mod cnf;
pub mod config;
pub mod error;
pub(crate) mod eval;
pub mod frontend;
pub mod gates;
pub mod ir;
pub mod model;
pub mod query;
pub mod sat;
pub mod simplify;
pub mod solver;
#[cfg(feature = "wire")]
pub mod wire;

pub use builder::Builder;
pub use config::{Config, SatBackendKind};
pub use error::{Error, Result};
pub use frontend::{format_smt2_response, parse_smt2, solve_smt2};
pub use ir::{Sort, TermId};
pub use model::{Model, ModelEntry, ScalarValue};
pub use query::{Assertion, Command, Query};
pub use solver::{solve_query, SolveResult, SolveStatus, Solver};
#[cfg(feature = "wire")]
pub use wire::{model_to_wire, query_from_wire};
