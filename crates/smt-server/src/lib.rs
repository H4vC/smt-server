//! Reference server-side implementation for the SMT wire protocol.
//!
//! The crate provides a small dependency-free TCP server, binary request
//! handling, a packaged exhaustive backend for deterministic tests and small
//! queries, a CLI Z3 adapter for deployments that have `z3` on `PATH`, backend
//! racing, request/response caching, and a compact SMT-LIB frontend.

pub mod backend;
pub mod cache;
pub mod eval;
pub mod protocol;
pub mod racing;
pub mod server;
pub mod smt2;
pub mod smtlib;
pub mod z3cli;

pub use backend::{Backend, QueryResult, QueryStatus};
pub use cache::ResponseCache;
pub use eval::ExhaustiveBackend;
pub use protocol::{handle_binary_frame, handle_binary_request, response_from_query_result};
pub use racing::RacingBackend;
pub use server::{serve_tcp, ServerConfig};
pub use smt2::{request_to_smt2, Smt2Script, Smt2Variable};
pub use smtlib::{handle_text_frame, parse_smtlib_script, TextQuery};
pub use z3cli::Z3CliBackend;
