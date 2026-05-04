//! Rust support for the SMT v1 binary wire format.
//!
//! The crate intentionally has no runtime dependencies. All parsing uses
//! explicit little-endian byte reads and never relies on host alignment.

pub mod constants;
pub mod error;
pub mod expr;
pub mod le;
pub mod types;

pub use constants::{command, request_flags, response_flags, status, tag, Command, Status, Tag};
pub use error::{Result, WireError};
pub use expr::{ExprHeader, ExprView, ExpressionBuffer, RawNode, MAX_BV_WIDTH, MAX_NODE_COUNT};
pub use types::{BlobRef, NodeRef, Sort};
