//! Rust support for the SMT v1 binary wire format.
//!
//! The crate intentionally has no runtime dependencies. All parsing uses
//! explicit little-endian byte reads and never relies on host alignment.

pub mod builder;
pub mod client;
pub mod constants;
pub mod error;
pub mod expr;
pub mod le;
pub mod request;
pub mod response;
pub mod types;

pub use builder::{Assertion, CompactedExpression, ExprBuilder};
pub use client::{ClientError, ClientResult, TcpClient};
pub use constants::{command, request_flags, response_flags, status, tag, Command, Status, Tag};
pub use error::{Result, WireError};
pub use expr::{ExprHeader, ExprView, ExpressionBuffer, RawNode, MAX_BV_WIDTH, MAX_NODE_COUNT};
pub use request::{BinaryRequest, RequestEnvelope};
pub use response::{
    BinaryResponse, ModelBlock, ModelEntry, OptimizationValueBlock, ResponseEnvelope, ScalarValue,
    SimplifyBlock, UnsatCoreBlock,
};
pub use types::{BlobRef, NodeRef, Sort};
