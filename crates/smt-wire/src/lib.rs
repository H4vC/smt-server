//! Rust support for the SMT v1 binary wire format.
//!
//! The public client API is context-oriented: build formulas through
//! [`Context`], pass typed [`BvTerm`]/[`BoolTerm`] handles around, and use
//! [`Client`] for solve/simplify/optimization requests.
//!
//! Low-level wire codecs still exist for the server implementation under
//! [`raw`]. They are not re-exported at the crate root.

mod api;
mod builder;
mod client;
mod constants;
mod error;
mod expr;
mod le;
mod request;
mod response;
mod types;

pub use api::{
    BoolTerm, BvOperand, BvTerm, Client, Context, Model, OptimizationResult, OptimizeOptions,
    Response, SimplifyResult, SolveOptions, Term, WalkOrder,
};
pub use client::{ClientError, ClientResult};
pub use constants::Tag as Op;
pub use constants::{Status, Tag};
pub use error::{Result, WireError};
pub use response::ScalarValue;
pub use types::Sort;

#[doc(hidden)]
pub mod raw {
    pub mod constants {
        pub use crate::constants::*;
    }

    pub mod expr {
        pub use crate::expr::*;
    }

    pub mod request {
        pub use crate::request::*;
    }

    pub mod response {
        pub use crate::response::*;
    }

    pub mod le {
        pub use crate::le::*;
    }

    pub use crate::builder::{Assertion, CompactedExpression, ExprBuilder};
    pub use crate::client::{ClientError, ClientResult, TcpClient};
    pub use crate::constants::{
        command, request_flags, response_flags, status, tag, Command, Status, Tag,
    };
    pub use crate::error::{Result, WireError};
    pub use crate::expr::{
        ExprHeader, ExprView, ExpressionBuffer, RawNode, MAX_BV_WIDTH, MAX_NODE_COUNT,
    };
    pub use crate::request::{is_binary_request_payload, BinaryRequest, RequestEnvelope};
    pub use crate::response::{
        BinaryResponse, ModelBlock, ModelEntry, OptimizationValueBlock, ResponseEnvelope,
        ScalarValue, SimplifyBlock, UnsatCoreBlock,
    };
    pub use crate::types::{BlobRef, NodeRef, Sort};
}
