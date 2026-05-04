use smt_wire::{ModelBlock, OptimizationValueBlock, SimplifyBlock, UnsatCoreBlock};

/// Solver-level status independent from the wire response envelope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryStatus {
    Sat,
    Unsat,
    Unknown,
    Ok,
}

/// Backend result before it is encoded as a wire response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueryResult {
    pub status: QueryStatus,
    pub model: Option<ModelBlock>,
    pub core: Option<UnsatCoreBlock>,
    pub simplify: Option<SimplifyBlock>,
    pub optimization: Option<OptimizationValueBlock>,
    pub message: Option<String>,
}

impl QueryResult {
    pub fn sat(model: Option<ModelBlock>) -> Self {
        Self {
            status: QueryStatus::Sat,
            model,
            core: None,
            simplify: None,
            optimization: None,
            message: None,
        }
    }

    pub fn unsat(core: Option<UnsatCoreBlock>) -> Self {
        Self {
            status: QueryStatus::Unsat,
            model: None,
            core,
            simplify: None,
            optimization: None,
            message: None,
        }
    }

    pub fn unknown(message: impl Into<String>) -> Self {
        Self {
            status: QueryStatus::Unknown,
            model: None,
            core: None,
            simplify: None,
            optimization: None,
            message: Some(message.into()),
        }
    }

    pub fn ok_simplify(simplify: SimplifyBlock) -> Self {
        Self {
            status: QueryStatus::Ok,
            model: None,
            core: None,
            simplify: Some(simplify),
            optimization: None,
            message: None,
        }
    }

    pub fn sat_optimization(optimization: OptimizationValueBlock) -> Self {
        Self {
            status: QueryStatus::Sat,
            model: optimization.model.clone(),
            core: None,
            simplify: None,
            optimization: Some(optimization),
            message: None,
        }
    }

    pub fn is_conclusive(&self) -> bool {
        matches!(
            self.status,
            QueryStatus::Sat | QueryStatus::Unsat | QueryStatus::Ok
        )
    }
}

/// Backend interface shared by the CLI server, racing layer, cache tests, and
/// SMT-LIB path.
pub trait Backend: Send + Sync {
    fn name(&self) -> &'static str;
    fn handle(&self, request: &smt_wire::BinaryRequest) -> smt_wire::Result<QueryResult>;
}
