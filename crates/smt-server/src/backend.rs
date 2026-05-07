use std::collections::HashSet;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

use smt_wire::{
    expr::validate_node_ref, request_flags, BinaryRequest, Command, ModelBlock,
    OptimizationValueBlock, SimplifyBlock, Sort, UnsatCoreBlock, WireError,
};

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

    pub fn is_conclusive_for(&self, request: &BinaryRequest) -> bool {
        let status_matches_command = match request.envelope.command {
            Command::Solve => matches!(self.status, QueryStatus::Sat | QueryStatus::Unsat),
            Command::Simplify => self.status == QueryStatus::Ok,
            Command::Minimize | Command::Maximize => {
                matches!(self.status, QueryStatus::Sat | QueryStatus::Unsat)
            }
        };
        status_matches_command && self.validate_artifacts_for(request).is_ok()
    }

    pub fn validate_artifacts_for(&self, request: &BinaryRequest) -> smt_wire::Result<()> {
        match request.envelope.command {
            Command::Solve => self.validate_solve_artifacts(request),
            Command::Simplify => self.validate_simplify_artifacts(request),
            Command::Minimize | Command::Maximize => self.validate_optimization_artifacts(request),
        }
    }

    fn validate_solve_artifacts(&self, request: &BinaryRequest) -> smt_wire::Result<()> {
        let want_model = (request.envelope.flags & request_flags::WANT_MODEL) != 0;
        let want_core = (request.envelope.flags & request_flags::WANT_CORE) != 0;
        match self.status {
            QueryStatus::Sat if want_model => self
                .model
                .as_ref()
                .ok_or_else(|| WireError::invalid("solve result", "SAT without requested model"))
                .and_then(|model| validate_model(request, model)),
            QueryStatus::Unsat if want_core => self
                .core
                .as_ref()
                .ok_or_else(|| WireError::invalid("solve result", "UNSAT without requested core"))
                .and_then(|core| validate_unsat_core(request, core)),
            QueryStatus::Sat | QueryStatus::Unsat | QueryStatus::Unknown => Ok(()),
            QueryStatus::Ok => Err(WireError::invalid("solve result", "SOLVE returned OK")),
        }
    }

    fn validate_simplify_artifacts(&self, request: &BinaryRequest) -> smt_wire::Result<()> {
        match self.status {
            QueryStatus::Ok => {
                let simplify = self.simplify.as_ref().ok_or_else(|| {
                    WireError::invalid("simplify result", "OK without simplify block")
                })?;
                validate_simplify_result(request, simplify)
            }
            QueryStatus::Unknown => Ok(()),
            QueryStatus::Sat | QueryStatus::Unsat => Err(WireError::invalid(
                "simplify result",
                "SIMPLIFY returned SAT/UNSAT",
            )),
        }
    }

    fn validate_optimization_artifacts(&self, request: &BinaryRequest) -> smt_wire::Result<()> {
        match self.status {
            QueryStatus::Sat => {
                let optimization = self.optimization.as_ref().ok_or_else(|| {
                    WireError::invalid("optimization result", "SAT without optimum block")
                })?;
                if (request.envelope.flags & request_flags::WANT_MODEL) != 0
                    && optimization.model.is_none()
                {
                    return Err(WireError::invalid(
                        "optimization result",
                        "SAT without requested model",
                    ));
                }
                validate_optimization(request, optimization)
            }
            QueryStatus::Unsat | QueryStatus::Unknown => Ok(()),
            QueryStatus::Ok => Err(WireError::invalid(
                "optimization result",
                "optimization returned OK",
            )),
        }
    }
}

fn validate_model(request: &BinaryRequest, model: &ModelBlock) -> smt_wire::Result<()> {
    let expr = request.expression_view()?;
    model.validate_against_expr(&expr)
}

fn validate_unsat_core(request: &BinaryRequest, core: &UnsatCoreBlock) -> smt_wire::Result<()> {
    let expr = request.expression_view()?;
    let mut allowed = HashSet::with_capacity(request.named_assertion_refs.len());
    for name_ref in &request.named_assertion_refs {
        allowed.insert(expr.blob_str(*name_ref, "named assertion")?.to_owned());
    }
    let mut seen = HashSet::with_capacity(core.names.len());
    for name in &core.names {
        if !allowed.contains(name) {
            return Err(WireError::invalid(
                "unsat core",
                format!("backend returned unknown core name {name:?}"),
            ));
        }
        if !seen.insert(name) {
            return Err(WireError::invalid(
                "unsat core",
                format!("backend returned duplicate core name {name:?}"),
            ));
        }
    }
    Ok(())
}

fn validate_simplify_result(
    request: &BinaryRequest,
    simplify: &SimplifyBlock,
) -> smt_wire::Result<()> {
    simplify.validate()?;
    let request_target = request
        .target_ref()
        .ok_or_else(|| WireError::invalid("simplify result", "request is missing target_node"))?;
    let request_expr = request.expression_view()?;
    let request_node = validate_node_ref(
        &request_expr,
        request_target,
        request_target.sort(),
        "simplify request target",
    )?;
    let response_buffer = simplify.expression_buffer()?;
    let response_expr = response_buffer.view()?;
    let response_node = validate_node_ref(
        &response_expr,
        simplify.target_node,
        request_target.sort(),
        "simplify response target",
    )?;
    if response_node.width != request_node.width {
        return Err(WireError::invalid(
            "simplify response target",
            format!(
                "request target width {} but response target width {}",
                request_node.width, response_node.width
            ),
        ));
    }
    Ok(())
}

fn validate_optimization(
    request: &BinaryRequest,
    optimization: &OptimizationValueBlock,
) -> smt_wire::Result<()> {
    optimization.optimum.validate()?;
    let expr = request.expression_view()?;
    let target = request
        .target_ref()
        .ok_or_else(|| WireError::invalid("optimization response", "missing target node"))?;
    let target_node = validate_node_ref(&expr, target, Sort::Bv, "optimization target")?;
    if optimization.optimum.width != target_node.width {
        return Err(WireError::invalid(
            "optimization optimum",
            format!(
                "target width {} but optimum width {}",
                target_node.width, optimization.optimum.width
            ),
        ));
    }
    if (request.envelope.flags & request_flags::WANT_MODEL) != 0 {
        if let Some(model) = &optimization.model {
            model.validate_against_expr(&expr)?;
        }
    }
    Ok(())
}

/// Cooperative cancellation token passed to backends that can stop in-flight
/// work. Backends that do not support cancellation can ignore it and continue
/// using `handle`.
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

/// Per-request context for backend execution.
#[derive(Debug, Clone, Default)]
pub struct SolveContext {
    cancellation: CancellationToken,
}

impl SolveContext {
    pub fn new(cancellation: CancellationToken) -> Self {
        Self { cancellation }
    }

    pub fn cancellation_token(&self) -> &CancellationToken {
        &self.cancellation
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancellation.is_cancelled()
    }
}

/// Backend interface shared by the TCP server, racing layer, cache tests, and
/// SMT-LIB path.
pub trait Backend: Send + Sync {
    fn name(&self) -> &'static str;

    fn supports_qfbvsmtrs_text_fallback(&self) -> bool {
        false
    }

    fn handle(&self, request: &smt_wire::BinaryRequest) -> smt_wire::Result<QueryResult>;

    fn handle_with_context(
        &self,
        request: &smt_wire::BinaryRequest,
        context: &SolveContext,
    ) -> smt_wire::Result<QueryResult> {
        if context.is_cancelled() {
            Ok(QueryResult::unknown(
                "backend request cancelled before start",
            ))
        } else {
            self.handle(request)
        }
    }
}
