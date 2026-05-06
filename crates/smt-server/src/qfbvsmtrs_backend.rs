use std::time::Duration;

use smt_wire::{
    BinaryRequest, Command, OptimizationValueBlock, ScalarValue, SimplifyBlock, UnsatCoreBlock,
};

use crate::backend::{Backend, QueryResult, SolveContext};

#[derive(Debug, Clone, Default)]
pub struct QfbvsmtrsBackend;

impl Backend for QfbvsmtrsBackend {
    fn name(&self) -> &'static str {
        "qfbvsmtrs"
    }

    fn supports_qfbvsmtrs_text_fallback(&self) -> bool {
        true
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        match request.envelope.command {
            Command::Simplify => Ok(QueryResult::ok_simplify(SimplifyBlock {
                expression: request.expression.clone(),
                assertion_roots: request.assertion_roots.clone(),
                named_assertion_refs: request.named_assertion_refs.clone(),
                assumption_roots: request.assumption_roots.clone(),
            })),
            Command::Solve | Command::Minimize | Command::Maximize => solve(request),
        }
    }

    fn handle_with_context(
        &self,
        request: &BinaryRequest,
        context: &SolveContext,
    ) -> smt_wire::Result<QueryResult> {
        if context.is_cancelled() {
            return Ok(QueryResult::unknown(
                "qfbvsmtrs request cancelled before start",
            ));
        }
        match request.envelope.command {
            Command::Simplify => self.handle(request),
            Command::Solve | Command::Minimize | Command::Maximize => {
                solve_with_context(request, context)
            }
        }
    }
}

fn scalar_to_wire(value: &qfbvsmtrs::ScalarValue) -> smt_wire::Result<ScalarValue> {
    match value {
        qfbvsmtrs::ScalarValue::Bool(value) => Ok(ScalarValue::bool(*value)),
        qfbvsmtrs::ScalarValue::Bv { width, bytes } => ScalarValue::bv(*width, bytes.clone()),
    }
}

fn solve(request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
    let request = request.clone();
    let worker = spawn_worker(request, None)?;
    join_worker(worker)
}

fn solve_with_context(
    request: &BinaryRequest,
    context: &SolveContext,
) -> smt_wire::Result<QueryResult> {
    let cancellation = qfbvsmtrs::CancellationToken::new();
    let worker = spawn_worker(request.clone(), Some(cancellation.clone()))?;
    loop {
        if worker.is_finished() {
            return join_worker(worker);
        }
        if context.is_cancelled() {
            cancellation.cancel();
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn spawn_worker(
    request: BinaryRequest,
    cancellation: Option<qfbvsmtrs::CancellationToken>,
) -> smt_wire::Result<std::thread::JoinHandle<smt_wire::Result<QueryResult>>> {
    std::thread::Builder::new()
        .name("qfbvsmtrs-backend".to_owned())
        .stack_size(qfbvsmtrs::DEFAULT_WORKER_STACK_BYTES)
        .spawn(move || solve_on_worker(&request, cancellation))
        .map_err(|err| smt_wire::WireError::invalid("qfbvsmtrs worker", err.to_string()))
}

fn join_worker(
    worker: std::thread::JoinHandle<smt_wire::Result<QueryResult>>,
) -> smt_wire::Result<QueryResult> {
    match worker.join() {
        Ok(result) => result,
        Err(_) => Ok(QueryResult::unknown("qfbvsmtrs worker panicked")),
    }
}

fn solve_on_worker(
    request: &BinaryRequest,
    cancellation: Option<qfbvsmtrs::CancellationToken>,
) -> smt_wire::Result<QueryResult> {
    let query = match qfbvsmtrs::query_from_wire(request) {
        Ok(query) => query,
        Err(err) => return Ok(QueryResult::unknown(format!("qfbvsmtrs: {err}"))),
    };
    let budget = if request.envelope.budget_ms == 0 {
        None
    } else {
        Some(Duration::from_millis(u64::from(request.envelope.budget_ms)))
    };
    let has_cancellation = cancellation.is_some();
    let mut config = qfbvsmtrs::Config::default()
        .with_budget(budget)
        .with_cancellation_token(cancellation);
    if budget.is_some() || has_cancellation {
        // SPLR's library timeout can be conservative under some workloads.
        // The server adapter uses the polling DPLL backend for budgeted
        // qfbvsmtrs requests so request deadlines are hard-bounded in-process.
        config = config.with_sat_backend(qfbvsmtrs::SatBackendKind::Dpll);
    }
    let mut solver = qfbvsmtrs::Solver::new(config);
    let result = match solver.solve(&query) {
        Ok(result) => result,
        Err(err) => return Ok(QueryResult::unknown(format!("qfbvsmtrs: {err}"))),
    };

    match result.status {
        qfbvsmtrs::SolveStatus::Sat => {
            let model = if let Some(model) = &result.model {
                match qfbvsmtrs::model_to_wire(model) {
                    Ok(model) => Some(model),
                    Err(err) => return Ok(QueryResult::unknown(format!("qfbvsmtrs model: {err}"))),
                }
            } else {
                None
            };
            if let Some(optimum) = result.optimum {
                Ok(QueryResult::sat_optimization(OptimizationValueBlock {
                    optimum: scalar_to_wire(&optimum)?,
                    model,
                }))
            } else {
                Ok(QueryResult::sat(model))
            }
        }
        qfbvsmtrs::SolveStatus::Unsat => Ok(QueryResult::unsat(
            result.core.map(|names| UnsatCoreBlock { names }),
        )),
        qfbvsmtrs::SolveStatus::Unknown => {
            Ok(QueryResult::unknown(result.message.unwrap_or_else(|| {
                "qfbvsmtrs returned unknown".to_owned()
            })))
        }
        qfbvsmtrs::SolveStatus::Ok => Ok(QueryResult::unknown(
            "qfbvsmtrs returned OK for a solve request",
        )),
    }
}
