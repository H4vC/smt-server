use std::collections::HashMap;
use std::time::Duration;

use smt_wire::raw::{
    tag, BinaryRequest, BlobRef, Command, ModelBlock, ModelEntry, OptimizationValueBlock,
    ScalarValue, SimplifyBlock, Sort, UnsatCoreBlock, WireError,
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
            Command::Simplify => Ok(QueryResult::simplified(SimplifyBlock {
                expression: request.expression.clone(),
                target_node: request
                    .target_ref()
                    .ok_or_else(|| WireError::invalid("simplify request", "missing target_node"))?,
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

fn model_to_wire_for_request(
    model: &qfbvsmtrs::Model,
    request: &BinaryRequest,
) -> smt_wire::Result<ModelBlock> {
    let mut values = HashMap::<(String, Sort, u32), ScalarValue>::new();
    for entry in &model.entries {
        let value = scalar_to_wire(&entry.value)?;
        let key = (entry.name.clone(), value_sort(&value), value.width);
        if let Some(existing) = values.insert(key, value.clone()) {
            if existing != value {
                return Err(WireError::invalid(
                    "qfbvsmtrs model",
                    format!("inconsistent values for symbol {:?}", entry.name),
                ));
            }
        }
    }

    let expr = request.expression_view()?;
    let mut entries = Vec::new();
    for index in 0..expr.node_count() {
        let node = expr.node(index)?;
        let (sort, width, name) = match node.tag {
            tag::BV_VAR => (
                Sort::Bv,
                node.width,
                expr.blob_str(BlobRef::from_payload(node.payload), "BV variable")?,
            ),
            tag::BOOL_VAR => (
                Sort::Bool,
                0,
                expr.blob_str(BlobRef::from_payload(node.payload), "Bool variable")?,
            ),
            _ => continue,
        };
        let key = (name.to_owned(), sort, width);
        if let Some(value) = values.get(&key).cloned() {
            entries.push(ModelEntry {
                node_ref: smt_wire::raw::NodeRef::new(sort, index)?,
                value,
            });
        }
    }
    Ok(ModelBlock { entries })
}

fn value_sort(value: &ScalarValue) -> Sort {
    if value.width == 0 {
        Sort::Bool
    } else {
        Sort::Bv
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
                match model_to_wire_for_request(model, request) {
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
        qfbvsmtrs::SolveStatus::Simplified => Ok(QueryResult::unknown(
            "qfbvsmtrs returned SIMPLIFIED for a solve request",
        )),
    }
}
