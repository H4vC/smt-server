use std::time::Duration;

use smt_wire::{
    BinaryRequest, Command, OptimizationValueBlock, ScalarValue, SimplifyBlock, UnsatCoreBlock,
};

use crate::backend::{Backend, QueryResult};

#[derive(Debug, Clone, Default)]
pub struct QfbvsmtrsBackend;

impl Backend for QfbvsmtrsBackend {
    fn name(&self) -> &'static str {
        "qfbvsmtrs"
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
}

fn scalar_to_wire(value: &qfbvsmtrs::ScalarValue) -> smt_wire::Result<ScalarValue> {
    match value {
        qfbvsmtrs::ScalarValue::Bool(value) => Ok(ScalarValue::bool(*value)),
        qfbvsmtrs::ScalarValue::Bv { width, bytes } => ScalarValue::bv(*width, bytes.clone()),
    }
}

fn solve(request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
    let query = match qfbvsmtrs::query_from_wire(request) {
        Ok(query) => query,
        Err(err) => return Ok(QueryResult::unknown(format!("qfbvsmtrs: {err}"))),
    };
    let budget = if request.envelope.budget_ms == 0 {
        None
    } else {
        Some(Duration::from_millis(u64::from(request.envelope.budget_ms)))
    };
    let config = qfbvsmtrs::Config::default().with_budget(budget);
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
