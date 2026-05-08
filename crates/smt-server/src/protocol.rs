use std::collections::HashSet;

use smt_wire::raw::{
    expr::validate_node_ref, request::is_binary_request_payload, response_flags, BinaryRequest,
    BinaryResponse, Command, ModelBlock, OptimizationValueBlock, SimplifyBlock, Sort, Status,
    UnsatCoreBlock, WireError,
};

use crate::backend::{Backend, QueryResult, QueryStatus};

/// Decode a binary frame payload, execute it with `backend`, and encode the
/// binary response payload (without the transport length prefix).
pub fn handle_binary_frame(
    frame_payload: &[u8],
    backend: &dyn Backend,
) -> smt_wire::Result<BinaryResponse> {
    if !is_binary_request_payload(frame_payload) {
        return BinaryResponse::error(0, "frame payload is not a binary SMTQ request");
    }
    match BinaryRequest::parse(frame_payload) {
        Ok(request) => handle_binary_request(&request, backend),
        Err(err) => BinaryResponse::error(0, &err.to_string()),
    }
}

pub fn handle_binary_request(
    request: &BinaryRequest,
    backend: &dyn Backend,
) -> smt_wire::Result<BinaryResponse> {
    match backend.handle(request) {
        Ok(result) => response_from_query_result(request, result),
        Err(err) => BinaryResponse::error(request.envelope.request_id, &err.to_string()),
    }
}

pub fn response_from_query_result(
    request: &BinaryRequest,
    result: QueryResult,
) -> smt_wire::Result<BinaryResponse> {
    match request.envelope.command {
        Command::Solve => solve_response(request, result),
        Command::Simplify => simplify_response(request, result),
        Command::Minimize | Command::Maximize => optimize_response(request, result),
    }
}

fn solve_response(
    request: &BinaryRequest,
    result: QueryResult,
) -> smt_wire::Result<BinaryResponse> {
    let request_id = request.envelope.request_id;
    let want_model = (request.envelope.flags & smt_wire::raw::request_flags::WANT_MODEL) != 0;
    let want_core = (request.envelope.flags & smt_wire::raw::request_flags::WANT_CORE) != 0;
    match result.status {
        QueryStatus::Sat => {
            if want_model {
                if let Some(model) = result.model {
                    if let Err(err) = validate_model(request, &model) {
                        return BinaryResponse::error(
                            request_id,
                            &format!("invalid backend model: {err}"),
                        );
                    }
                    BinaryResponse::new(
                        request_id,
                        Status::Sat,
                        response_flags::HAS_MODEL,
                        model.encode()?,
                    )
                } else {
                    BinaryResponse::error(request_id, "SAT backend omitted requested model")
                }
            } else {
                BinaryResponse::new(request_id, Status::Sat, 0, Vec::new())
            }
        }
        QueryStatus::Unsat => {
            if want_core {
                if let Some(core) = result.core {
                    if let Err(err) = validate_unsat_core(request, &core) {
                        return BinaryResponse::error(
                            request_id,
                            &format!("invalid backend unsat core: {err}"),
                        );
                    }
                    BinaryResponse::new(
                        request_id,
                        Status::Unsat,
                        response_flags::HAS_CORE,
                        core.encode()?,
                    )
                } else {
                    BinaryResponse::error(request_id, "UNSAT backend omitted requested core")
                }
            } else {
                BinaryResponse::new(request_id, Status::Unsat, 0, Vec::new())
            }
        }
        QueryStatus::Unknown => unknown_response(request_id, result.message),
        QueryStatus::Simplified => {
            BinaryResponse::error(request_id, "SOLVE backend returned SIMPLIFIED")
        }
    }
}

fn unknown_response(request_id: u32, message: Option<String>) -> smt_wire::Result<BinaryResponse> {
    if let Some(message) = message.filter(|message| !message.is_empty()) {
        BinaryResponse::new(
            request_id,
            Status::Unknown,
            response_flags::HAS_MESSAGE,
            message.into_bytes(),
        )
    } else {
        BinaryResponse::new(request_id, Status::Unknown, 0, Vec::new())
    }
}

fn simplify_response(
    request: &BinaryRequest,
    result: QueryResult,
) -> smt_wire::Result<BinaryResponse> {
    let request_id = request.envelope.request_id;
    match result.status {
        QueryStatus::Simplified => {
            let simplify = result.simplify.ok_or_else(|| {
                WireError::invalid(
                    "simplify response",
                    "SIMPLIFIED result without simplify block",
                )
            })?;
            if let Err(err) = validate_simplify(request, &simplify) {
                return BinaryResponse::error(
                    request_id,
                    &format!("invalid backend simplify block: {err}"),
                );
            }
            BinaryResponse::new(
                request_id,
                Status::Simplified,
                response_flags::HAS_EXPR,
                simplify.encode()?,
            )
        }
        QueryStatus::Unknown => unknown_response(request_id, result.message),
        QueryStatus::Sat | QueryStatus::Unsat => {
            BinaryResponse::error(request_id, "SIMPLIFY backend returned SAT/UNSAT")
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

fn validate_simplify(request: &BinaryRequest, simplify: &SimplifyBlock) -> smt_wire::Result<()> {
    simplify.validate()?;
    let request_target = request
        .target_ref()
        .ok_or_else(|| WireError::invalid("simplify response", "missing target node"))?;
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
    if let Some(model) = &optimization.model {
        model.validate_against_expr(&expr)?;
    }
    Ok(())
}

fn optimize_response(
    request: &BinaryRequest,
    result: QueryResult,
) -> smt_wire::Result<BinaryResponse> {
    let request_id = request.envelope.request_id;
    match result.status {
        QueryStatus::Sat => {
            let mut optimization = result.optimization.ok_or_else(|| {
                WireError::invalid("optimization response", "SAT result without optimum block")
            })?;
            let want_model =
                (request.envelope.flags & smt_wire::raw::request_flags::WANT_MODEL) != 0;
            if want_model && optimization.model.is_none() {
                return BinaryResponse::error(
                    request_id,
                    "optimization backend omitted requested model",
                );
            }
            if !want_model {
                optimization.model = None;
            }
            if let Err(err) = validate_optimization(request, &optimization) {
                return BinaryResponse::error(
                    request_id,
                    &format!("invalid backend optimization block: {err}"),
                );
            }
            let mut flags = response_flags::HAS_VALUE;
            if optimization.model.is_some() {
                flags |= response_flags::HAS_MODEL;
            }
            BinaryResponse::new(request_id, Status::Sat, flags, optimization.encode()?)
        }
        QueryStatus::Unsat => BinaryResponse::new(request_id, Status::Unsat, 0, Vec::new()),
        QueryStatus::Unknown => unknown_response(request_id, result.message),
        QueryStatus::Simplified => {
            BinaryResponse::error(request_id, "optimization backend returned SIMPLIFIED")
        }
    }
}
