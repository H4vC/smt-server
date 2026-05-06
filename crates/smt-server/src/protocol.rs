use smt_wire::{
    request::is_binary_request_payload, response_flags, BinaryRequest, BinaryResponse, Command,
    Status, WireError,
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
    let request_id = request.envelope.request_id;
    match request.envelope.command {
        Command::Solve => solve_response(request, result),
        Command::Simplify => simplify_response(request_id, result),
        Command::Minimize | Command::Maximize => optimize_response(request, result),
    }
}

fn solve_response(
    request: &BinaryRequest,
    result: QueryResult,
) -> smt_wire::Result<BinaryResponse> {
    let request_id = request.envelope.request_id;
    let want_model = (request.envelope.flags & smt_wire::request_flags::WANT_MODEL) != 0;
    let want_core = (request.envelope.flags & smt_wire::request_flags::WANT_CORE) != 0;
    match result.status {
        QueryStatus::Sat => {
            if want_model {
                if let Some(model) = result.model {
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
        QueryStatus::Ok => BinaryResponse::error(request_id, "SOLVE backend returned OK"),
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

fn simplify_response(request_id: u32, result: QueryResult) -> smt_wire::Result<BinaryResponse> {
    match result.status {
        QueryStatus::Ok => {
            let simplify = result.simplify.ok_or_else(|| {
                WireError::invalid("simplify response", "OK result without simplify block")
            })?;
            BinaryResponse::new(
                request_id,
                Status::Ok,
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
            let want_model = (request.envelope.flags & smt_wire::request_flags::WANT_MODEL) != 0;
            if want_model && optimization.model.is_none() {
                return BinaryResponse::error(
                    request_id,
                    "optimization backend omitted requested model",
                );
            }
            if !want_model {
                optimization.model = None;
            }
            let mut flags = response_flags::HAS_VALUE;
            if optimization.model.is_some() {
                flags |= response_flags::HAS_MODEL;
            }
            BinaryResponse::new(request_id, Status::Sat, flags, optimization.encode()?)
        }
        QueryStatus::Unsat => BinaryResponse::new(request_id, Status::Unsat, 0, Vec::new()),
        QueryStatus::Unknown => unknown_response(request_id, result.message),
        QueryStatus::Ok => BinaryResponse::error(request_id, "optimization backend returned OK"),
    }
}
