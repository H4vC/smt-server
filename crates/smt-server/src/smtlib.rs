use smt_wire::BinaryRequest;

use crate::backend::Backend;

#[derive(Debug, Clone)]
pub struct TextQuery {
    pub request: BinaryRequest,
    pub want_model: bool,
    pub want_core: bool,
}

pub fn parse_smtlib_script(_script: &str) -> smt_wire::Result<TextQuery> {
    Err(smt_wire::WireError::invalid(
        "SMT-LIB frontend",
        "SMT-LIB text parsing is implemented in phase 4",
    ))
}

pub fn handle_text_frame(
    frame_payload: &[u8],
    _backend: &dyn Backend,
) -> smt_wire::Result<Vec<u8>> {
    let script = std::str::from_utf8(frame_payload).map_err(|_| {
        smt_wire::WireError::invalid("SMT-LIB frontend", "text request is not UTF-8")
    })?;
    let _ = script;
    Ok(b"(error \"SMT-LIB text frontend is not enabled in this phase\")\n".to_vec())
}
