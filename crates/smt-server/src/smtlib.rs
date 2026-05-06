use std::collections::HashMap;
use std::time::Duration;

use smt_qfbv_smtlib::{lower_script, FrontendError, FrontendOptions, QfBvSink};
use smt_wire::{
    BinaryRequest, ExprBuilder, ModelBlock, NodeRef, ScalarValue, UnsatCoreBlock, WireError,
};

use crate::backend::{Backend, QueryResult, QueryStatus};
use crate::smt2::quote_symbol;

#[derive(Debug, Clone)]
pub struct TextQuery {
    pub request: BinaryRequest,
    pub want_model: bool,
    pub want_core: bool,
    pub get_values: Vec<String>,
}

pub struct WireSmtLibSink<'a> {
    builder: &'a mut ExprBuilder,
}

impl<'a> WireSmtLibSink<'a> {
    pub fn new(builder: &'a mut ExprBuilder) -> Self {
        Self { builder }
    }

    pub fn builder(&self) -> &ExprBuilder {
        self.builder
    }

    pub fn builder_mut(&mut self) -> &mut ExprBuilder {
        self.builder
    }
}

macro_rules! forward_wire_unary {
    ($name:ident) => {
        fn $name(&mut self, x: NodeRef) -> smt_wire::Result<NodeRef> {
            self.builder.$name(x)
        }
    };
}

macro_rules! forward_wire_binary {
    ($name:ident) => {
        fn $name(&mut self, a: NodeRef, b: NodeRef) -> smt_wire::Result<NodeRef> {
            self.builder.$name(a, b)
        }
    };
}

impl QfBvSink for WireSmtLibSink<'_> {
    type Node = NodeRef;
    type Error = WireError;

    fn bool_const(&mut self, value: bool) -> smt_wire::Result<NodeRef> {
        if value {
            self.builder.bool_true()
        } else {
            self.builder.bool_false()
        }
    }

    fn bv_const(&mut self, bytes_le: &[u8], width: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_const_wide(bytes_le, width)
    }

    fn bool_var(&mut self, name: &str) -> smt_wire::Result<NodeRef> {
        self.builder.bool_var(name)
    }

    fn bv_var(&mut self, name: &str, width: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_var(name, width)
    }

    forward_wire_unary!(bool_not);
    forward_wire_binary!(bool_and);
    forward_wire_binary!(bool_or);
    forward_wire_binary!(bool_implies);
    forward_wire_binary!(bool_eq);
    forward_wire_binary!(bool_xor);

    fn bool_ite(&mut self, c: NodeRef, t: NodeRef, e: NodeRef) -> smt_wire::Result<NodeRef> {
        self.builder.bool_ite(c, t, e)
    }

    forward_wire_unary!(bv_not);
    forward_wire_unary!(bv_neg);
    forward_wire_binary!(bv_and);
    forward_wire_binary!(bv_or);
    forward_wire_binary!(bv_xor);
    forward_wire_binary!(bv_add);
    forward_wire_binary!(bv_sub);
    forward_wire_binary!(bv_mul);
    forward_wire_binary!(bv_udiv);
    forward_wire_binary!(bv_urem);
    forward_wire_binary!(bv_sdiv);
    forward_wire_binary!(bv_srem);
    forward_wire_binary!(bv_smod);
    forward_wire_binary!(bv_shl);
    forward_wire_binary!(bv_lshr);
    forward_wire_binary!(bv_ashr);

    fn bv_extract(&mut self, x: NodeRef, hi: u32, lo: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_extract(x, hi, lo)
    }

    forward_wire_binary!(bv_concat);

    fn bv_zext(&mut self, x: NodeRef, amount: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_zext(x, checked_u16(amount, "zero_extend")?)
    }

    fn bv_sext(&mut self, x: NodeRef, amount: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_sext(x, checked_u16(amount, "sign_extend")?)
    }

    fn bv_repeat(&mut self, x: NodeRef, count: u32) -> smt_wire::Result<NodeRef> {
        if count == 0 {
            return Err(WireError::invalid(
                "repeat",
                "repeat count must be positive",
            ));
        }
        let mut out = x;
        for _ in 1..count {
            out = self.builder.bv_concat(out, x)?;
        }
        Ok(out)
    }

    fn bv_rotate_left(&mut self, x: NodeRef, amount: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_rotate_left(x, u64::from(amount))
    }

    fn bv_rotate_right(&mut self, x: NodeRef, amount: u32) -> smt_wire::Result<NodeRef> {
        self.builder.bv_rotate_right(x, u64::from(amount))
    }

    fn bv_ite(&mut self, c: NodeRef, t: NodeRef, e: NodeRef) -> smt_wire::Result<NodeRef> {
        self.builder.bv_ite(c, t, e)
    }

    forward_wire_binary!(bv_eq);
    forward_wire_binary!(bv_ult);
    forward_wire_binary!(bv_ule);
    forward_wire_binary!(bv_slt);
    forward_wire_binary!(bv_sle);
    forward_wire_binary!(uadd_ovf);
    forward_wire_binary!(sadd_ovf);
    forward_wire_binary!(usub_ovf);
    forward_wire_binary!(ssub_ovf);
    forward_wire_binary!(umul_ovf);
    forward_wire_binary!(smul_ovf);
    forward_wire_unary!(neg_ovf);
    forward_wire_binary!(sdiv_ovf);

    fn assert(&mut self, root: NodeRef, name: Option<&str>) -> smt_wire::Result<()> {
        if let Some(name) = name {
            self.builder.assert_named(name, root)
        } else {
            self.builder.assert(root)
        }
    }

    fn assume(&mut self, root: NodeRef) -> smt_wire::Result<()> {
        self.builder.assume(root)
    }

    fn push(&mut self) -> smt_wire::Result<()> {
        self.builder.push();
        Ok(())
    }

    fn pop(&mut self) -> smt_wire::Result<()> {
        self.builder.pop()
    }
}

fn checked_u16(value: u32, context: &'static str) -> smt_wire::Result<u16> {
    u16::try_from(value)
        .map_err(|_| WireError::invalid(context, format!("amount {value} exceeds u16::MAX")))
}

pub fn parse_smtlib_script(script: &str) -> smt_wire::Result<TextQuery> {
    let mut builder = ExprBuilder::new();
    let lowered = {
        let mut sink = WireSmtLibSink::new(&mut builder);
        lower_script(script, &mut sink, &FrontendOptions::server_text()).map_err(frontend_error)?
    };
    let request_bytes = builder.build_solve_request(0, 0, lowered.want_model, lowered.want_core)?;
    let request = BinaryRequest::parse(&request_bytes)?;
    Ok(TextQuery {
        request,
        want_model: lowered.want_model,
        want_core: lowered.want_core,
        get_values: lowered.get_values,
    })
}

pub fn handle_text_frame(frame_payload: &[u8], backend: &dyn Backend) -> smt_wire::Result<Vec<u8>> {
    let script = std::str::from_utf8(frame_payload)
        .map_err(|_| WireError::invalid("SMT-LIB frontend", "text request is not UTF-8"))?;
    let query = match parse_smtlib_script(script) {
        Ok(query) => query,
        Err(err) => {
            if allows_qfbvsmtrs_text_fallback(backend) {
                return Ok(handle_qfbvsmtrs_text_fallback(script, &err).into_bytes());
            }
            return Ok(format!("(error {:?})\n", err.to_string()).into_bytes());
        }
    };
    match backend.handle(&query.request) {
        Ok(result) => Ok(text_response(&query, result).into_bytes()),
        Err(err) => Ok(format!("(error {:?})\n", err.to_string()).into_bytes()),
    }
}

fn allows_qfbvsmtrs_text_fallback(backend: &dyn Backend) -> bool {
    backend.supports_qfbvsmtrs_text_fallback()
}

fn handle_qfbvsmtrs_text_fallback(script: &str, frontend_error: &WireError) -> String {
    let script = script.to_owned();
    let frontend_error = frontend_error.to_string();
    let worker = match std::thread::Builder::new()
        .name("qfbvsmtrs-text-fallback".to_owned())
        .stack_size(qfbvsmtrs::DEFAULT_WORKER_STACK_BYTES)
        .spawn(move || handle_qfbvsmtrs_text_fallback_on_worker(&script, &frontend_error))
    {
        Ok(worker) => worker,
        Err(err) => {
            return format!(
                "(error {:?})\n",
                format!("qfbvsmtrs fallback worker: {err}")
            )
        }
    };
    match worker.join() {
        Ok(response) => response,
        Err(_) => "(error \"qfbvsmtrs fallback worker panicked\")\n".to_owned(),
    }
}

fn handle_qfbvsmtrs_text_fallback_on_worker(script: &str, frontend_error: &str) -> String {
    let query = match qfbvsmtrs::parse_smt2(script) {
        Ok(query) => query,
        Err(err) => {
            return format!(
                "(error {:?})\n",
                format!("{frontend_error}; qfbvsmtrs fallback: {err}")
            )
        }
    };
    let config = match qfbvsmtrs_text_config() {
        Ok(config) => config,
        Err(err) => return format!("(error {:?})\n", err),
    };
    let mut solver = qfbvsmtrs::Solver::new(config);
    match solver.solve(&query) {
        Ok(result) => qfbvsmtrs::format_smt2_response(&query, &result),
        Err(err) => format!("(error {:?})\n", format!("qfbvsmtrs fallback: {err}")),
    }
}

fn qfbvsmtrs_text_config() -> std::result::Result<qfbvsmtrs::Config, String> {
    let budget_ms = match std::env::var("SMT_SERVER_TEXT_QFBVSMTRS_BUDGET_MS") {
        Ok(value) => value.parse::<u64>().map_err(|_| {
            "invalid SMT_SERVER_TEXT_QFBVSMTRS_BUDGET_MS: expected integer milliseconds".to_owned()
        })?,
        Err(std::env::VarError::NotPresent) => 30_000,
        Err(std::env::VarError::NotUnicode(_)) => {
            return Err("invalid SMT_SERVER_TEXT_QFBVSMTRS_BUDGET_MS: not UTF-8".to_owned())
        }
    };
    let budget = (budget_ms != 0).then(|| Duration::from_millis(budget_ms));
    let mut config = qfbvsmtrs::Config::default().with_budget(budget);
    if budget.is_some() {
        config = config.with_sat_backend(qfbvsmtrs::SatBackendKind::Dpll);
    }
    Ok(config)
}

fn text_response(query: &TextQuery, result: QueryResult) -> String {
    match result.status {
        QueryStatus::Sat => {
            let mut out = "sat\n".to_owned();
            if query.want_model {
                if let Some(model) = result.model {
                    if query.get_values.is_empty() {
                        out.push_str(
                            &format_model(&query.request, &model)
                                .unwrap_or_else(|err| format!("; model formatting error: {err}\n")),
                        );
                    } else {
                        out.push_str(
                            &format_get_values(&query.request, &model, &query.get_values)
                                .unwrap_or_else(|err| {
                                    format!("; get-value formatting error: {err}\n")
                                }),
                        );
                    }
                } else {
                    return format_unknown(Some("backend omitted requested model"));
                }
            }
            out
        }
        QueryStatus::Unsat => {
            let mut out = "unsat\n".to_owned();
            if query.want_core {
                if let Some(core) = result.core {
                    out.push_str(&format_core(&core));
                } else {
                    return format_unknown(Some("backend omitted requested unsat core"));
                }
            }
            out
        }
        QueryStatus::Unknown => format_unknown(result.message.as_deref()),
        QueryStatus::Ok => "success\n".to_owned(),
    }
}

fn format_unknown(message: Option<&str>) -> String {
    let mut out = "unknown\n".to_owned();
    if let Some(message) = message.filter(|message| !message.is_empty()) {
        out.push_str("; ");
        out.push_str(message);
        out.push('\n');
    }
    out
}

fn format_model(request: &BinaryRequest, model: &ModelBlock) -> smt_wire::Result<String> {
    let expr = request.expression_view()?;
    let mut out = "(model\n".to_owned();
    for entry in &model.entries {
        let node = expr.node(entry.node_ref.index())?;
        let name = expr.blob_str(
            smt_wire::BlobRef::from_payload(node.payload),
            "model variable",
        )?;
        out.push_str("  (define-fun ");
        out.push_str(&quote_symbol(name));
        out.push_str(" () ");
        match entry.value.width {
            0 => {
                out.push_str("Bool ");
                out.push_str(if entry.value.bytes[0] == 0 {
                    "false"
                } else {
                    "true"
                });
            }
            width => {
                out.push_str(&format!("(_ BitVec {width}) "));
                out.push_str(&scalar_to_bv_literal(&entry.value));
            }
        }
        out.push_str(")\n");
    }
    out.push_str(")\n");
    Ok(out)
}

fn format_get_values(
    request: &BinaryRequest,
    model: &ModelBlock,
    names: &[String],
) -> smt_wire::Result<String> {
    let expr = request.expression_view()?;
    let mut values = HashMap::new();
    for entry in &model.entries {
        let node = expr.node(entry.node_ref.index())?;
        let name = expr.blob_str(
            smt_wire::BlobRef::from_payload(node.payload),
            "model variable",
        )?;
        values.insert(name.to_owned(), scalar_to_smt_value(&entry.value));
    }
    let mut out = "(".to_owned();
    let mut emitted = 0usize;
    for name in names {
        if let Some(value) = values.get(name) {
            if emitted > 0 {
                out.push(' ');
            }
            emitted += 1;
            out.push('(');
            out.push_str(&quote_symbol(name));
            out.push(' ');
            out.push_str(value);
            out.push(')');
        }
    }
    out.push_str(")\n");
    Ok(out)
}

fn format_core(core: &UnsatCoreBlock) -> String {
    let mut out = "(".to_owned();
    for (index, name) in core.names.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        out.push_str(&quote_symbol(name));
    }
    out.push_str(")\n");
    out
}

fn scalar_to_smt_value(value: &ScalarValue) -> String {
    if value.width == 0 {
        if value.bytes[0] == 0 {
            "false".to_owned()
        } else {
            "true".to_owned()
        }
    } else {
        scalar_to_bv_literal(value)
    }
}

fn scalar_to_bv_literal(value: &ScalarValue) -> String {
    let mut out = String::with_capacity(value.width as usize + 2);
    out.push_str("#b");
    for bit in (0..value.width).rev() {
        let byte = value.bytes[(bit / 8) as usize];
        out.push(if ((byte >> (bit % 8)) & 1) != 0 {
            '1'
        } else {
            '0'
        });
    }
    out
}

fn frontend_error(err: FrontendError) -> WireError {
    match err {
        FrontendError::Parse(message) => WireError::invalid("SMT-LIB parse", message),
        FrontendError::Unsupported(message) => WireError::invalid("SMT-LIB unsupported", message),
        FrontendError::Invalid { context, message } => WireError::invalid(context, message),
        FrontendError::Sink(message) => WireError::invalid("SMT-LIB sink", message),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_sink_adapter_builds_basic_request() -> smt_wire::Result<()> {
        let mut builder = ExprBuilder::new();
        {
            let mut sink = WireSmtLibSink::new(&mut builder);
            let x = sink.bv_var("x", 1)?;
            let one = sink.bv_const(&[1], 1)?;
            let eq = sink.bv_eq(x, one)?;
            sink.assert(eq, None)?;
        }
        let request = BinaryRequest::parse(&builder.build_solve_request(0, 0, false, false)?)?;
        assert_eq!(request.assertion_roots.len(), 1);
        Ok(())
    }
}
