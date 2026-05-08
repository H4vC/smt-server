use crate::builder::Builder;
use crate::error::{Error, Result};
use crate::ir::TermId;
use crate::model::{scalar_to_smt, Model, ScalarValue};
use crate::query::Query;
use crate::solver::{SolveResult, SolveStatus};
use crate::{Config, Solver};
use smt_qfbv_smtlib::{lower_script, FrontendError, FrontendOptions, QfBvSink};

pub struct QfbvSmtLibSink<'a> {
    builder: &'a mut Builder,
}

impl<'a> QfbvSmtLibSink<'a> {
    pub fn new(builder: &'a mut Builder) -> Self {
        Self { builder }
    }

    pub fn builder(&self) -> &Builder {
        self.builder
    }

    pub fn builder_mut(&mut self) -> &mut Builder {
        self.builder
    }
}

macro_rules! forward_qfbv_unary {
    ($name:ident) => {
        fn $name(&mut self, x: TermId) -> Result<TermId> {
            self.builder.$name(x)
        }
    };
}

macro_rules! forward_qfbv_binary {
    ($name:ident) => {
        fn $name(&mut self, a: TermId, b: TermId) -> Result<TermId> {
            self.builder.$name(a, b)
        }
    };
}

impl QfBvSink for QfbvSmtLibSink<'_> {
    type Node = TermId;
    type Error = Error;

    fn bool_const(&mut self, value: bool) -> Result<TermId> {
        self.builder.bool_const(value)
    }

    fn bv_const(&mut self, bytes_le: &[u8], width: u32) -> Result<TermId> {
        self.builder.bv_const_bytes(bytes_le, width)
    }

    fn bool_var(&mut self, name: &str) -> Result<TermId> {
        self.builder.bool_var(name)
    }

    fn bv_var(&mut self, name: &str, width: u32) -> Result<TermId> {
        self.builder.bv_var(name, width)
    }

    forward_qfbv_unary!(bool_not);
    forward_qfbv_binary!(bool_and);
    forward_qfbv_binary!(bool_or);
    forward_qfbv_binary!(bool_implies);
    forward_qfbv_binary!(bool_eq);
    forward_qfbv_binary!(bool_xor);

    fn bool_ite(&mut self, c: TermId, t: TermId, e: TermId) -> Result<TermId> {
        self.builder.bool_ite(c, t, e)
    }

    forward_qfbv_unary!(bv_not);
    forward_qfbv_unary!(bv_neg);
    forward_qfbv_binary!(bv_and);
    forward_qfbv_binary!(bv_or);
    forward_qfbv_binary!(bv_xor);
    forward_qfbv_binary!(bv_add);
    forward_qfbv_binary!(bv_sub);
    forward_qfbv_binary!(bv_mul);
    forward_qfbv_binary!(bv_udiv);
    forward_qfbv_binary!(bv_urem);
    forward_qfbv_binary!(bv_sdiv);
    forward_qfbv_binary!(bv_srem);
    forward_qfbv_binary!(bv_smod);
    forward_qfbv_binary!(bv_shl);
    forward_qfbv_binary!(bv_lshr);
    forward_qfbv_binary!(bv_ashr);

    fn bv_extract(&mut self, x: TermId, hi: u32, lo: u32) -> Result<TermId> {
        self.builder.bv_extract(x, hi, lo)
    }

    forward_qfbv_binary!(bv_concat);

    fn bv_zext(&mut self, x: TermId, amount: u32) -> Result<TermId> {
        self.builder.bv_zext(x, amount)
    }

    fn bv_sext(&mut self, x: TermId, amount: u32) -> Result<TermId> {
        self.builder.bv_sext(x, amount)
    }

    fn bv_repeat(&mut self, x: TermId, count: u32) -> Result<TermId> {
        self.builder.bv_repeat(x, count)
    }

    fn bv_rotate_left(&mut self, x: TermId, amount: u32) -> Result<TermId> {
        self.builder.bv_rotate_left(x, amount)
    }

    fn bv_rotate_right(&mut self, x: TermId, amount: u32) -> Result<TermId> {
        self.builder.bv_rotate_right(x, amount)
    }

    fn bv_ite(&mut self, c: TermId, t: TermId, e: TermId) -> Result<TermId> {
        self.builder.bv_ite(c, t, e)
    }

    forward_qfbv_binary!(bv_eq);
    forward_qfbv_binary!(bv_ult);
    forward_qfbv_binary!(bv_ule);
    forward_qfbv_binary!(bv_slt);
    forward_qfbv_binary!(bv_sle);
    forward_qfbv_binary!(uadd_ovf);
    forward_qfbv_binary!(sadd_ovf);
    forward_qfbv_binary!(usub_ovf);
    forward_qfbv_binary!(ssub_ovf);
    forward_qfbv_binary!(umul_ovf);
    forward_qfbv_binary!(smul_ovf);
    forward_qfbv_unary!(neg_ovf);
    forward_qfbv_binary!(sdiv_ovf);

    fn assert(&mut self, root: TermId, name: Option<&str>) -> Result<()> {
        if let Some(name) = name {
            self.builder.assert_named(name, root)
        } else {
            self.builder.assert(root)
        }
    }

    fn assume(&mut self, root: TermId) -> Result<()> {
        self.builder.assume(root)
    }

    fn push(&mut self) -> Result<()> {
        self.builder.push();
        Ok(())
    }

    fn pop(&mut self) -> Result<()> {
        self.builder.pop()
    }
}

pub fn parse_smt2(script: &str) -> Result<Query> {
    let mut builder = Builder::new();
    let lowered = {
        let mut sink = QfbvSmtLibSink::new(&mut builder);
        lower_script(script, &mut sink, &FrontendOptions::standalone()).map_err(frontend_error)?
    };
    builder.set_want_model(lowered.want_model);
    builder.set_want_core(lowered.want_core);
    for name in lowered.get_values {
        builder.add_get_value(name);
    }
    builder.finish()
}

pub fn solve_smt2(script: &str, config: &Config) -> Result<SolveResult> {
    let query = parse_smt2(script)?;
    Solver::new(config.clone()).solve(&query)
}

pub fn format_smt2_response(query: &Query, result: &SolveResult) -> String {
    match result.status {
        SolveStatus::Sat => {
            let mut out = "sat\n".to_owned();
            if query.want_model {
                if let Some(model) = &result.model {
                    if query.get_values.is_empty() {
                        out.push_str(&format_model(model));
                    } else {
                        out.push_str(&format_get_values(model, &query.get_values));
                    }
                } else {
                    return format_unknown(Some("solver omitted requested model"));
                }
            }
            out
        }
        SolveStatus::Unsat => {
            let mut out = "unsat\n".to_owned();
            if query.want_core {
                if let Some(core) = &result.core {
                    out.push('(');
                    for (index, name) in core.iter().enumerate() {
                        if index > 0 {
                            out.push(' ');
                        }
                        out.push_str(&quote_symbol(name));
                    }
                    out.push_str(")\n");
                } else {
                    return format_unknown(Some("solver omitted requested unsat core"));
                }
            }
            out
        }
        SolveStatus::Unknown => format_unknown(result.message.as_deref()),
        SolveStatus::Simplified => "success\n".to_owned(),
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

fn format_model(model: &Model) -> String {
    let mut out = "(model\n".to_owned();
    for entry in &model.entries {
        out.push_str("  (define-fun ");
        out.push_str(&quote_symbol(&entry.name));
        out.push_str(" () ");
        match &entry.value {
            ScalarValue::Bool(_) => out.push_str("Bool "),
            ScalarValue::Bv { width, .. } => out.push_str(&format!("(_ BitVec {width}) ")),
        }
        out.push_str(&scalar_to_smt(&entry.value));
        out.push_str(")\n");
    }
    out.push_str(")\n");
    out
}

fn format_get_values(model: &Model, names: &[String]) -> String {
    let mut out = "(".to_owned();
    let mut emitted = 0usize;
    for name in names {
        if let Some(value) = model.get(name) {
            if emitted > 0 {
                out.push(' ');
            }
            emitted += 1;
            out.push('(');
            out.push_str(&quote_symbol(name));
            out.push(' ');
            out.push_str(&scalar_to_smt(value));
            out.push(')');
        }
    }
    out.push_str(")\n");
    out
}

fn quote_symbol(name: &str) -> String {
    if name
        .chars()
        .all(|ch| ch.is_ascii_alphanumeric() || "~!@$%^&*_+-=<>.?/".contains(ch))
        && !name.is_empty()
        && !name.chars().next().unwrap().is_ascii_digit()
    {
        name.to_owned()
    } else {
        format!("|{}|", name.replace('|', "||"))
    }
}

fn frontend_error(err: FrontendError) -> Error {
    match err {
        FrontendError::Parse(message) => Error::parse(message),
        FrontendError::Unsupported(message) => Error::unsupported(message),
        FrontendError::Invalid { context, message } => Error::invalid(context, message),
        FrontendError::Sink(message) => Error::invalid("SMT-LIB sink", message),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Config;

    #[test]
    fn let_bindings_are_simultaneous() -> Result<()> {
        let query = parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun x () (_ BitVec 1))
(assert (= x (_ bv1 1)))
(assert (let ((x (_ bv0 1)) (y x)) (= y (_ bv1 1))))
(check-sat)
"#,
        )?;
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Sat);
        Ok(())
    }

    #[test]
    fn qfbv_sink_adapter_builds_basic_query() -> Result<()> {
        let mut builder = Builder::new();
        {
            let mut sink = QfbvSmtLibSink::new(&mut builder);
            let x = sink.bv_var("x", 1)?;
            let one = sink.bv_const(&[1], 1)?;
            let eq = sink.bv_eq(x, one)?;
            sink.assert(eq, None)?;
        }
        let query = builder.finish()?;
        assert_eq!(query.assertions.len(), 1);
        Ok(())
    }

    #[test]
    fn get_value_rejects_unknown_symbols() {
        let err = parse_smt2(
            r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(assert (= x #b1))
(check-sat)
(get-value (y))
"#,
        )
        .unwrap_err();
        assert!(err.to_string().contains("y"), "{err}");
    }
}
