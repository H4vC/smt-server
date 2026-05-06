use std::collections::HashMap;
use std::time::Duration;

use dashu::{float::DBig, integer::UBig};
use smt_wire::{
    BinaryRequest, ExprBuilder, ModelBlock, NodeRef, ScalarValue, UnsatCoreBlock, WireError,
};

use crate::backend::{Backend, QueryResult, QueryStatus};
use crate::smt2::quote_symbol;
use yaspar::{
    action::{
        ActionOnAttribute, ActionOnConstant, ActionOnIdentifier, ActionOnIndex, ActionOnSort,
        ActionOnString, ActionOnTerm, ParsingAction, ParsingResult, Pattern,
    },
    ast::{DatatypeDec, DatatypeDef, FunctionDef, Keyword},
    position::Range,
};

#[derive(Debug, Clone)]
pub struct TextQuery {
    pub request: BinaryRequest,
    pub want_model: bool,
    pub want_core: bool,
    pub get_values: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SmtSort {
    Bool,
    Bv(u32),
}

#[derive(Debug, Clone)]
struct Binding {
    node: NodeRef,
    sort: SmtSort,
}

#[derive(Debug, Clone)]
struct FunctionBinding {
    params: Vec<(String, SmtSort)>,
    result: SmtSort,
    body: SExpr,
}

#[derive(Debug, Default)]
struct ScriptState {
    builder: ExprBuilder,
    env: HashMap<String, Binding>,
    functions: HashMap<String, FunctionBinding>,
    expansion_depth: usize,
    want_model: bool,
    want_core: bool,
    get_values: Vec<String>,
    saw_check_sat: bool,
}

pub fn parse_smtlib_script(script: &str) -> smt_wire::Result<TextQuery> {
    let exprs = parse_sexprs(script)?;
    let mut state = ScriptState::default();
    for expr in exprs {
        let list = match expr {
            SExpr::List(list) => list,
            SExpr::Atom(atom) => {
                return Err(WireError::invalid(
                    "SMT-LIB command",
                    format!("top-level atom {atom:?}"),
                ))
            }
        };
        if list.is_empty() {
            continue;
        }
        let cmd = atom(&list[0])?;
        match cmd {
            "set-logic" => {
                if list.len() == 2 && atom(&list[1])? != "QF_BV" {
                    return Err(WireError::invalid(
                        "SMT-LIB set-logic",
                        "only QF_BV is supported",
                    ));
                }
            }
            "set-info" | "set-option" | "exit" => {}
            "push" | "pop" | "reset" => {
                return Err(WireError::invalid(
                    "SMT-LIB incremental command",
                    format!("{cmd} is not supported on the stateless text path"),
                ))
            }
            "declare-const" => declare_const(&mut state, &list)?,
            "declare-fun" => declare_fun(&mut state, &list)?,
            "define-const" => define_const(&mut state, &list)?,
            "define-fun" => define_fun(&mut state, &list)?,
            "assert" => assert_command(&mut state, &list)?,
            "check-sat" => state.saw_check_sat = true,
            "check-sat-assuming" => check_sat_assuming(&mut state, &list)?,
            "get-model" => state.want_model = true,
            "get-value" => get_value_command(&mut state, &list)?,
            "get-unsat-core" => state.want_core = true,
            other => {
                return Err(WireError::invalid(
                    "SMT-LIB command",
                    format!("unsupported command {other}"),
                ))
            }
        }
    }
    if !state.saw_check_sat {
        return Err(WireError::invalid(
            "SMT-LIB script",
            "script does not contain check-sat",
        ));
    }
    let request_bytes =
        state
            .builder
            .build_solve_request(0, 0, state.want_model, state.want_core)?;
    let request = BinaryRequest::parse(&request_bytes)?;
    Ok(TextQuery {
        request,
        want_model: state.want_model,
        want_core: state.want_core,
        get_values: state.get_values,
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

fn declare_const(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 3 {
        return Err(WireError::invalid(
            "declare-const",
            "expected name and sort",
        ));
    }
    let name = atom(&list[1])?.to_owned();
    let sort = parse_sort(&list[2])?;
    let node = match sort {
        SmtSort::Bool => state.builder.bool_var(&name)?,
        SmtSort::Bv(width) => state.builder.bv_var(&name, width)?,
    };
    state.env.insert(name, Binding { node, sort });
    Ok(())
}

fn declare_fun(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 4 {
        return Err(WireError::invalid(
            "declare-fun",
            "expected name, args, sort",
        ));
    }
    match &list[2] {
        SExpr::List(args) if args.is_empty() => {}
        _ => {
            return Err(WireError::invalid(
                "declare-fun",
                "only 0-arity functions are supported",
            ))
        }
    }
    declare_const(state, &[list[0].clone(), list[1].clone(), list[3].clone()])
}

fn define_const(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 4 {
        return Err(WireError::invalid(
            "define-const",
            "expected name, sort, value",
        ));
    }
    let name = atom(&list[1])?.to_owned();
    let declared = parse_sort(&list[2])?;
    let binding = parse_expr_with_locals(state, &list[3], &mut HashMap::new())?;
    if declared != binding.sort {
        return Err(WireError::invalid(
            "define-const",
            "declared sort does not match value",
        ));
    }
    state.env.insert(name, binding);
    Ok(())
}

fn define_fun(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 5 {
        return Err(WireError::invalid(
            "define-fun",
            "expected name, args, sort, body",
        ));
    }
    let name = atom(&list[1])?.to_owned();
    let params = parse_function_params(&list[2])?;
    if params.is_empty() {
        return define_const(
            state,
            &[
                list[0].clone(),
                list[1].clone(),
                list[3].clone(),
                list[4].clone(),
            ],
        );
    }
    let result = parse_sort(&list[3])?;
    state.functions.insert(
        name,
        FunctionBinding {
            params,
            result,
            body: list[4].clone(),
        },
    );
    Ok(())
}

fn parse_function_params(expr: &SExpr) -> smt_wire::Result<Vec<(String, SmtSort)>> {
    let SExpr::List(params) = expr else {
        return Err(WireError::invalid("define-fun", "expected parameter list"));
    };
    let mut out = Vec::with_capacity(params.len());
    for param in params {
        let SExpr::List(items) = param else {
            return Err(WireError::invalid("define-fun", "bad parameter"));
        };
        if items.len() != 2 {
            return Err(WireError::invalid(
                "define-fun",
                "expected parameter name and sort",
            ));
        }
        let name = atom(&items[0])?.to_owned();
        if out.iter().any(|(existing, _)| existing == &name) {
            return Err(WireError::invalid(
                "define-fun",
                format!("duplicate parameter {name:?}"),
            ));
        }
        out.push((name, parse_sort(&items[1])?));
    }
    Ok(out)
}

fn assert_command(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 2 {
        return Err(WireError::invalid("assert", "expected one expression"));
    }
    if let Some((inner, name)) = named_annotation(&list[1])? {
        let binding = parse_expr_with_locals(state, inner, &mut HashMap::new())?;
        expect_sort(binding.sort, SmtSort::Bool, "assert")?;
        state.builder.assert_named(&name, binding.node)?;
    } else {
        let binding = parse_expr_with_locals(state, &list[1], &mut HashMap::new())?;
        expect_sort(binding.sort, SmtSort::Bool, "assert")?;
        state.builder.assert(binding.node)?;
    }
    Ok(())
}

fn check_sat_assuming(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 2 {
        return Err(WireError::invalid(
            "check-sat-assuming",
            "expected one assumption list",
        ));
    }
    let assumptions = match &list[1] {
        SExpr::List(items) => items,
        _ => {
            return Err(WireError::invalid(
                "check-sat-assuming",
                "expected assumption list",
            ))
        }
    };
    for item in assumptions {
        let binding = parse_expr_with_locals(state, item, &mut HashMap::new())?;
        expect_sort(binding.sort, SmtSort::Bool, "check-sat-assuming")?;
        state.builder.assume(binding.node)?;
    }
    state.saw_check_sat = true;
    Ok(())
}

fn get_value_command(state: &mut ScriptState, list: &[SExpr]) -> smt_wire::Result<()> {
    if list.len() != 2 {
        return Err(WireError::invalid("get-value", "expected one term list"));
    }
    let terms = match &list[1] {
        SExpr::List(items) => items,
        _ => return Err(WireError::invalid("get-value", "expected term list")),
    };
    state.want_model = true;
    for term in terms {
        match term {
            SExpr::Atom(name) => state.get_values.push(name.clone()),
            _ => {
                return Err(WireError::invalid(
                    "get-value",
                    "this frontend supports get-value for declared symbols",
                ))
            }
        }
    }
    Ok(())
}

fn named_annotation(expr: &SExpr) -> smt_wire::Result<Option<(&SExpr, String)>> {
    let SExpr::List(items) = expr else {
        return Ok(None);
    };
    let Some((term, name)) = parse_annotation(items)? else {
        return Ok(None);
    };
    Ok(name.map(|name| (term, name)))
}

fn parse_annotation(items: &[SExpr]) -> smt_wire::Result<Option<(&SExpr, Option<String>)>> {
    if items.is_empty() || atom(&items[0])? != "!" {
        return Ok(None);
    }
    if items.len() < 4 || !(items.len() - 2).is_multiple_of(2) {
        return Err(WireError::invalid(
            "annotation",
            "expected annotated term followed by keyword/value pairs",
        ));
    }
    let mut name = None;
    for pair in items[2..].chunks_exact(2) {
        let key = atom(&pair[0])?;
        if !key.starts_with(':') {
            return Err(WireError::invalid(
                "annotation",
                "expected annotation keyword",
            ));
        }
        if key == ":named" {
            name = Some(atom(&pair[1])?.to_owned());
        }
    }
    Ok(Some((&items[1], name)))
}

fn parse_expr_with_locals(
    state: &mut ScriptState,
    expr: &SExpr,
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    match expr {
        SExpr::Atom(atom) => parse_atom_expr(state, atom, locals),
        SExpr::List(items) => parse_list_expr(state, items, locals),
    }
}

fn parse_atom_expr(
    state: &mut ScriptState,
    value: &str,
    locals: &HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    if value == "true" {
        return Ok(Binding {
            node: state.builder.bool_true()?,
            sort: SmtSort::Bool,
        });
    }
    if value == "false" {
        return Ok(Binding {
            node: state.builder.bool_false()?,
            sort: SmtSort::Bool,
        });
    }
    if let Some((digits, radix)) = value
        .strip_prefix("#b")
        .map(|s| (s, 2))
        .or_else(|| value.strip_prefix("#x").map(|s| (s, 16)))
    {
        let width = if radix == 2 {
            digits.len() as u32
        } else {
            digits.len() as u32 * 4
        };
        let bytes = literal_bytes(digits, radix, width, value)?;
        let node = if width <= 64 {
            let mut raw = [0u8; 8];
            raw[..bytes.len()].copy_from_slice(&bytes);
            state.builder.bv_const(u64::from_le_bytes(raw), width)?
        } else {
            state.builder.bv_const_wide(&bytes, width)?
        };
        return Ok(Binding {
            node,
            sort: SmtSort::Bv(width),
        });
    }
    locals
        .get(value)
        .or_else(|| state.env.get(value))
        .cloned()
        .ok_or_else(|| WireError::invalid("SMT-LIB symbol", format!("undefined symbol {value:?}")))
}

fn literal_bytes(
    digits: &str,
    radix: u32,
    width: u32,
    original: &str,
) -> smt_wire::Result<Vec<u8>> {
    let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
    match radix {
        2 => {
            for (offset, ch) in digits.chars().rev().enumerate() {
                match ch {
                    '0' => {}
                    '1' => bytes[offset / 8] |= 1 << (offset % 8),
                    _ => {
                        return Err(WireError::invalid(
                            "bitvector literal",
                            format!("invalid binary literal {original}"),
                        ))
                    }
                }
            }
        }
        16 => {
            for (nibble, ch) in digits.chars().rev().enumerate() {
                let value = ch.to_digit(16).ok_or_else(|| {
                    WireError::invalid(
                        "bitvector literal",
                        format!("invalid hex literal {original}"),
                    )
                })? as u8;
                let bit = nibble * 4;
                bytes[bit / 8] |= value << (bit % 8);
            }
        }
        _ => unreachable!("only binary and hex literals are passed"),
    }
    Ok(bytes)
}

fn parse_list_expr(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    if items.is_empty() {
        return Err(WireError::invalid("SMT-LIB expression", "empty list"));
    }
    if let SExpr::List(op_items) = &items[0] {
        return parse_indexed_op(state, op_items, &items[1..], locals);
    }
    if atom(&items[0])? == "_" {
        return parse_indexed_literal(state, items);
    }
    let op = atom(&items[0])?;
    match op {
        "!" => {
            let Some((term, _)) = parse_annotation(items)? else {
                return Err(WireError::invalid("annotation", "expected annotation"));
            };
            parse_expr_with_locals(state, term, locals)
        }
        "let" => parse_let(state, items, locals),
        "ite" => {
            expect_len(items, 4, "ite")?;
            let c = parse_expr_with_locals(state, &items[1], locals)?;
            let t = parse_expr_with_locals(state, &items[2], locals)?;
            let e = parse_expr_with_locals(state, &items[3], locals)?;
            expect_sort(c.sort, SmtSort::Bool, "ite condition")?;
            match (t.sort, e.sort) {
                (SmtSort::Bool, SmtSort::Bool) => Ok(Binding {
                    node: state.builder.bool_ite(c.node, t.node, e.node)?,
                    sort: SmtSort::Bool,
                }),
                (SmtSort::Bv(w1), SmtSort::Bv(w2)) if w1 == w2 => Ok(Binding {
                    node: state.builder.bv_ite(c.node, t.node, e.node)?,
                    sort: SmtSort::Bv(w1),
                }),
                _ => Err(WireError::invalid("ite", "branch sorts differ")),
            }
        }
        "=" => parse_equals(state, &items[1..], locals),
        "distinct" => parse_distinct(state, &items[1..], locals),
        "not" => unary_bool(state, items, locals, |b, x| b.bool_not(x)),
        "and" => fold_bool(state, &items[1..], locals, true, |b, a, c| b.bool_and(a, c)),
        "or" => fold_bool(state, &items[1..], locals, false, |b, a, c| b.bool_or(a, c)),
        "=>" => binary_bool(state, items, locals, |b, a, c| b.bool_implies(a, c)),
        "bvnot" => unary_bv(state, items, locals, |b, x| b.bv_not(x)),
        "bvneg" => unary_bv(state, items, locals, |b, x| b.bv_neg(x)),
        "bvand" => binary_bv(state, items, locals, |b, a, c| b.bv_and(a, c)),
        "bvor" => binary_bv(state, items, locals, |b, a, c| b.bv_or(a, c)),
        "bvxor" => binary_bv(state, items, locals, |b, a, c| b.bv_xor(a, c)),
        "bvadd" => binary_bv(state, items, locals, |b, a, c| b.bv_add(a, c)),
        "bvsub" => binary_bv(state, items, locals, |b, a, c| b.bv_sub(a, c)),
        "bvmul" => binary_bv(state, items, locals, |b, a, c| b.bv_mul(a, c)),
        "bvudiv" => binary_bv(state, items, locals, |b, a, c| b.bv_udiv(a, c)),
        "bvurem" => binary_bv(state, items, locals, |b, a, c| b.bv_urem(a, c)),
        "bvsdiv" => binary_bv(state, items, locals, |b, a, c| b.bv_sdiv(a, c)),
        "bvsrem" => binary_bv(state, items, locals, |b, a, c| b.bv_srem(a, c)),
        "bvsmod" => binary_bv(state, items, locals, |b, a, c| b.bv_smod(a, c)),
        "bvshl" => binary_bv(state, items, locals, |b, a, c| b.bv_shl(a, c)),
        "bvlshr" => binary_bv(state, items, locals, |b, a, c| b.bv_lshr(a, c)),
        "bvashr" => binary_bv(state, items, locals, |b, a, c| b.bv_ashr(a, c)),
        "concat" => binary_bv(state, items, locals, |b, a, c| b.bv_concat(a, c)),
        "bvult" => bv_cmp(state, items, locals, |b, a, c| b.bv_ult(a, c)),
        "bvule" => bv_cmp(state, items, locals, |b, a, c| b.bv_ule(a, c)),
        "bvugt" => bv_cmp(state, items, locals, |b, a, c| b.bv_ugt(a, c)),
        "bvuge" => bv_cmp(state, items, locals, |b, a, c| b.bv_uge(a, c)),
        "bvslt" => bv_cmp(state, items, locals, |b, a, c| b.bv_slt(a, c)),
        "bvsle" => bv_cmp(state, items, locals, |b, a, c| b.bv_sle(a, c)),
        "bvsgt" => bv_cmp(state, items, locals, |b, a, c| b.bv_sgt(a, c)),
        "bvsge" => bv_cmp(state, items, locals, |b, a, c| b.bv_sge(a, c)),
        other => {
            if let Some(function) = state.functions.get(other).cloned() {
                parse_function_call(state, other, &function, &items[1..], locals)
            } else {
                Err(WireError::invalid(
                    "SMT-LIB expression",
                    format!("unsupported operator {other}"),
                ))
            }
        }
    }
}

fn parse_function_call(
    state: &mut ScriptState,
    name: &str,
    function: &FunctionBinding,
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    if args.len() != function.params.len() {
        return Err(WireError::invalid(
            "define-fun application",
            format!(
                "{name} expected {} arguments, got {}",
                function.params.len(),
                args.len()
            ),
        ));
    }
    if state.expansion_depth >= 64 {
        return Err(WireError::invalid(
            "define-fun application",
            "macro expansion depth exceeded",
        ));
    }
    let mut expansion_locals = HashMap::with_capacity(function.params.len());
    for ((param_name, param_sort), arg) in function.params.iter().zip(args) {
        let binding = parse_expr_with_locals(state, arg, locals)?;
        expect_sort(binding.sort, *param_sort, "define-fun application")?;
        expansion_locals.insert(param_name.clone(), binding);
    }
    state.expansion_depth += 1;
    let result = parse_expr_with_locals(state, &function.body, &mut expansion_locals);
    state.expansion_depth -= 1;
    let binding = result?;
    expect_sort(binding.sort, function.result, "define-fun result")?;
    Ok(binding)
}

fn parse_indexed_literal(state: &mut ScriptState, items: &[SExpr]) -> smt_wire::Result<Binding> {
    let literal = if items.len() == 4 && atom(&items[1])? == "bv" {
        Some((atom(&items[2])?, atom(&items[3])?))
    } else if items.len() == 3 {
        let symbol = atom(&items[1])?;
        if let Some(value) = symbol.strip_prefix("bv") {
            Some((value, atom(&items[2])?))
        } else {
            None
        }
    } else {
        None
    };
    let Some((value, width)) = literal else {
        return Err(WireError::invalid("indexed literal", "expected (_ bvN W)"));
    };
    if value.is_empty() {
        return Err(WireError::invalid("bv literal", "missing value"));
    }
    let width = width
        .parse::<u32>()
        .map_err(|_| WireError::invalid("bv literal", "invalid width"))?;
    validate_bv_width(width, "bv literal")?;
    let bytes = decimal_literal_bytes(value, width)?;
    let node = if width <= 64 {
        let mut raw = [0u8; 8];
        raw[..bytes.len()].copy_from_slice(&bytes);
        state.builder.bv_const(u64::from_le_bytes(raw), width)?
    } else {
        state.builder.bv_const_wide(&bytes, width)?
    };
    Ok(Binding {
        node,
        sort: SmtSort::Bv(width),
    })
}

fn validate_bv_width(width: u32, context: &'static str) -> smt_wire::Result<()> {
    if !(1..=smt_wire::MAX_BV_WIDTH).contains(&width) {
        return Err(WireError::invalid(
            context,
            format!("width {width} is outside 1..={}", smt_wire::MAX_BV_WIDTH),
        ));
    }
    Ok(())
}

fn decimal_literal_bytes(value: &str, width: u32) -> smt_wire::Result<Vec<u8>> {
    let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
    for ch in value.bytes() {
        let digit = match ch {
            b'0'..=b'9' => ch - b'0',
            _ => return Err(WireError::invalid("bv literal", "invalid decimal value")),
        };
        let mut carry = u16::from(digit);
        for byte in &mut bytes {
            let next = u16::from(*byte) * 10 + carry;
            *byte = next as u8;
            carry = next >> 8;
        }
        mask_unused_high_bits(width, &mut bytes);
    }
    Ok(bytes)
}

fn mask_unused_high_bits(width: u32, bytes: &mut [u8]) {
    let valid_bits = width % 8;
    if valid_bits != 0 && !bytes.is_empty() {
        let mask = (1u8 << valid_bits) - 1;
        if let Some(last) = bytes.last_mut() {
            *last &= mask;
        }
    }
}

fn parse_indexed_op(
    state: &mut ScriptState,
    op_items: &[SExpr],
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    if op_items.len() == 4 && atom(&op_items[0])? == "_" && atom(&op_items[1])? == "extract" {
        if args.len() != 1 {
            return Err(WireError::invalid("extract", "expected one argument"));
        }
        let hi = atom(&op_items[2])?
            .parse::<u32>()
            .map_err(|_| WireError::invalid("extract", "bad high index"))?;
        let lo = atom(&op_items[3])?
            .parse::<u32>()
            .map_err(|_| WireError::invalid("extract", "bad low index"))?;
        let x = parse_expr_with_locals(state, &args[0], locals)?;
        let SmtSort::Bv(_) = x.sort else {
            return Err(WireError::invalid("extract", "argument is not BV"));
        };
        let result_width = hi
            .checked_sub(lo)
            .and_then(|value| value.checked_add(1))
            .ok_or(WireError::invalid("extract", "invalid bounds"))?;
        return Ok(Binding {
            node: state.builder.bv_extract(x.node, hi, lo)?,
            sort: SmtSort::Bv(result_width),
        });
    }
    if op_items.len() == 3 && atom(&op_items[0])? == "_" {
        if args.len() != 1 {
            return Err(WireError::invalid("extension", "expected one argument"));
        }
        let amount = atom(&op_items[2])?
            .parse::<u16>()
            .map_err(|_| WireError::invalid("extension", "bad amount"))?;
        let x = parse_expr_with_locals(state, &args[0], locals)?;
        let SmtSort::Bv(width) = x.sort else {
            return Err(WireError::invalid("extension", "argument is not BV"));
        };
        let result_width = width
            .checked_add(u32::from(amount))
            .ok_or(WireError::IntegerOverflow("extension width"))?;
        return match atom(&op_items[1])? {
            "zero_extend" => Ok(Binding {
                node: state.builder.bv_zext(x.node, amount)?,
                sort: SmtSort::Bv(result_width),
            }),
            "sign_extend" => Ok(Binding {
                node: state.builder.bv_sext(x.node, amount)?,
                sort: SmtSort::Bv(result_width),
            }),
            _ => Err(WireError::invalid(
                "indexed operator",
                "unsupported indexed operator",
            )),
        };
    }
    Err(WireError::invalid(
        "indexed operator",
        "unsupported indexed operator",
    ))
}

fn parse_let(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    expect_len(items, 3, "let")?;
    let bindings = match &items[1] {
        SExpr::List(items) => items,
        _ => return Err(WireError::invalid("let", "expected binding list")),
    };
    let mut nested = locals.clone();
    for binding in bindings {
        let pair = match binding {
            SExpr::List(pair) if pair.len() == 2 => pair,
            _ => return Err(WireError::invalid("let", "bad binding")),
        };
        let name = atom(&pair[0])?.to_owned();
        let value = parse_expr_with_locals(state, &pair[1], &mut nested)?;
        nested.insert(name, value);
    }
    parse_expr_with_locals(state, &items[2], &mut nested)
}

fn parse_equals(
    state: &mut ScriptState,
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    if args.len() < 2 {
        return Err(WireError::invalid("=", "expected at least two arguments"));
    }
    let first = parse_expr_with_locals(state, &args[0], locals)?;
    let mut result = state.builder.bool_true()?;
    let mut previous = first;
    for arg in &args[1..] {
        let next = parse_expr_with_locals(state, arg, locals)?;
        let eq = equality_node(state, previous.clone(), next.clone(), "=")?;
        result = state.builder.bool_and(result, eq)?;
        previous = next;
    }
    Ok(Binding {
        node: result,
        sort: SmtSort::Bool,
    })
}

fn parse_distinct(
    state: &mut ScriptState,
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> smt_wire::Result<Binding> {
    let mut values = Vec::with_capacity(args.len());
    for arg in args {
        values.push(parse_expr_with_locals(state, arg, locals)?);
    }
    let mut result = state.builder.bool_true()?;
    for i in 0..values.len() {
        for j in i + 1..values.len() {
            let eq = equality_node(state, values[i].clone(), values[j].clone(), "distinct")?;
            let ne = state.builder.bool_not(eq)?;
            result = state.builder.bool_and(result, ne)?;
        }
    }
    Ok(Binding {
        node: result,
        sort: SmtSort::Bool,
    })
}

fn equality_node(
    state: &mut ScriptState,
    a: Binding,
    b: Binding,
    context: &'static str,
) -> smt_wire::Result<NodeRef> {
    match (a.sort, b.sort) {
        (SmtSort::Bool, SmtSort::Bool) => state.builder.bool_eq(a.node, b.node),
        (SmtSort::Bv(w1), SmtSort::Bv(w2)) if w1 == w2 => state.builder.bv_eq(a.node, b.node),
        _ => Err(WireError::invalid(context, "argument sorts differ")),
    }
}

fn unary_bool(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut ExprBuilder, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<Binding> {
    expect_len(items, 2, "unary bool")?;
    let x = parse_expr_with_locals(state, &items[1], locals)?;
    expect_sort(x.sort, SmtSort::Bool, "unary bool")?;
    Ok(Binding {
        node: f(&mut state.builder, x.node)?,
        sort: SmtSort::Bool,
    })
}

fn binary_bool(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut ExprBuilder, NodeRef, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<Binding> {
    expect_len(items, 3, "binary bool")?;
    let a = parse_expr_with_locals(state, &items[1], locals)?;
    let b = parse_expr_with_locals(state, &items[2], locals)?;
    expect_sort(a.sort, SmtSort::Bool, "binary bool")?;
    expect_sort(b.sort, SmtSort::Bool, "binary bool")?;
    Ok(Binding {
        node: f(&mut state.builder, a.node, b.node)?,
        sort: SmtSort::Bool,
    })
}

fn fold_bool(
    state: &mut ScriptState,
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    identity: bool,
    f: fn(&mut ExprBuilder, NodeRef, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<Binding> {
    if args.is_empty() {
        let node = if identity {
            state.builder.bool_true()?
        } else {
            state.builder.bool_false()?
        };
        return Ok(Binding {
            node,
            sort: SmtSort::Bool,
        });
    }
    let mut cur = parse_expr_with_locals(state, &args[0], locals)?;
    expect_sort(cur.sort, SmtSort::Bool, "fold bool")?;
    for arg in &args[1..] {
        let next = parse_expr_with_locals(state, arg, locals)?;
        expect_sort(next.sort, SmtSort::Bool, "fold bool")?;
        cur = Binding {
            node: f(&mut state.builder, cur.node, next.node)?,
            sort: SmtSort::Bool,
        };
    }
    Ok(cur)
}

fn unary_bv(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut ExprBuilder, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<Binding> {
    expect_len(items, 2, "unary BV")?;
    let x = parse_expr_with_locals(state, &items[1], locals)?;
    let SmtSort::Bv(width) = x.sort else {
        return Err(WireError::invalid("unary BV", "argument is not BV"));
    };
    Ok(Binding {
        node: f(&mut state.builder, x.node)?,
        sort: SmtSort::Bv(width),
    })
}

fn binary_bv(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut ExprBuilder, NodeRef, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<Binding> {
    expect_len(items, 3, "binary BV")?;
    let a = parse_expr_with_locals(state, &items[1], locals)?;
    let b = parse_expr_with_locals(state, &items[2], locals)?;
    let (SmtSort::Bv(w1), SmtSort::Bv(w2)) = (a.sort, b.sort) else {
        return Err(WireError::invalid("binary BV", "argument is not BV"));
    };
    if w1 != w2 {
        return Err(WireError::invalid("binary BV", "width mismatch"));
    }
    Ok(Binding {
        node: f(&mut state.builder, a.node, b.node)?,
        sort: SmtSort::Bv(w1),
    })
}

fn bv_cmp(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut ExprBuilder, NodeRef, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<Binding> {
    let value = binary_bv(state, items, locals, f)?;
    Ok(Binding {
        node: value.node,
        sort: SmtSort::Bool,
    })
}

fn parse_sort(expr: &SExpr) -> smt_wire::Result<SmtSort> {
    match expr {
        SExpr::Atom(atom) if atom == "Bool" => Ok(SmtSort::Bool),
        SExpr::List(items)
            if items.len() == 3 && atom(&items[0])? == "_" && atom(&items[1])? == "BitVec" =>
        {
            let width = atom(&items[2])?
                .parse::<u32>()
                .map_err(|_| WireError::invalid("sort", "invalid BitVec width"))?;
            validate_bv_width(width, "sort")?;
            Ok(SmtSort::Bv(width))
        }
        _ => Err(WireError::invalid("sort", "expected Bool or (_ BitVec n)")),
    }
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

fn expect_len(items: &[SExpr], len: usize, context: &'static str) -> smt_wire::Result<()> {
    if items.len() != len {
        return Err(WireError::invalid(context, format!("expected {len} items")));
    }
    Ok(())
}

fn expect_sort(actual: SmtSort, expected: SmtSort, context: &'static str) -> smt_wire::Result<()> {
    if actual != expected {
        return Err(WireError::invalid(
            context,
            format!("expected {expected:?}, got {actual:?}"),
        ));
    }
    Ok(())
}

fn atom(expr: &SExpr) -> smt_wire::Result<&str> {
    match expr {
        SExpr::Atom(atom) => Ok(atom),
        SExpr::List(_) => Err(WireError::invalid("SMT-LIB atom", "expected atom")),
    }
}

fn parse_sexprs(input: &str) -> smt_wire::Result<Vec<SExpr>> {
    let mut action = SExprAction;
    yaspar::smtlib2::ScriptParser::new()
        .parse(&mut action, yaspar::tokenize_str(input, true))
        .map_err(|err| WireError::invalid("SMT-LIB parser", err.to_string()))
}

struct SExprAction;

fn sexpr_atom(value: impl Into<String>) -> SExpr {
    SExpr::Atom(value.into())
}

fn sexpr_list(items: impl IntoIterator<Item = SExpr>) -> SExpr {
    SExpr::List(items.into_iter().collect())
}

fn indexed_symbol(symbol: String, indices: Vec<SExpr>) -> SExpr {
    if indices.is_empty() {
        sexpr_atom(symbol)
    } else {
        let mut items = Vec::with_capacity(indices.len() + 2);
        items.push(sexpr_atom("_"));
        items.push(sexpr_atom(symbol));
        items.extend(indices);
        sexpr_list(items)
    }
}

fn byte_bits(bytes: &[u8], len: usize) -> String {
    let mut out = String::with_capacity(len + 2);
    out.push_str("#b");
    for bit in (0..len).rev() {
        let byte = bytes[bit / 8];
        out.push(if ((byte >> (bit % 8)) & 1) != 0 {
            '1'
        } else {
            '0'
        });
    }
    out
}

fn byte_hex(bytes: &[u8], len: usize) -> String {
    let mut out = String::with_capacity(len + 2);
    out.push_str("#x");
    for nibble in (0..len).rev() {
        let byte = bytes[nibble / 2];
        let value = (byte >> ((nibble % 2) * 4)) & 0xf;
        out.push(char::from_digit(u32::from(value), 16).expect("hex digit"));
    }
    out
}

fn command(name: &str, args: impl IntoIterator<Item = SExpr>) -> SExpr {
    let mut items = vec![sexpr_atom(name)];
    items.extend(args);
    sexpr_list(items)
}

fn vars_to_sexpr(vars: Vec<(String, SExpr)>) -> SExpr {
    sexpr_list(
        vars.into_iter()
            .map(|(name, sort)| sexpr_list([sexpr_atom(name), sort])),
    )
}

impl ActionOnString for SExprAction {
    type Str = String;

    fn on_string(&mut self, _range: Range, s: String) -> ParsingResult<Self::Str> {
        Ok(s)
    }
}

impl ActionOnConstant for SExprAction {
    type Constant = SExpr;

    fn on_constant_binary(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(sexpr_atom(byte_bits(&bytes, len)))
    }

    fn on_constant_hexadecimal(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(sexpr_atom(byte_hex(&bytes, len)))
    }

    fn on_constant_decimal(
        &mut self,
        _range: Range,
        decimal: DBig,
    ) -> ParsingResult<Self::Constant> {
        Ok(sexpr_atom(decimal.to_string()))
    }

    fn on_constant_numeral(
        &mut self,
        _range: Range,
        numeral: UBig,
    ) -> ParsingResult<Self::Constant> {
        Ok(sexpr_atom(numeral.to_string()))
    }

    fn on_constant_string(
        &mut self,
        _range: Range,
        string: Self::Str,
    ) -> ParsingResult<Self::Constant> {
        Ok(sexpr_atom(string))
    }

    fn on_constant_bool(&mut self, _range: Range, boolean: bool) -> ParsingResult<Self::Constant> {
        Ok(sexpr_atom(if boolean { "true" } else { "false" }))
    }
}

impl ActionOnIndex for SExprAction {
    type Index = SExpr;

    fn on_index_numeral(&mut self, _range: Range, index: UBig) -> ParsingResult<Self::Index> {
        Ok(sexpr_atom(index.to_string()))
    }

    fn on_index_symbol(&mut self, _range: Range, index: Self::Str) -> ParsingResult<Self::Index> {
        Ok(sexpr_atom(index))
    }

    fn on_index_hexadecimal(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Index> {
        Ok(sexpr_atom(byte_hex(&bytes, len)))
    }
}

impl ActionOnIdentifier for SExprAction {
    type Identifier = SExpr;

    fn on_identifier(
        &mut self,
        _range: Range,
        symbol: Self::Str,
        indices: Vec<Self::Index>,
    ) -> ParsingResult<Self::Identifier> {
        Ok(indexed_symbol(symbol, indices))
    }
}

impl ActionOnAttribute for SExprAction {
    type Term = SExpr;
    type Attribute = SExpr;

    fn on_attribute_keyword(
        &mut self,
        _range: Range,
        keyword: Keyword,
    ) -> ParsingResult<Self::Attribute> {
        Ok(sexpr_list([sexpr_atom(keyword.to_string())]))
    }

    fn on_attribute_constant(
        &mut self,
        _range: Range,
        keyword: Keyword,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Attribute> {
        Ok(sexpr_list([sexpr_atom(keyword.to_string()), constant]))
    }

    fn on_attribute_symbol(
        &mut self,
        _range: Range,
        keyword: Keyword,
        symbol: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        Ok(sexpr_list([
            sexpr_atom(keyword.to_string()),
            sexpr_atom(symbol),
        ]))
    }

    fn on_attribute_named(
        &mut self,
        _range: Range,
        name: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        Ok(sexpr_list([sexpr_atom(":named"), sexpr_atom(name)]))
    }

    fn on_attribute_pattern(
        &mut self,
        _range: Range,
        patterns: Vec<Self::Term>,
    ) -> ParsingResult<Self::Attribute> {
        Ok(command(":pattern", patterns))
    }
}

impl ActionOnSort for SExprAction {
    type Sort = SExpr;

    fn on_sort(
        &mut self,
        _range: Range,
        identifier: Self::Identifier,
        args: Vec<Self::Sort>,
    ) -> ParsingResult<Self::Sort> {
        if args.is_empty() {
            Ok(identifier)
        } else {
            let mut items = vec![identifier];
            items.extend(args);
            Ok(sexpr_list(items))
        }
    }
}

impl ActionOnTerm for SExprAction {
    fn on_term_constant(
        &mut self,
        _range: Range,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Term> {
        Ok(constant)
    }

    fn on_term_identifier(
        &mut self,
        _range: Range,
        identifier: Self::Identifier,
        sort: Option<Self::Sort>,
    ) -> ParsingResult<Self::Term> {
        Ok(match sort {
            Some(sort) => command("as", [identifier, sort]),
            None => identifier,
        })
    }

    fn on_term_app(
        &mut self,
        _range: Range,
        identifier: Self::Identifier,
        sort: Option<Self::Sort>,
        args: Vec<Self::Term>,
    ) -> ParsingResult<Self::Term> {
        let head = match sort {
            Some(sort) => command("as", [identifier, sort]),
            None => identifier,
        };
        let mut items = vec![head];
        items.extend(args);
        Ok(sexpr_list(items))
    }

    fn on_term_let(
        &mut self,
        _range: Range,
        bindings: Vec<(Self::Str, Self::Term)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        let binding_list = sexpr_list(
            bindings
                .into_iter()
                .map(|(name, term)| sexpr_list([sexpr_atom(name), term])),
        );
        Ok(command("let", [binding_list, body]))
    }

    fn on_term_lambda(
        &mut self,
        _range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(command("lambda", [vars_to_sexpr(names), body]))
    }

    fn on_term_exists(
        &mut self,
        _range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(command("exists", [vars_to_sexpr(names), body]))
    }

    fn on_term_forall(
        &mut self,
        _range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(command("forall", [vars_to_sexpr(names), body]))
    }

    fn on_term_match(
        &mut self,
        _range: Range,
        scrutinee: Self::Term,
        cases: Vec<(Pattern<Self::Str>, Self::Term)>,
    ) -> ParsingResult<Self::Term> {
        let case_exprs = cases.into_iter().map(|(_, body)| body);
        Ok(command("match", [scrutinee, sexpr_list(case_exprs)]))
    }

    fn on_term_annotated(
        &mut self,
        _range: Range,
        t: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> ParsingResult<Self::Term> {
        let mut items = vec![sexpr_atom("!"), t];
        for attribute in attributes {
            match attribute {
                SExpr::List(values) => items.extend(values),
                atom @ SExpr::Atom(_) => items.push(atom),
            }
        }
        Ok(sexpr_list(items))
    }
}

impl ParsingAction for SExprAction {
    type Command = SExpr;

    fn on_command_assert(&mut self, _range: Range, t: Self::Term) -> ParsingResult<Self::Command> {
        Ok(command("assert", [t]))
    }

    fn on_command_check_sat(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("check-sat", []))
    }

    fn on_command_check_sat_assuming(
        &mut self,
        _range: Range,
        terms: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(command("check-sat-assuming", [sexpr_list(terms)]))
    }

    fn on_command_declare_const(
        &mut self,
        _range: Range,
        name: Self::Str,
        sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(command("declare-const", [sexpr_atom(name), sort]))
    }

    fn on_command_declare_datatype(
        &mut self,
        _range: Range,
        name: Self::Str,
        _datatype: DatatypeDec<Self::Str, Self::Sort>,
    ) -> ParsingResult<Self::Command> {
        Ok(command("declare-datatype", [sexpr_atom(name)]))
    }

    fn on_command_declare_datatypes(
        &mut self,
        _range: Range,
        _defs: Vec<DatatypeDef<Self::Str, Self::Sort>>,
    ) -> ParsingResult<Self::Command> {
        Ok(command("declare-datatypes", []))
    }

    fn on_command_declare_fun(
        &mut self,
        _range: Range,
        name: Self::Str,
        input_sorts: Vec<Self::Sort>,
        out_sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(command(
            "declare-fun",
            [sexpr_atom(name), sexpr_list(input_sorts), out_sort],
        ))
    }

    fn on_command_declare_sort(
        &mut self,
        _range: Range,
        name: Self::Str,
        arity: UBig,
    ) -> ParsingResult<Self::Command> {
        Ok(command(
            "declare-sort",
            [sexpr_atom(name), sexpr_atom(arity.to_string())],
        ))
    }

    fn on_command_declare_sort_parameter(
        &mut self,
        _range: Range,
        name: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(command("declare-sort-parameter", [sexpr_atom(name)]))
    }

    fn on_command_define_const(
        &mut self,
        _range: Range,
        name: Self::Str,
        sort: Self::Sort,
        term: Self::Term,
    ) -> ParsingResult<Self::Command> {
        Ok(command("define-const", [sexpr_atom(name), sort, term]))
    }

    fn on_command_define_fun(
        &mut self,
        _range: Range,
        definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(command(
            "define-fun",
            [
                sexpr_atom(definition.name),
                vars_to_sexpr(definition.vars),
                definition.out_sort,
                definition.body,
            ],
        ))
    }

    fn on_command_define_fun_rec(
        &mut self,
        _range: Range,
        definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(command(
            "define-fun-rec",
            [
                sexpr_atom(definition.name),
                vars_to_sexpr(definition.vars),
                definition.out_sort,
                definition.body,
            ],
        ))
    }

    fn on_command_define_funs_rec(
        &mut self,
        _range: Range,
        _definitions: Vec<FunctionDef<Self::Str, Self::Sort, Self::Term>>,
    ) -> ParsingResult<Self::Command> {
        Ok(command("define-funs-rec", []))
    }

    fn on_command_define_sort(
        &mut self,
        _range: Range,
        name: Self::Str,
        params: Vec<Self::Str>,
        sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(command(
            "define-sort",
            [
                sexpr_atom(name),
                sexpr_list(params.into_iter().map(sexpr_atom)),
                sort,
            ],
        ))
    }

    fn on_command_echo(&mut self, _range: Range, s: Self::Str) -> ParsingResult<Self::Command> {
        Ok(command("echo", [sexpr_atom(s)]))
    }

    fn on_command_exit(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("exit", []))
    }

    fn on_command_get_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("get-assertions", []))
    }

    fn on_command_get_assignment(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("get-assignment", []))
    }

    fn on_command_get_info(&mut self, _range: Range, kw: Keyword) -> ParsingResult<Self::Command> {
        Ok(command("get-info", [sexpr_atom(kw.to_string())]))
    }

    fn on_command_get_model(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("get-model", []))
    }

    fn on_command_get_option(
        &mut self,
        _range: Range,
        kw: Keyword,
    ) -> ParsingResult<Self::Command> {
        Ok(command("get-option", [sexpr_atom(kw.to_string())]))
    }

    fn on_command_get_proof(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("get-proof", []))
    }

    fn on_command_get_unsat_assumptions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("get-unsat-assumptions", []))
    }

    fn on_command_get_unsat_core(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("get-unsat-core", []))
    }

    fn on_command_get_value(
        &mut self,
        _range: Range,
        ts: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(command("get-value", [sexpr_list(ts)]))
    }

    fn on_command_pop(&mut self, _range: Range, lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(command("pop", [sexpr_atom(lvl.to_string())]))
    }

    fn on_command_push(&mut self, _range: Range, lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(command("push", [sexpr_atom(lvl.to_string())]))
    }

    fn on_command_reset(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("reset", []))
    }

    fn on_command_reset_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(command("reset-assertions", []))
    }

    fn on_command_set_info(
        &mut self,
        _range: Range,
        attributes: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(command("set-info", [attributes]))
    }

    fn on_command_set_logic(
        &mut self,
        _range: Range,
        logic: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(command("set-logic", [sexpr_atom(logic)]))
    }

    fn on_command_set_option(
        &mut self,
        _range: Range,
        attribute: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(command("set-option", [attribute]))
    }
}
