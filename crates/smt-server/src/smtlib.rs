use std::collections::HashMap;

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

#[derive(Debug, Default)]
struct ScriptState {
    builder: ExprBuilder,
    env: HashMap<String, Binding>,
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
            "set-option" | "exit" => {}
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
        Err(err) => return Ok(format!("(error {:?})\n", err.to_string()).into_bytes()),
    };
    match backend.handle(&query.request) {
        Ok(result) => Ok(text_response(&query, result).into_bytes()),
        Err(err) => Ok(format!("(error {:?})\n", err.to_string()).into_bytes()),
    }
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
    match &list[2] {
        SExpr::List(args) if args.is_empty() => {}
        _ => {
            return Err(WireError::invalid(
                "define-fun",
                "only 0-arity functions are supported",
            ))
        }
    }
    define_const(
        state,
        &[
            list[0].clone(),
            list[1].clone(),
            list[3].clone(),
            list[4].clone(),
        ],
    )
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
    if items.len() >= 4 && atom(&items[0])? == "!" {
        let mut name = None;
        let mut index = 2;
        while index + 1 < items.len() {
            if atom(&items[index])? == ":named" {
                name = Some(atom(&items[index + 1])?.to_owned());
            }
            index += 2;
        }
        if let Some(name) = name {
            return Ok(Some((&items[1], name)));
        }
    }
    Ok(None)
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
    if let Some((bits, radix)) = value
        .strip_prefix("#b")
        .map(|s| (s, 2))
        .or_else(|| value.strip_prefix("#x").map(|s| (s, 16)))
    {
        let width = if radix == 2 {
            bits.len() as u32
        } else {
            bits.len() as u32 * 4
        };
        let parsed = u128::from_str_radix(bits, radix)
            .map_err(|_| WireError::invalid("bitvector literal", value.to_owned()))?;
        let node = if width <= 64 {
            state.builder.bv_const(parsed as u64, width)?
        } else {
            let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
            for (index, byte) in bytes.iter_mut().enumerate().take(16) {
                *byte = ((parsed >> (index * 8)) & 0xff) as u8;
            }
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
        "!" => parse_expr_with_locals(state, &items[1], locals),
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
        other => Err(WireError::invalid(
            "SMT-LIB expression",
            format!("unsupported operator {other}"),
        )),
    }
}

fn parse_indexed_literal(state: &mut ScriptState, items: &[SExpr]) -> smt_wire::Result<Binding> {
    if items.len() == 4 && atom(&items[1])? == "bv" {
        let value = atom(&items[2])?
            .parse::<u64>()
            .map_err(|_| WireError::invalid("bv literal", "invalid value"))?;
        let width = atom(&items[3])?
            .parse::<u32>()
            .map_err(|_| WireError::invalid("bv literal", "invalid width"))?;
        return Ok(Binding {
            node: state.builder.bv_const(value, width)?,
            sort: SmtSort::Bv(width),
        });
    }
    Err(WireError::invalid("indexed literal", "expected (_ bvN W)"))
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
        return Ok(Binding {
            node: state.builder.bv_extract(x.node, hi, lo)?,
            sort: SmtSort::Bv(hi - lo + 1),
        });
    }
    if op_items.len() == 3 && atom(&op_items[0])? == "_" {
        let amount = atom(&op_items[2])?
            .parse::<u16>()
            .map_err(|_| WireError::invalid("extension", "bad amount"))?;
        let x = parse_expr_with_locals(state, &args[0], locals)?;
        let SmtSort::Bv(width) = x.sort else {
            return Err(WireError::invalid("extension", "argument is not BV"));
        };
        return match atom(&op_items[1])? {
            "zero_extend" => Ok(Binding {
                node: state.builder.bv_zext(x.node, amount)?,
                sort: SmtSort::Bv(width + u32::from(amount)),
            }),
            "sign_extend" => Ok(Binding {
                node: state.builder.bv_sext(x.node, amount)?,
                sort: SmtSort::Bv(width + u32::from(amount)),
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
    if args.len() != 2 {
        return Err(WireError::invalid("=", "expected two arguments"));
    }
    let a = parse_expr_with_locals(state, &args[0], locals)?;
    let b = parse_expr_with_locals(state, &args[1], locals)?;
    match (a.sort, b.sort) {
        (SmtSort::Bool, SmtSort::Bool) => Ok(Binding {
            node: state.builder.bool_eq(a.node, b.node)?,
            sort: SmtSort::Bool,
        }),
        (SmtSort::Bv(w1), SmtSort::Bv(w2)) if w1 == w2 => Ok(Binding {
            node: state.builder.bv_eq(a.node, b.node)?,
            sort: SmtSort::Bool,
        }),
        _ => Err(WireError::invalid("=", "argument sorts differ")),
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
                }
            }
            out
        }
        QueryStatus::Unsat => {
            let mut out = "unsat\n".to_owned();
            if query.want_core {
                if let Some(core) = result.core {
                    out.push_str(&format_core(&core));
                }
            }
            out
        }
        QueryStatus::Unknown => "unknown\n".to_owned(),
        QueryStatus::Ok => "success\n".to_owned(),
    }
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
    let tokens = tokenize(input)?;
    let mut parser = Parser { tokens, pos: 0 };
    let mut exprs = Vec::new();
    while parser.pos < parser.tokens.len() {
        exprs.push(parser.parse_expr()?);
    }
    Ok(exprs)
}

fn tokenize(input: &str) -> smt_wire::Result<Vec<String>> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            ';' => {
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '(' | ')' => tokens.push(ch.to_string()),
            c if c.is_whitespace() => {}
            '|' => {
                let mut atom = String::new();
                loop {
                    match chars.next() {
                        Some('|') => break,
                        Some('\\') => atom.push(chars.next().unwrap_or('\\')),
                        Some(c) => atom.push(c),
                        None => {
                            return Err(WireError::invalid(
                                "SMT-LIB token",
                                "unterminated quoted symbol",
                            ))
                        }
                    }
                }
                tokens.push(atom);
            }
            c => {
                let mut atom = c.to_string();
                while let Some(&next) = chars.peek() {
                    if next.is_whitespace() || next == '(' || next == ')' || next == ';' {
                        break;
                    }
                    atom.push(chars.next().expect("peeked char"));
                }
                tokens.push(atom);
            }
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<String>,
    pos: usize,
}

impl Parser {
    fn parse_expr(&mut self) -> smt_wire::Result<SExpr> {
        if self.pos >= self.tokens.len() {
            return Err(WireError::invalid(
                "SMT-LIB parser",
                "unexpected end of input",
            ));
        }
        let token = self.tokens[self.pos].clone();
        self.pos += 1;
        if token == "(" {
            let mut items = Vec::new();
            while self.pos < self.tokens.len() && self.tokens[self.pos] != ")" {
                items.push(self.parse_expr()?);
            }
            if self.pos == self.tokens.len() {
                return Err(WireError::invalid("SMT-LIB parser", "missing ')'"));
            }
            self.pos += 1;
            Ok(SExpr::List(items))
        } else if token == ")" {
            Err(WireError::invalid("SMT-LIB parser", "unexpected ')'"))
        } else {
            Ok(SExpr::Atom(token))
        }
    }
}
