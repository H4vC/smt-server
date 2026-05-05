use std::collections::HashMap;

use dashu::{float::DBig, integer::UBig};
use yaspar::{
    action::{
        ActionOnAttribute, ActionOnConstant, ActionOnIdentifier, ActionOnIndex, ActionOnSort,
        ActionOnString, ActionOnTerm, ParsingAction, ParsingResult, Pattern,
    },
    ast::{DatatypeDec, DatatypeDef, FunctionDef, Keyword},
    position::Range,
};

use crate::builder::Builder;
use crate::error::{Error, Result};
use crate::ir::TermId;
use crate::model::{scalar_to_smt, Model, ScalarValue};
use crate::query::Query;
use crate::solver::{SolveResult, SolveStatus};
use crate::{Config, Solver};

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
    node: TermId,
    sort: SmtSort,
}

#[derive(Debug, Default)]
struct ScriptState {
    builder: Builder,
    env: HashMap<String, Binding>,
    saw_check_sat: bool,
}

pub fn parse_smt2(script: &str) -> Result<Query> {
    let exprs = parse_sexprs(script)?;
    let mut state = ScriptState::default();
    for expr in exprs {
        let list = match expr {
            SExpr::List(list) => list,
            SExpr::Atom(atom) => {
                return Err(Error::invalid(
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
                if list.len() == 2 {
                    let logic = atom(&list[1])?;
                    if logic != "QF_BV" && logic != "ALL" {
                        return Err(Error::invalid("set-logic", "only QF_BV is supported"));
                    }
                }
            }
            "set-option" | "set-info" | "echo" | "exit" => {}
            "push" => push_command(&mut state, &list)?,
            "pop" => pop_command(&mut state, &list)?,
            "reset" | "reset-assertions" => {
                return Err(Error::unsupported(format!(
                    "command {cmd} is not supported by parse_smt2"
                )))
            }
            "declare-const" => declare_const(&mut state, &list)?,
            "declare-fun" => declare_fun(&mut state, &list)?,
            "define-const" => define_const(&mut state, &list)?,
            "define-fun" => define_fun(&mut state, &list)?,
            "assert" => assert_command(&mut state, &list)?,
            "check-sat" => state.saw_check_sat = true,
            "check-sat-assuming" => check_sat_assuming(&mut state, &list)?,
            "get-model" => state.builder.set_want_model(true),
            "get-value" => get_value_command(&mut state, &list)?,
            "get-unsat-core" => state.builder.set_want_core(true),
            other => return Err(Error::unsupported(format!("SMT-LIB command {other}"))),
        }
    }
    if !state.saw_check_sat {
        return Err(Error::invalid(
            "SMT-LIB script",
            "script does not contain check-sat",
        ));
    }
    state.builder.finish()
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
                }
            }
            out
        }
        SolveStatus::Unknown => "unknown\n".to_owned(),
        SolveStatus::Ok => "success\n".to_owned(),
    }
}

fn declare_const(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 3 {
        return Err(Error::invalid("declare-const", "expected name and sort"));
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

fn declare_fun(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 4 {
        return Err(Error::invalid("declare-fun", "expected name, args, sort"));
    }
    match &list[2] {
        SExpr::List(args) if args.is_empty() => {}
        _ => return Err(Error::unsupported("only 0-arity declare-fun is supported")),
    }
    declare_const(state, &[list[0].clone(), list[1].clone(), list[3].clone()])
}

fn define_const(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 4 {
        return Err(Error::invalid("define-const", "expected name, sort, value"));
    }
    let name = atom(&list[1])?.to_owned();
    let declared = parse_sort(&list[2])?;
    let binding = parse_expr_with_locals(state, &list[3], &mut HashMap::new())?;
    expect_sort(binding.sort, declared, "define-const")?;
    state.env.insert(name, binding);
    Ok(())
}

fn define_fun(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 5 {
        return Err(Error::invalid(
            "define-fun",
            "expected name, args, sort, body",
        ));
    }
    match &list[2] {
        SExpr::List(args) if args.is_empty() => {}
        _ => return Err(Error::unsupported("only 0-arity define-fun is supported")),
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

fn push_command(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    let levels = command_level(list, "push")?;
    for _ in 0..levels {
        state.builder.push();
    }
    Ok(())
}

fn pop_command(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    let levels = command_level(list, "pop")?;
    for _ in 0..levels {
        state.builder.pop()?;
    }
    Ok(())
}

fn command_level(list: &[SExpr], context: &'static str) -> Result<u32> {
    if list.len() == 1 {
        return Ok(1);
    }
    if list.len() != 2 {
        return Err(Error::invalid(context, "expected optional level"));
    }
    parse_u32_atom(&list[1], context)
}

fn assert_command(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 2 {
        return Err(Error::invalid("assert", "expected one expression"));
    }
    if let Some((inner, name)) = named_annotation(&list[1])? {
        let binding = parse_expr_with_locals(state, inner, &mut HashMap::new())?;
        expect_sort(binding.sort, SmtSort::Bool, "assert")?;
        state.builder.assert_named(name, binding.node)
    } else {
        let binding = parse_expr_with_locals(state, &list[1], &mut HashMap::new())?;
        expect_sort(binding.sort, SmtSort::Bool, "assert")?;
        state.builder.assert(binding.node)
    }
}

fn check_sat_assuming(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 2 {
        return Err(Error::invalid(
            "check-sat-assuming",
            "expected assumption list",
        ));
    }
    let assumptions = match &list[1] {
        SExpr::List(items) => items,
        _ => return Err(Error::invalid("check-sat-assuming", "expected list")),
    };
    for item in assumptions {
        let binding = parse_expr_with_locals(state, item, &mut HashMap::new())?;
        expect_sort(binding.sort, SmtSort::Bool, "check-sat-assuming")?;
        state.builder.assume(binding.node)?;
    }
    state.saw_check_sat = true;
    Ok(())
}

fn get_value_command(state: &mut ScriptState, list: &[SExpr]) -> Result<()> {
    if list.len() != 2 {
        return Err(Error::invalid("get-value", "expected one term list"));
    }
    let terms = match &list[1] {
        SExpr::List(items) => items,
        _ => return Err(Error::invalid("get-value", "expected term list")),
    };
    for term in terms {
        match term {
            SExpr::Atom(name) => state.builder.add_get_value(name.clone()),
            _ => {
                return Err(Error::unsupported(
                    "get-value currently supports declared symbols",
                ))
            }
        }
    }
    Ok(())
}

fn named_annotation(expr: &SExpr) -> Result<Option<(&SExpr, String)>> {
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
) -> Result<Binding> {
    match expr {
        SExpr::Atom(atom) => parse_atom_expr(state, atom, locals),
        SExpr::List(items) => parse_list_expr(state, items, locals),
    }
}

fn parse_atom_expr(
    state: &mut ScriptState,
    value: &str,
    locals: &HashMap<String, Binding>,
) -> Result<Binding> {
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
        return Ok(Binding {
            node: state.builder.bv_const_bytes(&bytes, width)?,
            sort: SmtSort::Bv(width),
        });
    }
    locals
        .get(value)
        .or_else(|| state.env.get(value))
        .cloned()
        .ok_or_else(|| Error::invalid("SMT-LIB symbol", format!("undefined symbol {value:?}")))
}

fn parse_list_expr(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> Result<Binding> {
    if items.is_empty() {
        return Err(Error::invalid("SMT-LIB expression", "empty list"));
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
        "ite" => parse_ite(state, items, locals),
        "=" => parse_equals(state, &items[1..], locals),
        "distinct" => parse_distinct(state, &items[1..], locals),
        "not" => unary_bool(state, items, locals, |b, x| b.bool_not(x)),
        "and" => fold_bool(state, &items[1..], locals, true, |b, a, c| b.bool_and(a, c)),
        "or" => fold_bool(state, &items[1..], locals, false, |b, a, c| b.bool_or(a, c)),
        "=>" => binary_bool(state, items, locals, |b, a, c| b.bool_implies(a, c)),
        "xor" => binary_bool(state, items, locals, |b, a, c| b.bool_xor(a, c)),
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
        "concat" => concat_bv(state, items, locals),
        "bvult" => bv_cmp(state, items, locals, |b, a, c| b.bv_ult(a, c)),
        "bvule" => bv_cmp(state, items, locals, |b, a, c| b.bv_ule(a, c)),
        "bvugt" => bv_cmp(state, items, locals, |b, a, c| b.bv_ugt(a, c)),
        "bvuge" => bv_cmp(state, items, locals, |b, a, c| b.bv_uge(a, c)),
        "bvslt" => bv_cmp(state, items, locals, |b, a, c| b.bv_slt(a, c)),
        "bvsle" => bv_cmp(state, items, locals, |b, a, c| b.bv_sle(a, c)),
        "bvsgt" => bv_cmp(state, items, locals, |b, a, c| b.bv_sgt(a, c)),
        "bvsge" => bv_cmp(state, items, locals, |b, a, c| b.bv_sge(a, c)),
        "bvuaddo" | "uaddo" => overflow_cmp(state, items, locals, |b, a, c| b.uadd_ovf(a, c)),
        "bvsaddo" | "saddo" => overflow_cmp(state, items, locals, |b, a, c| b.sadd_ovf(a, c)),
        "bvusubo" | "usubo" => overflow_cmp(state, items, locals, |b, a, c| b.usub_ovf(a, c)),
        "bvssubo" | "ssubo" => overflow_cmp(state, items, locals, |b, a, c| b.ssub_ovf(a, c)),
        "bvumulo" | "umulo" => overflow_cmp(state, items, locals, |b, a, c| b.umul_ovf(a, c)),
        "bvsmulo" | "smulo" => overflow_cmp(state, items, locals, |b, a, c| b.smul_ovf(a, c)),
        "bvsdivo" | "sdivo" => overflow_cmp(state, items, locals, |b, a, c| b.sdiv_ovf(a, c)),
        "bvnego" | "nego" => unary_overflow(state, items, locals, |b, x| b.neg_ovf(x)),
        other => Err(Error::unsupported(format!("SMT-LIB operator {other}"))),
    }
}

fn parse_ite(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> Result<Binding> {
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
        _ => Err(Error::invalid("ite", "branch sorts differ")),
    }
}

fn parse_indexed_literal(state: &mut ScriptState, items: &[SExpr]) -> Result<Binding> {
    let (value, width) = if items.len() == 3 {
        let bv_atom = atom(&items[1])?;
        let value = bv_atom
            .strip_prefix("bv")
            .ok_or_else(|| Error::invalid("indexed literal", "expected (_ bvN W)"))?;
        let width = atom(&items[2])?
            .parse::<u32>()
            .map_err(|_| Error::invalid("bv literal", "invalid width"))?;
        (value, width)
    } else if items.len() == 4 && atom(&items[1])? == "bv" {
        let value = atom(&items[2])?;
        let width = atom(&items[3])?
            .parse::<u32>()
            .map_err(|_| Error::invalid("bv literal", "invalid width"))?;
        (value, width)
    } else {
        return Err(Error::invalid("indexed literal", "expected (_ bvN W)"));
    };
    let bytes = decimal_to_le_bytes(value, (width as usize).div_ceil(8))?;
    Ok(Binding {
        node: state.builder.bv_const_bytes(&bytes, width)?,
        sort: SmtSort::Bv(width),
    })
}

fn parse_indexed_op(
    state: &mut ScriptState,
    op_items: &[SExpr],
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> Result<Binding> {
    if op_items.len() == 4 && atom(&op_items[0])? == "_" && atom(&op_items[1])? == "extract" {
        if args.len() != 1 {
            return Err(Error::invalid("extract", "expected one argument"));
        }
        let hi = parse_u32_atom(&op_items[2], "extract high")?;
        let lo = parse_u32_atom(&op_items[3], "extract low")?;
        let x = parse_expr_with_locals(state, &args[0], locals)?;
        let SmtSort::Bv(_) = x.sort else {
            return Err(Error::invalid("extract", "argument is not BV"));
        };
        return Ok(Binding {
            node: state.builder.bv_extract(x.node, hi, lo)?,
            sort: SmtSort::Bv(hi - lo + 1),
        });
    }
    if op_items.len() == 3 && atom(&op_items[0])? == "_" {
        let amount = parse_u32_atom(&op_items[2], "indexed amount")?;
        if args.len() != 1 {
            return Err(Error::invalid("indexed operator", "expected one argument"));
        }
        let x = parse_expr_with_locals(state, &args[0], locals)?;
        let SmtSort::Bv(width) = x.sort else {
            return Err(Error::invalid("indexed operator", "argument is not BV"));
        };
        return match atom(&op_items[1])? {
            "zero_extend" => Ok(Binding {
                node: state.builder.bv_zext(x.node, amount)?,
                sort: SmtSort::Bv(width + amount),
            }),
            "sign_extend" => Ok(Binding {
                node: state.builder.bv_sext(x.node, amount)?,
                sort: SmtSort::Bv(width + amount),
            }),
            "repeat" => Ok(Binding {
                node: state.builder.bv_repeat(x.node, amount)?,
                sort: SmtSort::Bv(width * amount),
            }),
            "rotate_left" => Ok(Binding {
                node: state.builder.bv_rotate_left(x.node, amount)?,
                sort: SmtSort::Bv(width),
            }),
            "rotate_right" => Ok(Binding {
                node: state.builder.bv_rotate_right(x.node, amount)?,
                sort: SmtSort::Bv(width),
            }),
            _ => Err(Error::unsupported("indexed operator")),
        };
    }
    Err(Error::unsupported("indexed operator"))
}

fn parse_let(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> Result<Binding> {
    expect_len(items, 3, "let")?;
    let bindings = match &items[1] {
        SExpr::List(items) => items,
        _ => return Err(Error::invalid("let", "expected binding list")),
    };
    let mut nested = locals.clone();
    for binding in bindings {
        let pair = match binding {
            SExpr::List(pair) if pair.len() == 2 => pair,
            _ => return Err(Error::invalid("let", "bad binding")),
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
) -> Result<Binding> {
    if args.len() != 2 {
        return Err(Error::invalid("=", "expected two arguments"));
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
        _ => Err(Error::invalid("=", "argument sorts differ")),
    }
}

fn parse_distinct(
    state: &mut ScriptState,
    args: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> Result<Binding> {
    if args.len() != 2 {
        return Err(Error::unsupported(
            "distinct currently supports exactly two arguments",
        ));
    }
    let eq = parse_equals(state, args, locals)?;
    Ok(Binding {
        node: state.builder.bool_not(eq.node)?,
        sort: SmtSort::Bool,
    })
}

fn unary_bool(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut Builder, TermId) -> Result<TermId>,
) -> Result<Binding> {
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
    f: fn(&mut Builder, TermId, TermId) -> Result<TermId>,
) -> Result<Binding> {
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
    f: fn(&mut Builder, TermId, TermId) -> Result<TermId>,
) -> Result<Binding> {
    if args.is_empty() {
        let node = state.builder.bool_const(identity)?;
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
    f: fn(&mut Builder, TermId) -> Result<TermId>,
) -> Result<Binding> {
    expect_len(items, 2, "unary BV")?;
    let x = parse_expr_with_locals(state, &items[1], locals)?;
    let SmtSort::Bv(width) = x.sort else {
        return Err(Error::invalid("unary BV", "argument is not BV"));
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
    f: fn(&mut Builder, TermId, TermId) -> Result<TermId>,
) -> Result<Binding> {
    expect_len(items, 3, "binary BV")?;
    let a = parse_expr_with_locals(state, &items[1], locals)?;
    let b = parse_expr_with_locals(state, &items[2], locals)?;
    let (SmtSort::Bv(w1), SmtSort::Bv(w2)) = (a.sort, b.sort) else {
        return Err(Error::invalid("binary BV", "argument is not BV"));
    };
    if w1 != w2 {
        return Err(Error::invalid("binary BV", "width mismatch"));
    }
    Ok(Binding {
        node: f(&mut state.builder, a.node, b.node)?,
        sort: SmtSort::Bv(w1),
    })
}

fn concat_bv(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
) -> Result<Binding> {
    expect_len(items, 3, "concat")?;
    let a = parse_expr_with_locals(state, &items[1], locals)?;
    let b = parse_expr_with_locals(state, &items[2], locals)?;
    let (SmtSort::Bv(w1), SmtSort::Bv(w2)) = (a.sort, b.sort) else {
        return Err(Error::invalid("concat", "argument is not BV"));
    };
    Ok(Binding {
        node: state.builder.bv_concat(a.node, b.node)?,
        sort: SmtSort::Bv(w1 + w2),
    })
}

fn bv_cmp(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut Builder, TermId, TermId) -> Result<TermId>,
) -> Result<Binding> {
    let value = binary_bv(state, items, locals, f)?;
    Ok(Binding {
        node: value.node,
        sort: SmtSort::Bool,
    })
}

fn overflow_cmp(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut Builder, TermId, TermId) -> Result<TermId>,
) -> Result<Binding> {
    bv_cmp(state, items, locals, f)
}

fn unary_overflow(
    state: &mut ScriptState,
    items: &[SExpr],
    locals: &mut HashMap<String, Binding>,
    f: fn(&mut Builder, TermId) -> Result<TermId>,
) -> Result<Binding> {
    let value = unary_bv(state, items, locals, f)?;
    Ok(Binding {
        node: value.node,
        sort: SmtSort::Bool,
    })
}

fn parse_sort(expr: &SExpr) -> Result<SmtSort> {
    match expr {
        SExpr::Atom(atom) if atom == "Bool" => Ok(SmtSort::Bool),
        SExpr::List(items)
            if items.len() == 3 && atom(&items[0])? == "_" && atom(&items[1])? == "BitVec" =>
        {
            let width = atom(&items[2])?
                .parse::<u32>()
                .map_err(|_| Error::invalid("sort", "invalid BitVec width"))?;
            Ok(SmtSort::Bv(width))
        }
        _ => Err(Error::invalid("sort", "expected Bool or (_ BitVec n)")),
    }
}

fn decimal_to_le_bytes(text: &str, len: usize) -> Result<Vec<u8>> {
    let mut digits = text
        .bytes()
        .map(|byte| match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            _ => Err(Error::invalid("bv literal", "invalid decimal value")),
        })
        .collect::<Result<Vec<_>>>()?;
    let mut out = Vec::with_capacity(len);
    while !digits.is_empty() && out.len() < len {
        let mut carry = 0u16;
        let mut quotient = Vec::new();
        for digit in digits {
            let n = carry * 10 + u16::from(digit);
            let q = (n / 256) as u8;
            carry = n % 256;
            if !quotient.is_empty() || q != 0 {
                quotient.push(q);
            }
        }
        out.push(carry as u8);
        digits = quotient;
    }
    out.resize(len, 0);
    Ok(out)
}

fn literal_bytes(digits: &str, radix: u32, width: u32, original: &str) -> Result<Vec<u8>> {
    let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
    match radix {
        2 => {
            for (offset, ch) in digits.chars().rev().enumerate() {
                match ch {
                    '0' => {}
                    '1' => bytes[offset / 8] |= 1 << (offset % 8),
                    _ => {
                        return Err(Error::invalid(
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
                    Error::invalid(
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

fn expect_len(items: &[SExpr], len: usize, context: &'static str) -> Result<()> {
    if items.len() != len {
        return Err(Error::invalid(context, format!("expected {len} items")));
    }
    Ok(())
}

fn expect_sort(actual: SmtSort, expected: SmtSort, context: &'static str) -> Result<()> {
    if actual != expected {
        return Err(Error::invalid(
            context,
            format!("expected {expected:?}, got {actual:?}"),
        ));
    }
    Ok(())
}

fn atom(expr: &SExpr) -> Result<&str> {
    match expr {
        SExpr::Atom(atom) => Ok(atom),
        SExpr::List(_) => Err(Error::invalid("SMT-LIB atom", "expected atom")),
    }
}

fn parse_u32_atom(expr: &SExpr, context: &'static str) -> Result<u32> {
    atom(expr)?
        .parse::<u32>()
        .map_err(|_| Error::invalid(context, "expected u32 numeral"))
}

fn parse_sexprs(input: &str) -> Result<Vec<SExpr>> {
    let mut action = SExprAction;
    yaspar::smtlib2::ScriptParser::new()
        .parse(&mut action, yaspar::tokenize_str(input, true))
        .map_err(|err| Error::parse(err.to_string()))
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
