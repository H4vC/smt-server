use smt_wire::{request_flags, tag, BinaryRequest, BlobRef, ExprView, NodeRef, Sort, WireError};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Smt2Variable {
    pub node_ref: NodeRef,
    pub name: String,
    pub sort: Sort,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Smt2Script {
    pub script: String,
    pub variables: Vec<Smt2Variable>,
}

pub fn request_to_smt2(request: &BinaryRequest) -> smt_wire::Result<Smt2Script> {
    let expr = request.expression_view()?;
    let variables = collect_variables(&expr)?;
    let mut out = String::new();
    out.push_str("(set-logic QF_BV)\n");
    if (request.envelope.flags & request_flags::WANT_CORE) != 0 {
        out.push_str("(set-option :produce-unsat-cores true)\n");
    }
    if (request.envelope.flags & request_flags::WANT_MODEL) != 0 {
        out.push_str("(set-option :produce-models true)\n");
    }
    for variable in &variables {
        out.push_str("(declare-fun ");
        out.push_str(&quote_symbol(&variable.name));
        out.push_str(" () ");
        out.push_str(&sort_to_smt2(variable.sort, variable.width));
        out.push_str(")\n");
    }

    let mut cache = vec![None; expr.node_count() as usize];
    for (index, root) in request.assertion_roots.iter().enumerate() {
        let term = term_ref(&expr, *root, &mut cache)?;
        if index < request.named_assertion_refs.len() {
            let name = expr.blob_str(request.named_assertion_refs[index], "named assertion")?;
            out.push_str("(assert (! ");
            out.push_str(&term);
            out.push_str(" :named ");
            out.push_str(&quote_symbol(name));
            out.push_str("))\n");
        } else {
            out.push_str("(assert ");
            out.push_str(&term);
            out.push_str(")\n");
        }
    }
    for root in &request.assumption_roots {
        let term = term_ref(&expr, *root, &mut cache)?;
        out.push_str("(assert ");
        out.push_str(&term);
        out.push_str(")\n");
    }
    out.push_str("(check-sat)\n");
    if (request.envelope.flags & request_flags::WANT_MODEL) != 0 && !variables.is_empty() {
        out.push_str("(get-value (");
        for variable in &variables {
            out.push(' ');
            out.push_str(&quote_symbol(&variable.name));
        }
        out.push_str("))\n");
    }
    if (request.envelope.flags & request_flags::WANT_CORE) != 0 {
        out.push_str("(get-unsat-core)\n");
    }
    Ok(Smt2Script {
        script: out,
        variables,
    })
}

pub fn collect_variables(expr: &ExprView<'_>) -> smt_wire::Result<Vec<Smt2Variable>> {
    let mut vars = Vec::new();
    for index in 0..expr.node_count() {
        let node = expr.node(index)?;
        match node.tag {
            tag::BV_VAR => vars.push(Smt2Variable {
                node_ref: NodeRef::bv(index)?,
                name: expr
                    .blob_str(BlobRef::from_payload(node.payload), "BV variable")?
                    .to_owned(),
                sort: Sort::Bv,
                width: node.width,
            }),
            tag::BOOL_VAR => vars.push(Smt2Variable {
                node_ref: NodeRef::bool(index)?,
                name: expr
                    .blob_str(BlobRef::from_payload(node.payload), "Bool variable")?
                    .to_owned(),
                sort: Sort::Bool,
                width: 0,
            }),
            _ => {}
        }
    }
    Ok(vars)
}

pub fn quote_symbol(symbol: &str) -> String {
    if !symbol.is_empty()
        && symbol.chars().all(|c| {
            c.is_ascii_alphanumeric()
                || matches!(
                    c,
                    '_' | '-'
                        | '.'
                        | '$'
                        | '/'
                        | ':'
                        | '+'
                        | '*'
                        | '='
                        | '<'
                        | '>'
                        | '?'
                        | '!'
                        | '~'
                        | '&'
                        | '^'
                        | '%'
                        | '@'
                )
        })
        && !symbol.chars().next().unwrap().is_ascii_digit()
        && !matches!(
            symbol,
            "true" | "false" | "Bool" | "let" | "assert" | "check-sat"
        )
    {
        symbol.to_owned()
    } else {
        let escaped = symbol.replace('\\', "\\\\").replace('|', "\\|");
        format!("|{escaped}|")
    }
}

pub fn sort_to_smt2(sort: Sort, width: u32) -> String {
    match sort {
        Sort::Bool => "Bool".to_owned(),
        Sort::Bv => format!("(_ BitVec {width})"),
    }
}

fn term_ref(
    expr: &ExprView<'_>,
    reference: NodeRef,
    cache: &mut [Option<String>],
) -> smt_wire::Result<String> {
    let term = term_node(expr, reference.index(), cache)?;
    Ok(term)
}

fn term_node(
    expr: &ExprView<'_>,
    index: u32,
    cache: &mut [Option<String>],
) -> smt_wire::Result<String> {
    if let Some(term) = &cache[index as usize] {
        return Ok(term.clone());
    }
    let node = expr.node(index)?;
    let term = match node.tag {
        tag::BV_VAR | tag::BOOL_VAR => {
            quote_symbol(expr.blob_str(BlobRef::from_payload(node.payload), "variable name")?)
        }
        tag::BV_CONST => const_to_smt2(expr, node.width, node.payload)?,
        tag::BOOL_TRUE => "true".to_owned(),
        tag::BOOL_FALSE => "false".to_owned(),
        tag::BV_NOT => unary(expr, node.children, cache, "bvnot")?,
        tag::BV_NEG => unary(expr, node.children, cache, "bvneg")?,
        tag::BV_AND => binary(expr, node.children, cache, "bvand")?,
        tag::BV_OR => binary(expr, node.children, cache, "bvor")?,
        tag::BV_XOR => binary(expr, node.children, cache, "bvxor")?,
        tag::BV_ADD => binary(expr, node.children, cache, "bvadd")?,
        tag::BV_SUB => binary(expr, node.children, cache, "bvsub")?,
        tag::BV_MUL => binary(expr, node.children, cache, "bvmul")?,
        tag::BV_UDIV => binary(expr, node.children, cache, "bvudiv")?,
        tag::BV_UREM => binary(expr, node.children, cache, "bvurem")?,
        tag::BV_SDIV => binary(expr, node.children, cache, "bvsdiv")?,
        tag::BV_SREM => binary(expr, node.children, cache, "bvsrem")?,
        tag::BV_SMOD => binary(expr, node.children, cache, "bvsmod")?,
        tag::BV_SHL => binary(expr, node.children, cache, "bvshl")?,
        tag::BV_LSHR => binary(expr, node.children, cache, "bvlshr")?,
        tag::BV_ASHR => binary(expr, node.children, cache, "bvashr")?,
        tag::BV_EXTRACT => {
            let child = child_term(expr, node.children, cache)?;
            format!("((_ extract {} {}) {child})", node.aux_hi, node.aux_lo)
        }
        tag::BV_CONCAT => binary(expr, node.children, cache, "concat")?,
        tag::BV_ZEXT => {
            let child = child_term(expr, node.children, cache)?;
            format!("((_ zero_extend {}) {child})", node.aux_hi)
        }
        tag::BV_SEXT => {
            let child = child_term(expr, node.children, cache)?;
            format!("((_ sign_extend {}) {child})", node.aux_hi)
        }
        tag::BV_ITE => {
            let c = child_term(expr, node.children, cache)?;
            let t = child_term(expr, node.children + 1, cache)?;
            let e = child_term(expr, node.children + 2, cache)?;
            format!("(ite {c} {t} {e})")
        }
        tag::BV_SELECT => {
            let pairs = u32::from(node.aux_hi);
            let mut result = child_term(expr, node.children + pairs * 2, cache)?;
            for pair in (0..pairs).rev() {
                let selector = child_term(expr, node.children + pair * 2, cache)?;
                let value = child_term(expr, node.children + pair * 2 + 1, cache)?;
                result = format!("(ite {selector} {value} {result})");
            }
            result
        }
        tag::BOOL_NOT => unary(expr, node.children, cache, "not")?,
        tag::BOOL_AND => binary(expr, node.children, cache, "and")?,
        tag::BOOL_OR => binary(expr, node.children, cache, "or")?,
        tag::BOOL_IMPLIES => binary(expr, node.children, cache, "=>")?,
        tag::BV_EQ => binary(expr, node.children, cache, "=")?,
        tag::BV_ULT => binary(expr, node.children, cache, "bvult")?,
        tag::BV_ULE => binary(expr, node.children, cache, "bvule")?,
        tag::BV_SLT => binary(expr, node.children, cache, "bvslt")?,
        tag::BV_SLE => binary(expr, node.children, cache, "bvsle")?,
        tag::UADD_OVF => {
            let a = child_term(expr, node.children, cache)?;
            let b = child_term(expr, node.children + 1, cache)?;
            format!("(bvult (bvadd {a} {b}) {a})")
        }
        tag::USUB_OVF => binary(expr, node.children, cache, "bvult")?,
        tag::UMUL_OVF => {
            let a_ref = expr.child_ref(node.children)?;
            let width = expr.node(a_ref.index())?.width;
            let a = child_term(expr, node.children, cache)?;
            let b = child_term(expr, node.children + 1, cache)?;
            let product =
                format!("(bvmul ((_ zero_extend {width}) {a}) ((_ zero_extend {width}) {b}))");
            format!(
                "(not (= ((_ extract {} {}) {product}) {}))",
                width * 2 - 1,
                width,
                zero_bv(width)
            )
        }
        tag::SADD_OVF => signed_add_overflow(expr, node.children, cache)?,
        tag::SSUB_OVF => signed_sub_overflow(expr, node.children, cache)?,
        tag::SMUL_OVF => signed_mul_overflow(expr, node.children, cache)?,
        tag::NEG_OVF => {
            let a_ref = expr.child_ref(node.children)?;
            let width = expr.node(a_ref.index())?.width;
            let a = child_term(expr, node.children, cache)?;
            format!("(= {a} {})", signed_min_bv(width))
        }
        tag::SDIV_OVF => {
            let a_ref = expr.child_ref(node.children)?;
            let width = expr.node(a_ref.index())?.width;
            let a = child_term(expr, node.children, cache)?;
            let b = child_term(expr, node.children + 1, cache)?;
            format!(
                "(and (= {a} {}) (= {b} {}))",
                signed_min_bv(width),
                ones_bv(width)
            )
        }
        other => {
            return Err(WireError::invalid(
                "SMT-LIB translation",
                format!("unknown tag {other}"),
            ))
        }
    };
    cache[index as usize] = Some(term.clone());
    Ok(term)
}

fn child_term(
    expr: &ExprView<'_>,
    child_index: u32,
    cache: &mut [Option<String>],
) -> smt_wire::Result<String> {
    term_ref(expr, expr.child_ref(child_index)?, cache)
}

fn unary(
    expr: &ExprView<'_>,
    child_index: u32,
    cache: &mut [Option<String>],
    op: &str,
) -> smt_wire::Result<String> {
    let child = child_term(expr, child_index, cache)?;
    Ok(format!("({op} {child})"))
}

fn binary(
    expr: &ExprView<'_>,
    child_index: u32,
    cache: &mut [Option<String>],
    op: &str,
) -> smt_wire::Result<String> {
    let a = child_term(expr, child_index, cache)?;
    let b = child_term(expr, child_index + 1, cache)?;
    Ok(format!("({op} {a} {b})"))
}

fn const_to_smt2(expr: &ExprView<'_>, width: u32, payload: u64) -> smt_wire::Result<String> {
    let mut bytes = if width <= 64 {
        let mut raw = payload.to_le_bytes().to_vec();
        raw.truncate((width as usize).div_ceil(8));
        raw
    } else {
        expr.blob_ref(BlobRef::from_payload(payload))?.to_vec()
    };
    let valid = width % 8;
    if valid != 0 && !bytes.is_empty() {
        let last = bytes.len() - 1;
        bytes[last] &= (1 << valid) - 1;
    }
    let mut bits = String::with_capacity(width as usize + 2);
    bits.push_str("#b");
    for bit in (0..width).rev() {
        let byte = bytes[(bit / 8) as usize];
        bits.push(if ((byte >> (bit % 8)) & 1) == 1 {
            '1'
        } else {
            '0'
        });
    }
    Ok(bits)
}

fn signed_add_overflow(
    expr: &ExprView<'_>,
    child_index: u32,
    cache: &mut [Option<String>],
) -> smt_wire::Result<String> {
    let a_ref = expr.child_ref(child_index)?;
    let width = expr.node(a_ref.index())?.width;
    let a = child_term(expr, child_index, cache)?;
    let b = child_term(expr, child_index + 1, cache)?;
    let sum = format!("(bvadd {a} {b})");
    Ok(format!(
        "(or (and (= {} #b0) (= {} #b0) (= {} #b1)) (and (= {} #b1) (= {} #b1) (= {} #b0)))",
        sign(&a, width),
        sign(&b, width),
        sign(&sum, width),
        sign(&a, width),
        sign(&b, width),
        sign(&sum, width)
    ))
}

fn signed_sub_overflow(
    expr: &ExprView<'_>,
    child_index: u32,
    cache: &mut [Option<String>],
) -> smt_wire::Result<String> {
    let a_ref = expr.child_ref(child_index)?;
    let width = expr.node(a_ref.index())?.width;
    let a = child_term(expr, child_index, cache)?;
    let b = child_term(expr, child_index + 1, cache)?;
    let diff = format!("(bvsub {a} {b})");
    Ok(format!(
        "(or (and (= {} #b0) (= {} #b1) (= {} #b1)) (and (= {} #b1) (= {} #b0) (= {} #b0)))",
        sign(&a, width),
        sign(&b, width),
        sign(&diff, width),
        sign(&a, width),
        sign(&b, width),
        sign(&diff, width)
    ))
}

fn signed_mul_overflow(
    expr: &ExprView<'_>,
    child_index: u32,
    cache: &mut [Option<String>],
) -> smt_wire::Result<String> {
    let a_ref = expr.child_ref(child_index)?;
    let width = expr.node(a_ref.index())?.width;
    let a = child_term(expr, child_index, cache)?;
    let b = child_term(expr, child_index + 1, cache)?;
    let product = format!("(bvmul ((_ sign_extend {width}) {a}) ((_ sign_extend {width}) {b}))");
    let low = format!("((_ extract {} 0) {product})", width - 1);
    Ok(format!(
        "(not (= {product} ((_ sign_extend {width}) {low})))"
    ))
}

fn sign(term: &str, width: u32) -> String {
    format!("((_ extract {} {}) {term})", width - 1, width - 1)
}

fn zero_bv(width: u32) -> String {
    format!("#b{}", "0".repeat(width as usize))
}

fn ones_bv(width: u32) -> String {
    format!("#b{}", "1".repeat(width as usize))
}

fn signed_min_bv(width: u32) -> String {
    let mut bits = String::with_capacity(width as usize + 2);
    bits.push_str("#b1");
    bits.push_str(&"0".repeat(width.saturating_sub(1) as usize));
    bits
}
