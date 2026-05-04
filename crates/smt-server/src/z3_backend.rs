use smt_wire::{
    request_flags, tag, BinaryRequest, BlobRef, Command, ModelBlock, ModelEntry, NodeRef,
    OptimizationValueBlock, ScalarValue, SimplifyBlock, Sort, UnsatCoreBlock, WireError,
};
use z3::{
    ast::{Bool, BV},
    Config, Model, SatResult, Solver,
};

use crate::backend::{Backend, QueryResult};

#[derive(Debug, Clone, Default)]
pub struct Z3Backend;

impl Backend for Z3Backend {
    fn name(&self) -> &'static str {
        "z3"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        match request.envelope.command {
            Command::Simplify => Ok(QueryResult::ok_simplify(SimplifyBlock {
                expression: request.expression.clone(),
                assertion_roots: request.assertion_roots.clone(),
                named_assertion_refs: request.named_assertion_refs.clone(),
                assumption_roots: request.assumption_roots.clone(),
            })),
            Command::Solve | Command::Minimize | Command::Maximize => {
                let mut cfg = Config::new();
                cfg.set_model_generation(true);
                if request.envelope.budget_ms != 0 {
                    cfg.set_timeout_msec(u64::from(request.envelope.budget_ms));
                }
                z3::with_z3_config(&cfg, || match request.envelope.command {
                    Command::Solve => solve(request),
                    Command::Minimize | Command::Maximize => optimize(request),
                    Command::Simplify => unreachable!("handled above"),
                })
            }
        }
    }
}

#[derive(Clone)]
struct Z3Variable {
    node_ref: NodeRef,
    sort: Sort,
    width: u32,
}

struct Z3Translation {
    bvs: Vec<Option<BV>>,
    bools: Vec<Option<Bool>>,
    variables: Vec<Z3Variable>,
}

impl Z3Translation {
    fn bv(&self, reference: NodeRef) -> smt_wire::Result<BV> {
        if !reference.is_bv() {
            return Err(WireError::invalid(
                "Z3 translation",
                "expected BV reference",
            ));
        }
        self.bvs
            .get(reference.index() as usize)
            .and_then(Clone::clone)
            .ok_or_else(|| WireError::invalid("Z3 translation", "missing BV term"))
    }

    fn bool(&self, reference: NodeRef) -> smt_wire::Result<Bool> {
        if !reference.is_bool() {
            return Err(WireError::invalid(
                "Z3 translation",
                "expected Bool reference",
            ));
        }
        self.bools
            .get(reference.index() as usize)
            .and_then(Clone::clone)
            .ok_or_else(|| WireError::invalid("Z3 translation", "missing Bool term"))
    }
}

fn translate(request: &BinaryRequest) -> smt_wire::Result<Z3Translation> {
    let expr = request.expression_view()?;
    let mut out = Z3Translation {
        bvs: vec![None; expr.node_count() as usize],
        bools: vec![None; expr.node_count() as usize],
        variables: Vec::new(),
    };

    for index in 0..expr.node_count() {
        let node = expr.node(index)?;
        match node.tag {
            tag::BV_VAR => {
                let name = format!("bv_{index}");
                let term = BV::new_const(name, node.width);
                out.variables.push(Z3Variable {
                    node_ref: NodeRef::bv(index)?,
                    sort: Sort::Bv,
                    width: node.width,
                });
                out.bvs[index as usize] = Some(term);
            }
            tag::BV_CONST => {
                out.bvs[index as usize] = Some(z3_bv_const(&expr, node.width, node.payload)?);
            }
            tag::BV_NOT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(x.bvnot());
            }
            tag::BV_NEG => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(x.bvneg());
            }
            tag::BV_AND => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvand(&b));
            }
            tag::BV_OR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvor(&b));
            }
            tag::BV_XOR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvxor(&b));
            }
            tag::BV_ADD => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvadd(&b));
            }
            tag::BV_SUB => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvsub(&b));
            }
            tag::BV_MUL => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvmul(&b));
            }
            tag::BV_UDIV => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvudiv(&b));
            }
            tag::BV_UREM => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvurem(&b));
            }
            tag::BV_SDIV => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvsdiv(&b));
            }
            tag::BV_SREM => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvsrem(&b));
            }
            tag::BV_SMOD => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvsmod(&b));
            }
            tag::BV_SHL => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvshl(&b));
            }
            tag::BV_LSHR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvlshr(&b));
            }
            tag::BV_ASHR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.bvashr(&b));
            }
            tag::BV_EXTRACT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(x.extract(u32::from(node.aux_hi), node.aux_lo));
            }
            tag::BV_CONCAT => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(a.concat(&b));
            }
            tag::BV_ZEXT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(x.zero_ext(u32::from(node.aux_hi)));
            }
            tag::BV_SEXT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(x.sign_ext(u32::from(node.aux_hi)));
            }
            tag::BV_ITE => {
                let c = child_bool(&expr, &out, &node, 0)?;
                let t = child_bv(&expr, &out, &node, 1)?;
                let e = child_bv(&expr, &out, &node, 2)?;
                out.bvs[index as usize] = Some(c.ite(&t, &e));
            }
            tag::BV_SELECT => {
                let pairs = u32::from(node.aux_hi);
                let mut result = child_bv(&expr, &out, &node, pairs * 2)?;
                for pair in (0..pairs).rev() {
                    let selector = child_bool(&expr, &out, &node, pair * 2)?;
                    let value = child_bv(&expr, &out, &node, pair * 2 + 1)?;
                    result = selector.ite(&value, &result);
                }
                out.bvs[index as usize] = Some(result);
            }
            tag::BOOL_TRUE => out.bools[index as usize] = Some(Bool::from_bool(true)),
            tag::BOOL_FALSE => out.bools[index as usize] = Some(Bool::from_bool(false)),
            tag::BOOL_VAR => {
                let name = format!("bool_{index}");
                let term = Bool::new_const(name);
                out.variables.push(Z3Variable {
                    node_ref: NodeRef::bool(index)?,
                    sort: Sort::Bool,
                    width: 0,
                });
                out.bools[index as usize] = Some(term);
            }
            tag::BOOL_NOT => {
                let x = child_bool(&expr, &out, &node, 0)?;
                out.bools[index as usize] = Some(x.not());
            }
            tag::BOOL_AND => {
                let (a, b) = child_bool2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(Bool::and(&[&a, &b]));
            }
            tag::BOOL_OR => {
                let (a, b) = child_bool2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(Bool::or(&[&a, &b]));
            }
            tag::BOOL_IMPLIES => {
                let (a, b) = child_bool2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.implies(&b));
            }
            tag::BV_EQ => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.eq(&b));
            }
            tag::BV_ULT => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.bvult(&b));
            }
            tag::BV_ULE => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.bvule(&b));
            }
            tag::BV_SLT => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.bvslt(&b));
            }
            tag::BV_SLE => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.bvsle(&b));
            }
            tag::UADD_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                let sum = a.bvadd(&b);
                out.bools[index as usize] = Some(sum.bvult(&a));
            }
            tag::USUB_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(a.bvult(&b));
            }
            tag::UMUL_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(unsigned_mul_overflow(&a, &b));
            }
            tag::SADD_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(signed_add_overflow(&a, &b));
            }
            tag::SSUB_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(signed_sub_overflow(&a, &b));
            }
            tag::SMUL_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(signed_mul_overflow(&a, &b));
            }
            tag::NEG_OVF => {
                let a = child_bv(&expr, &out, &node, 0)?;
                out.bools[index as usize] = Some(a.eq(signed_min_bv(a.get_size())));
            }
            tag::SDIV_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                let width = a.get_size();
                out.bools[index as usize] = Some(Bool::and(&[
                    &a.eq(signed_min_bv(width)),
                    &b.eq(ones_bv(width)),
                ]));
            }
            other => {
                return Err(WireError::invalid(
                    "Z3 translation",
                    format!("unknown tag {other}"),
                ))
            }
        }
    }
    Ok(out)
}

fn solve(request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
    let expr = request.expression_view()?;
    let translation = translate(request)?;
    let solver = Solver::new();
    let want_model = (request.envelope.flags & request_flags::WANT_MODEL) != 0;
    let want_core = (request.envelope.flags & request_flags::WANT_CORE) != 0;
    let mut trackers = Vec::<(String, Bool)>::new();

    for (index, root) in request.assertion_roots.iter().enumerate() {
        let assertion = translation.bool(*root)?;
        if want_core && index < request.named_assertion_refs.len() {
            let name = expr
                .blob_str(request.named_assertion_refs[index], "named assertion")?
                .to_owned();
            let tracker = Bool::new_const(format!("core_{index}"));
            solver.assert_and_track(assertion, &tracker);
            trackers.push((name, tracker));
        } else {
            solver.assert(&assertion);
        }
    }

    let assumptions = request
        .assumption_roots
        .iter()
        .map(|root| translation.bool(*root))
        .collect::<smt_wire::Result<Vec<_>>>()?;

    match solver.check_assumptions(&assumptions) {
        SatResult::Sat => {
            let model = if want_model {
                let model = solver.get_model().ok_or_else(|| {
                    WireError::invalid("Z3 model", "solver returned SAT without a model")
                })?;
                Some(build_model(&translation, &model)?)
            } else {
                None
            };
            Ok(QueryResult::sat(model))
        }
        SatResult::Unsat => {
            let core = if want_core {
                Some(build_core(&solver, &trackers))
            } else {
                None
            };
            Ok(QueryResult::unsat(core))
        }
        SatResult::Unknown => Ok(QueryResult::unknown(
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "z3 returned unknown".to_owned()),
        )),
    }
}

fn optimize(request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
    let translation = translate(request)?;
    let solver = Solver::new();
    for root in &request.assertion_roots {
        solver.assert(&translation.bool(*root)?);
    }

    let mut fixed = request
        .assumption_roots
        .iter()
        .map(|root| translation.bool(*root))
        .collect::<smt_wire::Result<Vec<_>>>()?;

    match solver.check_assumptions(&fixed) {
        SatResult::Sat => {}
        SatResult::Unsat => return Ok(QueryResult::unsat(None)),
        SatResult::Unknown => {
            return Ok(QueryResult::unknown(
                solver
                    .get_reason_unknown()
                    .unwrap_or_else(|| "z3 returned unknown".to_owned()),
            ))
        }
    }

    let target_ref = request
        .target_ref()
        .ok_or_else(|| WireError::invalid("optimization", "missing target"))?;
    let target = translation.bv(target_ref)?;
    let width = target.get_size();
    let signed = (request.envelope.flags & request_flags::SIGNED) != 0;
    let minimize = request.envelope.command == Command::Minimize;
    let mut optimum = vec![0u8; (width as usize).div_ceil(8)];

    for bit in (0..width).rev() {
        let prefer_one = match (signed, minimize, bit == width - 1) {
            (false, true, _) => false,
            (false, false, _) => true,
            (true, true, true) => true,
            (true, true, false) => false,
            (true, false, true) => false,
            (true, false, false) => true,
        };
        let bit_is_one = target.extract(bit, bit).eq(BV::from_u64(1, 1));
        let first_try = if prefer_one {
            bit_is_one.clone()
        } else {
            bit_is_one.not()
        };
        let mut assumptions = fixed.clone();
        assumptions.push(first_try.clone());
        match solver.check_assumptions(&assumptions) {
            SatResult::Sat => {
                fixed.push(first_try);
                if prefer_one {
                    set_bit(&mut optimum, bit);
                }
            }
            SatResult::Unsat => {
                fixed.push(if prefer_one {
                    bit_is_one.not()
                } else {
                    bit_is_one
                });
                if !prefer_one {
                    set_bit(&mut optimum, bit);
                }
            }
            SatResult::Unknown => {
                return Ok(QueryResult::unknown(
                    solver
                        .get_reason_unknown()
                        .unwrap_or_else(|| "z3 returned unknown".to_owned()),
                ))
            }
        }
    }

    match solver.check_assumptions(&fixed) {
        SatResult::Sat => {}
        SatResult::Unsat => return Ok(QueryResult::unsat(None)),
        SatResult::Unknown => return Ok(QueryResult::unknown("z3 returned unknown")),
    }

    let want_model = (request.envelope.flags & request_flags::WANT_MODEL) != 0;
    let model = if want_model {
        let model = solver
            .get_model()
            .ok_or_else(|| WireError::invalid("Z3 model", "optimizer SAT without model"))?;
        Some(build_model(&translation, &model)?)
    } else {
        None
    };
    Ok(QueryResult::sat_optimization(OptimizationValueBlock {
        optimum: ScalarValue::bv(width, optimum)?,
        model,
    }))
}

fn child_bv(
    expr: &smt_wire::ExprView<'_>,
    translation: &Z3Translation,
    node: &smt_wire::RawNode,
    offset: u32,
) -> smt_wire::Result<BV> {
    translation.bv(expr.child_ref(node.children + offset)?)
}

fn child_bool(
    expr: &smt_wire::ExprView<'_>,
    translation: &Z3Translation,
    node: &smt_wire::RawNode,
    offset: u32,
) -> smt_wire::Result<Bool> {
    translation.bool(expr.child_ref(node.children + offset)?)
}

fn child_bv2(
    expr: &smt_wire::ExprView<'_>,
    translation: &Z3Translation,
    node: &smt_wire::RawNode,
) -> smt_wire::Result<(BV, BV)> {
    Ok((
        child_bv(expr, translation, node, 0)?,
        child_bv(expr, translation, node, 1)?,
    ))
}

fn child_bool2(
    expr: &smt_wire::ExprView<'_>,
    translation: &Z3Translation,
    node: &smt_wire::RawNode,
) -> smt_wire::Result<(Bool, Bool)> {
    Ok((
        child_bool(expr, translation, node, 0)?,
        child_bool(expr, translation, node, 1)?,
    ))
}

fn z3_bv_const(expr: &smt_wire::ExprView<'_>, width: u32, payload: u64) -> smt_wire::Result<BV> {
    if width <= 64 {
        return Ok(BV::from_u64(payload, width));
    }
    let bytes = expr.blob_ref(BlobRef::from_payload(payload))?;
    let mut bits = Vec::with_capacity(width as usize);
    for bit in 0..width {
        let byte = bytes[(bit / 8) as usize];
        bits.push(((byte >> (bit % 8)) & 1) != 0);
    }
    BV::from_bits(&bits).ok_or_else(|| WireError::invalid("BV_CONST", "failed to build Z3 BV"))
}

fn build_model(translation: &Z3Translation, model: &Model) -> smt_wire::Result<ModelBlock> {
    let mut entries = Vec::with_capacity(translation.variables.len());
    for variable in &translation.variables {
        let value = match variable.sort {
            Sort::Bool => {
                let ast = translation.bool(variable.node_ref)?;
                let value = model
                    .eval(&ast, true)
                    .and_then(|value| value.as_bool())
                    .ok_or_else(|| WireError::invalid("Z3 model", "missing Bool value"))?;
                ScalarValue::bool(value)
            }
            Sort::Bv => {
                let ast = translation.bv(variable.node_ref)?;
                let value = model
                    .eval(&ast, true)
                    .ok_or_else(|| WireError::invalid("Z3 model", "missing BV value"))?;
                bv_model_value(variable.width, &value)?
            }
        };
        entries.push(ModelEntry {
            node_ref: variable.node_ref,
            value,
        });
    }
    Ok(ModelBlock { entries })
}

fn build_core(solver: &Solver, trackers: &[(String, Bool)]) -> UnsatCoreBlock {
    let core = solver.get_unsat_core();
    let names = trackers
        .iter()
        .filter(|(_, tracker)| core.iter().any(|item| tracker.ast_eq(item)))
        .map(|(name, _)| name.clone())
        .collect();
    UnsatCoreBlock { names }
}

fn bv_model_value(width: u32, value: &BV) -> smt_wire::Result<ScalarValue> {
    if width <= 64 {
        if let Some(value) = value.as_u64() {
            let mut bytes = value.to_le_bytes().to_vec();
            bytes.truncate((width as usize).div_ceil(8));
            return ScalarValue::bv(width, bytes);
        }
    }
    parse_bv_literal(&value.to_string(), width)
}

fn parse_bv_literal(text: &str, width: u32) -> smt_wire::Result<ScalarValue> {
    let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
    if let Some(bits) = text.strip_prefix("#b") {
        for (offset, ch) in bits.chars().rev().enumerate() {
            if offset >= width as usize {
                break;
            }
            match ch {
                '0' => {}
                '1' => bytes[offset / 8] |= 1 << (offset % 8),
                _ => return Err(WireError::invalid("Z3 model", "bad binary BV literal")),
            }
        }
    } else if let Some(hex) = text.strip_prefix("#x") {
        for (nibble, ch) in hex.chars().rev().enumerate() {
            let value = ch
                .to_digit(16)
                .ok_or_else(|| WireError::invalid("Z3 model", "bad hex BV literal"))?
                as u8;
            let bit = nibble * 4;
            if bit / 8 < bytes.len() {
                bytes[bit / 8] |= value << (bit % 8);
            }
        }
    } else {
        bytes = decimal_to_le_bytes(text, (width as usize).div_ceil(8))?;
    }
    ScalarValue::bv(width, bytes)
}

fn decimal_to_le_bytes(text: &str, len: usize) -> smt_wire::Result<Vec<u8>> {
    let mut digits = text
        .bytes()
        .map(|byte| match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            _ => Err(WireError::invalid("Z3 model", "bad decimal BV literal")),
        })
        .collect::<smt_wire::Result<Vec<_>>>()?;
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

fn sign_bool(value: &BV) -> Bool {
    value
        .extract(value.get_size() - 1, value.get_size() - 1)
        .eq(BV::from_u64(1, 1))
}

fn signed_add_overflow(a: &BV, b: &BV) -> Bool {
    let sum = a.bvadd(b);
    let sa = sign_bool(a);
    let sb = sign_bool(b);
    let ss = sign_bool(&sum);
    Bool::or(&[
        &Bool::and(&[&sa.not(), &sb.not(), &ss]),
        &Bool::and(&[&sa, &sb, &ss.not()]),
    ])
}

fn signed_sub_overflow(a: &BV, b: &BV) -> Bool {
    let diff = a.bvsub(b);
    let sa = sign_bool(a);
    let sb = sign_bool(b);
    let sd = sign_bool(&diff);
    Bool::or(&[
        &Bool::and(&[&sa.not(), &sb, &sd]),
        &Bool::and(&[&sa, &sb.not(), &sd.not()]),
    ])
}

fn unsigned_mul_overflow(a: &BV, b: &BV) -> Bool {
    let width = a.get_size();
    let product = a.zero_ext(width).bvmul(b.zero_ext(width));
    let high = product.extract(width * 2 - 1, width);
    high.eq(BV::from_u64(0, width)).not()
}

fn signed_mul_overflow(a: &BV, b: &BV) -> Bool {
    let width = a.get_size();
    let product = a.sign_ext(width).bvmul(b.sign_ext(width));
    let low = product.extract(width - 1, 0);
    product.eq(low.sign_ext(width)).not()
}

fn signed_min_bv(width: u32) -> BV {
    let mut bits = vec![false; width as usize];
    bits[width as usize - 1] = true;
    BV::from_bits(&bits).expect("non-empty bitvector")
}

fn ones_bv(width: u32) -> BV {
    BV::from_bits(&vec![true; width as usize]).expect("non-empty bitvector")
}

fn set_bit(bytes: &mut [u8], bit: u32) {
    bytes[(bit / 8) as usize] |= 1 << (bit % 8);
}
