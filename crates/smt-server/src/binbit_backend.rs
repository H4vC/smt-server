use std::collections::HashMap;
use std::time::{Duration, Instant};

use binbit::{BoolTerm, BvTerm, SmtResult, SmtSolver};
use smt_wire::{
    request_flags, tag, BinaryRequest, BlobRef, Command, ModelBlock, ModelEntry, NodeRef,
    OptimizationValueBlock, ScalarValue, SimplifyBlock, Sort, UnsatCoreBlock, WireError,
};

use crate::backend::{Backend, QueryResult, SolveContext};

#[derive(Debug, Clone, Default)]
pub struct BinbitBackend;

impl Backend for BinbitBackend {
    fn name(&self) -> &'static str {
        "binbit"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        match request.envelope.command {
            Command::Simplify => Ok(QueryResult::simplified(SimplifyBlock {
                expression: request.expression.clone(),
                target_node: request
                    .target_ref()
                    .ok_or_else(|| WireError::invalid("simplify request", "missing target_node"))?,
            })),
            Command::Solve => solve(request),
            Command::Minimize | Command::Maximize => optimize(request),
        }
    }

    fn handle_with_context(
        &self,
        request: &BinaryRequest,
        context: &SolveContext,
    ) -> smt_wire::Result<QueryResult> {
        if context.is_cancelled() {
            return Ok(QueryResult::unknown(
                "binbit request cancelled before start",
            ));
        }
        match request.envelope.command {
            Command::Simplify => self.handle(request),
            Command::Solve => solve_with_context(request, context),
            Command::Minimize | Command::Maximize => Ok(QueryResult::unknown(
                "binbit optimization does not support cooperative cancellation",
            )),
        }
    }
}

#[derive(Debug, Clone)]
struct BinbitVariable {
    node_ref: NodeRef,
    sort: Sort,
    width: u32,
}

struct BinbitTranslation {
    solver: SmtSolver,
    bvs: Vec<Option<BvTerm>>,
    bools: Vec<Option<BoolTerm>>,
    variables: Vec<BinbitVariable>,
}

impl BinbitTranslation {
    fn bv(&self, reference: NodeRef) -> smt_wire::Result<BvTerm> {
        if !reference.is_bv() {
            return Err(WireError::invalid(
                "binbit translation",
                "expected BV reference",
            ));
        }
        self.bvs
            .get(reference.index() as usize)
            .and_then(|term| *term)
            .ok_or_else(|| WireError::invalid("binbit translation", "missing BV term"))
    }

    fn bool(&self, reference: NodeRef) -> smt_wire::Result<BoolTerm> {
        if !reference.is_bool() {
            return Err(WireError::invalid(
                "binbit translation",
                "expected Bool reference",
            ));
        }
        self.bools
            .get(reference.index() as usize)
            .and_then(|term| *term)
            .ok_or_else(|| WireError::invalid("binbit translation", "missing Bool term"))
    }
}

fn translate(request: &BinaryRequest) -> smt_wire::Result<BinbitTranslation> {
    translate_with_context(request, None)
}

fn translate_with_context(
    request: &BinaryRequest,
    context: Option<&SolveContext>,
) -> smt_wire::Result<BinbitTranslation> {
    let expr = request.expression_view()?;
    let mut out = BinbitTranslation {
        solver: SmtSolver::new(),
        bvs: vec![None; expr.node_count() as usize],
        bools: vec![None; expr.node_count() as usize],
        variables: Vec::new(),
    };
    let mut bv_vars = HashMap::<(String, u32), BvTerm>::new();
    let mut bool_vars = HashMap::<String, BoolTerm>::new();

    for index in 0..expr.node_count() {
        if index % 1024 == 0 && context.is_some_and(SolveContext::is_cancelled) {
            return Err(WireError::invalid(
                "binbit translation",
                "request cancelled",
            ));
        }
        let node = expr.node(index)?;
        match node.tag {
            tag::BV_VAR => {
                let name = expr
                    .blob_str(BlobRef::from_payload(node.payload), "BV variable")?
                    .to_owned();
                let term = if let Some(term) = bv_vars.get(&(name.clone(), node.width)).copied() {
                    term
                } else {
                    let term = out.solver.bv_var(node.width);
                    bv_vars.insert((name, node.width), term);
                    term
                };
                out.variables.push(BinbitVariable {
                    node_ref: NodeRef::bv(index)?,
                    sort: Sort::Bv,
                    width: node.width,
                });
                out.bvs[index as usize] = Some(term);
            }
            tag::BV_CONST => {
                out.bvs[index as usize] = Some(binbit_bv_const(
                    &mut out.solver,
                    &expr,
                    node.width,
                    node.payload,
                )?);
            }
            tag::BV_NOT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(out.solver.bv_not(x));
            }
            tag::BV_NEG => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(out.solver.bv_neg(x));
            }
            tag::BV_AND => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_and(a, b));
            }
            tag::BV_OR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_or(a, b));
            }
            tag::BV_XOR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_xor(a, b));
            }
            tag::BV_ADD => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_add(a, b));
            }
            tag::BV_SUB => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_sub(a, b));
            }
            tag::BV_MUL => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_mul(a, b));
            }
            tag::BV_UDIV => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_udiv(a, b));
            }
            tag::BV_UREM => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_urem(a, b));
            }
            tag::BV_SDIV => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_sdiv(a, b));
            }
            tag::BV_SREM => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_srem(a, b));
            }
            tag::BV_SMOD => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_smod(a, b));
            }
            tag::BV_SHL => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_shl(a, b));
            }
            tag::BV_LSHR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_lshr(a, b));
            }
            tag::BV_ASHR => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_ashr(a, b));
            }
            tag::BV_EXTRACT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] = Some(out.solver.bv_extract(
                    x,
                    u32::from(node.aux_hi),
                    node.aux_lo,
                ));
            }
            tag::BV_CONCAT => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bvs[index as usize] = Some(out.solver.bv_concat(a, b));
            }
            tag::BV_ZEXT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] =
                    Some(out.solver.bv_zero_extend(x, u32::from(node.aux_hi)));
            }
            tag::BV_SEXT => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bvs[index as usize] =
                    Some(out.solver.bv_sign_extend(x, u32::from(node.aux_hi)));
            }
            tag::BV_ITE => {
                let c = child_bool(&expr, &out, &node, 0)?;
                let t = child_bv(&expr, &out, &node, 1)?;
                let e = child_bv(&expr, &out, &node, 2)?;
                out.bvs[index as usize] = Some(out.solver.bv_ite(c, t, e));
            }
            tag::BV_SELECT => {
                let pairs = u32::from(node.aux_hi);
                let mut selectors = Vec::with_capacity(pairs as usize);
                let mut values = Vec::with_capacity(pairs as usize);
                for pair in 0..pairs {
                    selectors.push(child_bool(&expr, &out, &node, pair * 2)?);
                    values.push(child_bv(&expr, &out, &node, pair * 2 + 1)?);
                }
                let default = child_bv(&expr, &out, &node, pairs * 2)?;
                out.bvs[index as usize] = Some(out.solver.bv_select(&selectors, &values, default));
            }
            tag::BOOL_TRUE => out.bools[index as usize] = Some(out.solver.bool_true()),
            tag::BOOL_FALSE => out.bools[index as usize] = Some(out.solver.bool_false()),
            tag::BOOL_VAR => {
                let name = expr
                    .blob_str(BlobRef::from_payload(node.payload), "Bool variable")?
                    .to_owned();
                let term = if let Some(term) = bool_vars.get(&name).copied() {
                    term
                } else {
                    let term = out.solver.bool_var();
                    bool_vars.insert(name, term);
                    term
                };
                out.variables.push(BinbitVariable {
                    node_ref: NodeRef::bool(index)?,
                    sort: Sort::Bool,
                    width: 0,
                });
                out.bools[index as usize] = Some(term);
            }
            tag::BOOL_NOT => {
                let x = child_bool(&expr, &out, &node, 0)?;
                out.bools[index as usize] = Some(out.solver.bool_not(x));
            }
            tag::BOOL_AND => {
                let (a, b) = child_bool2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bool_and(a, b));
            }
            tag::BOOL_OR => {
                let (a, b) = child_bool2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bool_or(a, b));
            }
            tag::BOOL_IMPLIES => {
                let (a, b) = child_bool2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bool_implies(a, b));
            }
            tag::BV_EQ => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_eq(a, b));
            }
            tag::BV_ULT => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_ult(a, b));
            }
            tag::BV_ULE => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_ule(a, b));
            }
            tag::BV_SLT => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_slt(a, b));
            }
            tag::BV_SLE => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_sle(a, b));
            }
            tag::UADD_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_uadd_overflow(a, b));
            }
            tag::SADD_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_sadd_overflow(a, b));
            }
            tag::USUB_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_usub_overflow(a, b));
            }
            tag::SSUB_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_ssub_overflow(a, b));
            }
            tag::UMUL_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_umul_overflow(a, b));
            }
            tag::SMUL_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_smul_overflow(a, b));
            }
            tag::NEG_OVF => {
                let x = child_bv(&expr, &out, &node, 0)?;
                out.bools[index as usize] = Some(out.solver.bv_neg_overflow(x));
            }
            tag::SDIV_OVF => {
                let (a, b) = child_bv2(&expr, &out, &node)?;
                out.bools[index as usize] = Some(out.solver.bv_sdiv_overflow(a, b));
            }
            other => {
                return Err(WireError::invalid(
                    "binbit translation",
                    format!("unknown tag {other}"),
                ))
            }
        }
    }

    Ok(out)
}

fn solve(request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
    solve_inner(request, None)
}

fn solve_with_context(
    request: &BinaryRequest,
    context: &SolveContext,
) -> smt_wire::Result<QueryResult> {
    solve_inner(request, Some(context))
}

fn solve_inner(
    request: &BinaryRequest,
    context: Option<&SolveContext>,
) -> smt_wire::Result<QueryResult> {
    let expr = request.expression_view()?;
    let mut translation = match translate_with_context(request, context) {
        Ok(translation) => translation,
        Err(_) if context.is_some_and(SolveContext::is_cancelled) => {
            return Ok(QueryResult::unknown("binbit request cancelled"));
        }
        Err(err) => return Err(err),
    };
    let want_model = (request.envelope.flags & request_flags::WANT_MODEL) != 0;
    let want_core = (request.envelope.flags & request_flags::WANT_CORE) != 0;

    for (index, root) in request.assertion_roots.iter().enumerate() {
        if context.is_some_and(SolveContext::is_cancelled) {
            return Ok(QueryResult::unknown("binbit request cancelled"));
        }
        let assertion = translation.bool(*root)?;
        if want_core && index < request.named_assertion_refs.len() {
            let name = expr.blob_str(request.named_assertion_refs[index], "named assertion")?;
            translation.solver.assert_named(name, assertion);
        } else {
            translation.solver.assert(assertion);
        }
    }
    let assumptions = request
        .assumption_roots
        .iter()
        .map(|root| translation.bool(*root))
        .collect::<smt_wire::Result<Vec<_>>>()?;

    let result = solve_binbit(
        &mut translation.solver,
        &assumptions,
        request.envelope.budget_ms,
        context,
    );

    match result {
        Some(SmtResult::Sat) => {
            let model = if want_model {
                Some(build_model(&mut translation)?)
            } else {
                None
            };
            Ok(QueryResult::sat(model))
        }
        Some(SmtResult::Unsat) => {
            let core = if want_core {
                Some(UnsatCoreBlock {
                    names: translation
                        .solver
                        .unsat_core_names()
                        .into_iter()
                        .map(str::to_owned)
                        .collect(),
                })
            } else {
                None
            };
            Ok(QueryResult::unsat(core))
        }
        None if context.is_some_and(SolveContext::is_cancelled) => {
            Ok(QueryResult::unknown("binbit request cancelled"))
        }
        None => Ok(QueryResult::unknown("binbit budget exhausted")),
    }
}

fn solve_binbit(
    solver: &mut SmtSolver,
    assumptions: &[BoolTerm],
    budget_ms: u32,
    context: Option<&SolveContext>,
) -> Option<SmtResult> {
    let Some(context) = context else {
        return if budget_ms == 0 {
            Some(solver.solve_under_assumptions(assumptions))
        } else {
            solver.solve_under_assumptions_timed(
                assumptions,
                Duration::from_millis(u64::from(budget_ms)),
            )
        };
    };

    let deadline =
        (budget_ms != 0).then(|| Instant::now() + Duration::from_millis(u64::from(budget_ms)));
    loop {
        if context.is_cancelled() {
            return None;
        }
        let slice = match deadline {
            Some(deadline) => {
                let remaining = deadline.checked_duration_since(Instant::now())?;
                if remaining.is_zero() {
                    return None;
                }
                remaining.min(Duration::from_millis(10))
            }
            None => Duration::from_millis(10),
        };
        if let Some(result) = solver.solve_under_assumptions_timed(assumptions, slice) {
            return Some(result);
        }
    }
}

fn optimize(request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
    if request.envelope.budget_ms != 0 {
        return Ok(QueryResult::unknown(
            "binbit optimization currently supports unbounded searches only",
        ));
    }
    let mut translation = translate(request)?;
    for root in &request.assertion_roots {
        let assertion = translation.bool(*root)?;
        translation.solver.assert(assertion);
    }
    for root in &request.assumption_roots {
        let assumption = translation.bool(*root)?;
        translation.solver.assert(assumption);
    }
    let target = translation.bv(request.target_ref().ok_or_else(|| {
        WireError::invalid("optimization", "missing MINIMIZE/MAXIMIZE target node")
    })?)?;
    let signed = (request.envelope.flags & request_flags::SIGNED) != 0;
    let minimize = request.envelope.command == Command::Minimize;
    let optimum_limbs = match (signed, minimize) {
        (false, true) => translation.solver.solve_min_u_limbs(target),
        (false, false) => translation.solver.solve_max_u_limbs(target),
        (true, true) => translation.solver.solve_min_s_limbs(target),
        (true, false) => translation.solver.solve_max_s_limbs(target),
    };
    let Some(optimum_limbs) = optimum_limbs else {
        return Ok(QueryResult::unsat(None));
    };
    let width = translation.solver.bv_width(target);
    let model = if (request.envelope.flags & request_flags::WANT_MODEL) != 0 {
        Some(build_model(&mut translation)?)
    } else {
        None
    };
    Ok(QueryResult::sat_optimization(OptimizationValueBlock {
        optimum: scalar_from_limbs(width, &optimum_limbs)?,
        model,
    }))
}

fn child_bv(
    expr: &smt_wire::ExprView<'_>,
    translation: &BinbitTranslation,
    node: &smt_wire::RawNode,
    offset: u32,
) -> smt_wire::Result<BvTerm> {
    translation.bv(expr.child_ref(node.children + offset)?)
}

fn child_bool(
    expr: &smt_wire::ExprView<'_>,
    translation: &BinbitTranslation,
    node: &smt_wire::RawNode,
    offset: u32,
) -> smt_wire::Result<BoolTerm> {
    translation.bool(expr.child_ref(node.children + offset)?)
}

fn child_bv2(
    expr: &smt_wire::ExprView<'_>,
    translation: &BinbitTranslation,
    node: &smt_wire::RawNode,
) -> smt_wire::Result<(BvTerm, BvTerm)> {
    Ok((
        child_bv(expr, translation, node, 0)?,
        child_bv(expr, translation, node, 1)?,
    ))
}

fn child_bool2(
    expr: &smt_wire::ExprView<'_>,
    translation: &BinbitTranslation,
    node: &smt_wire::RawNode,
) -> smt_wire::Result<(BoolTerm, BoolTerm)> {
    Ok((
        child_bool(expr, translation, node, 0)?,
        child_bool(expr, translation, node, 1)?,
    ))
}

fn binbit_bv_const(
    solver: &mut SmtSolver,
    expr: &smt_wire::ExprView<'_>,
    width: u32,
    payload: u64,
) -> smt_wire::Result<BvTerm> {
    if width <= 128 {
        let value = if width <= 64 {
            payload as u128
        } else {
            bytes_to_u128(expr.blob_ref(BlobRef::from_payload(payload))?)
        };
        Ok(solver.bv_const(value, width))
    } else {
        let bytes = expr.blob_ref(BlobRef::from_payload(payload))?;
        let limbs = bytes_to_limbs(bytes, width);
        Ok(solver.bv_const_wide(&limbs, width))
    }
}

fn build_model(translation: &mut BinbitTranslation) -> smt_wire::Result<ModelBlock> {
    let mut entries = Vec::with_capacity(translation.variables.len());
    for variable in translation.variables.clone() {
        let value = match variable.sort {
            Sort::Bool => ScalarValue::bool(
                translation
                    .solver
                    .get_bool_value(translation.bool(variable.node_ref)?),
            ),
            Sort::Bv => {
                let term = translation.bv(variable.node_ref)?;
                scalar_from_limbs(variable.width, &translation.solver.get_bv_value_limbs(term))?
            }
        };
        entries.push(ModelEntry {
            node_ref: variable.node_ref,
            value,
        });
    }
    Ok(ModelBlock { entries })
}

fn bytes_to_u128(bytes: &[u8]) -> u128 {
    let mut value = 0u128;
    for (index, byte) in bytes.iter().enumerate().take(16) {
        value |= u128::from(*byte) << (index * 8);
    }
    value
}

fn bytes_to_limbs(bytes: &[u8], width: u32) -> Vec<u64> {
    let mut limbs = vec![0u64; (width as usize).div_ceil(64)];
    for (index, byte) in bytes.iter().enumerate() {
        limbs[index / 8] |= u64::from(*byte) << ((index % 8) * 8);
    }
    limbs
}

fn scalar_from_limbs(width: u32, limbs: &[u64]) -> smt_wire::Result<ScalarValue> {
    let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = ((limbs[index / 8] >> ((index % 8) * 8)) & 0xff) as u8;
    }
    ScalarValue::bv(width, bytes)
}
