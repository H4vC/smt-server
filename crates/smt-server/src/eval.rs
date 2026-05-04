use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use smt_wire::{
    request_flags, tag, BinaryRequest, BlobRef, Command, ExprView, ModelBlock, ModelEntry, NodeRef,
    OptimizationValueBlock, ScalarValue, SimplifyBlock, Sort, UnsatCoreBlock, WireError,
};

use crate::backend::{Backend, QueryResult};

const DEFAULT_MAX_STATES: u128 = 1_000_000;
const DEFAULT_MAX_WIDTH: u32 = 128;

#[derive(Debug, Clone)]
pub struct ExhaustiveBackend {
    max_states: u128,
    max_width: u32,
}

impl Default for ExhaustiveBackend {
    fn default() -> Self {
        Self {
            max_states: DEFAULT_MAX_STATES,
            max_width: DEFAULT_MAX_WIDTH,
        }
    }
}

impl ExhaustiveBackend {
    pub fn new(max_states: u128) -> Self {
        Self {
            max_states,
            ..Self::default()
        }
    }

    pub fn with_limits(max_states: u128, max_width: u32) -> Self {
        Self {
            max_states,
            max_width,
        }
    }

    fn execute(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        match request.envelope.command {
            Command::Simplify => Ok(QueryResult::ok_simplify(SimplifyBlock {
                expression: request.expression.clone(),
                assertion_roots: request.assertion_roots.clone(),
                named_assertion_refs: request.named_assertion_refs.clone(),
                assumption_roots: request.assumption_roots.clone(),
            })),
            Command::Solve => self.solve(request),
            Command::Minimize | Command::Maximize => self.optimize(request),
        }
    }

    fn solve(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        let expr = request.expression_view()?;
        let env = match Enumeration::prepare(self, request, None) {
            Ok(env) => env,
            Err(err) => return Ok(QueryResult::unknown(err.to_string())),
        };
        let want_model = (request.envelope.flags & request_flags::WANT_MODEL) != 0;
        let want_core = (request.envelope.flags & request_flags::WANT_CORE) != 0;
        let deadline = deadline_from_budget(request.envelope.budget_ms);
        let mut hit_unknown = None;
        for assignment in env.assignments(deadline) {
            let assignment = match assignment {
                Ok(assignment) => assignment,
                Err(reason) => {
                    hit_unknown = Some(reason);
                    break;
                }
            };
            match formula_holds(&expr, request, &assignment) {
                Ok(true) => {
                    let model = if want_model {
                        Some(build_model(&expr, &env.variables, &assignment)?)
                    } else {
                        None
                    };
                    return Ok(QueryResult::sat(model));
                }
                Ok(false) => {}
                Err(reason) => return Ok(QueryResult::unknown(reason)),
            }
        }
        if let Some(reason) = hit_unknown {
            return Ok(QueryResult::unknown(reason));
        }
        let core = if want_core {
            Some(build_core(&expr, &request.named_assertion_refs)?)
        } else {
            None
        };
        Ok(QueryResult::unsat(core))
    }

    fn optimize(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        let expr = request.expression_view()?;
        let target = request.target_ref().ok_or_else(|| {
            WireError::invalid("optimization", "missing MINIMIZE/MAXIMIZE target node")
        })?;
        let target_node = smt_wire::expr::validate_node_ref(&expr, target, Sort::Bv, "target")?;
        if target_node.width > self.max_width {
            return Ok(QueryResult::unknown(format!(
                "target width {} exceeds exhaustive backend width limit {}",
                target_node.width, self.max_width
            )));
        }
        let env = match Enumeration::prepare(self, request, Some(target)) {
            Ok(env) => env,
            Err(err) => return Ok(QueryResult::unknown(err.to_string())),
        };
        let signed = (request.envelope.flags & request_flags::SIGNED) != 0;
        let want_model = (request.envelope.flags & request_flags::WANT_MODEL) != 0;
        let minimize = request.envelope.command == Command::Minimize;
        let deadline = deadline_from_budget(request.envelope.budget_ms);
        let mut best_value = None::<Bv>;
        let mut best_assignment = None::<Assignment>;
        let mut hit_unknown = None;

        for assignment in env.assignments(deadline) {
            let assignment = match assignment {
                Ok(assignment) => assignment,
                Err(reason) => {
                    hit_unknown = Some(reason);
                    break;
                }
            };
            match formula_holds(&expr, request, &assignment) {
                Ok(true) => {}
                Ok(false) => continue,
                Err(reason) => return Ok(QueryResult::unknown(reason)),
            }
            let value = match eval_ref(
                &expr,
                target,
                &assignment,
                &mut vec![None; expr.node_count() as usize],
            ) {
                Ok(Value::Bv(value)) => value,
                Ok(Value::Bool(_)) => {
                    return Err(WireError::invalid(
                        "optimization",
                        "target evaluated to Bool",
                    ))
                }
                Err(reason) => return Ok(QueryResult::unknown(reason)),
            };
            let is_better = match &best_value {
                None => true,
                Some(best) => match compare_bv(&value, best, signed) {
                    Ok(ord) => {
                        if minimize {
                            ord.is_lt()
                        } else {
                            ord.is_gt()
                        }
                    }
                    Err(reason) => return Ok(QueryResult::unknown(reason)),
                },
            };
            if is_better {
                best_value = Some(value);
                best_assignment = Some(assignment);
            }
        }

        if let Some(reason) = hit_unknown {
            return Ok(QueryResult::unknown(reason));
        }
        let Some(best_value) = best_value else {
            return Ok(QueryResult::unsat(None));
        };
        let model = if want_model {
            Some(build_model(
                &expr,
                &env.variables,
                best_assignment.as_ref().expect("best assignment is set"),
            )?)
        } else {
            None
        };
        Ok(QueryResult::sat_optimization(OptimizationValueBlock {
            optimum: scalar_from_bv(best_value)?,
            model,
        }))
    }
}

impl Backend for ExhaustiveBackend {
    fn name(&self) -> &'static str {
        "exhaustive"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        self.execute(request)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Bv {
    width: u32,
    value: u128,
}

impl Bv {
    fn new(width: u32, value: u128) -> Result<Self, String> {
        if !(1..=128).contains(&width) {
            return Err(format!("width {width} is outside exhaustive range 1..=128"));
        }
        Ok(Self {
            width,
            value: value & mask(width),
        })
    }

    fn all_ones(width: u32) -> Self {
        Self {
            width,
            value: mask(width),
        }
    }

    fn sign_bit(self) -> bool {
        ((self.value >> (self.width - 1)) & 1) != 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Value {
    Bv(Bv),
    Bool(bool),
}

#[derive(Debug, Clone)]
struct Variable {
    node_ref: NodeRef,
    sort: Sort,
    width: u32,
}

type Assignment = HashMap<u32, Value>;

#[derive(Debug, Clone)]
struct Enumeration {
    variables: Vec<Variable>,
    total_states: u128,
}

impl Enumeration {
    fn prepare(
        backend: &ExhaustiveBackend,
        request: &BinaryRequest,
        extra_root: Option<NodeRef>,
    ) -> smt_wire::Result<Self> {
        let expr = request.expression_view()?;
        let mut live = HashSet::new();
        for root in &request.assertion_roots {
            mark_live(&expr, *root, &mut live)?;
        }
        for root in &request.assumption_roots {
            mark_live(&expr, *root, &mut live)?;
        }
        if let Some(root) = extra_root {
            mark_live(&expr, root, &mut live)?;
        }

        let mut variables = Vec::new();
        for index in 0..expr.node_count() {
            if !live.contains(&index) {
                continue;
            }
            let node = expr.node(index)?;
            match node.tag {
                tag::BV_VAR => {
                    if node.width > backend.max_width {
                        return Err(WireError::invalid(
                            "exhaustive backend",
                            format!(
                                "variable width {} exceeds configured width limit {}",
                                node.width, backend.max_width
                            ),
                        ));
                    }
                    variables.push(Variable {
                        node_ref: NodeRef::bv(index)?,
                        sort: Sort::Bv,
                        width: node.width,
                    });
                }
                tag::BOOL_VAR => variables.push(Variable {
                    node_ref: NodeRef::bool(index)?,
                    sort: Sort::Bool,
                    width: 0,
                }),
                _ => {}
            }
        }

        let mut total_states = 1u128;
        for var in &variables {
            let domain = match var.sort {
                Sort::Bool => 2,
                Sort::Bv => {
                    if var.width >= 128 {
                        return Err(WireError::invalid(
                            "exhaustive backend",
                            "128-bit variable domains are too large to enumerate",
                        ));
                    }
                    1u128 << var.width
                }
            };
            total_states = total_states.saturating_mul(domain);
            if total_states > backend.max_states {
                break;
            }
        }
        if total_states > backend.max_states {
            return Err(WireError::invalid(
                "exhaustive backend",
                format!(
                    "query has {total_states} candidate assignments, limit is {}",
                    backend.max_states
                ),
            ));
        }
        Ok(Self {
            variables,
            total_states,
        })
    }

    fn assignments(&self, deadline: Option<Instant>) -> AssignmentIter<'_> {
        AssignmentIter {
            env: self,
            next: 0,
            deadline,
        }
    }
}

struct AssignmentIter<'a> {
    env: &'a Enumeration,
    next: u128,
    deadline: Option<Instant>,
}

impl Iterator for AssignmentIter<'_> {
    type Item = Result<Assignment, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next >= self.env.total_states {
            return None;
        }
        if let Some(deadline) = self.deadline {
            if Instant::now() >= deadline {
                return Some(Err(
                    "budget exhausted during exhaustive enumeration".to_owned()
                ));
            }
        }
        let mut ordinal = self.next;
        self.next += 1;
        let mut assignment = Assignment::new();
        for var in &self.env.variables {
            match var.sort {
                Sort::Bool => {
                    assignment.insert(var.node_ref.index(), Value::Bool((ordinal & 1) != 0));
                    ordinal >>= 1;
                }
                Sort::Bv => {
                    let domain_bits = var.width;
                    let value = ordinal & mask(domain_bits);
                    ordinal >>= domain_bits;
                    assignment.insert(
                        var.node_ref.index(),
                        Value::Bv(Bv {
                            width: var.width,
                            value,
                        }),
                    );
                }
            }
        }
        Some(Ok(assignment))
    }
}

fn deadline_from_budget(budget_ms: u32) -> Option<Instant> {
    if budget_ms == 0 {
        None
    } else {
        Some(Instant::now() + Duration::from_millis(u64::from(budget_ms)))
    }
}

fn formula_holds(
    expr: &ExprView<'_>,
    request: &BinaryRequest,
    assignment: &Assignment,
) -> Result<bool, String> {
    let mut cache = vec![None; expr.node_count() as usize];
    for root in request
        .assertion_roots
        .iter()
        .chain(&request.assumption_roots)
    {
        match eval_ref(expr, *root, assignment, &mut cache)? {
            Value::Bool(true) => {}
            Value::Bool(false) => return Ok(false),
            Value::Bv(_) => return Err("assertion root evaluated to BV".to_owned()),
        }
    }
    Ok(true)
}

fn mark_live(
    expr: &ExprView<'_>,
    reference: NodeRef,
    live: &mut HashSet<u32>,
) -> smt_wire::Result<()> {
    let index = reference.index();
    if !live.insert(index) {
        return Ok(());
    }
    let node = expr.node(index)?;
    for child_offset in 0..node.arity {
        let child = expr.child_ref(node.children + u32::from(child_offset))?;
        mark_live(expr, child, live)?;
    }
    Ok(())
}

fn eval_ref(
    expr: &ExprView<'_>,
    reference: NodeRef,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
) -> Result<Value, String> {
    let value = eval_node(expr, reference.index(), assignment, cache)?;
    match (reference.sort(), value) {
        (Sort::Bool, Value::Bool(_)) | (Sort::Bv, Value::Bv(_)) => Ok(value),
        (expected, actual) => Err(format!(
            "typed reference {reference:?} expected {expected:?}, got value {actual:?}"
        )),
    }
}

fn eval_node(
    expr: &ExprView<'_>,
    index: u32,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
) -> Result<Value, String> {
    if let Some(value) = cache[index as usize] {
        return Ok(value);
    }
    let node = expr.node(index).map_err(|err| err.to_string())?;
    let value = match node.tag {
        tag::BV_VAR | tag::BOOL_VAR => *assignment
            .get(&index)
            .ok_or_else(|| format!("missing assignment for variable node {index}"))?,
        tag::BV_CONST => Value::Bv(read_bv_const(expr, node.width, node.payload)?),
        tag::BOOL_TRUE => Value::Bool(true),
        tag::BOOL_FALSE => Value::Bool(false),
        tag::BV_NOT => Value::Bv(unary_bv(expr, node.children, assignment, cache, |a| {
            Bv::new(a.width, !a.value)
        })?),
        tag::BV_NEG => Value::Bv(unary_bv(expr, node.children, assignment, cache, |a| {
            Bv::new(a.width, (!a.value).wrapping_add(1))
        })?),
        tag::BV_AND => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Bv::new(a.width, a.value & b.value),
        )?),
        tag::BV_OR => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Bv::new(a.width, a.value | b.value),
        )?),
        tag::BV_XOR => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Bv::new(a.width, a.value ^ b.value),
        )?),
        tag::BV_ADD => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Bv::new(a.width, a.value.wrapping_add(b.value)),
        )?),
        tag::BV_SUB => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Bv::new(a.width, a.value.wrapping_sub(b.value)),
        )?),
        tag::BV_MUL => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Bv::new(a.width, a.value.wrapping_mul(b.value)),
        )?),
        tag::BV_UDIV => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                if let Some(quotient) = a.value.checked_div(b.value) {
                    Bv::new(a.width, quotient)
                } else {
                    Ok(Bv::all_ones(a.width))
                }
            },
        )?),
        tag::BV_UREM => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                if let Some(remainder) = a.value.checked_rem(b.value) {
                    Bv::new(a.width, remainder)
                } else {
                    Ok(a)
                }
            },
        )?),
        tag::BV_SDIV => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            signed_div,
        )?),
        tag::BV_SREM => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            signed_rem,
        )?),
        tag::BV_SMOD => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            signed_mod,
        )?),
        tag::BV_SHL => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                if b.value >= u128::from(a.width) {
                    Bv::new(a.width, 0)
                } else {
                    Bv::new(a.width, a.value << (b.value as u32))
                }
            },
        )?),
        tag::BV_LSHR => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                if b.value >= u128::from(a.width) {
                    Bv::new(a.width, 0)
                } else {
                    Bv::new(a.width, a.value >> (b.value as u32))
                }
            },
        )?),
        tag::BV_ASHR => Value::Bv(binary_bv(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                if b.value >= u128::from(a.width) {
                    if a.sign_bit() {
                        Ok(Bv::all_ones(a.width))
                    } else {
                        Bv::new(a.width, 0)
                    }
                } else {
                    let shift = b.value as u32;
                    if shift == 0 {
                        Ok(a)
                    } else if !a.sign_bit() {
                        Bv::new(a.width, a.value >> shift)
                    } else {
                        let shifted = a.value >> shift;
                        let fill = mask(a.width) << (a.width - shift);
                        Bv::new(a.width, shifted | fill)
                    }
                }
            },
        )?),
        tag::BV_EXTRACT => {
            let child = child_bv(expr, node.children, assignment, cache)?;
            let lo = node.aux_lo;
            let width = u32::from(node.aux_hi) - lo + 1;
            Value::Bv(Bv::new(width, child.value >> lo)?)
        }
        tag::BV_CONCAT => {
            let a = child_bv(expr, node.children, assignment, cache)?;
            let b = child_bv(expr, node.children + 1, assignment, cache)?;
            Value::Bv(Bv::new(a.width + b.width, (a.value << b.width) | b.value)?)
        }
        tag::BV_ZEXT => {
            let child = child_bv(expr, node.children, assignment, cache)?;
            Value::Bv(Bv::new(node.width, child.value)?)
        }
        tag::BV_SEXT => {
            let child = child_bv(expr, node.children, assignment, cache)?;
            let value = if child.sign_bit() {
                child.value | (mask(node.width) & !mask(child.width))
            } else {
                child.value
            };
            Value::Bv(Bv::new(node.width, value)?)
        }
        tag::BV_ITE => {
            let cond = child_bool(expr, node.children, assignment, cache)?;
            if cond {
                Value::Bv(child_bv(expr, node.children + 1, assignment, cache)?)
            } else {
                Value::Bv(child_bv(expr, node.children + 2, assignment, cache)?)
            }
        }
        tag::BV_SELECT => {
            let pairs = u32::from(node.aux_hi);
            let mut selected = None;
            for pair in 0..pairs {
                if child_bool(expr, node.children + pair * 2, assignment, cache)? {
                    selected = Some(child_bv(
                        expr,
                        node.children + pair * 2 + 1,
                        assignment,
                        cache,
                    )?);
                    break;
                }
            }
            Value::Bv(selected.unwrap_or(child_bv(
                expr,
                node.children + pairs * 2,
                assignment,
                cache,
            )?))
        }
        tag::BOOL_NOT => Value::Bool(!child_bool(expr, node.children, assignment, cache)?),
        tag::BOOL_AND => Value::Bool(
            child_bool(expr, node.children, assignment, cache)?
                && child_bool(expr, node.children + 1, assignment, cache)?,
        ),
        tag::BOOL_OR => Value::Bool(
            child_bool(expr, node.children, assignment, cache)?
                || child_bool(expr, node.children + 1, assignment, cache)?,
        ),
        tag::BOOL_IMPLIES => Value::Bool(
            !child_bool(expr, node.children, assignment, cache)?
                || child_bool(expr, node.children + 1, assignment, cache)?,
        ),
        tag::BV_EQ => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(a.value == b.value),
        )?),
        tag::BV_ULT => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(a.value < b.value),
        )?),
        tag::BV_ULE => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(a.value <= b.value),
        )?),
        tag::BV_SLT => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(compare_bv(&a, &b, true)?.is_lt()),
        )?),
        tag::BV_SLE => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(!compare_bv(&a, &b, true)?.is_gt()),
        )?),
        tag::UADD_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                Ok(a.value
                    .checked_add(b.value)
                    .is_none_or(|sum| sum > mask(a.width)))
            },
        )?),
        tag::USUB_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(a.value < b.value),
        )?),
        tag::UMUL_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| {
                Ok(a.value
                    .checked_mul(b.value)
                    .is_none_or(|product| product > mask(a.width)))
            },
        )?),
        tag::SADD_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            signed_add_ovf,
        )?),
        tag::SSUB_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            signed_sub_ovf,
        )?),
        tag::SMUL_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            signed_mul_ovf,
        )?),
        tag::NEG_OVF => {
            let a = child_bv(expr, node.children, assignment, cache)?;
            Value::Bool(a.value == signed_min_value(a.width))
        }
        tag::SDIV_OVF => Value::Bool(binary_bv_cmp(
            expr,
            node.children,
            assignment,
            cache,
            |a, b| Ok(a.value == signed_min_value(a.width) && b.value == mask(a.width)),
        )?),
        other => return Err(format!("unknown tag {other}")),
    };
    cache[index as usize] = Some(value);
    Ok(value)
}

fn child_ref(expr: &ExprView<'_>, child_index: u32) -> Result<NodeRef, String> {
    expr.child_ref(child_index).map_err(|err| err.to_string())
}

fn child_bv(
    expr: &ExprView<'_>,
    child_index: u32,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
) -> Result<Bv, String> {
    match eval_ref(expr, child_ref(expr, child_index)?, assignment, cache)? {
        Value::Bv(value) => Ok(value),
        Value::Bool(_) => Err("expected BV child".to_owned()),
    }
}

fn child_bool(
    expr: &ExprView<'_>,
    child_index: u32,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
) -> Result<bool, String> {
    match eval_ref(expr, child_ref(expr, child_index)?, assignment, cache)? {
        Value::Bool(value) => Ok(value),
        Value::Bv(_) => Err("expected Bool child".to_owned()),
    }
}

fn unary_bv(
    expr: &ExprView<'_>,
    child_index: u32,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
    f: impl FnOnce(Bv) -> Result<Bv, String>,
) -> Result<Bv, String> {
    f(child_bv(expr, child_index, assignment, cache)?)
}

fn binary_bv(
    expr: &ExprView<'_>,
    child_index: u32,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
    f: impl FnOnce(Bv, Bv) -> Result<Bv, String>,
) -> Result<Bv, String> {
    let a = child_bv(expr, child_index, assignment, cache)?;
    let b = child_bv(expr, child_index + 1, assignment, cache)?;
    f(a, b)
}

fn binary_bv_cmp(
    expr: &ExprView<'_>,
    child_index: u32,
    assignment: &Assignment,
    cache: &mut [Option<Value>],
    f: impl FnOnce(Bv, Bv) -> Result<bool, String>,
) -> Result<bool, String> {
    let a = child_bv(expr, child_index, assignment, cache)?;
    let b = child_bv(expr, child_index + 1, assignment, cache)?;
    f(a, b)
}

fn read_bv_const(expr: &ExprView<'_>, width: u32, payload: u64) -> Result<Bv, String> {
    if width > 128 {
        return Err(format!(
            "constant width {width} exceeds exhaustive backend width limit 128"
        ));
    }
    if width <= 64 {
        return Bv::new(width, payload as u128);
    }
    let blob_ref = BlobRef::from_payload(payload);
    let bytes = expr.blob_ref(blob_ref).map_err(|err| err.to_string())?;
    let mut value = 0u128;
    for (index, byte) in bytes.iter().enumerate().take(16) {
        value |= u128::from(*byte) << (index * 8);
    }
    Bv::new(width, value)
}

fn build_model(
    _expr: &ExprView<'_>,
    variables: &[Variable],
    assignment: &Assignment,
) -> smt_wire::Result<ModelBlock> {
    let mut entries = Vec::with_capacity(variables.len());
    for var in variables {
        let value = assignment.get(&var.node_ref.index()).ok_or_else(|| {
            WireError::invalid("model", format!("missing value for variable {var:?}"))
        })?;
        let scalar = match *value {
            Value::Bool(value) => ScalarValue::bool(value),
            Value::Bv(value) => scalar_from_bv(value)?,
        };
        entries.push(ModelEntry {
            node_ref: var.node_ref,
            value: scalar,
        });
    }
    Ok(ModelBlock { entries })
}

fn build_core(expr: &ExprView<'_>, names: &[BlobRef]) -> smt_wire::Result<UnsatCoreBlock> {
    let mut out = Vec::with_capacity(names.len());
    for name in names {
        out.push(expr.blob_str(*name, "unsat core name")?.to_owned());
    }
    Ok(UnsatCoreBlock { names: out })
}

fn scalar_from_bv(value: Bv) -> smt_wire::Result<ScalarValue> {
    let len = (value.width as usize).div_ceil(8);
    let mut bytes = vec![0u8; len];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = ((value.value >> (index * 8)) & 0xff) as u8;
    }
    ScalarValue::bv(value.width, bytes)
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn signed_min_value(width: u32) -> u128 {
    1u128 << (width - 1)
}

fn signed_bounds(width: u32) -> Result<(i128, i128), String> {
    if width >= 128 {
        return Err("signed 128-bit arithmetic is not supported by exhaustive backend".to_owned());
    }
    Ok((-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1))
}

fn to_signed(value: Bv) -> Result<i128, String> {
    if value.width >= 128 {
        return Err("signed 128-bit values are not supported by exhaustive backend".to_owned());
    }
    if !value.sign_bit() {
        Ok(value.value as i128)
    } else {
        Ok((value.value as i128) - (1i128 << value.width))
    }
}

fn from_signed(width: u32, value: i128) -> Result<Bv, String> {
    if width >= 128 {
        return Err("signed 128-bit values are not supported by exhaustive backend".to_owned());
    }
    Bv::new(width, value as u128)
}

fn signed_div(a: Bv, b: Bv) -> Result<Bv, String> {
    if b.value == 0 {
        return Ok(Bv::all_ones(a.width));
    }
    let lhs = to_signed(a)?;
    let rhs = to_signed(b)?;
    let (min, _) = signed_bounds(a.width)?;
    if lhs == min && rhs == -1 {
        return from_signed(a.width, min);
    }
    from_signed(a.width, lhs / rhs)
}

fn signed_rem(a: Bv, b: Bv) -> Result<Bv, String> {
    if b.value == 0 {
        return Ok(a);
    }
    let lhs = to_signed(a)?;
    let rhs = to_signed(b)?;
    let (min, _) = signed_bounds(a.width)?;
    if lhs == min && rhs == -1 {
        return from_signed(a.width, 0);
    }
    from_signed(a.width, lhs % rhs)
}

fn signed_mod(a: Bv, b: Bv) -> Result<Bv, String> {
    if b.value == 0 {
        return Ok(a);
    }
    let lhs = to_signed(a)?;
    let rhs = to_signed(b)?;
    let r = lhs % rhs;
    if r == 0 || (r > 0) == (rhs > 0) {
        from_signed(a.width, r)
    } else {
        from_signed(a.width, r + rhs)
    }
}

fn signed_add_ovf(a: Bv, b: Bv) -> Result<bool, String> {
    let lhs = to_signed(a)?;
    let rhs = to_signed(b)?;
    let (min, max) = signed_bounds(a.width)?;
    let sum = lhs + rhs;
    Ok(sum < min || sum > max)
}

fn signed_sub_ovf(a: Bv, b: Bv) -> Result<bool, String> {
    let lhs = to_signed(a)?;
    let rhs = to_signed(b)?;
    let (min, max) = signed_bounds(a.width)?;
    let diff = lhs - rhs;
    Ok(diff < min || diff > max)
}

fn signed_mul_ovf(a: Bv, b: Bv) -> Result<bool, String> {
    let lhs = to_signed(a)?;
    let rhs = to_signed(b)?;
    let (min, max) = signed_bounds(a.width)?;
    let product = lhs.saturating_mul(rhs);
    Ok(product < min || product > max)
}

fn compare_bv(a: &Bv, b: &Bv, signed: bool) -> Result<std::cmp::Ordering, String> {
    if a.width != b.width {
        return Err(format!("cannot compare widths {} and {}", a.width, b.width));
    }
    if signed {
        Ok(to_signed(*a)?.cmp(&to_signed(*b)?))
    } else {
        Ok(a.value.cmp(&b.value))
    }
}
