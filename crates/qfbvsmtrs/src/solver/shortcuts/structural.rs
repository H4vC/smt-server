use std::collections::HashMap;

use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{collect_bv_equalities_and_disequalities, TermUnion};

#[derive(Debug, Clone, PartialEq, Eq)]
enum BvDefinition {
    Term(TermId),
    Ite {
        cond: TermId,
        then_value: Box<BvDefinition>,
        else_value: Box<BvDefinition>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SigId(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum StructuralSigNode {
    ConstBool(bool),
    ConstBv {
        width: u32,
        bytes: Vec<u8>,
    },
    FreeVar {
        sort: Sort,
        term: TermId,
    },
    Op {
        op: StructuralSigOp,
        children: Vec<SigId>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum StructuralSigOp {
    BvNot,
    BvNeg,
    BvAnd,
    BvOr,
    BvXor,
    BvAdd,
    BvSub,
    BvMul,
    BvUDiv,
    BvURem,
    BvSDiv,
    BvSRem,
    BvSMod,
    BvShl,
    BvLShr,
    BvAShr,
    BvExtract { high: u32, low: u32 },
    BvConcat,
    BvZeroExtend { extra: u32 },
    BvSignExtend { extra: u32 },
    BvRepeat { count: u32 },
    BvRotateLeft { amount: u32 },
    BvRotateRight { amount: u32 },
    BvIte,
    BvSelect,
    BoolNot,
    BoolAnd,
    BoolOr,
    BoolImplies,
    BoolEq,
    BoolIte,
    BvEq,
    BvUlt,
    BvUle,
    BvSlt,
    BvSle,
    UAddOverflow,
    SAddOverflow,
    USubOverflow,
    SSubOverflow,
    UMulOverflow,
    SMulOverflow,
    NegOverflow,
    SDivOverflow,
}

#[derive(Debug, Default)]
struct StructuralSigInterner {
    nodes: Vec<StructuralSigNode>,
    ids: HashMap<StructuralSigNode, SigId>,
}

impl StructuralSigInterner {
    const MAX_NODES: usize = 250_000;

    fn intern(&mut self, node: StructuralSigNode) -> Option<SigId> {
        if let Some(id) = self.ids.get(&node) {
            return Some(*id);
        }
        if self.nodes.len() >= Self::MAX_NODES {
            return None;
        }
        let id = SigId(self.nodes.len());
        self.nodes.push(node.clone());
        self.ids.insert(node, id);
        Some(id)
    }
}

pub(in crate::solver) fn has_structural_definition_contradiction(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 300_000 {
        return Ok(false);
    }
    let mut definitions = HashMap::<TermId, Option<BvDefinition>>::new();
    let mut union = TermUnion::default();
    let mut disequalities = Vec::new();
    for assertion in &query.assertions {
        collect_structural_definitions(query, assertion.root, &mut definitions, &mut union)?;
        collect_bv_equalities_and_disequalities(
            query,
            assertion.root,
            &mut Vec::new(),
            &mut disequalities,
        )?;
    }
    if definitions.is_empty() || disequalities.is_empty() {
        return Ok(false);
    }
    let definitions = definitions
        .into_iter()
        .filter_map(|(var, definition)| definition.map(|definition| (var, definition)))
        .collect::<HashMap<_, _>>();
    let mut interner = StructuralSigInterner::default();
    let mut memo = HashMap::new();
    for (a, b) in disequalities {
        let Some(left) = structural_sig(
            query,
            a,
            &definitions,
            &mut union,
            &mut interner,
            &mut memo,
            &mut Vec::new(),
        )?
        else {
            continue;
        };
        let Some(right) = structural_sig(
            query,
            b,
            &definitions,
            &mut union,
            &mut interner,
            &mut memo,
            &mut Vec::new(),
        )?
        else {
            continue;
        };
        if left == right {
            return Ok(true);
        }
    }
    Ok(false)
}

fn collect_structural_definitions(
    query: &Query,
    term: TermId,
    definitions: &mut HashMap<TermId, Option<BvDefinition>>,
    union: &mut TermUnion,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => {
            if bv_var_term(query, *a)? && bv_var_term(query, *b)? {
                union.union(*a, *b);
            } else {
                record_structural_definition(query, *a, BvDefinition::Term(*b), definitions)?;
                record_structural_definition(query, *b, BvDefinition::Term(*a), definitions)?;
            }
        }
        NodeKind::BoolEq(a, b) if bool_var_term(query, *a)? && bool_var_term(query, *b)? => {
            union.union(*a, *b);
        }
        NodeKind::BoolAnd(a, b) => {
            collect_structural_definitions(query, *a, definitions, union)?;
            collect_structural_definitions(query, *b, definitions, union)?;
        }
        NodeKind::BoolIte { .. } => {
            let mut assignments = HashMap::new();
            collect_implied_bv_assignments(query, term, &mut assignments)?;
            for (var, definition) in assignments {
                record_structural_definition(query, var, definition, definitions)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn record_structural_definition(
    query: &Query,
    var: TermId,
    definition: BvDefinition,
    definitions: &mut HashMap<TermId, Option<BvDefinition>>,
) -> Result<()> {
    if !bv_var_term(query, var)? || bv_definition_is_bare_var(query, &definition)? {
        return Ok(());
    }
    definitions.entry(var).or_insert(Some(definition));
    Ok(())
}

fn collect_implied_bv_assignments(
    query: &Query,
    term: TermId,
    out: &mut HashMap<TermId, BvDefinition>,
) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvEq(a, b) => {
            if bv_var_term(query, *a)? && !bv_var_term(query, *b)? {
                out.entry(*a).or_insert(BvDefinition::Term(*b));
            } else if bv_var_term(query, *b)? && !bv_var_term(query, *a)? {
                out.entry(*b).or_insert(BvDefinition::Term(*a));
            }
        }
        NodeKind::BoolAnd(a, b) => {
            collect_implied_bv_assignments(query, *a, out)?;
            collect_implied_bv_assignments(query, *b, out)?;
        }
        NodeKind::BoolIte {
            cond,
            then_value,
            else_value,
        } => {
            let mut then_assignments = HashMap::new();
            let mut else_assignments = HashMap::new();
            collect_implied_bv_assignments(query, *then_value, &mut then_assignments)?;
            collect_implied_bv_assignments(query, *else_value, &mut else_assignments)?;
            for (var, then_definition) in then_assignments {
                let Some(else_definition) = else_assignments.get(&var).cloned() else {
                    continue;
                };
                out.entry(var).or_insert(BvDefinition::Ite {
                    cond: *cond,
                    then_value: Box::new(then_definition),
                    else_value: Box::new(else_definition),
                });
            }
        }
        _ => {}
    }
    Ok(())
}

fn bv_definition_is_bare_var(query: &Query, definition: &BvDefinition) -> Result<bool> {
    Ok(match definition {
        BvDefinition::Term(term) => bv_var_term(query, *term)?,
        BvDefinition::Ite { .. } => false,
    })
}

fn bv_var_term(query: &Query, term: TermId) -> Result<bool> {
    Ok(matches!(
        query.arena.node(term)?.kind,
        NodeKind::BvVar { .. }
    ))
}

fn bool_var_term(query: &Query, term: TermId) -> Result<bool> {
    Ok(matches!(
        query.arena.node(term)?.kind,
        NodeKind::BoolVar { .. }
    ))
}

fn structural_sig(
    query: &Query,
    term: TermId,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    if let Some(id) = memo.get(&term) {
        return Ok(Some(*id));
    }
    if stack.len() > 256 || stack.contains(&term) {
        return structural_free_var_sig(query, term, union, interner);
    }
    stack.push(term);
    let result = match &query.arena.node(term)?.kind {
        NodeKind::BvVar { .. } => {
            if let Some(definition) = definitions.get(&term).cloned() {
                structural_definition_sig(
                    query,
                    definition,
                    definitions,
                    union,
                    interner,
                    memo,
                    stack,
                )?
            } else {
                structural_free_var_sig(query, term, union, interner)?
            }
        }
        NodeKind::BoolVar { .. } => structural_free_var_sig(query, term, union, interner)?,
        NodeKind::BvConst { width, bytes } => interner.intern(StructuralSigNode::ConstBv {
            width: *width,
            bytes: bytes.clone(),
        }),
        NodeKind::BoolConst(value) => interner.intern(StructuralSigNode::ConstBool(*value)),
        NodeKind::BvNot(child) => structural_unary_sig(
            query,
            StructuralSigOp::BvNot,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvNeg(child) => structural_unary_sig(
            query,
            StructuralSigOp::BvNeg,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvAnd(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvAnd,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvOr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvOr,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvXor(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvXor,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvAdd(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvAdd,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSub(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSub,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvMul(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvMul,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvUDiv(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvUDiv,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvURem(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvURem,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSDiv(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSDiv,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSRem(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSRem,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSMod(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSMod,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvShl(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvShl,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvLShr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvLShr,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvAShr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvAShr,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvExtract { child, high, low } => structural_op_sig(
            query,
            StructuralSigOp::BvExtract {
                high: *high,
                low: *low,
            },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvConcat(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvConcat,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvZeroExtend { child, extra } => structural_op_sig(
            query,
            StructuralSigOp::BvZeroExtend { extra: *extra },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSignExtend { child, extra } => structural_op_sig(
            query,
            StructuralSigOp::BvSignExtend { extra: *extra },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvRepeat { child, count } => structural_op_sig(
            query,
            StructuralSigOp::BvRepeat { count: *count },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvRotateLeft { child, amount } => structural_op_sig(
            query,
            StructuralSigOp::BvRotateLeft { amount: *amount },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvRotateRight { child, amount } => structural_op_sig(
            query,
            StructuralSigOp::BvRotateRight { amount: *amount },
            &[*child],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvIte {
            cond,
            then_value,
            else_value,
        } => structural_op_sig(
            query,
            StructuralSigOp::BvIte,
            &[*cond, *then_value, *else_value],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSelect { cases, default } => {
            let mut children = Vec::with_capacity(cases.len() * 2 + 1);
            for (selector, value) in cases {
                children.push(*selector);
                children.push(*value);
            }
            children.push(*default);
            structural_op_sig(
                query,
                StructuralSigOp::BvSelect,
                &children,
                definitions,
                union,
                interner,
                memo,
                stack,
            )?
        }
        NodeKind::BoolNot(child) => structural_unary_sig(
            query,
            StructuralSigOp::BoolNot,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolAnd(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolAnd,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolOr(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolOr,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolImplies(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolImplies,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolEq(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BoolEq,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BoolIte {
            cond,
            then_value,
            else_value,
        } => structural_op_sig(
            query,
            StructuralSigOp::BoolIte,
            &[*cond, *then_value, *else_value],
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvEq(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvEq,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvUlt(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvUlt,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvUle(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvUle,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSlt(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSlt,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::BvSle(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::BvSle,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::UAddOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::UAddOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SAddOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SAddOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::USubOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::USubOverflow,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SSubOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SSubOverflow,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::UMulOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::UMulOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SMulOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SMulOverflow,
            *a,
            *b,
            true,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::NegOverflow(child) => structural_unary_sig(
            query,
            StructuralSigOp::NegOverflow,
            *child,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
        NodeKind::SDivOverflow(a, b) => structural_binary_sig(
            query,
            StructuralSigOp::SDivOverflow,
            *a,
            *b,
            false,
            definitions,
            union,
            interner,
            memo,
            stack,
        )?,
    };
    stack.pop();
    if let Some(id) = result {
        memo.insert(term, id);
    }
    Ok(result)
}

fn structural_definition_sig(
    query: &Query,
    definition: BvDefinition,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    match definition {
        BvDefinition::Term(term) => {
            structural_sig(query, term, definitions, union, interner, memo, stack)
        }
        BvDefinition::Ite {
            cond,
            then_value,
            else_value,
        } => {
            let Some(cond_id) =
                structural_sig(query, cond, definitions, union, interner, memo, stack)?
            else {
                return Ok(None);
            };
            let Some(then_id) = structural_definition_sig(
                query,
                *then_value,
                definitions,
                union,
                interner,
                memo,
                stack,
            )?
            else {
                return Ok(None);
            };
            let Some(else_id) = structural_definition_sig(
                query,
                *else_value,
                definitions,
                union,
                interner,
                memo,
                stack,
            )?
            else {
                return Ok(None);
            };
            Ok(interner.intern(StructuralSigNode::Op {
                op: StructuralSigOp::BvIte,
                children: vec![cond_id, then_id, else_id],
            }))
        }
    }
}

fn structural_free_var_sig(
    query: &Query,
    term: TermId,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
) -> Result<Option<SigId>> {
    let sort = query.arena.sort(term)?;
    let root = union.find(term);
    Ok(interner.intern(StructuralSigNode::FreeVar { sort, term: root }))
}

#[allow(clippy::too_many_arguments)]
fn structural_unary_sig(
    query: &Query,
    op: StructuralSigOp,
    child: TermId,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    structural_op_sig(
        query,
        op,
        &[child],
        definitions,
        union,
        interner,
        memo,
        stack,
    )
}

#[allow(clippy::too_many_arguments)]
fn structural_binary_sig(
    query: &Query,
    op: StructuralSigOp,
    a: TermId,
    b: TermId,
    commutative: bool,
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    let Some(left) = structural_sig(query, a, definitions, union, interner, memo, stack)? else {
        return Ok(None);
    };
    let Some(right) = structural_sig(query, b, definitions, union, interner, memo, stack)? else {
        return Ok(None);
    };
    let mut children = vec![left, right];
    if commutative {
        children.sort_by_key(|id| id.0);
    }
    Ok(interner.intern(StructuralSigNode::Op { op, children }))
}

#[allow(clippy::too_many_arguments)]
fn structural_op_sig(
    query: &Query,
    op: StructuralSigOp,
    children: &[TermId],
    definitions: &HashMap<TermId, BvDefinition>,
    union: &mut TermUnion,
    interner: &mut StructuralSigInterner,
    memo: &mut HashMap<TermId, SigId>,
    stack: &mut Vec<TermId>,
) -> Result<Option<SigId>> {
    let mut child_ids = Vec::with_capacity(children.len());
    for &child in children {
        let Some(id) = structural_sig(query, child, definitions, union, interner, memo, stack)?
        else {
            return Ok(None);
        };
        child_ids.push(id);
    }
    Ok(interner.intern(StructuralSigNode::Op {
        op,
        children: child_ids,
    }))
}
