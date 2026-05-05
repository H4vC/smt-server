use crate::circuits;
use crate::error::{Error, Result};
use crate::gates::{GateArena, GateId};
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

#[derive(Debug, Clone)]
pub enum BlastedValue {
    Bool(GateId),
    Bv(Vec<GateId>),
}

#[derive(Debug, Clone)]
pub struct BlastedVariable {
    pub term: TermId,
    pub name: String,
    pub external: Option<u32>,
    pub sort: Sort,
    pub bits: Vec<GateId>,
}

#[derive(Debug, Clone)]
pub struct BlastResult {
    pub gates: GateArena,
    pub assertion: GateId,
    pub variables: Vec<BlastedVariable>,
}

pub fn blast_query(query: &Query) -> Result<BlastResult> {
    let mut ctx = BlastContext {
        gates: GateArena::new(),
        values: vec![None; query.arena.len()],
        variables: Vec::new(),
    };

    for (index, node) in query.arena.nodes().iter().enumerate() {
        let id = TermId(index as u32);
        let value = match &node.kind {
            NodeKind::BvConst { width, bytes } => {
                let bits = (0..*width)
                    .map(|bit| {
                        let byte = bytes[(bit / 8) as usize];
                        ctx.gates.const_gate(((byte >> (bit % 8)) & 1) != 0)
                    })
                    .collect();
                BlastedValue::Bv(bits)
            }
            NodeKind::BvVar {
                width,
                name,
                external,
            } => {
                let bits = (0..*width).map(|_| ctx.gates.input()).collect::<Vec<_>>();
                ctx.variables.push(BlastedVariable {
                    term: id,
                    name: name.clone(),
                    external: *external,
                    sort: Sort::Bv(*width),
                    bits: bits.clone(),
                });
                BlastedValue::Bv(bits)
            }
            NodeKind::BoolConst(value) => BlastedValue::Bool(ctx.gates.const_gate(*value)),
            NodeKind::BoolVar { name, external } => {
                let bit = ctx.gates.input();
                ctx.variables.push(BlastedVariable {
                    term: id,
                    name: name.clone(),
                    external: *external,
                    sort: Sort::Bool,
                    bits: vec![bit],
                });
                BlastedValue::Bool(bit)
            }

            NodeKind::BvNot(x) => {
                let x = ctx.bv(*x)?;
                BlastedValue::Bv(circuits::bitwise_not(&mut ctx.gates, &x))
            }
            NodeKind::BvNeg(x) => {
                let x = ctx.bv(*x)?;
                BlastedValue::Bv(circuits::neg(&mut ctx.gates, &x))
            }
            NodeKind::BvAnd(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::bv_and(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvOr(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::bv_or(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvXor(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::bv_xor(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvAdd(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::add(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvSub(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::sub(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvMul(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::mul(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvUDiv(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                let (q, _) = circuits::udiv_urem(&mut ctx.gates, &a, &b);
                BlastedValue::Bv(q)
            }
            NodeKind::BvURem(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                let (_, r) = circuits::udiv_urem(&mut ctx.gates, &a, &b);
                BlastedValue::Bv(r)
            }
            NodeKind::BvSDiv(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::sdiv(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvSRem(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::srem(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvSMod(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::smod(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvShl(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::shl(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvLShr(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::lshr(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvAShr(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bv(circuits::ashr(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvExtract { child, high, low } => {
                let child = ctx.bv(*child)?;
                BlastedValue::Bv(circuits::extract(&child, *high, *low))
            }
            NodeKind::BvConcat(high, low) => {
                let high = ctx.bv(*high)?;
                let low = ctx.bv(*low)?;
                BlastedValue::Bv(circuits::concat(&high, &low))
            }
            NodeKind::BvZeroExtend { child, extra } => {
                let child = ctx.bv(*child)?;
                BlastedValue::Bv(circuits::zext(&ctx.gates, &child, *extra))
            }
            NodeKind::BvSignExtend { child, extra } => {
                let child = ctx.bv(*child)?;
                BlastedValue::Bv(circuits::sext(&child, *extra))
            }
            NodeKind::BvRepeat { child, count } => {
                let child = ctx.bv(*child)?;
                BlastedValue::Bv(circuits::repeat(&child, *count))
            }
            NodeKind::BvRotateLeft { child, amount } => {
                let child = ctx.bv(*child)?;
                BlastedValue::Bv(circuits::rotate_left(&child, *amount))
            }
            NodeKind::BvRotateRight { child, amount } => {
                let child = ctx.bv(*child)?;
                BlastedValue::Bv(circuits::rotate_right(&child, *amount))
            }
            NodeKind::BvIte {
                cond,
                then_value,
                else_value,
            } => {
                let cond = ctx.bool(*cond)?;
                let then_value = ctx.bv(*then_value)?;
                let else_value = ctx.bv(*else_value)?;
                BlastedValue::Bv(circuits::mux_bits(
                    &mut ctx.gates,
                    cond,
                    &then_value,
                    &else_value,
                ))
            }
            NodeKind::BvSelect { cases, default } => {
                let mut result = ctx.bv(*default)?;
                for (selector, value) in cases.iter().rev() {
                    let selector = ctx.bool(*selector)?;
                    let value = ctx.bv(*value)?;
                    result = circuits::mux_bits(&mut ctx.gates, selector, &value, &result);
                }
                BlastedValue::Bv(result)
            }

            NodeKind::BoolNot(x) => {
                let child = ctx.bool(*x)?;
                BlastedValue::Bool(ctx.gates.not(child))
            }
            NodeKind::BoolAnd(a, b) => {
                let av = ctx.bool(*a)?;
                let bv = ctx.bool(*b)?;
                BlastedValue::Bool(ctx.gates.and(av, bv))
            }
            NodeKind::BoolOr(a, b) => {
                let av = ctx.bool(*a)?;
                let bv = ctx.bool(*b)?;
                BlastedValue::Bool(ctx.gates.or(av, bv))
            }
            NodeKind::BoolImplies(a, b) => {
                let av = ctx.bool(*a)?;
                let bv = ctx.bool(*b)?;
                BlastedValue::Bool(ctx.gates.implies(av, bv))
            }
            NodeKind::BoolEq(a, b) => {
                let av = ctx.bool(*a)?;
                let bv = ctx.bool(*b)?;
                BlastedValue::Bool(ctx.gates.xnor(av, bv))
            }
            NodeKind::BoolIte {
                cond,
                then_value,
                else_value,
            } => {
                let c = ctx.bool(*cond)?;
                let t = ctx.bool(*then_value)?;
                let e = ctx.bool(*else_value)?;
                BlastedValue::Bool(ctx.gates.mux(c, t, e))
            }

            NodeKind::BvEq(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::eq_bits(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvUlt(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::ult(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvUle(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::ule(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvSlt(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::slt(&mut ctx.gates, &a, &b))
            }
            NodeKind::BvSle(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::sle(&mut ctx.gates, &a, &b))
            }

            NodeKind::UAddOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::uadd_overflow(&mut ctx.gates, &a, &b))
            }
            NodeKind::SAddOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::sadd_overflow(&mut ctx.gates, &a, &b))
            }
            NodeKind::USubOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::usub_overflow(&mut ctx.gates, &a, &b))
            }
            NodeKind::SSubOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::ssub_overflow(&mut ctx.gates, &a, &b))
            }
            NodeKind::UMulOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::umul_overflow(&mut ctx.gates, &a, &b))
            }
            NodeKind::SMulOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::smul_overflow(&mut ctx.gates, &a, &b))
            }
            NodeKind::NegOverflow(x) => {
                let x = ctx.bv(*x)?;
                BlastedValue::Bool(circuits::neg_overflow(&mut ctx.gates, &x))
            }
            NodeKind::SDivOverflow(a, b) => {
                let a = ctx.bv(*a)?;
                let b = ctx.bv(*b)?;
                BlastedValue::Bool(circuits::sdiv_overflow(&mut ctx.gates, &a, &b))
            }
        };
        ctx.values[index] = Some(value);
    }

    let assertion_bits = query
        .assertions_and_assumptions()
        .map(|root| ctx.bool(root))
        .collect::<Result<Vec<_>>>()?;
    let assertion = ctx.gates.and_many(assertion_bits);
    Ok(BlastResult {
        gates: ctx.gates,
        assertion,
        variables: ctx.variables,
    })
}

struct BlastContext {
    gates: GateArena,
    values: Vec<Option<BlastedValue>>,
    variables: Vec<BlastedVariable>,
}

impl BlastContext {
    fn value(&self, id: TermId) -> Result<&BlastedValue> {
        self.values
            .get(id.index())
            .and_then(Option::as_ref)
            .ok_or_else(|| Error::internal(format!("term {} has not been blasted", id.raw())))
    }

    fn bool(&self, id: TermId) -> Result<GateId> {
        match self.value(id)? {
            BlastedValue::Bool(gate) => Ok(*gate),
            BlastedValue::Bv(_) => Err(Error::internal("expected Bool blasted value")),
        }
    }

    fn bv(&self, id: TermId) -> Result<Vec<GateId>> {
        match self.value(id)? {
            BlastedValue::Bv(bits) => Ok(bits.clone()),
            BlastedValue::Bool(_) => Err(Error::internal("expected BV blasted value")),
        }
    }
}
