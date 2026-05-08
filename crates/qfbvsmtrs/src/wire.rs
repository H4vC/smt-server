#![cfg(feature = "wire")]

use std::collections::HashMap;

use crate::builder::Builder;
use crate::error::{Error, Result};
use crate::ir::TermId;
use crate::model::{Model, ScalarValue as QScalarValue};
use crate::query::{Command as QCommand, Query};

use smt_wire::raw::{
    request_flags, tag, BinaryRequest, BlobRef, Command, ExprView, ModelBlock, ModelEntry, NodeRef,
    RawNode, ScalarValue,
};

pub fn query_from_wire(request: &BinaryRequest) -> Result<Query> {
    let expr = request
        .expression_view()
        .map_err(|err| Error::invalid("smt-wire expression", err.to_string()))?;
    let mut builder = Builder::new();
    let mut terms = vec![None; expr.node_count() as usize];
    let mut bv_vars = HashMap::<(String, u32), TermId>::new();
    let mut bool_vars = HashMap::<String, TermId>::new();

    for index in 0..expr.node_count() {
        let node = expr
            .node(index)
            .map_err(|err| Error::invalid("smt-wire node", err.to_string()))?;
        let term = match node.tag {
            tag::BV_VAR => {
                let name = expr
                    .blob_str(BlobRef::from_payload(node.payload), "BV variable")
                    .map_err(|err| Error::invalid("smt-wire BV variable", err.to_string()))?
                    .to_owned();
                if let Some(term) = bv_vars.get(&(name.clone(), node.width)).copied() {
                    term
                } else {
                    let term = builder.bv_var_external(
                        &name,
                        node.width,
                        Some(
                            NodeRef::bv(index)
                                .map_err(|err| Error::invalid("node ref", err.to_string()))?
                                .raw(),
                        ),
                    )?;
                    bv_vars.insert((name, node.width), term);
                    term
                }
            }
            tag::BOOL_VAR => {
                let name = expr
                    .blob_str(BlobRef::from_payload(node.payload), "Bool variable")
                    .map_err(|err| Error::invalid("smt-wire Bool variable", err.to_string()))?
                    .to_owned();
                if let Some(term) = bool_vars.get(&name).copied() {
                    term
                } else {
                    let term = builder.bool_var_external(
                        &name,
                        Some(
                            NodeRef::bool(index)
                                .map_err(|err| Error::invalid("node ref", err.to_string()))?
                                .raw(),
                        ),
                    )?;
                    bool_vars.insert(name, term);
                    term
                }
            }
            tag::BV_CONST => {
                let bytes = bv_const_bytes(&expr, node.width, node.payload)?;
                builder.bv_const_bytes(&bytes, node.width)?
            }
            tag::BOOL_TRUE => builder.bool_true()?,
            tag::BOOL_FALSE => builder.bool_false()?,

            tag::BV_NOT => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.bv_not(x)?
            }
            tag::BV_NEG => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.bv_neg(x)?
            }
            tag::BV_AND => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_and(a, b)?
            }
            tag::BV_OR => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_or(a, b)?
            }
            tag::BV_XOR => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_xor(a, b)?
            }
            tag::BV_ADD => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_add(a, b)?
            }
            tag::BV_SUB => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_sub(a, b)?
            }
            tag::BV_MUL => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_mul(a, b)?
            }
            tag::BV_UDIV => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_udiv(a, b)?
            }
            tag::BV_UREM => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_urem(a, b)?
            }
            tag::BV_SDIV => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_sdiv(a, b)?
            }
            tag::BV_SREM => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_srem(a, b)?
            }
            tag::BV_SMOD => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_smod(a, b)?
            }
            tag::BV_SHL => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_shl(a, b)?
            }
            tag::BV_LSHR => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_lshr(a, b)?
            }
            tag::BV_ASHR => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_ashr(a, b)?
            }
            tag::BV_EXTRACT => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.bv_extract(x, u32::from(node.aux_hi), node.aux_lo)?
            }
            tag::BV_CONCAT => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_concat(a, b)?
            }
            tag::BV_ZEXT => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.bv_zext(x, u32::from(node.aux_hi))?
            }
            tag::BV_SEXT => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.bv_sext(x, u32::from(node.aux_hi))?
            }
            tag::BV_ITE => {
                let c = child(&expr, &terms, &node, 0)?;
                let t = child(&expr, &terms, &node, 1)?;
                let e = child(&expr, &terms, &node, 2)?;
                builder.bv_ite(c, t, e)?
            }
            tag::BV_SELECT => {
                let pairs = u32::from(node.aux_hi);
                let mut cases = Vec::with_capacity(pairs as usize);
                for pair in 0..pairs {
                    let selector = child(&expr, &terms, &node, pair * 2)?;
                    let value = child(&expr, &terms, &node, pair * 2 + 1)?;
                    cases.push((selector, value));
                }
                let default = child(&expr, &terms, &node, pairs * 2)?;
                builder.bv_select(&cases, default)?
            }

            tag::BOOL_NOT => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.bool_not(x)?
            }
            tag::BOOL_AND => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bool_and(a, b)?
            }
            tag::BOOL_OR => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bool_or(a, b)?
            }
            tag::BOOL_IMPLIES => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bool_implies(a, b)?
            }
            tag::BV_EQ => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_eq(a, b)?
            }
            tag::BV_ULT => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_ult(a, b)?
            }
            tag::BV_ULE => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_ule(a, b)?
            }
            tag::BV_SLT => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_slt(a, b)?
            }
            tag::BV_SLE => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.bv_sle(a, b)?
            }
            tag::UADD_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.uadd_ovf(a, b)?
            }
            tag::SADD_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.sadd_ovf(a, b)?
            }
            tag::USUB_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.usub_ovf(a, b)?
            }
            tag::SSUB_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.ssub_ovf(a, b)?
            }
            tag::UMUL_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.umul_ovf(a, b)?
            }
            tag::SMUL_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.smul_ovf(a, b)?
            }
            tag::NEG_OVF => {
                let x = child(&expr, &terms, &node, 0)?;
                builder.neg_ovf(x)?
            }
            tag::SDIV_OVF => {
                let (a, b) = child2(&expr, &terms, &node)?;
                builder.sdiv_ovf(a, b)?
            }
            other => return Err(Error::unsupported(format!("smt-wire tag {other}"))),
        };
        terms[index as usize] = Some(term);
    }

    builder.set_want_model((request.envelope.flags & request_flags::WANT_MODEL) != 0);
    builder.set_want_core((request.envelope.flags & request_flags::WANT_CORE) != 0);

    match request.envelope.command {
        Command::Solve => builder.set_command(QCommand::Solve),
        Command::Simplify => builder.set_command(QCommand::Simplify),
        Command::Minimize | Command::Maximize => {
            let target_ref = request
                .target_ref()
                .ok_or_else(|| Error::invalid("wire target", "missing target node"))?;
            let target = term_for_ref(&terms, target_ref)?;
            let signed = (request.envelope.flags & request_flags::SIGNED) != 0;
            let command = if request.envelope.command == Command::Minimize {
                QCommand::Minimize
            } else {
                QCommand::Maximize
            };
            builder.set_optimization(command, target, signed)?;
        }
    }

    for (index, root) in request.assertion_roots.iter().enumerate() {
        let term = term_for_ref(&terms, *root)?;
        if index < request.named_assertion_refs.len() {
            let name = expr
                .blob_str(request.named_assertion_refs[index], "named assertion")
                .map_err(|err| Error::invalid("named assertion", err.to_string()))?;
            builder.assert_named(name, term)?;
        } else {
            builder.assert(term)?;
        }
    }
    for root in &request.assumption_roots {
        builder.assume(term_for_ref(&terms, *root)?)?;
    }

    builder.finish()
}

pub fn model_to_wire(model: &Model) -> Result<ModelBlock> {
    let mut entries = Vec::with_capacity(model.entries.len());
    for entry in &model.entries {
        let Some(raw_ref) = entry.external else {
            continue;
        };
        let value = match &entry.value {
            QScalarValue::Bool(value) => ScalarValue::bool(*value),
            QScalarValue::Bv { width, bytes } => ScalarValue::bv(*width, bytes.clone())
                .map_err(|err| Error::invalid("wire model value", err.to_string()))?,
        };
        entries.push(ModelEntry {
            node_ref: NodeRef::from_raw(raw_ref),
            value,
        });
    }
    Ok(ModelBlock { entries })
}

fn child(
    expr: &ExprView<'_>,
    terms: &[Option<TermId>],
    node: &RawNode,
    offset: u32,
) -> Result<TermId> {
    let reference = expr
        .child_ref(node.children + offset)
        .map_err(|err| Error::invalid("child reference", err.to_string()))?;
    term_for_ref(terms, reference)
}

fn child2(
    expr: &ExprView<'_>,
    terms: &[Option<TermId>],
    node: &RawNode,
) -> Result<(TermId, TermId)> {
    Ok((child(expr, terms, node, 0)?, child(expr, terms, node, 1)?))
}

fn term_for_ref(terms: &[Option<TermId>], reference: NodeRef) -> Result<TermId> {
    terms
        .get(reference.index() as usize)
        .copied()
        .flatten()
        .ok_or_else(|| Error::invalid("node reference", format!("missing term for {reference:?}")))
}

fn bv_const_bytes(expr: &ExprView<'_>, width: u32, payload: u64) -> Result<Vec<u8>> {
    let len = (width as usize).div_ceil(8);
    if width <= 64 {
        let mut bytes = payload.to_le_bytes().to_vec();
        bytes.truncate(len);
        return Ok(bytes);
    }
    expr.blob_ref(BlobRef::from_payload(payload))
        .map(|bytes| bytes.to_vec())
        .map_err(|err| Error::invalid("wide BV const", err.to_string()))
}
