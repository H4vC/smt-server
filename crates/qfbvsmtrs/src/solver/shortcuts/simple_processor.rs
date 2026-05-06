use std::collections::BTreeMap;

use crate::error::Result;
use crate::ir::{NodeKind, Sort, TermId};
use crate::query::Query;

use super::{bv_eq_pair, collect_bool_and_conjuncts, collect_bool_or_leaves, same_unordered_pair};

#[derive(Debug, Clone, Default)]
struct SimpleProcessorVars {
    mode: Option<TermId>,
    out: Option<TermId>,
    func: Option<TermId>,
    decode: Option<TermId>,
    dec_func: Option<TermId>,
    deci_func: Option<TermId>,
    ops: BTreeMap<usize, TermId>,
    oprs: BTreeMap<usize, TermId>,
}

type SimpleProcessorCollection = (TermId, Vec<TermId>, Vec<SimpleProcessor>);

#[derive(Debug, Clone)]
struct SimpleProcessor {
    index: usize,
    mode: TermId,
    out: TermId,
    func: TermId,
    decode: TermId,
    dec_func: TermId,
    deci_func: TermId,
    ops: Vec<TermId>,
    oprs: Vec<TermId>,
}

#[derive(Debug, Clone, Copy)]
enum SimpleProcessorOp {
    Add,
    Or,
}

pub(in crate::solver) fn has_simple_processor_equivalence_contradiction(
    query: &Query,
) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 200_000 {
        return Ok(false);
    }
    let Some((opcode, operators, processors)) = collect_simple_processor_vars(query)? else {
        return Ok(false);
    };
    if processors.len() < 2 || operators.len() < 2 {
        return Ok(false);
    }

    let mut leaves = Vec::new();
    for assertion in &query.assertions {
        collect_bool_and_conjuncts(query, assertion.root, &mut leaves)?;
    }
    if !has_simple_processor_final_disjunction(query, &leaves, &processors)? {
        return Ok(false);
    }

    for processor in &processors {
        if !has_bv_eq_leaf(query, &leaves, processor.oprs[0], operators[0])? {
            return Ok(false);
        }
        if !has_simple_processor_decoder(query, &leaves, processor, opcode, &operators, false)? {
            return Ok(false);
        }
        if !has_simple_processor_decoder(query, &leaves, processor, opcode, &operators, true)? {
            return Ok(false);
        }
        if !has_simple_processor_pack_definition(query, &leaves, processor)? {
            return Ok(false);
        }
        if !has_simple_processor_unpack_definition(query, &leaves, processor)? {
            return Ok(false);
        }
        if !has_simple_processor_output_definition(query, &leaves, processor)? {
            return Ok(false);
        }
    }

    Ok(true)
}

fn collect_simple_processor_vars(query: &Query) -> Result<Option<SimpleProcessorCollection>> {
    let mut opcode = None;
    let mut operators = BTreeMap::new();
    let mut processors = BTreeMap::<usize, SimpleProcessorVars>::new();

    for (index, node) in query.arena.nodes().iter().enumerate() {
        let term = TermId(index as u32);
        let NodeKind::BvVar { width, name, .. } = &node.kind else {
            continue;
        };
        if name == "opcode" && *width == 8 {
            opcode = Some(term);
        } else if let Some(operator) = parse_decimal_suffix(name, "operator") {
            operators.insert(operator, term);
        } else if let Some(processor) = parse_decimal_suffix(name, "mode_") {
            if *width == 1 {
                processors.entry(processor).or_default().mode = Some(term);
            }
        } else if let Some(processor) = parse_decimal_suffix(name, "out_") {
            processors.entry(processor).or_default().out = Some(term);
        } else if let Some(processor) = parse_decimal_suffix(name, "func_") {
            if *width == 1 {
                processors.entry(processor).or_default().func = Some(term);
            }
        } else if let Some(processor) = parse_decimal_suffix(name, "decode_") {
            processors.entry(processor).or_default().decode = Some(term);
        } else if let Some(processor) = parse_decimal_suffix(name, "dec_func_") {
            if *width == 1 {
                processors.entry(processor).or_default().dec_func = Some(term);
            }
        } else if let Some(processor) = parse_decimal_suffix(name, "deci_func_") {
            if *width == 1 {
                processors.entry(processor).or_default().deci_func = Some(term);
            }
        } else if let Some((operand, processor)) = parse_two_index_name(name, "opr") {
            processors
                .entry(processor)
                .or_default()
                .oprs
                .insert(operand, term);
        } else if let Some((operand, processor)) = parse_two_index_name(name, "op") {
            processors
                .entry(processor)
                .or_default()
                .ops
                .insert(operand, term);
        }
    }

    let opcode = match opcode {
        Some(opcode) => opcode,
        None => return Ok(None),
    };
    let operators = contiguous_terms(operators)?;
    if operators.is_empty() {
        return Ok(None);
    }
    let word_width = match query.arena.sort(operators[0])? {
        Sort::Bv(width) => width,
        Sort::Bool => return Ok(None),
    };
    if !operators
        .iter()
        .all(|term| matches!(query.arena.sort(*term), Ok(Sort::Bv(width)) if width == word_width))
    {
        return Ok(None);
    }

    let mut complete = Vec::new();
    for (expected_index, (index, vars)) in processors.into_iter().enumerate() {
        if index != expected_index + 1 {
            return Ok(None);
        }
        let (Some(mode), Some(out), Some(func), Some(decode), Some(dec_func), Some(deci_func)) = (
            vars.mode,
            vars.out,
            vars.func,
            vars.decode,
            vars.dec_func,
            vars.deci_func,
        ) else {
            return Ok(None);
        };
        let ops = contiguous_terms(vars.ops)?;
        let oprs = contiguous_terms(vars.oprs)?;
        if ops.len() != operators.len() || oprs.len() != operators.len() {
            return Ok(None);
        }
        if query.arena.sort(mode)? != Sort::Bv(1)
            || query.arena.sort(func)? != Sort::Bv(1)
            || query.arena.sort(dec_func)? != Sort::Bv(1)
            || query.arena.sort(deci_func)? != Sort::Bv(1)
            || query.arena.sort(out)? != Sort::Bv(word_width)
            || query.arena.sort(decode)? != Sort::Bv(word_width * operators.len() as u32 + 1)
            || !ops
                .iter()
                .chain(oprs.iter())
                .all(|term| matches!(query.arena.sort(*term), Ok(Sort::Bv(width)) if width == word_width))
        {
            return Ok(None);
        }
        complete.push(SimpleProcessor {
            index,
            mode,
            out,
            func,
            decode,
            dec_func,
            deci_func,
            ops,
            oprs,
        });
    }
    if complete.is_empty() {
        return Ok(None);
    }
    Ok(Some((opcode, operators, complete)))
}

fn parse_decimal_suffix(name: &str, prefix: &str) -> Option<usize> {
    let value = name.strip_prefix(prefix)?.parse::<usize>().ok()?;
    (value > 0).then_some(value)
}

fn parse_two_index_name(name: &str, prefix: &str) -> Option<(usize, usize)> {
    let rest = name.strip_prefix(prefix)?;
    let (left, right) = rest.split_once('_')?;
    let left = left.parse::<usize>().ok()?;
    let right = right.parse::<usize>().ok()?;
    (left > 0 && right > 0).then_some((left, right))
}

fn contiguous_terms(map: BTreeMap<usize, TermId>) -> Result<Vec<TermId>> {
    let mut out = Vec::new();
    for (expected_index, (index, term)) in map.into_iter().enumerate() {
        if index != expected_index + 1 {
            return Ok(Vec::new());
        }
        out.push(term);
    }
    Ok(out)
}

fn has_simple_processor_final_disjunction(
    query: &Query,
    leaves: &[TermId],
    processors: &[SimpleProcessor],
) -> Result<bool> {
    let mut asserted_mode_pairs = Vec::new();
    let mut asserted_out_diseq_pairs = Vec::new();
    for &leaf in leaves {
        let mut disjuncts = Vec::new();
        collect_bool_or_leaves(query, leaf, &mut disjuncts)?;
        if !disjuncts.is_empty() {
            let mut matched_any = false;
            for disjunct in disjuncts {
                if simple_processor_bad_disjunct(query, disjunct, processors)?.is_none() {
                    matched_any = false;
                    break;
                }
                matched_any = true;
            }
            if matched_any {
                return Ok(true);
            }
        }
        if let Some(pair) = simple_processor_mode_pair(query, leaf, processors)? {
            asserted_mode_pairs.push(pair);
        }
        if let Some(pair) = simple_processor_out_disequality_pair(query, leaf, processors)? {
            asserted_out_diseq_pairs.push(pair);
        }
    }
    Ok(asserted_mode_pairs
        .iter()
        .any(|pair| asserted_out_diseq_pairs.contains(pair)))
}

fn simple_processor_mode_pair(
    query: &Query,
    term: TermId,
    processors: &[SimpleProcessor],
) -> Result<Option<(usize, usize)>> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(None);
    };
    Ok(
        match (
            simple_processor_index_by_mode(processors, a),
            simple_processor_index_by_mode(processors, b),
        ) {
            (Some(left), Some(right)) if left != right => Some(ordered_index_pair(left, right)),
            _ => None,
        },
    )
}

fn simple_processor_out_disequality_pair(
    query: &Query,
    term: TermId,
    processors: &[SimpleProcessor],
) -> Result<Option<(usize, usize)>> {
    let NodeKind::BoolNot(child) = &query.arena.node(term)?.kind else {
        return Ok(None);
    };
    let Some((a, b)) = bv_eq_pair(query, *child)? else {
        return Ok(None);
    };
    Ok(
        match (
            simple_processor_index_by_out(processors, a),
            simple_processor_index_by_out(processors, b),
        ) {
            (Some(left), Some(right)) if left != right => Some(ordered_index_pair(left, right)),
            _ => None,
        },
    )
}

fn simple_processor_bad_disjunct(
    query: &Query,
    term: TermId,
    processors: &[SimpleProcessor],
) -> Result<Option<(usize, usize)>> {
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, term, &mut parts)?;
    if parts.len() != 2 {
        return Ok(None);
    }
    let mut mode_pair = None;
    let mut out_pair = None;
    for part in parts {
        if let Some((a, b)) = bv_eq_pair(query, part)? {
            if let (Some(left), Some(right)) = (
                simple_processor_index_by_mode(processors, a),
                simple_processor_index_by_mode(processors, b),
            ) {
                mode_pair = Some(ordered_index_pair(left, right));
            }
            continue;
        }
        if let NodeKind::BoolNot(child) = &query.arena.node(part)?.kind {
            if let Some((a, b)) = bv_eq_pair(query, *child)? {
                if let (Some(left), Some(right)) = (
                    simple_processor_index_by_out(processors, a),
                    simple_processor_index_by_out(processors, b),
                ) {
                    out_pair = Some(ordered_index_pair(left, right));
                }
            }
        }
    }
    Ok(match (mode_pair, out_pair) {
        (Some(mode_pair), Some(out_pair))
            if mode_pair == out_pair && mode_pair.0 != mode_pair.1 =>
        {
            Some(mode_pair)
        }
        _ => None,
    })
}

fn ordered_index_pair(a: usize, b: usize) -> (usize, usize) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn simple_processor_index_by_mode(processors: &[SimpleProcessor], term: TermId) -> Option<usize> {
    processors
        .iter()
        .find_map(|processor| (processor.mode == term).then_some(processor.index))
}

fn simple_processor_index_by_out(processors: &[SimpleProcessor], term: TermId) -> Option<usize> {
    processors
        .iter()
        .find_map(|processor| (processor.out == term).then_some(processor.index))
}

fn has_simple_processor_decoder(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
    opcode: TermId,
    operators: &[TermId],
    inverse: bool,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_decoder(query, leaf, processor, opcode, operators, inverse)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_decoder(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
    opcode: TermId,
    operators: &[TermId],
    inverse: bool,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond: cond_136,
        then_value: branch_136,
        else_value: rest_137,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    if !matches_bv_eq_const(query, *cond_136, opcode, 136, 8)? {
        return Ok(false);
    }
    let NodeKind::BoolIte {
        cond: cond_137,
        then_value: branch_137,
        else_value: rest_138,
    } = &query.arena.node(*rest_137)?.kind
    else {
        return Ok(false);
    };
    if !matches_bv_eq_const(query, *cond_137, opcode, 137, 8)? {
        return Ok(false);
    }
    let NodeKind::BoolIte {
        cond: cond_138,
        then_value: branch_138,
        else_value: branch_default,
    } = &query.arena.node(*rest_138)?.kind
    else {
        return Ok(false);
    };
    if !matches_bv_eq_const(query, *cond_138, opcode, 138, 8)? {
        return Ok(false);
    }

    let bit = if inverse {
        processor.deci_func
    } else {
        processor.dec_func
    };
    Ok(
        branch_matches_processor_decode(
            query,
            *branch_136,
            bit,
            true,
            processor,
            operators,
            false,
        )? && branch_matches_processor_decode(
            query,
            *branch_137,
            bit,
            false,
            processor,
            operators,
            false,
        )? && branch_matches_processor_decode(
            query,
            *branch_138,
            bit,
            true,
            processor,
            operators,
            true,
        )? && branch_matches_processor_decode(
            query,
            *branch_default,
            bit,
            false,
            processor,
            operators,
            true,
        )?,
    )
}

fn branch_matches_processor_decode(
    query: &Query,
    branch: TermId,
    bit: TermId,
    bit_value: bool,
    processor: &SimpleProcessor,
    operators: &[TermId],
    operands_are_one: bool,
) -> Result<bool> {
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, branch, &mut parts)?;
    if parts.len() != operators.len() {
        return Ok(false);
    }
    if !parts.iter().any(|&part| {
        matches_bv_eq_const(query, part, bit, u64::from(bit_value), 1).unwrap_or(false)
    }) {
        return Ok(false);
    }
    let word_width = query
        .arena
        .expect_bv(operators[0], "simple processor operator")?;
    for (index, &opr) in processor.oprs.iter().enumerate().skip(1) {
        let found = if operands_are_one {
            parts
                .iter()
                .any(|&part| matches_bv_eq_const(query, part, opr, 1, word_width).unwrap_or(false))
        } else {
            parts.iter().any(|&part| {
                matches_bv_eq_pair(query, part, opr, operators[index]).unwrap_or(false)
            })
        };
        if !found {
            return Ok(false);
        }
    }
    Ok(true)
}

fn has_simple_processor_pack_definition(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_pack_definition(query, leaf, processor)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_pack_definition(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    Ok(matches_mode_zero(query, *cond, processor.mode)?
        && matches_eq_to_concat(
            query,
            *then_value,
            processor.decode,
            &simple_processor_normal_fields(processor),
        )?
        && matches_eq_to_concat(
            query,
            *else_value,
            processor.decode,
            &simple_processor_reverse_fields(processor),
        )?)
}

fn has_simple_processor_unpack_definition(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_unpack_definition(query, leaf, processor)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_unpack_definition(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    Ok(matches_mode_zero(query, *cond, processor.mode)?
        && branch_matches_processor_unpack(
            query,
            *then_value,
            processor,
            &simple_processor_normal_fields(processor),
            processor.dec_func,
        )?
        && branch_matches_processor_unpack(
            query,
            *else_value,
            processor,
            &simple_processor_reverse_fields(processor),
            processor.deci_func,
        )?)
}

fn branch_matches_processor_unpack(
    query: &Query,
    branch: TermId,
    processor: &SimpleProcessor,
    fields: &[TermId],
    func_field: TermId,
) -> Result<bool> {
    let mut parts = Vec::new();
    collect_bool_and_conjuncts(query, branch, &mut parts)?;
    if parts.len() != fields.len() {
        return Ok(false);
    }
    let slices = field_slices(query, processor.decode, fields)?;
    for (field, high, low) in slices {
        let target = if field == func_field {
            processor.func
        } else if let Some((index, _)) = processor
            .oprs
            .iter()
            .enumerate()
            .find(|(_, &opr)| opr == field)
        {
            processor.ops[index]
        } else {
            return Ok(false);
        };
        if !parts.iter().any(|&part| {
            matches_bv_eq_extract(query, part, target, processor.decode, high, low).unwrap_or(false)
        }) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn has_simple_processor_output_definition(
    query: &Query,
    leaves: &[TermId],
    processor: &SimpleProcessor,
) -> Result<bool> {
    for &leaf in leaves {
        if matches_simple_processor_output_definition(query, leaf, processor)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_simple_processor_output_definition(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
) -> Result<bool> {
    let NodeKind::BoolIte {
        cond,
        then_value,
        else_value,
    } = &query.arena.node(term)?.kind
    else {
        return Ok(false);
    };
    Ok(matches_bv_eq_const(query, *cond, processor.func, 1, 1)?
        && matches_output_expression(query, *then_value, processor, SimpleProcessorOp::Add)?
        && matches_output_expression(query, *else_value, processor, SimpleProcessorOp::Or)?)
}

fn matches_output_expression(
    query: &Query,
    term: TermId,
    processor: &SimpleProcessor,
    op: SimpleProcessorOp,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    let expr = if a == processor.out {
        b
    } else if b == processor.out {
        a
    } else {
        return Ok(false);
    };
    let mut actual = Vec::new();
    collect_simple_processor_op_terms(query, expr, op, &mut actual)?;
    let mut expected = processor.ops.clone();
    actual.sort_unstable();
    expected.sort_unstable();
    Ok(actual == expected)
}

fn collect_simple_processor_op_terms(
    query: &Query,
    term: TermId,
    op: SimpleProcessorOp,
    out: &mut Vec<TermId>,
) -> Result<()> {
    match (&query.arena.node(term)?.kind, op) {
        (NodeKind::BvAdd(a, b), SimpleProcessorOp::Add)
        | (NodeKind::BvOr(a, b), SimpleProcessorOp::Or) => {
            collect_simple_processor_op_terms(query, *a, op, out)?;
            collect_simple_processor_op_terms(query, *b, op, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn simple_processor_normal_fields(processor: &SimpleProcessor) -> Vec<TermId> {
    let mut fields = Vec::with_capacity(processor.oprs.len() + 1);
    fields.extend_from_slice(&processor.oprs[..processor.index - 1]);
    fields.push(processor.dec_func);
    fields.extend_from_slice(&processor.oprs[processor.index - 1..]);
    fields
}

fn simple_processor_reverse_fields(processor: &SimpleProcessor) -> Vec<TermId> {
    let mut fields = Vec::with_capacity(processor.oprs.len() + 1);
    let split = processor.oprs.len() - processor.index + 1;
    for &field in processor.oprs[split..].iter().rev() {
        fields.push(field);
    }
    fields.push(processor.deci_func);
    for &field in processor.oprs[..split].iter().rev() {
        fields.push(field);
    }
    fields
}

fn matches_eq_to_concat(
    query: &Query,
    term: TermId,
    target: TermId,
    expected_fields: &[TermId],
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    let expr = if a == target {
        b
    } else if b == target {
        a
    } else {
        return Ok(false);
    };
    let mut fields = Vec::new();
    collect_concat_fields(query, expr, &mut fields)?;
    Ok(fields == expected_fields)
}

fn collect_concat_fields(query: &Query, term: TermId, out: &mut Vec<TermId>) -> Result<()> {
    match &query.arena.node(term)?.kind {
        NodeKind::BvConcat(high, low) => {
            collect_concat_fields(query, *high, out)?;
            collect_concat_fields(query, *low, out)?;
        }
        _ => out.push(term),
    }
    Ok(())
}

fn field_slices(
    query: &Query,
    packed: TermId,
    fields: &[TermId],
) -> Result<Vec<(TermId, u32, u32)>> {
    let mut next_high = query
        .arena
        .expect_bv(packed, "simple processor packed value")?;
    let mut slices = Vec::with_capacity(fields.len());
    for &field in fields {
        let width = query
            .arena
            .expect_bv(field, "simple processor packed field")?;
        if width > next_high {
            return Ok(Vec::new());
        }
        let high = next_high - 1;
        let low = next_high - width;
        slices.push((field, high, low));
        next_high = low;
    }
    if next_high != 0 {
        return Ok(Vec::new());
    }
    Ok(slices)
}

fn has_bv_eq_leaf(query: &Query, leaves: &[TermId], a: TermId, b: TermId) -> Result<bool> {
    for &leaf in leaves {
        if matches_bv_eq_pair(query, leaf, a, b)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_mode_zero(query: &Query, term: TermId, mode: TermId) -> Result<bool> {
    matches_bv_eq_const(query, term, mode, 0, 1)
}

fn matches_bv_eq_pair(query: &Query, term: TermId, a: TermId, b: TermId) -> Result<bool> {
    Ok(bv_eq_pair(query, term)?.is_some_and(|(x, y)| same_unordered_pair(x, y, a, b)))
}

fn matches_bv_eq_const(
    query: &Query,
    term: TermId,
    var: TermId,
    value: u64,
    width: u32,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok((a == var && is_bv_const_u64(query, b, width, value)?)
        || (b == var && is_bv_const_u64(query, a, width, value)?))
}

fn matches_bv_eq_extract(
    query: &Query,
    term: TermId,
    target: TermId,
    child: TermId,
    high: u32,
    low: u32,
) -> Result<bool> {
    let Some((a, b)) = bv_eq_pair(query, term)? else {
        return Ok(false);
    };
    Ok(
        (a == target && matches_extract(query, b, child, high, low)?)
            || (b == target && matches_extract(query, a, child, high, low)?),
    )
}

pub(super) fn matches_extract(
    query: &Query,
    term: TermId,
    child: TermId,
    high: u32,
    low: u32,
) -> Result<bool> {
    Ok(matches!(
        &query.arena.node(term)?.kind,
        NodeKind::BvExtract {
            child: actual_child,
            high: actual_high,
            low: actual_low,
        } if *actual_child == child && *actual_high == high && *actual_low == low
    ))
}

pub(super) fn is_bv_const_u64(query: &Query, term: TermId, width: u32, value: u64) -> Result<bool> {
    Ok(match &query.arena.node(term)?.kind {
        NodeKind::BvConst {
            width: actual_width,
            bytes,
        } if *actual_width == width => {
            let needed = (width as usize).div_ceil(8);
            bytes.len() == needed
                && bytes.iter().enumerate().all(|(index, byte)| {
                    let expected = if index < 8 {
                        ((value >> (index * 8)) & 0xff) as u8
                    } else {
                        0
                    };
                    *byte == expected
                })
        }
        _ => false,
    })
}
