use std::collections::BTreeMap;

use crate::error::Result;
use crate::ir::{NodeKind, TermId};
use crate::query::Query;

use super::mask_for_width;

pub(in crate::solver) fn has_constant_assignment_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 300_000 {
        return Ok(false);
    }
    if crate::eval::query_satisfied_by_constant_assignment(query, false)?
        || crate::eval::query_satisfied_by_constant_assignment(query, true)?
    {
        return Ok(true);
    }
    if !small_enough_for_seeded_witness(query)? {
        return Ok(false);
    }
    for seed in [
        0x243f_6a88_85a3_08d3,
        0x1319_8a2e_0370_7344,
        0xa409_3822_299f_31d0,
        0x082e_fa98_ec4e_6c89,
        0x4528_21e6_38d0_1377,
        0xbe54_66cf_34e9_0c6c,
        0xc0ac_29b7_c97c_50dd,
        0x3f84_d5b5_b547_0917,
    ] {
        if crate::eval::query_satisfied_by_seeded_assignment(query, seed)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(in crate::solver) fn has_small_explicit_assignment_witness(query: &Query) -> Result<bool> {
    if !query.assumptions.is_empty() || query.arena.len() > 10_000 {
        return Ok(false);
    }
    let mut vars = Vec::new();
    for (index, node) in query.arena.nodes().iter().enumerate() {
        match node.kind {
            NodeKind::BvVar { width, .. } if width <= 64 => {
                vars.push((TermId(index as u32), width));
            }
            NodeKind::BoolVar { .. } => return Ok(false),
            NodeKind::BvVar { .. } => return Ok(false),
            _ => {}
        }
    }
    if vars.is_empty() || vars.len() > 3 {
        return Ok(false);
    }
    let candidates = vars
        .iter()
        .map(|&(_, width)| explicit_assignment_candidates(width))
        .collect::<Vec<_>>();
    let product = candidates
        .iter()
        .map(Vec::len)
        .try_fold(1usize, |acc, len| acc.checked_mul(len))
        .unwrap_or(usize::MAX);
    if product > 20_000 {
        return Ok(false);
    }
    let mut assignment = BTreeMap::new();
    explicit_assignment_search(query, &vars, &candidates, 0, &mut assignment)
}

fn small_enough_for_seeded_witness(query: &Query) -> Result<bool> {
    let mut bits = 0u64;
    for node in query.arena.nodes() {
        match node.kind {
            NodeKind::BvVar { width, .. } => bits = bits.saturating_add(u64::from(width)),
            NodeKind::BoolVar { .. } => bits = bits.saturating_add(1),
            _ => {}
        }
        if bits > 4096 {
            return Ok(false);
        }
    }
    Ok(query.arena.len() <= 20_000)
}

fn explicit_assignment_search(
    query: &Query,
    vars: &[(TermId, u32)],
    candidates: &[Vec<u64>],
    index: usize,
    assignment: &mut BTreeMap<TermId, Vec<u8>>,
) -> Result<bool> {
    if index == vars.len() {
        return crate::eval::query_satisfied_by_bv_assignment(query, assignment);
    }
    let (var, width) = vars[index];
    for &value in &candidates[index] {
        assignment.insert(var, bytes_from_u64(width, value)?);
        if explicit_assignment_search(query, vars, candidates, index + 1, assignment)? {
            return Ok(true);
        }
    }
    assignment.remove(&var);
    Ok(false)
}

fn explicit_assignment_candidates(width: u32) -> Vec<u64> {
    let mask = mask_for_width(width);
    let mut values = vec![
        0,
        1,
        2,
        3,
        4,
        7,
        8,
        15,
        16,
        31,
        32,
        63,
        64,
        0x7f,
        0x80,
        0xff,
        0x100,
        0xffff,
        0x1_0000,
        0x1000_0000,
        0x1000_0001,
        0x4000_0000,
        0x8000_0000,
        u64::MAX,
    ];
    if width > 1 {
        values.push(1u64 << ((width - 1).min(63)));
    }
    values.iter_mut().for_each(|value| *value &= mask);
    values.sort_unstable();
    values.dedup();
    values
}

fn bytes_from_u64(width: u32, value: u64) -> Result<Vec<u8>> {
    let mut bytes = vec![0u8; crate::ir::bytes_for_width(width)?];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = (value >> (index * 8)) as u8;
    }
    crate::ir::mask_unused_high_bits(&mut bytes, width);
    Ok(bytes)
}
