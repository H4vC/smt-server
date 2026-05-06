use std::cmp::Ordering;
use std::collections::BTreeMap;

use crate::error::{Error, Result};
use crate::ir::{
    bytes_for_width, mask_unused_high_bits, normalized_bytes, validate_bv_width, Arena, NodeKind,
    Sort, TermId,
};
use crate::query::{Assertion, Command, Query};

type Monomial = Vec<TermId>;
type Polynomial = BTreeMap<Monomial, Vec<u8>>;

#[derive(Debug, Clone)]
pub struct Builder {
    arena: Arena,
    assertions: Vec<Assertion>,
    assumptions: Vec<TermId>,
    command: Command,
    target: Option<TermId>,
    signed: bool,
    want_model: bool,
    want_core: bool,
    get_values: Vec<String>,
    scopes: Vec<usize>,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            assertions: Vec::new(),
            assumptions: Vec::new(),
            command: Command::Solve,
            target: None,
            signed: false,
            want_model: false,
            want_core: false,
            get_values: Vec::new(),
            scopes: Vec::new(),
        }
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn finish(self) -> Result<Query> {
        if matches!(self.command, Command::Minimize | Command::Maximize) && self.target.is_none() {
            return Err(Error::invalid(
                "query target",
                "MINIMIZE/MAXIMIZE require a target",
            ));
        }
        Ok(Query {
            arena: self.arena,
            assertions: self.assertions,
            assumptions: self.assumptions,
            command: self.command,
            target: self.target,
            signed: self.signed,
            want_model: self.want_model,
            want_core: self.want_core,
            get_values: self.get_values,
        })
    }

    pub fn set_want_model(&mut self, want_model: bool) {
        self.want_model = want_model;
    }

    pub fn set_want_core(&mut self, want_core: bool) {
        self.want_core = want_core;
    }

    pub fn add_get_value(&mut self, name: impl Into<String>) {
        self.want_model = true;
        self.get_values.push(name.into());
    }

    pub fn set_command(&mut self, command: Command) {
        self.command = command;
    }

    pub fn set_optimization(
        &mut self,
        command: Command,
        target: TermId,
        signed: bool,
    ) -> Result<()> {
        if !matches!(command, Command::Minimize | Command::Maximize) {
            return Err(Error::invalid(
                "optimization command",
                "expected Minimize or Maximize",
            ));
        }
        self.arena.expect_bv(target, "optimization target")?;
        self.command = command;
        self.target = Some(target);
        self.signed = signed;
        Ok(())
    }

    pub fn push(&mut self) {
        self.scopes.push(self.assertions.len());
    }

    pub fn pop(&mut self) -> Result<()> {
        let len = self
            .scopes
            .pop()
            .ok_or_else(|| Error::invalid("scope", "pop without matching push"))?;
        self.assertions.truncate(len);
        Ok(())
    }

    pub fn assert(&mut self, root: TermId) -> Result<()> {
        self.arena.expect_bool(root, "assertion")?;
        self.assertions.push(Assertion { root, name: None });
        Ok(())
    }

    pub fn assert_named(&mut self, name: impl Into<String>, root: TermId) -> Result<()> {
        self.arena.expect_bool(root, "named assertion")?;
        self.assertions.push(Assertion {
            root,
            name: Some(name.into()),
        });
        Ok(())
    }

    pub fn assume(&mut self, root: TermId) -> Result<()> {
        self.arena.expect_bool(root, "assumption")?;
        self.assumptions.push(root);
        Ok(())
    }

    pub fn bv_var(&mut self, name: impl Into<String>, width: u32) -> Result<TermId> {
        self.bv_var_external(name, width, None)
    }

    pub fn bv_var_external(
        &mut self,
        name: impl Into<String>,
        width: u32,
        external: Option<u32>,
    ) -> Result<TermId> {
        validate_bv_width(width, "BV variable width")?;
        self.arena.add(
            NodeKind::BvVar {
                width,
                name: name.into(),
                external,
            },
            Sort::Bv(width),
        )
    }

    pub fn bool_var(&mut self, name: impl Into<String>) -> Result<TermId> {
        self.bool_var_external(name, None)
    }

    pub fn bool_var_external(
        &mut self,
        name: impl Into<String>,
        external: Option<u32>,
    ) -> Result<TermId> {
        self.arena.add(
            NodeKind::BoolVar {
                name: name.into(),
                external,
            },
            Sort::Bool,
        )
    }

    pub fn bool_const(&mut self, value: bool) -> Result<TermId> {
        self.arena.add(NodeKind::BoolConst(value), Sort::Bool)
    }

    pub fn bool_true(&mut self) -> Result<TermId> {
        self.bool_const(true)
    }

    pub fn bool_false(&mut self) -> Result<TermId> {
        self.bool_const(false)
    }

    pub fn bv_const(&mut self, value: u64, width: u32) -> Result<TermId> {
        validate_bv_width(width, "BV constant width")?;
        let mut bytes = vec![0u8; bytes_for_width(width)?];
        let raw = value.to_le_bytes();
        let count = bytes.len().min(raw.len());
        bytes[..count].copy_from_slice(&raw[..count]);
        mask_unused_high_bits(&mut bytes, width);
        self.bv_const_bytes(&bytes, width)
    }

    pub fn bv_const_bytes(&mut self, bytes: &[u8], width: u32) -> Result<TermId> {
        let bytes = normalized_bytes(bytes, width)?;
        self.arena
            .add(NodeKind::BvConst { width, bytes }, Sort::Bv(width))
    }

    pub fn bv_not(&mut self, x: TermId) -> Result<TermId> {
        if let Some((width, mut bytes)) = self.bv_const_value(x)? {
            for byte in &mut bytes {
                *byte = !*byte;
            }
            mask_unused_high_bits(&mut bytes, width);
            return self.bv_const_bytes(&bytes, width);
        }
        if let NodeKind::BvNot(inner) = &self.arena.node(x)?.kind {
            return Ok(*inner);
        }
        self.bv_unary(x, NodeKind::BvNot)
    }

    pub fn bv_neg(&mut self, x: TermId) -> Result<TermId> {
        if let Some((width, bytes)) = self.bv_const_value(x)? {
            return self.bv_const_bytes(&neg_bytes(&bytes, width), width);
        }
        if let Some(inner) = self.bv_neg_child(x)? {
            return Ok(inner);
        }
        self.bv_unary(x, NodeKind::BvNeg)
    }

    pub fn bv_and(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        let width = self.arena.expect_same_bv(a, b, "BV_AND")?;
        if a == b {
            return Ok(a);
        }
        if self.is_zero(a)? || self.is_zero(b)? {
            return Ok(if self.is_zero(a)? { a } else { b });
        }
        if self.is_all_ones(a)? || self.is_all_ones(b)? {
            return Ok(if self.is_all_ones(a)? { b } else { a });
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            let bytes = av.iter().zip(bv).map(|(x, y)| x & y).collect::<Vec<_>>();
            return self.bv_const_bytes(&bytes, width);
        }
        if self.is_bv_negation_pair(a, b)? {
            return self.zero(width);
        }
        if self.have_disjoint_possible_bits(a, b, width)? {
            return self.zero(width);
        }
        if self.bv_or_contains(a, b)? {
            return Ok(b);
        }
        if self.bv_or_contains(b, a)? {
            return Ok(a);
        }
        self.arena.add(NodeKind::BvAnd(a, b), Sort::Bv(width))
    }

    pub fn bv_or(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        let width = self.arena.expect_same_bv(a, b, "BV_OR")?;
        if a == b {
            return Ok(a);
        }
        if self.is_zero(a)? || self.is_zero(b)? {
            return Ok(if self.is_zero(a)? { b } else { a });
        }
        if self.is_all_ones(a)? || self.is_all_ones(b)? {
            return Ok(if self.is_all_ones(a)? { a } else { b });
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            let bytes = av.iter().zip(bv).map(|(x, y)| x | y).collect::<Vec<_>>();
            return self.bv_const_bytes(&bytes, width);
        }
        if self.is_bv_negation_pair(a, b)? {
            return self.all_ones(width);
        }
        if self.bv_and_contains(a, b)? {
            return Ok(b);
        }
        if self.bv_and_contains(b, a)? {
            return Ok(a);
        }
        if self.self_shift_left_pair(a, b)? {
            return self.bv_add(a, b);
        }
        self.arena.add(NodeKind::BvOr(a, b), Sort::Bv(width))
    }

    pub fn bv_xor(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        let width = self.arena.expect_same_bv(a, b, "BV_XOR")?;
        if a == b {
            return self.zero(width);
        }
        if self.is_zero(a)? || self.is_zero(b)? {
            return Ok(if self.is_zero(a)? { b } else { a });
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            let bytes = av.iter().zip(bv).map(|(x, y)| x ^ y).collect::<Vec<_>>();
            return self.bv_const_bytes(&bytes, width);
        }
        if self.is_bv_negation_pair(a, b)? {
            return self.all_ones(width);
        }
        if self.have_disjoint_possible_bits(a, b, width)? {
            return self.bv_or(a, b);
        }
        self.arena.add(NodeKind::BvXor(a, b), Sort::Bv(width))
    }

    pub fn bv_add(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        let width = self.arena.expect_same_bv(a, b, "BV_ADD")?;
        if self.is_zero(a)? || self.is_zero(b)? {
            return Ok(if self.is_zero(a)? { b } else { a });
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            return self.bv_const_bytes(&add_bytes(&av, &bv, width), width);
        }
        if self.have_disjoint_possible_bits(a, b, width)? {
            return self.bv_or(a, b);
        }
        if let Some(canonical) = self.canonical_bv_add(a, b, width)? {
            return Ok(canonical);
        }
        if let Some((value, amount)) = self.shifted_same_add_parts(a, b)? {
            let one = self.bv_const(1, width)?;
            let shifted_one = self.bv_shl(one, amount)?;
            let factor = self.bv_add(one, shifted_one)?;
            return self.bv_mul(value, factor);
        }
        self.bv_add_node(a, b, width)
    }

    pub fn bv_sub(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV_SUB")?;
        if a == b || self.is_zero(a)? && self.is_zero(b)? {
            return self.zero(width);
        }
        if self.is_zero(b)? {
            return Ok(a);
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            return self.bv_const_bytes(&sub_bytes(&av, &bv, width), width);
        }
        self.arena.add(NodeKind::BvSub(a, b), Sort::Bv(width))
    }

    pub fn bv_mul(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        let width = self.arena.expect_same_bv(a, b, "BV_MUL")?;
        if self.is_zero(a)? || self.is_zero(b)? {
            return self.zero(width);
        }
        if self.is_one(a)? || self.is_one(b)? {
            return Ok(if self.is_one(a)? { b } else { a });
        }
        if self.is_all_ones(a)? || self.is_all_ones(b)? {
            let value = if self.is_all_ones(a)? { b } else { a };
            return self.bv_neg(value);
        }
        if let Some(inner) = self.bv_neg_child(a)? {
            let product = self.bv_mul(inner, b)?;
            return self.bv_neg(product);
        }
        if let Some(inner) = self.bv_neg_child(b)? {
            let product = self.bv_mul(a, inner)?;
            return self.bv_neg(product);
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            return self.bv_const_bytes(&mul_bytes(&av, &bv, width), width);
        }
        if let Some((value, amount)) = self.bv_shl_parts(a)? {
            let product = self.bv_mul(value, b)?;
            return self.bv_shl(product, amount);
        }
        if let Some((value, amount)) = self.bv_shl_parts(b)? {
            let product = self.bv_mul(a, value)?;
            return self.bv_shl(product, amount);
        }
        if let Some(canonical) = self.canonical_bv_mul(a, b, width)? {
            return Ok(canonical);
        }
        self.bv_mul_node(a, b, width)
    }

    pub fn bv_udiv(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV udiv")?;
        if self.is_zero(b)? {
            return self.all_ones(width);
        }
        if self.is_one(b)? {
            return Ok(a);
        }
        if self.is_zero(a)? && self.bv_const_value(b)?.is_some() {
            return self.zero(width);
        }
        self.arena.add(NodeKind::BvUDiv(a, b), Sort::Bv(width))
    }

    pub fn bv_urem(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV urem")?;
        if self.is_zero(a)? || self.is_one(b)? {
            return self.zero(width);
        }
        if self.is_zero(b)? {
            return Ok(a);
        }
        self.arena.add(NodeKind::BvURem(a, b), Sort::Bv(width))
    }

    pub fn bv_sdiv(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvSDiv)
    }

    pub fn bv_srem(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvSRem)
    }

    pub fn bv_smod(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvSMod)
    }

    pub fn bv_shl(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV shl")?;
        if self.is_zero(a)? {
            return self.zero(width);
        }
        if let Some(amount) = self.const_shift_amount(b, width)? {
            if amount == 0 {
                return Ok(a);
            }
            if amount >= width as usize {
                return self.zero(width);
            }
            if let Some((_, bytes)) = self.bv_const_value(a)? {
                return self.bv_const_bytes(&shl_bytes(&bytes, width, amount), width);
            }
        }
        if let Some(inner) = self.bv_neg_child(a)? {
            let shifted = self.bv_shl(inner, b)?;
            return self.bv_neg(shifted);
        }
        self.arena.add(NodeKind::BvShl(a, b), Sort::Bv(width))
    }

    pub fn bv_lshr(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV lshr")?;
        if a == b || self.is_zero(a)? {
            return self.zero(width);
        }
        if let Some(amount) = self.const_shift_amount(b, width)? {
            if amount == 0 {
                return Ok(a);
            }
            if amount >= width as usize {
                return self.zero(width);
            }
            if let Some((_, bytes)) = self.bv_const_value(a)? {
                return self.bv_const_bytes(&lshr_bytes(&bytes, width, amount), width);
            }
        }
        if let Some((inner, inner_amount)) = self.bv_lshr_parts(a)? {
            if b < inner_amount {
                let shifted = self.bv_lshr(inner, b)?;
                return self.bv_lshr(shifted, inner_amount);
            }
        }
        self.arena.add(NodeKind::BvLShr(a, b), Sort::Bv(width))
    }

    pub fn bv_ashr(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV ashr")?;
        if let Some(amount) = self.const_shift_amount(b, width)? {
            if amount == 0 {
                return Ok(a);
            }
            if let Some((_, bytes)) = self.bv_const_value(a)? {
                return self.bv_const_bytes(&ashr_bytes(&bytes, width, amount), width);
            }
        }
        self.arena.add(NodeKind::BvAShr(a, b), Sort::Bv(width))
    }

    pub fn bv_extract(&mut self, child: TermId, high: u32, low: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV extract")?;
        if low > high || high >= width {
            return Err(Error::invalid(
                "BV extract",
                format!("invalid bounds high={high}, low={low}, child width={width}"),
            ));
        }
        if low == 0 && high + 1 == width {
            return Ok(child);
        }
        let out_width = high - low + 1;
        if let Some((_, bytes)) = self.bv_const_value(child)? {
            return self.bv_const_bytes(&extract_bytes(&bytes, low, out_width), out_width);
        }
        if let NodeKind::BvExtract {
            child: inner,
            high: _,
            low: inner_low,
        } = self.arena.node(child)?.kind
        {
            return self.bv_extract(inner, inner_low + high, inner_low + low);
        }
        if let NodeKind::BvConcat(high_child, low_child) = self.arena.node(child)?.kind {
            let low_width = self.arena.expect_bv(low_child, "BV concat low child")?;
            if high < low_width {
                return self.bv_extract(low_child, high, low);
            }
            if low >= low_width {
                return self.bv_extract(high_child, high - low_width, low - low_width);
            }
            let low_part = self.bv_extract(low_child, low_width - 1, low)?;
            let high_part = self.bv_extract(high_child, high - low_width, 0)?;
            return self.bv_concat(high_part, low_part);
        }
        self.arena.add(
            NodeKind::BvExtract { child, high, low },
            Sort::Bv(out_width),
        )
    }

    pub fn bv_concat(&mut self, high: TermId, low: TermId) -> Result<TermId> {
        let high_width = self.arena.expect_bv(high, "BV concat")?;
        let low_width = self.arena.expect_bv(low, "BV concat")?;
        let width = high_width
            .checked_add(low_width)
            .ok_or_else(|| Error::invalid("BV concat", "width overflow"))?;
        validate_bv_width(width, "BV concat width")?;
        if let (Some((_, high_bytes)), Some((_, low_bytes))) =
            (self.bv_const_value(high)?, self.bv_const_value(low)?)
        {
            return self.bv_const_bytes(
                &concat_bytes(&high_bytes, high_width, &low_bytes, low_width),
                width,
            );
        }
        if let (Some((high_child, high_hi, high_lo)), Some((low_child, low_hi, low_lo))) =
            (self.bv_extract_parts(high)?, self.bv_extract_parts(low)?)
        {
            if high_child == low_child && low_hi + 1 == high_lo {
                return self.bv_extract(high_child, high_hi, low_lo);
            }
        }
        self.arena
            .add(NodeKind::BvConcat(high, low), Sort::Bv(width))
    }

    pub fn bv_zext(&mut self, child: TermId, extra: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV zero extension")?;
        let out_width = width
            .checked_add(extra)
            .ok_or_else(|| Error::invalid("BV zero extension", "width overflow"))?;
        validate_bv_width(out_width, "BV zero extension width")?;
        if extra == 0 {
            return Ok(child);
        }
        if let Some((_, mut bytes)) = self.bv_const_value(child)? {
            bytes.resize(bytes_for_width(out_width)?, 0);
            return self.bv_const_bytes(&bytes, out_width);
        }
        self.arena
            .add(NodeKind::BvZeroExtend { child, extra }, Sort::Bv(out_width))
    }

    pub fn bv_sext(&mut self, child: TermId, extra: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV sign extension")?;
        let out_width = width
            .checked_add(extra)
            .ok_or_else(|| Error::invalid("BV sign extension", "width overflow"))?;
        validate_bv_width(out_width, "BV sign extension width")?;
        if extra == 0 {
            return Ok(child);
        }
        if let Some((_, bytes)) = self.bv_const_value(child)? {
            return self.bv_const_bytes(&sext_bytes(&bytes, width, extra), out_width);
        }
        self.arena
            .add(NodeKind::BvSignExtend { child, extra }, Sort::Bv(out_width))
    }

    pub fn bv_repeat(&mut self, child: TermId, count: u32) -> Result<TermId> {
        if count == 0 {
            return Err(Error::invalid("BV repeat", "count must be positive"));
        }
        let width = self.arena.expect_bv(child, "BV repeat")?;
        let out_width = width
            .checked_mul(count)
            .ok_or_else(|| Error::invalid("BV repeat", "width overflow"))?;
        validate_bv_width(out_width, "BV repeat width")?;
        if count == 1 {
            return Ok(child);
        }
        if let Some((_, bytes)) = self.bv_const_value(child)? {
            return self.bv_const_bytes(&repeat_bytes(&bytes, width, count), out_width);
        }
        self.arena
            .add(NodeKind::BvRepeat { child, count }, Sort::Bv(out_width))
    }

    pub fn bv_rotate_left(&mut self, child: TermId, amount: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV rotate_left")?;
        let amount = amount % width;
        if amount == 0 {
            return Ok(child);
        }
        if let Some((_, bytes)) = self.bv_const_value(child)? {
            return self.bv_const_bytes(&rotate_left_bytes(&bytes, width, amount), width);
        }
        self.arena
            .add(NodeKind::BvRotateLeft { child, amount }, Sort::Bv(width))
    }

    pub fn bv_rotate_right(&mut self, child: TermId, amount: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV rotate_right")?;
        let amount = amount % width;
        if amount == 0 {
            return Ok(child);
        }
        if let Some((_, bytes)) = self.bv_const_value(child)? {
            return self.bv_const_bytes(&rotate_right_bytes(&bytes, width, amount), width);
        }
        self.arena
            .add(NodeKind::BvRotateRight { child, amount }, Sort::Bv(width))
    }

    pub fn bv_ite(
        &mut self,
        cond: TermId,
        then_value: TermId,
        else_value: TermId,
    ) -> Result<TermId> {
        self.arena.expect_bool(cond, "BV ite condition")?;
        let width = self
            .arena
            .expect_same_bv(then_value, else_value, "BV ite branches")?;
        if then_value == else_value {
            return Ok(then_value);
        }
        if let Some(value) = self.bool_const_value(cond)? {
            return Ok(if value { then_value } else { else_value });
        }
        self.arena.add(
            NodeKind::BvIte {
                cond,
                then_value,
                else_value,
            },
            Sort::Bv(width),
        )
    }

    pub fn bv_select(&mut self, cases: &[(TermId, TermId)], default: TermId) -> Result<TermId> {
        let width = self.arena.expect_bv(default, "BV select default")?;
        for (selector, value) in cases {
            self.arena.expect_bool(*selector, "BV select selector")?;
            let value_width = self.arena.expect_bv(*value, "BV select value")?;
            if value_width != width {
                return Err(Error::invalid(
                    "BV select",
                    format!("value width {value_width} does not match default width {width}"),
                ));
            }
        }
        self.arena.add(
            NodeKind::BvSelect {
                cases: cases.to_vec(),
                default,
            },
            Sort::Bv(width),
        )
    }

    pub fn bool_not(&mut self, x: TermId) -> Result<TermId> {
        self.arena.expect_bool(x, "Bool not")?;
        if let Some(value) = self.bool_const_value(x)? {
            return self.bool_const(!value);
        }
        if let NodeKind::BoolNot(inner) = &self.arena.node(x)?.kind {
            return Ok(*inner);
        }
        self.arena.add(NodeKind::BoolNot(x), Sort::Bool)
    }

    pub fn bool_and(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        self.arena.expect_bool(a, "Bool and")?;
        self.arena.expect_bool(b, "Bool and")?;
        if a == b {
            return Ok(a);
        }
        if self.is_bool_negation_pair(a, b)? {
            return self.bool_false();
        }
        if let Some(value) = self.bool_const_value(a)? {
            return Ok(if value { b } else { a });
        }
        if let Some(value) = self.bool_const_value(b)? {
            return Ok(if value { a } else { b });
        }
        self.arena.add(NodeKind::BoolAnd(a, b), Sort::Bool)
    }

    pub fn bool_or(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        self.arena.expect_bool(a, "Bool or")?;
        self.arena.expect_bool(b, "Bool or")?;
        if a == b {
            return Ok(a);
        }
        if self.is_bool_negation_pair(a, b)? {
            return self.bool_true();
        }
        if let Some(value) = self.bool_const_value(a)? {
            return Ok(if value { a } else { b });
        }
        if let Some(value) = self.bool_const_value(b)? {
            return Ok(if value { b } else { a });
        }
        self.arena.add(NodeKind::BoolOr(a, b), Sort::Bool)
    }

    pub fn bool_implies(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.arena.expect_bool(a, "Bool implies")?;
        self.arena.expect_bool(b, "Bool implies")?;
        if a == b {
            return self.bool_true();
        }
        if let Some(value) = self.bool_const_value(a)? {
            return if value { Ok(b) } else { self.bool_true() };
        }
        if let Some(value) = self.bool_const_value(b)? {
            return if value {
                self.bool_true()
            } else {
                self.bool_not(a)
            };
        }
        self.arena.add(NodeKind::BoolImplies(a, b), Sort::Bool)
    }

    pub fn bool_eq(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.arena.expect_bool(a, "Bool eq")?;
        self.arena.expect_bool(b, "Bool eq")?;
        if a == b {
            return self.bool_true();
        }
        if self.is_bool_negation_pair(a, b)? {
            return self.bool_false();
        }
        if let (Some(av), Some(bv)) = (self.bool_const_value(a)?, self.bool_const_value(b)?) {
            return self.bool_const(av == bv);
        }
        let (a, b) = order_pair(a, b);
        self.arena.add(NodeKind::BoolEq(a, b), Sort::Bool)
    }

    pub fn bool_xor(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let eq = self.bool_eq(a, b)?;
        self.bool_not(eq)
    }

    pub fn bool_ite(
        &mut self,
        cond: TermId,
        then_value: TermId,
        else_value: TermId,
    ) -> Result<TermId> {
        self.arena.expect_bool(cond, "Bool ite condition")?;
        self.arena.expect_bool(then_value, "Bool ite then")?;
        self.arena.expect_bool(else_value, "Bool ite else")?;
        if then_value == else_value {
            return Ok(then_value);
        }
        if let Some(value) = self.bool_const_value(cond)? {
            return Ok(if value { then_value } else { else_value });
        }
        self.arena.add(
            NodeKind::BoolIte {
                cond,
                then_value,
                else_value,
            },
            Sort::Bool,
        )
    }

    pub fn bv_eq(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.arena.expect_same_bv(a, b, "BV eq")?;
        if a == b {
            return self.bool_true();
        }
        if self.is_bv_negation_pair(a, b)? {
            return self.bool_false();
        }
        if let Some(reduced) = self.one_bit_ite_const_equality(a, b)? {
            return Ok(reduced);
        }
        if let Some(reduced) = self.one_bit_ite_const_equality(b, a)? {
            return Ok(reduced);
        }
        if let Some(reduced) = self.extension_const_equality(a, b)? {
            return Ok(reduced);
        }
        if let Some(reduced) = self.extension_const_equality(b, a)? {
            return Ok(reduced);
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            return self.bool_const(av == bv);
        }
        if let Some(value) = self.polynomial_equality(a, b)? {
            return self.bool_const(value);
        }
        let (a, b) = order_pair(a, b);
        self.arena.add(NodeKind::BvEq(a, b), Sort::Bool)
    }

    pub fn bv_ne(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        let eq = self.bv_eq(a, b)?;
        self.bool_not(eq)
    }

    pub fn bv_ult(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_cmp(a, b, NodeKind::BvUlt)
    }

    pub fn bv_ule(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_cmp(a, b, NodeKind::BvUle)
    }

    pub fn bv_ugt(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_ult(b, a)
    }

    pub fn bv_uge(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_ule(b, a)
    }

    pub fn bv_slt(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_cmp(a, b, NodeKind::BvSlt)
    }

    pub fn bv_sle(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_cmp(a, b, NodeKind::BvSle)
    }

    pub fn bv_sgt(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_slt(b, a)
    }

    pub fn bv_sge(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_sle(b, a)
    }

    pub fn uadd_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::UAddOverflow)
    }

    pub fn sadd_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::SAddOverflow)
    }

    pub fn usub_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::USubOverflow)
    }

    pub fn ssub_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::SSubOverflow)
    }

    pub fn umul_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::UMulOverflow)
    }

    pub fn smul_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::SMulOverflow)
    }

    pub fn neg_ovf(&mut self, x: TermId) -> Result<TermId> {
        self.arena.expect_bv(x, "neg overflow")?;
        self.arena.add(NodeKind::NegOverflow(x), Sort::Bool)
    }

    pub fn sdiv_ovf(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.overflow_binary(a, b, NodeKind::SDivOverflow)
    }

    fn bv_unary(&mut self, x: TermId, f: fn(TermId) -> NodeKind) -> Result<TermId> {
        let width = self.arena.expect_bv(x, "BV unary")?;
        self.arena.add(f(x), Sort::Bv(width))
    }

    fn bv_binary(
        &mut self,
        a: TermId,
        b: TermId,
        f: fn(TermId, TermId) -> NodeKind,
    ) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV binary")?;
        self.arena.add(f(a, b), Sort::Bv(width))
    }

    fn bv_add_node(&mut self, a: TermId, b: TermId, width: u32) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        self.arena.add(NodeKind::BvAdd(a, b), Sort::Bv(width))
    }

    fn bv_mul_node(&mut self, a: TermId, b: TermId, width: u32) -> Result<TermId> {
        let (a, b) = order_pair(a, b);
        self.arena.add(NodeKind::BvMul(a, b), Sort::Bv(width))
    }

    fn canonical_bv_add(&mut self, a: TermId, b: TermId, width: u32) -> Result<Option<TermId>> {
        let mut terms = Vec::new();
        self.collect_bv_add(a, &mut terms)?;
        self.collect_bv_add(b, &mut terms)?;
        let mut changed = terms.len() > 2;
        let mut constant = vec![0u8; bytes_for_width(width)?];
        let mut non_const = Vec::new();
        for term in terms {
            if let Some((_, bytes)) = self.bv_const_value(term)? {
                constant = add_bytes(&constant, &bytes, width);
            } else {
                non_const.push(term);
            }
        }
        let mut scaled = Vec::with_capacity(non_const.len());
        for term in non_const {
            let (base, coefficient) = self.scaled_add_term(term, width)?;
            scaled.push((base, coefficient));
        }
        scaled.sort_unstable_by_key(|(base, _)| *base);
        let mut grouped = Vec::with_capacity(scaled.len());
        let mut index = 0;
        while index < scaled.len() {
            let base = scaled[index].0;
            let mut coefficient = vec![0u8; bytes_for_width(width)?];
            let mut count = 0usize;
            while index + count < scaled.len() && scaled[index + count].0 == base {
                coefficient = add_bytes(&coefficient, &scaled[index + count].1, width);
                count += 1;
            }
            if count > 1 {
                changed = true;
            }
            if coefficient.iter().any(|byte| *byte != 0) {
                if is_one_bytes(&coefficient) {
                    grouped.push(base);
                } else {
                    let coefficient = self.bv_const_bytes(&coefficient, width)?;
                    grouped.push(self.bv_mul(base, coefficient)?);
                }
            }
            index += count;
        }
        if constant.iter().any(|byte| *byte != 0) {
            grouped.push(self.bv_const_bytes(&constant, width)?);
        }
        if !changed {
            return Ok(None);
        }
        Ok(Some(self.rebuild_bv_add(grouped, width)?))
    }

    fn canonical_bv_mul(&mut self, a: TermId, b: TermId, width: u32) -> Result<Option<TermId>> {
        let mut terms = Vec::new();
        self.collect_bv_mul(a, &mut terms)?;
        self.collect_bv_mul(b, &mut terms)?;
        if terms.len() <= 2 {
            return Ok(None);
        }
        let mut constant = vec![0u8; bytes_for_width(width)?];
        constant[0] = 1;
        let mut non_const = Vec::new();
        for term in terms {
            if let Some((_, bytes)) = self.bv_const_value(term)? {
                if bytes.iter().all(|byte| *byte == 0) {
                    return Ok(Some(self.zero(width)?));
                }
                constant = mul_bytes(&constant, &bytes, width);
            } else {
                non_const.push(term);
            }
        }
        if !(constant.first().copied() == Some(1) && constant.iter().skip(1).all(|byte| *byte == 0))
        {
            non_const.push(self.bv_const_bytes(&constant, width)?);
        }
        Ok(Some(self.rebuild_bv_mul(non_const, width)?))
    }

    fn polynomial_equality(&self, a: TermId, b: TermId) -> Result<Option<bool>> {
        let width = self.arena.expect_same_bv(a, b, "BV polynomial equality")?;
        if width > 128 {
            return Ok(None);
        }
        let mut budget = 512usize;
        let Some(left) = self.polynomial(a, width, &mut budget)? else {
            return Ok(None);
        };
        let Some(right) = self.polynomial(b, width, &mut budget)? else {
            return Ok(None);
        };
        if left == right {
            return Ok(Some(true));
        }
        let diff = polynomial_sub(&left, &right, width);
        if diff.is_empty() {
            Ok(Some(true))
        } else if diff.keys().all(|monomial| monomial.is_empty()) {
            Ok(Some(false))
        } else {
            Ok(None)
        }
    }

    fn polynomial(
        &self,
        term: TermId,
        width: u32,
        budget: &mut usize,
    ) -> Result<Option<Polynomial>> {
        if *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        if self.arena.expect_bv(term, "BV polynomial term")? != width {
            return Ok(None);
        }
        match &self.arena.node(term)?.kind {
            NodeKind::BvConst { bytes, .. } => Ok(Some(polynomial_constant(bytes.clone()))),
            NodeKind::BvAdd(a, b) => {
                let Some(left) = self.polynomial(*a, width, budget)? else {
                    return Ok(None);
                };
                let Some(right) = self.polynomial(*b, width, budget)? else {
                    return Ok(None);
                };
                Ok(Some(polynomial_add(&left, &right, width)))
            }
            NodeKind::BvSub(a, b) => {
                let Some(left) = self.polynomial(*a, width, budget)? else {
                    return Ok(None);
                };
                let Some(right) = self.polynomial(*b, width, budget)? else {
                    return Ok(None);
                };
                Ok(Some(polynomial_sub(&left, &right, width)))
            }
            NodeKind::BvNeg(child) => {
                let Some(poly) = self.polynomial(*child, width, budget)? else {
                    return Ok(None);
                };
                Ok(Some(polynomial_neg(&poly, width)))
            }
            NodeKind::BvNot(child) => {
                let Some(poly) = self.polynomial(*child, width, budget)? else {
                    return Ok(None);
                };
                let mut minus = polynomial_neg(&poly, width);
                let mut one = vec![0u8; bytes_for_width(width)?];
                one[0] = 1;
                polynomial_add_assign(&mut minus, Vec::new(), neg_bytes(&one, width), width);
                Ok(Some(minus))
            }
            NodeKind::BvMul(a, b) => {
                let Some(left) = self.polynomial(*a, width, budget)? else {
                    return Ok(None);
                };
                let Some(right) = self.polynomial(*b, width, budget)? else {
                    return Ok(None);
                };
                polynomial_mul(&left, &right, width)
            }
            NodeKind::BvShl(value, amount) => {
                let Some(shift) = self.const_shift_amount(*amount, width)? else {
                    return Ok(Some(polynomial_atom(term, width)?));
                };
                if shift >= width as usize {
                    return Ok(Some(Polynomial::new()));
                }
                let Some(poly) = self.polynomial(*value, width, budget)? else {
                    return Ok(None);
                };
                let mut factor = vec![0u8; bytes_for_width(width)?];
                set_bit(&mut factor, shift as u32);
                Ok(Some(polynomial_scale(&poly, &factor, width)))
            }
            _ => Ok(Some(polynomial_atom(term, width)?)),
        }
    }

    fn collect_bv_add(&self, id: TermId, out: &mut Vec<TermId>) -> Result<()> {
        match &self.arena.node(id)?.kind {
            NodeKind::BvAdd(a, b) => {
                self.collect_bv_add(*a, out)?;
                self.collect_bv_add(*b, out)?;
            }
            _ => out.push(id),
        }
        Ok(())
    }

    fn collect_bv_mul(&self, id: TermId, out: &mut Vec<TermId>) -> Result<()> {
        match &self.arena.node(id)?.kind {
            NodeKind::BvMul(a, b) => {
                self.collect_bv_mul(*a, out)?;
                self.collect_bv_mul(*b, out)?;
            }
            _ => out.push(id),
        }
        Ok(())
    }

    fn scaled_add_term(&self, term: TermId, width: u32) -> Result<(TermId, Vec<u8>)> {
        let mut one = vec![0u8; bytes_for_width(width)?];
        one[0] = 1;
        let NodeKind::BvMul(a, b) = &self.arena.node(term)?.kind else {
            return Ok((term, one));
        };
        if let Some((_, coefficient)) = self.bv_const_value(*a)? {
            return Ok((*b, coefficient));
        }
        if let Some((_, coefficient)) = self.bv_const_value(*b)? {
            return Ok((*a, coefficient));
        }
        Ok((term, one))
    }

    fn rebuild_bv_add(&mut self, mut terms: Vec<TermId>, width: u32) -> Result<TermId> {
        if terms.is_empty() {
            return self.zero(width);
        }
        terms.sort_unstable();
        let mut iter = terms.into_iter();
        let mut cur = iter.next().expect("non-empty terms");
        for next in iter {
            cur = self.bv_add_node(cur, next, width)?;
        }
        Ok(cur)
    }

    fn rebuild_bv_mul(&mut self, mut terms: Vec<TermId>, width: u32) -> Result<TermId> {
        if terms.is_empty() {
            return self.bv_const(1, width);
        }
        terms.sort_unstable();
        let mut iter = terms.into_iter();
        let mut cur = iter.next().expect("non-empty terms");
        for next in iter {
            cur = self.bv_mul_node(cur, next, width)?;
        }
        Ok(cur)
    }

    fn bv_cmp(
        &mut self,
        a: TermId,
        b: TermId,
        f: fn(TermId, TermId) -> NodeKind,
    ) -> Result<TermId> {
        let width = self.arena.expect_same_bv(a, b, "BV comparison")?;
        if a == b {
            return match f(a, b) {
                NodeKind::BvUlt(_, _) | NodeKind::BvSlt(_, _) => self.bool_false(),
                NodeKind::BvUle(_, _) | NodeKind::BvSle(_, _) => self.bool_true(),
                _ => unreachable!("comparison constructor returned non-comparison"),
            };
        }
        let comparison = f(a, b);
        if matches!(comparison, NodeKind::BvUlt(_, _) | NodeKind::BvUle(_, _)) {
            let strict = matches!(comparison, NodeKind::BvUlt(_, _));
            if let Some(reduced) = self.zero_extend_const_unsigned_cmp(a, b, strict, true)? {
                return Ok(reduced);
            }
            if let Some(reduced) = self.zero_extend_const_unsigned_cmp(b, a, strict, false)? {
                return Ok(reduced);
            }
        }
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            let value = match comparison {
                NodeKind::BvUlt(_, _) => cmp_unsigned_bytes(&av, &bv) == Ordering::Less,
                NodeKind::BvUle(_, _) => cmp_unsigned_bytes(&av, &bv) != Ordering::Greater,
                NodeKind::BvSlt(_, _) => signed_less_than(&av, &bv, width),
                NodeKind::BvSle(_, _) => signed_less_than(&av, &bv, width) || av == bv,
                _ => unreachable!("comparison constructor returned non-comparison"),
            };
            return self.bool_const(value);
        }
        self.arena.add(comparison, Sort::Bool)
    }

    fn overflow_binary(
        &mut self,
        a: TermId,
        b: TermId,
        f: fn(TermId, TermId) -> NodeKind,
    ) -> Result<TermId> {
        self.arena.expect_same_bv(a, b, "overflow predicate")?;
        self.arena.add(f(a, b), Sort::Bool)
    }

    fn one_bit_ite_const_equality(
        &mut self,
        ite: TermId,
        constant: TermId,
    ) -> Result<Option<TermId>> {
        let Some((const_width, const_bytes)) = self.bv_const_value(constant)? else {
            return Ok(None);
        };
        if const_width != 1 {
            return Ok(None);
        }
        let Some((cond, then_value, else_value)) = self.bv_ite_parts(ite)? else {
            return Ok(None);
        };
        let Some(then_bit) = self.one_bit_const_value(then_value)? else {
            return Ok(None);
        };
        let Some(else_bit) = self.one_bit_const_value(else_value)? else {
            return Ok(None);
        };
        let expected = (const_bytes[0] & 1) != 0;
        if then_bit == expected && else_bit != expected {
            Ok(Some(cond))
        } else if then_bit != expected && else_bit == expected {
            Ok(Some(self.bool_not(cond)?))
        } else {
            Ok(Some(self.bool_const(then_bit == expected)?))
        }
    }

    fn extension_const_equality(
        &mut self,
        extended: TermId,
        constant: TermId,
    ) -> Result<Option<TermId>> {
        let Some((const_width, const_bytes)) = self.bv_const_value(constant)? else {
            return Ok(None);
        };
        let Some((child, child_width, extra, signed)) = self.extension_parts(extended)? else {
            return Ok(None);
        };
        if const_width != child_width + extra {
            return Ok(None);
        }
        let child_bytes = extract_bytes(&const_bytes, 0, child_width);
        let in_range = if signed {
            sext_bytes(&child_bytes, child_width, extra) == const_bytes
        } else {
            high_bits_zero(&const_bytes, child_width, const_width)
        };
        if !in_range {
            return Ok(Some(self.bool_false()?));
        }
        let child_const = self.bv_const_bytes(&child_bytes, child_width)?;
        Ok(Some(self.bv_eq(child, child_const)?))
    }

    fn zero_extend_const_unsigned_cmp(
        &mut self,
        extended: TermId,
        constant: TermId,
        strict: bool,
        extended_on_left: bool,
    ) -> Result<Option<TermId>> {
        let Some((const_width, const_bytes)) = self.bv_const_value(constant)? else {
            return Ok(None);
        };
        let Some((child, child_width, extra, signed)) = self.extension_parts(extended)? else {
            return Ok(None);
        };
        if signed || const_width != child_width + extra {
            return Ok(None);
        }
        let high_zero = high_bits_zero(&const_bytes, child_width, const_width);
        let const_zero = const_bytes.iter().all(|byte| *byte == 0);
        let const_low = extract_bytes(&const_bytes, 0, child_width);
        let low_const = self.bv_const_bytes(&const_low, child_width)?;
        if extended_on_left {
            if strict {
                if const_zero {
                    return Ok(Some(self.bool_false()?));
                }
                if !high_zero {
                    return Ok(Some(self.bool_true()?));
                }
                Ok(Some(self.bv_ult(child, low_const)?))
            } else {
                if !high_zero {
                    return Ok(Some(self.bool_true()?));
                }
                Ok(Some(self.bv_ule(child, low_const)?))
            }
        } else if !high_zero {
            Ok(Some(self.bool_false()?))
        } else if strict {
            if self.is_all_ones(low_const)? {
                return Ok(Some(self.bool_false()?));
            }
            Ok(Some(self.bv_ult(low_const, child)?))
        } else {
            if const_zero {
                return Ok(Some(self.bool_true()?));
            }
            Ok(Some(self.bv_ule(low_const, child)?))
        }
    }

    fn bv_ite_parts(&self, id: TermId) -> Result<Option<(TermId, TermId, TermId)>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvIte {
                cond,
                then_value,
                else_value,
            } => Some((*cond, *then_value, *else_value)),
            _ => None,
        })
    }

    fn extension_parts(&self, id: TermId) -> Result<Option<(TermId, u32, u32, bool)>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvZeroExtend { child, extra } => {
                let width = self.arena.expect_bv(*child, "BV zero extension child")?;
                Some((*child, width, *extra, false))
            }
            NodeKind::BvSignExtend { child, extra } => {
                let width = self.arena.expect_bv(*child, "BV sign extension child")?;
                Some((*child, width, *extra, true))
            }
            _ => None,
        })
    }

    fn one_bit_const_value(&self, id: TermId) -> Result<Option<bool>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvConst { width: 1, bytes } => Some((bytes[0] & 1) != 0),
            _ => None,
        })
    }

    fn bool_const_value(&self, id: TermId) -> Result<Option<bool>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BoolConst(value) => Some(*value),
            _ => None,
        })
    }

    fn bv_const_value(&self, id: TermId) -> Result<Option<(u32, Vec<u8>)>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvConst { width, bytes } => Some((*width, bytes.clone())),
            _ => None,
        })
    }

    fn is_zero(&self, id: TermId) -> Result<bool> {
        Ok(self
            .bv_const_value(id)?
            .is_some_and(|(_, bytes)| bytes.iter().all(|byte| *byte == 0)))
    }

    fn is_one(&self, id: TermId) -> Result<bool> {
        Ok(self.bv_const_value(id)?.is_some_and(|(_, bytes)| {
            bytes.first().copied() == Some(1) && bytes.iter().skip(1).all(|byte| *byte == 0)
        }))
    }

    fn is_all_ones(&self, id: TermId) -> Result<bool> {
        Ok(self.bv_const_value(id)?.is_some_and(|(width, bytes)| {
            let mut ones = vec![0xff; bytes.len()];
            mask_unused_high_bits(&mut ones, width);
            bytes == ones
        }))
    }

    fn is_bool_negation_pair(&self, a: TermId, b: TermId) -> Result<bool> {
        Ok(
            matches!(self.arena.node(a)?.kind, NodeKind::BoolNot(inner) if inner == b)
                || matches!(self.arena.node(b)?.kind, NodeKind::BoolNot(inner) if inner == a),
        )
    }

    fn is_bv_negation_pair(&self, a: TermId, b: TermId) -> Result<bool> {
        Ok(
            matches!(self.arena.node(a)?.kind, NodeKind::BvNot(inner) if inner == b)
                || matches!(self.arena.node(b)?.kind, NodeKind::BvNot(inner) if inner == a),
        )
    }

    fn bv_neg_child(&self, id: TermId) -> Result<Option<TermId>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvNeg(child) => Some(*child),
            _ => None,
        })
    }

    fn bv_and_contains(&self, id: TermId, child: TermId) -> Result<bool> {
        Ok(matches!(self.arena.node(id)?.kind, NodeKind::BvAnd(a, b) if a == child || b == child))
    }

    fn bv_or_contains(&self, id: TermId, child: TermId) -> Result<bool> {
        Ok(matches!(self.arena.node(id)?.kind, NodeKind::BvOr(a, b) if a == child || b == child))
    }

    fn self_shift_left_pair(&self, a: TermId, b: TermId) -> Result<bool> {
        Ok(
            matches!(self.bv_shl_parts(a)?, Some((value, amount)) if value == b && amount == b)
                || matches!(self.bv_shl_parts(b)?, Some((value, amount)) if value == a && amount == a),
        )
    }

    fn bv_shl_parts(&self, id: TermId) -> Result<Option<(TermId, TermId)>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvShl(value, amount) => Some((*value, *amount)),
            _ => None,
        })
    }

    fn bv_lshr_parts(&self, id: TermId) -> Result<Option<(TermId, TermId)>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvLShr(value, amount) => Some((*value, *amount)),
            _ => None,
        })
    }

    fn bv_extract_parts(&self, id: TermId) -> Result<Option<(TermId, u32, u32)>> {
        Ok(match &self.arena.node(id)?.kind {
            NodeKind::BvExtract { child, high, low } => Some((*child, *high, *low)),
            _ => None,
        })
    }

    fn have_disjoint_possible_bits(&self, a: TermId, b: TermId, width: u32) -> Result<bool> {
        const MAX_MASK_WIDTH: u32 = 4096;
        if width > MAX_MASK_WIDTH {
            return Ok(false);
        }
        let (Some(left), Some(right)) = (
            self.possible_bit_mask_bytes(a, width, 0)?,
            self.possible_bit_mask_bytes(b, width, 0)?,
        ) else {
            return Ok(false);
        };
        Ok(!left
            .iter()
            .zip(right)
            .any(|(left, right)| (left & right) != 0))
    }

    fn possible_bit_mask_bytes(
        &self,
        term: TermId,
        width: u32,
        depth: usize,
    ) -> Result<Option<Vec<u8>>> {
        if width > 4096 || depth > 64 {
            return Ok(None);
        }
        let byte_len = bytes_for_width(width)?;
        Ok(match &self.arena.node(term)?.kind {
            NodeKind::BvConst {
                width: actual_width,
                bytes,
            } if *actual_width == width => {
                let mut mask = bytes.clone();
                mask.resize(byte_len, 0);
                mask_unused_high_bits(&mut mask, width);
                Some(mask)
            }
            NodeKind::BvVar { width: actual, .. } if *actual == width => {
                let mut mask = vec![0xff; byte_len];
                mask_unused_high_bits(&mut mask, width);
                Some(mask)
            }
            NodeKind::BvZeroExtend { child, extra } => {
                let Sort::Bv(child_width) = self.arena.sort(*child)? else {
                    return Ok(None);
                };
                if child_width + extra == width {
                    self.possible_bit_mask_bytes(*child, child_width, depth + 1)?
                        .map(|mut mask| {
                            mask.resize(byte_len, 0);
                            mask_unused_high_bits(&mut mask, width);
                            mask
                        })
                } else {
                    None
                }
            }
            NodeKind::BvShl(value, amount) => {
                let Some(shift) = self.const_shift_amount(*amount, width)? else {
                    return Ok(None);
                };
                self.possible_bit_mask_bytes(*value, width, depth + 1)?
                    .map(|mask| shl_bytes(&mask, width, shift))
            }
            NodeKind::BvLShr(value, amount) => {
                let Some(shift) = self.const_shift_amount(*amount, width)? else {
                    return Ok(None);
                };
                self.possible_bit_mask_bytes(*value, width, depth + 1)?
                    .map(|mask| lshr_bytes(&mask, width, shift))
            }
            NodeKind::BvExtract { child, high, low } => {
                let Sort::Bv(child_width) = self.arena.sort(*child)? else {
                    return Ok(None);
                };
                if high - low + 1 != width {
                    return Ok(None);
                }
                self.possible_bit_mask_bytes(*child, child_width, depth + 1)?
                    .map(|mask| extract_bytes(&mask, *low, width))
            }
            NodeKind::BvConcat(high, low) => {
                let Sort::Bv(high_width) = self.arena.sort(*high)? else {
                    return Ok(None);
                };
                let Sort::Bv(low_width) = self.arena.sort(*low)? else {
                    return Ok(None);
                };
                if high_width + low_width != width {
                    return Ok(None);
                }
                match (
                    self.possible_bit_mask_bytes(*high, high_width, depth + 1)?,
                    self.possible_bit_mask_bytes(*low, low_width, depth + 1)?,
                ) {
                    (Some(high_mask), Some(low_mask)) => {
                        Some(concat_bytes(&high_mask, high_width, &low_mask, low_width))
                    }
                    _ => None,
                }
            }
            NodeKind::BvAnd(left, right) => match (
                self.possible_bit_mask_bytes(*left, width, depth + 1)?,
                self.possible_bit_mask_bytes(*right, width, depth + 1)?,
            ) {
                (Some(mut left), Some(right)) => {
                    for (left, right) in left.iter_mut().zip(right) {
                        *left &= right;
                    }
                    Some(left)
                }
                (Some(mask), None) | (None, Some(mask)) => Some(mask),
                (None, None) => None,
            },
            NodeKind::BvOr(left, right) | NodeKind::BvXor(left, right) => match (
                self.possible_bit_mask_bytes(*left, width, depth + 1)?,
                self.possible_bit_mask_bytes(*right, width, depth + 1)?,
            ) {
                (Some(mut left), Some(right)) => {
                    for (left, right) in left.iter_mut().zip(right) {
                        *left |= right;
                    }
                    Some(left)
                }
                _ => None,
            },
            NodeKind::BvIte { .. } => None,
            _ => None,
        })
    }

    fn shifted_same_add_parts(&self, a: TermId, b: TermId) -> Result<Option<(TermId, TermId)>> {
        if let Some((value, amount)) = self.bv_shl_parts(a)? {
            if value == b && self.bv_const_value(value)?.is_none() {
                return Ok(Some((value, amount)));
            }
        }
        if let Some((value, amount)) = self.bv_shl_parts(b)? {
            if value == a && self.bv_const_value(value)?.is_none() {
                return Ok(Some((value, amount)));
            }
        }
        Ok(None)
    }

    fn const_shift_amount(&self, id: TermId, width: u32) -> Result<Option<usize>> {
        let Some((_, bytes)) = self.bv_const_value(id)? else {
            return Ok(None);
        };
        Ok(Some(bytes_to_bounded_usize(&bytes, width as usize)))
    }

    fn zero(&mut self, width: u32) -> Result<TermId> {
        self.bv_const_bytes(&vec![0; bytes_for_width(width)?], width)
    }

    fn all_ones(&mut self, width: u32) -> Result<TermId> {
        let mut bytes = vec![0xff; bytes_for_width(width)?];
        mask_unused_high_bits(&mut bytes, width);
        self.bv_const_bytes(&bytes, width)
    }
}

fn polynomial_constant(bytes: Vec<u8>) -> Polynomial {
    let mut polynomial = Polynomial::new();
    if bytes.iter().any(|byte| *byte != 0) {
        polynomial.insert(Vec::new(), bytes);
    }
    polynomial
}

fn polynomial_atom(term: TermId, width: u32) -> Result<Polynomial> {
    let mut coefficient = vec![0u8; bytes_for_width(width)?];
    coefficient[0] = 1;
    let mut polynomial = Polynomial::new();
    polynomial.insert(vec![term], coefficient);
    Ok(polynomial)
}

fn polynomial_add(left: &Polynomial, right: &Polynomial, width: u32) -> Polynomial {
    let mut out = left.clone();
    for (monomial, coefficient) in right {
        polynomial_add_assign(&mut out, monomial.clone(), coefficient.clone(), width);
    }
    out
}

fn polynomial_sub(left: &Polynomial, right: &Polynomial, width: u32) -> Polynomial {
    let mut out = left.clone();
    for (monomial, coefficient) in right {
        polynomial_add_assign(
            &mut out,
            monomial.clone(),
            neg_bytes(coefficient, width),
            width,
        );
    }
    out
}

fn polynomial_neg(poly: &Polynomial, width: u32) -> Polynomial {
    let mut out = Polynomial::new();
    for (monomial, coefficient) in poly {
        polynomial_add_assign(
            &mut out,
            monomial.clone(),
            neg_bytes(coefficient, width),
            width,
        );
    }
    out
}

fn polynomial_scale(poly: &Polynomial, factor: &[u8], width: u32) -> Polynomial {
    if factor.iter().all(|byte| *byte == 0) {
        return Polynomial::new();
    }
    let mut out = Polynomial::new();
    for (monomial, coefficient) in poly {
        polynomial_add_assign(
            &mut out,
            monomial.clone(),
            mul_bytes(coefficient, factor, width),
            width,
        );
    }
    out
}

fn polynomial_mul(left: &Polynomial, right: &Polynomial, width: u32) -> Result<Option<Polynomial>> {
    let mut out = Polynomial::new();
    for (left_monomial, left_coefficient) in left {
        for (right_monomial, right_coefficient) in right {
            let mut monomial = Vec::with_capacity(left_monomial.len() + right_monomial.len());
            monomial.extend_from_slice(left_monomial);
            monomial.extend_from_slice(right_monomial);
            monomial.sort_unstable();
            if monomial.len() > 16 {
                return Ok(None);
            }
            let coefficient = mul_bytes(left_coefficient, right_coefficient, width);
            polynomial_add_assign(&mut out, monomial, coefficient, width);
            if out.len() > 512 {
                return Ok(None);
            }
        }
    }
    Ok(Some(out))
}

fn polynomial_add_assign(
    polynomial: &mut Polynomial,
    monomial: Monomial,
    coefficient: Vec<u8>,
    width: u32,
) {
    if coefficient.iter().all(|byte| *byte == 0) {
        return;
    }
    let updated = if let Some(existing) = polynomial.get(&monomial) {
        add_bytes(existing, &coefficient, width)
    } else {
        coefficient
    };
    if updated.iter().all(|byte| *byte == 0) {
        polynomial.remove(&monomial);
    } else {
        polynomial.insert(monomial, updated);
    }
}

fn order_pair(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

pub(crate) fn add_bytes(a: &[u8], b: &[u8], width: u32) -> Vec<u8> {
    let mut out = Vec::with_capacity(a.len());
    let mut carry = 0u16;
    for (&x, &y) in a.iter().zip(b) {
        let sum = u16::from(x) + u16::from(y) + carry;
        out.push(sum as u8);
        carry = sum >> 8;
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn sub_bytes(a: &[u8], b: &[u8], width: u32) -> Vec<u8> {
    let neg_b = neg_bytes(b, width);
    add_bytes(a, &neg_b, width)
}

pub(crate) fn neg_bytes(bytes: &[u8], width: u32) -> Vec<u8> {
    let mut out = bytes.iter().map(|byte| !byte).collect::<Vec<_>>();
    let mut carry = 1u16;
    for byte in &mut out {
        let sum = u16::from(*byte) + carry;
        *byte = sum as u8;
        carry = sum >> 8;
        if carry == 0 {
            break;
        }
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn mul_bytes(a: &[u8], b: &[u8], width: u32) -> Vec<u8> {
    let mut out = vec![0u8; a.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u16;
        for (j, &y) in b.iter().enumerate() {
            let Some(slot) = out.get_mut(i + j) else {
                break;
            };
            let product = u16::from(*slot) + u16::from(x) * u16::from(y) + carry;
            *slot = product as u8;
            carry = product >> 8;
        }
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn get_bit(bytes: &[u8], bit: u32) -> bool {
    bytes
        .get((bit / 8) as usize)
        .is_some_and(|byte| ((byte >> (bit % 8)) & 1) != 0)
}

pub(crate) fn set_bit(bytes: &mut [u8], bit: u32) {
    if let Some(byte) = bytes.get_mut((bit / 8) as usize) {
        *byte |= 1 << (bit % 8);
    }
}

fn high_bits_zero(bytes: &[u8], from: u32, width: u32) -> bool {
    (from..width).all(|bit| !get_bit(bytes, bit))
}

pub(crate) fn extract_bytes(bytes: &[u8], low: u32, width: u32) -> Vec<u8> {
    let mut out = vec![0u8; (width as usize).div_ceil(8)];
    for bit in 0..width {
        if get_bit(bytes, low + bit) {
            set_bit(&mut out, bit);
        }
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn concat_bytes(high: &[u8], high_width: u32, low: &[u8], low_width: u32) -> Vec<u8> {
    let width = high_width + low_width;
    let mut out = vec![0u8; (width as usize).div_ceil(8)];
    for bit in 0..low_width {
        if get_bit(low, bit) {
            set_bit(&mut out, bit);
        }
    }
    for bit in 0..high_width {
        if get_bit(high, bit) {
            set_bit(&mut out, low_width + bit);
        }
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn sext_bytes(bytes: &[u8], width: u32, extra: u32) -> Vec<u8> {
    let out_width = width + extra;
    let mut out = bytes.to_vec();
    out.resize((out_width as usize).div_ceil(8), 0);
    if get_bit(bytes, width - 1) {
        for bit in width..out_width {
            set_bit(&mut out, bit);
        }
    }
    mask_unused_high_bits(&mut out, out_width);
    out
}

pub(crate) fn repeat_bytes(bytes: &[u8], width: u32, count: u32) -> Vec<u8> {
    let out_width = width * count;
    let mut out = vec![0u8; (out_width as usize).div_ceil(8)];
    for copy in 0..count {
        let offset = copy * width;
        for bit in 0..width {
            if get_bit(bytes, bit) {
                set_bit(&mut out, offset + bit);
            }
        }
    }
    mask_unused_high_bits(&mut out, out_width);
    out
}

pub(crate) fn rotate_left_bytes(bytes: &[u8], width: u32, amount: u32) -> Vec<u8> {
    let mut out = vec![0u8; (width as usize).div_ceil(8)];
    for bit in 0..width {
        let source = (bit + width - amount) % width;
        if get_bit(bytes, source) {
            set_bit(&mut out, bit);
        }
    }
    out
}

pub(crate) fn rotate_right_bytes(bytes: &[u8], width: u32, amount: u32) -> Vec<u8> {
    let mut out = vec![0u8; (width as usize).div_ceil(8)];
    for bit in 0..width {
        let source = (bit + amount) % width;
        if get_bit(bytes, source) {
            set_bit(&mut out, bit);
        }
    }
    out
}

pub(crate) fn shl_bytes(bytes: &[u8], width: u32, amount: usize) -> Vec<u8> {
    let mut out = vec![0u8; (width as usize).div_ceil(8)];
    for bit in amount..width as usize {
        if get_bit(bytes, (bit - amount) as u32) {
            set_bit(&mut out, bit as u32);
        }
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn lshr_bytes(bytes: &[u8], width: u32, amount: usize) -> Vec<u8> {
    let mut out = vec![0u8; (width as usize).div_ceil(8)];
    let width_usize = width as usize;
    for bit in 0..width_usize.saturating_sub(amount) {
        if get_bit(bytes, (bit + amount) as u32) {
            set_bit(&mut out, bit as u32);
        }
    }
    out
}

pub(crate) fn ashr_bytes(bytes: &[u8], width: u32, amount: usize) -> Vec<u8> {
    let mut out = lshr_bytes(bytes, width, amount.min(width as usize));
    if get_bit(bytes, width - 1) {
        let start = width.saturating_sub(amount.min(width as usize) as u32);
        for bit in start..width {
            set_bit(&mut out, bit);
        }
    }
    mask_unused_high_bits(&mut out, width);
    out
}

pub(crate) fn bytes_to_bounded_usize(bytes: &[u8], bound: usize) -> usize {
    let mut value = 0usize;
    for (byte_index, byte) in bytes.iter().copied().enumerate() {
        if byte == 0 {
            continue;
        }
        for bit_in_byte in 0..8 {
            if ((byte >> bit_in_byte) & 1) == 0 {
                continue;
            }
            let bit = byte_index * 8 + bit_in_byte;
            if bit >= usize::BITS as usize {
                return bound;
            }
            value = value.saturating_add(1usize << bit);
            if value >= bound {
                return bound;
            }
        }
    }
    value
}

fn is_one_bytes(bytes: &[u8]) -> bool {
    bytes.first().copied() == Some(1) && bytes.iter().skip(1).all(|byte| *byte == 0)
}

pub(crate) fn cmp_unsigned_bytes(a: &[u8], b: &[u8]) -> Ordering {
    for (&av, &bv) in a.iter().zip(b).rev() {
        match av.cmp(&bv) {
            Ordering::Equal => {}
            non_eq => return non_eq,
        }
    }
    Ordering::Equal
}

pub(crate) fn signed_less_than(a: &[u8], b: &[u8], width: u32) -> bool {
    let sign_a = get_bit(a, width - 1);
    let sign_b = get_bit(b, width - 1);
    match (sign_a, sign_b) {
        (true, false) => true,
        (false, true) => false,
        _ => cmp_unsigned_bytes(a, b) == Ordering::Less,
    }
}
