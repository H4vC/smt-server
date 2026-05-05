use crate::error::{Error, Result};
use crate::ir::{
    bytes_for_width, mask_unused_high_bits, normalized_bytes, validate_bv_width, Arena, NodeKind,
    Sort, TermId,
};
use crate::query::{Assertion, Command, Query};

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
        self.arena.add(NodeKind::BvAdd(a, b), Sort::Bv(width))
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
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            return self.bv_const_bytes(&mul_bytes(&av, &bv, width), width);
        }
        self.arena.add(NodeKind::BvMul(a, b), Sort::Bv(width))
    }

    pub fn bv_udiv(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvUDiv)
    }

    pub fn bv_urem(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvURem)
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
        self.bv_binary(a, b, NodeKind::BvShl)
    }

    pub fn bv_lshr(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvLShr)
    }

    pub fn bv_ashr(&mut self, a: TermId, b: TermId) -> Result<TermId> {
        self.bv_binary(a, b, NodeKind::BvAShr)
    }

    pub fn bv_extract(&mut self, child: TermId, high: u32, low: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV extract")?;
        if low > high || high >= width {
            return Err(Error::invalid(
                "BV extract",
                format!("invalid bounds high={high}, low={low}, child width={width}"),
            ));
        }
        self.arena.add(
            NodeKind::BvExtract { child, high, low },
            Sort::Bv(high - low + 1),
        )
    }

    pub fn bv_concat(&mut self, high: TermId, low: TermId) -> Result<TermId> {
        let high_width = self.arena.expect_bv(high, "BV concat")?;
        let low_width = self.arena.expect_bv(low, "BV concat")?;
        let width = high_width
            .checked_add(low_width)
            .ok_or_else(|| Error::invalid("BV concat", "width overflow"))?;
        validate_bv_width(width, "BV concat width")?;
        self.arena
            .add(NodeKind::BvConcat(high, low), Sort::Bv(width))
    }

    pub fn bv_zext(&mut self, child: TermId, extra: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV zero extension")?;
        let out_width = width
            .checked_add(extra)
            .ok_or_else(|| Error::invalid("BV zero extension", "width overflow"))?;
        validate_bv_width(out_width, "BV zero extension width")?;
        self.arena
            .add(NodeKind::BvZeroExtend { child, extra }, Sort::Bv(out_width))
    }

    pub fn bv_sext(&mut self, child: TermId, extra: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV sign extension")?;
        let out_width = width
            .checked_add(extra)
            .ok_or_else(|| Error::invalid("BV sign extension", "width overflow"))?;
        validate_bv_width(out_width, "BV sign extension width")?;
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
        self.arena
            .add(NodeKind::BvRepeat { child, count }, Sort::Bv(out_width))
    }

    pub fn bv_rotate_left(&mut self, child: TermId, amount: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV rotate_left")?;
        self.arena.add(
            NodeKind::BvRotateLeft {
                child,
                amount: amount % width,
            },
            Sort::Bv(width),
        )
    }

    pub fn bv_rotate_right(&mut self, child: TermId, amount: u32) -> Result<TermId> {
        let width = self.arena.expect_bv(child, "BV rotate_right")?;
        self.arena.add(
            NodeKind::BvRotateRight {
                child,
                amount: amount % width,
            },
            Sort::Bv(width),
        )
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
        if let (Some((_, av)), Some((_, bv))) = (self.bv_const_value(a)?, self.bv_const_value(b)?) {
            return self.bool_const(av == bv);
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

    fn bv_cmp(
        &mut self,
        a: TermId,
        b: TermId,
        f: fn(TermId, TermId) -> NodeKind,
    ) -> Result<TermId> {
        self.arena.expect_same_bv(a, b, "BV comparison")?;
        self.arena.add(f(a, b), Sort::Bool)
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

    fn zero(&mut self, width: u32) -> Result<TermId> {
        self.bv_const_bytes(&vec![0; bytes_for_width(width)?], width)
    }
}

fn order_pair(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn add_bytes(a: &[u8], b: &[u8], width: u32) -> Vec<u8> {
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

fn sub_bytes(a: &[u8], b: &[u8], width: u32) -> Vec<u8> {
    let neg_b = neg_bytes(b, width);
    add_bytes(a, &neg_b, width)
}

fn neg_bytes(bytes: &[u8], width: u32) -> Vec<u8> {
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

fn mul_bytes(a: &[u8], b: &[u8], width: u32) -> Vec<u8> {
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
