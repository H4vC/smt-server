use crate::constants::{request_flags, Command, Tag};
use crate::error::{Result, WireError};
use crate::expr::{bytes_for_width, validate_bv_width_value, ExpressionBuffer, RawNode};
use crate::request::BinaryRequest;
use crate::types::{BlobRef, NodeRef, Sort};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NodeMeta {
    sort: Sort,
    width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Assertion {
    pub root: NodeRef,
    pub name: Option<BlobRef>,
}

#[derive(Debug, Clone)]
pub struct CompactedExpression {
    bytes: Vec<u8>,
    old_to_new: Vec<Option<NodeRef>>,
}

impl CompactedExpression {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    pub fn remap_ref(&self, old: NodeRef) -> Result<NodeRef> {
        let mapped = self
            .old_to_new
            .get(old.index() as usize)
            .copied()
            .flatten()
            .ok_or_else(|| {
                WireError::invalid(
                    "compacted node reference",
                    format!("old reference {:#010x} is not live", old.raw()),
                )
            })?;
        if mapped.sort() != old.sort() {
            return Err(WireError::invalid(
                "compacted node reference",
                format!(
                    "old reference {:#010x} has sort {:?}, remapped reference has {:?}",
                    old.raw(),
                    old.sort(),
                    mapped.sort()
                ),
            ));
        }
        Ok(mapped)
    }
}

/// Append-only expression and query builder with eager sort/width validation.
#[derive(Debug, Clone, Default)]
pub struct ExprBuilder {
    nodes: Vec<RawNode>,
    children: Vec<NodeRef>,
    blob: Vec<u8>,
    meta: Vec<NodeMeta>,
    assertions: Vec<Assertion>,
    assumptions: Vec<NodeRef>,
    scopes: Vec<usize>,
}

impl ExprBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reset(&mut self) {
        self.nodes.clear();
        self.children.clear();
        self.blob.clear();
        self.meta.clear();
        self.assertions.clear();
        self.assumptions.clear();
        self.scopes.clear();
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn child_count(&self) -> usize {
        self.children.len()
    }

    pub fn blob_len(&self) -> usize {
        self.blob.len()
    }

    pub fn assertions(&self) -> &[Assertion] {
        &self.assertions
    }

    pub fn assumptions(&self) -> &[NodeRef] {
        &self.assumptions
    }

    pub fn to_expression_buffer(&self) -> Result<ExpressionBuffer> {
        ExpressionBuffer::from_parts(&self.nodes, &self.children, &self.blob)
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        Ok(self.to_expression_buffer()?.into_bytes())
    }

    /// Compact nodes reachable from `roots`, preserving topological order and
    /// remapping typed references. The blob table is kept intact so named
    /// assertion references remain valid.
    pub fn compact(&self, roots: &[NodeRef]) -> Result<CompactedExpression> {
        let mut marked = vec![false; self.nodes.len()];
        for root in roots {
            self.mark_ref(*root, &mut marked)?;
        }

        let mut old_to_new = vec![None; self.nodes.len()];
        for (old_index, is_live) in marked.iter().copied().enumerate() {
            if is_live {
                let meta = self.meta[old_index];
                let new_index = old_to_new.iter().filter(|entry| entry.is_some()).count() as u32;
                old_to_new[old_index] = Some(NodeRef::new(meta.sort, new_index)?);
            }
        }

        let mut new_nodes = Vec::new();
        let mut new_children = Vec::new();
        for (old_index, is_live) in marked.iter().copied().enumerate() {
            if !is_live {
                continue;
            }
            let old_node = self.nodes[old_index];
            let child_start = new_children.len();
            for child_offset in 0..old_node.arity as usize {
                let old_child = self.children[old_node.children as usize + child_offset];
                let new_child = old_to_new
                    .get(old_child.index() as usize)
                    .copied()
                    .flatten()
                    .ok_or_else(|| {
                        WireError::invalid(
                            "compaction",
                            format!(
                                "live node {old_index} references non-live child {old_child:?}"
                            ),
                        )
                    })?;
                new_children.push(new_child);
            }
            let mut new_node = old_node;
            new_node.children = if old_node.arity == 0 {
                0
            } else {
                u32::try_from(child_start)
                    .map_err(|_| WireError::invalid("compaction", "child array exceeds u32::MAX"))?
            };
            new_nodes.push(new_node);
        }

        let expression = ExpressionBuffer::from_parts(&new_nodes, &new_children, &self.blob)?;
        Ok(CompactedExpression {
            bytes: expression.into_bytes(),
            old_to_new,
        })
    }

    pub fn push(&mut self) {
        self.scopes.push(self.assertions.len());
    }

    pub fn pop(&mut self) -> Result<()> {
        let len = self
            .scopes
            .pop()
            .ok_or_else(|| WireError::invalid("scope", "pop without matching push"))?;
        self.assertions.truncate(len);
        Ok(())
    }

    pub fn assert(&mut self, root: NodeRef) -> Result<()> {
        self.expect_bool(root)?;
        self.assertions.push(Assertion { root, name: None });
        Ok(())
    }

    pub fn assert_named(&mut self, name: &str, root: NodeRef) -> Result<()> {
        self.expect_bool(root)?;
        let name_ref = self.push_blob(name.as_bytes())?;
        self.assertions.push(Assertion {
            root,
            name: Some(name_ref),
        });
        Ok(())
    }

    pub fn assume(&mut self, root: NodeRef) -> Result<()> {
        self.expect_bool(root)?;
        self.assumptions.push(root);
        Ok(())
    }

    pub fn clear_assumptions(&mut self) {
        self.assumptions.clear();
    }

    pub fn build_solve_request(
        &self,
        request_id: u32,
        budget_ms: u32,
        want_model: bool,
        want_core: bool,
    ) -> Result<Vec<u8>> {
        let mut flags = 0;
        if want_model {
            flags |= request_flags::WANT_MODEL;
        }
        if want_core {
            flags |= request_flags::WANT_CORE;
        }
        self.build_request(request_id, Command::Solve, flags, budget_ms, None)
    }

    pub fn build_simplify_request(&self, request_id: u32, target: NodeRef) -> Result<Vec<u8>> {
        self.meta_for(target)?;
        self.build_request(request_id, Command::Simplify, 0, 0, Some(target))
    }

    pub fn build_minimize_request(
        &self,
        request_id: u32,
        target: NodeRef,
        signed: bool,
        budget_ms: u32,
        want_model: bool,
    ) -> Result<Vec<u8>> {
        self.expect_bv(target)?;
        let mut flags = 0;
        if signed {
            flags |= request_flags::SIGNED;
        }
        if want_model {
            flags |= request_flags::WANT_MODEL;
        }
        self.build_request(
            request_id,
            Command::Minimize,
            flags,
            budget_ms,
            Some(target),
        )
    }

    pub fn build_maximize_request(
        &self,
        request_id: u32,
        target: NodeRef,
        signed: bool,
        budget_ms: u32,
        want_model: bool,
    ) -> Result<Vec<u8>> {
        self.expect_bv(target)?;
        let mut flags = 0;
        if signed {
            flags |= request_flags::SIGNED;
        }
        if want_model {
            flags |= request_flags::WANT_MODEL;
        }
        self.build_request(
            request_id,
            Command::Maximize,
            flags,
            budget_ms,
            Some(target),
        )
    }

    pub fn build_request(
        &self,
        request_id: u32,
        command: Command,
        flags: u8,
        budget_ms: u32,
        target: Option<NodeRef>,
    ) -> Result<Vec<u8>> {
        let (ordered_assertions, named_refs, source_assumptions) =
            if matches!(command, Command::Simplify) {
                (Vec::new(), Vec::new(), Vec::new())
            } else {
                let mut named = Vec::new();
                let mut unnamed = Vec::new();
                for assertion in &self.assertions {
                    if assertion.name.is_some() {
                        named.push(*assertion);
                    } else {
                        unnamed.push(*assertion);
                    }
                }
                let ordered_assertions = named
                    .iter()
                    .copied()
                    .chain(unnamed.iter().copied())
                    .collect::<Vec<_>>();
                let named_refs = named
                    .iter()
                    .map(|assertion| assertion.name.expect("named assertion has name"))
                    .collect::<Vec<_>>();
                (ordered_assertions, named_refs, self.assumptions.clone())
            };

        let mut live_roots = Vec::new();
        live_roots.extend(ordered_assertions.iter().map(|assertion| assertion.root));
        live_roots.extend(source_assumptions.iter().copied());
        if let Some(target) = target {
            live_roots.push(target);
        }
        let compacted = self.compact(&live_roots)?;
        let assertion_roots = ordered_assertions
            .iter()
            .map(|assertion| compacted.remap_ref(assertion.root))
            .collect::<Result<Vec<_>>>()?;
        let assumption_roots = source_assumptions
            .iter()
            .map(|root| compacted.remap_ref(*root))
            .collect::<Result<Vec<_>>>()?;
        let target = target.map(|root| compacted.remap_ref(root)).transpose()?;

        let request = BinaryRequest::new(
            request_id,
            command,
            flags,
            budget_ms,
            compacted.into_bytes(),
            assertion_roots,
            named_refs,
            assumption_roots,
            target,
        )?;
        request.encode()
    }

    pub fn bv_var(&mut self, name: &str, width: u32) -> Result<NodeRef> {
        validate_bv_width_value(width, "BV variable width")?;
        let payload = self.push_blob(name.as_bytes())?.to_payload();
        self.push_node(Tag::BvVar, width, &[], 0, 0, payload)
    }

    pub fn bv_const(&mut self, value: u64, width: u32) -> Result<NodeRef> {
        validate_bv_width_value(width, "BV constant width")?;
        if width <= 64 {
            let payload = mask_u64(value, width);
            self.push_node(Tag::BvConst, width, &[], 0, 0, payload)
        } else {
            let mut bytes = vec![0u8; bytes_for_width(width)?];
            bytes[..8].copy_from_slice(&value.to_le_bytes());
            mask_unused_high_bits(&mut bytes, width);
            let payload = self.push_blob(&bytes)?.to_payload();
            self.push_node(Tag::BvConst, width, &[], 0, 0, payload)
        }
    }

    pub fn bv_const_wide(&mut self, bytes: &[u8], width: u32) -> Result<NodeRef> {
        validate_bv_width_value(width, "wide BV constant width")?;
        let expected = bytes_for_width(width)?;
        if bytes.len() != expected {
            return Err(WireError::invalid(
                "wide BV constant",
                format!(
                    "got {} bytes, expected {expected} for width {width}",
                    bytes.len()
                ),
            ));
        }
        let mut normalized = bytes.to_vec();
        mask_unused_high_bits(&mut normalized, width);
        if width <= 64 {
            let mut arr = [0u8; 8];
            arr[..normalized.len()].copy_from_slice(&normalized);
            self.bv_const(u64::from_le_bytes(arr), width)
        } else {
            let payload = self.push_blob(&normalized)?.to_payload();
            self.push_node(Tag::BvConst, width, &[], 0, 0, payload)
        }
    }

    pub fn bv_not(&mut self, x: NodeRef) -> Result<NodeRef> {
        self.bv_unary(Tag::BvNot, x)
    }

    pub fn bv_neg(&mut self, x: NodeRef) -> Result<NodeRef> {
        self.bv_unary(Tag::BvNeg, x)
    }

    pub fn bv_and(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvAnd, a, b)
    }

    pub fn bv_or(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvOr, a, b)
    }

    pub fn bv_xor(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvXor, a, b)
    }

    pub fn bv_add(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvAdd, a, b)
    }

    pub fn bv_sub(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvSub, a, b)
    }

    pub fn bv_mul(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvMul, a, b)
    }

    pub fn bv_udiv(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvUdiv, a, b)
    }

    pub fn bv_urem(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvUrem, a, b)
    }

    pub fn bv_sdiv(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvSdiv, a, b)
    }

    pub fn bv_srem(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvSrem, a, b)
    }

    pub fn bv_smod(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvSmod, a, b)
    }

    pub fn bv_shl(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvShl, a, b)
    }

    pub fn bv_lshr(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvLshr, a, b)
    }

    pub fn bv_ashr(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_binary(Tag::BvAshr, a, b)
    }

    pub fn bv_extract(&mut self, x: NodeRef, hi: u32, lo: u32) -> Result<NodeRef> {
        let width = self.expect_bv(x)?;
        if hi > u16::MAX as u32 {
            return Err(WireError::invalid(
                "BV_EXTRACT",
                format!("hi {hi} exceeds u16::MAX"),
            ));
        }
        if lo > hi || hi >= width {
            return Err(WireError::invalid(
                "BV_EXTRACT",
                format!("invalid bounds lo={lo}, hi={hi}, child width {width}"),
            ));
        }
        self.push_node(Tag::BvExtract, hi - lo + 1, &[x], hi as u16, lo, 0)
    }

    pub fn bv_concat(&mut self, high: NodeRef, low: NodeRef) -> Result<NodeRef> {
        let high_width = self.expect_bv(high)?;
        let low_width = self.expect_bv(low)?;
        let width = high_width
            .checked_add(low_width)
            .ok_or(WireError::IntegerOverflow("BV_CONCAT width"))?;
        validate_bv_width_value(width, "BV_CONCAT width")?;
        self.push_node(Tag::BvConcat, width, &[high, low], 0, 0, 0)
    }

    pub fn bv_zext(&mut self, x: NodeRef, amount: u16) -> Result<NodeRef> {
        self.bv_extend(Tag::BvZext, x, amount)
    }

    pub fn bv_sext(&mut self, x: NodeRef, amount: u16) -> Result<NodeRef> {
        self.bv_extend(Tag::BvSext, x, amount)
    }

    pub fn bv_ite(
        &mut self,
        cond: NodeRef,
        then_value: NodeRef,
        else_value: NodeRef,
    ) -> Result<NodeRef> {
        self.expect_bool(cond)?;
        let width = self.expect_same_bv_width(then_value, else_value, "BV_ITE")?;
        self.push_node(Tag::BvIte, width, &[cond, then_value, else_value], 0, 0, 0)
    }

    pub fn bv_select(
        &mut self,
        selectors: &[NodeRef],
        values: &[NodeRef],
        default: NodeRef,
    ) -> Result<NodeRef> {
        if selectors.len() != values.len() {
            return Err(WireError::invalid(
                "BV_SELECT",
                format!("{} selectors but {} values", selectors.len(), values.len()),
            ));
        }
        if selectors.len() > 127 {
            return Err(WireError::invalid(
                "BV_SELECT",
                format!("{} pairs exceeds v1 limit of 127", selectors.len()),
            ));
        }
        let width = self.expect_bv(default)?;
        let mut children = Vec::with_capacity(selectors.len() * 2 + 1);
        for (&selector, &value) in selectors.iter().zip(values) {
            self.expect_bool(selector)?;
            let value_width = self.expect_bv(value)?;
            if value_width != width {
                return Err(WireError::invalid(
                    "BV_SELECT",
                    format!("value width {value_width} does not match default width {width}"),
                ));
            }
            children.push(selector);
            children.push(value);
        }
        children.push(default);
        self.push_node(
            Tag::BvSelect,
            width,
            &children,
            selectors.len() as u16,
            0,
            0,
        )
    }

    pub fn bool_true(&mut self) -> Result<NodeRef> {
        self.push_node(Tag::BoolTrue, 0, &[], 0, 0, 0)
    }

    pub fn bool_false(&mut self) -> Result<NodeRef> {
        self.push_node(Tag::BoolFalse, 0, &[], 0, 0, 0)
    }

    pub fn bool_var(&mut self, name: &str) -> Result<NodeRef> {
        let payload = self.push_blob(name.as_bytes())?.to_payload();
        self.push_node(Tag::BoolVar, 0, &[], 0, 0, payload)
    }

    pub fn bool_not(&mut self, x: NodeRef) -> Result<NodeRef> {
        self.expect_bool(x)?;
        self.push_node(Tag::BoolNot, 0, &[x], 0, 0, 0)
    }

    pub fn bool_and(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bool_binary(Tag::BoolAnd, a, b)
    }

    pub fn bool_or(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bool_binary(Tag::BoolOr, a, b)
    }

    pub fn bool_implies(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bool_binary(Tag::BoolImplies, a, b)
    }

    pub fn bv_eq(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_comparison(Tag::BvEq, a, b)
    }

    pub fn bv_ult(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_comparison(Tag::BvUlt, a, b)
    }

    pub fn bv_ule(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_comparison(Tag::BvUle, a, b)
    }

    pub fn bv_slt(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_comparison(Tag::BvSlt, a, b)
    }

    pub fn bv_sle(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_comparison(Tag::BvSle, a, b)
    }

    pub fn uadd_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::UaddOvf, a, b)
    }

    pub fn sadd_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::SaddOvf, a, b)
    }

    pub fn usub_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::UsubOvf, a, b)
    }

    pub fn ssub_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::SsubOvf, a, b)
    }

    pub fn umul_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::UmulOvf, a, b)
    }

    pub fn smul_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::SmulOvf, a, b)
    }

    pub fn neg_ovf(&mut self, x: NodeRef) -> Result<NodeRef> {
        self.expect_bv(x)?;
        self.push_node(Tag::NegOvf, 0, &[x], 0, 0, 0)
    }

    pub fn sdiv_ovf(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.overflow_binary(Tag::SdivOvf, a, b)
    }

    pub fn bv_ne(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        let eq = self.bv_eq(a, b)?;
        self.bool_not(eq)
    }

    pub fn bv_ugt(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_ult(b, a)
    }

    pub fn bv_uge(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_ule(b, a)
    }

    pub fn bv_sgt(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_slt(b, a)
    }

    pub fn bv_sge(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.bv_sle(b, a)
    }

    pub fn bool_eq(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.expect_bool(a)?;
        self.expect_bool(b)?;
        let not_b = self.bool_not(b)?;
        let left = self.bool_or(a, not_b)?;
        let not_a = self.bool_not(a)?;
        let right = self.bool_or(not_a, b)?;
        self.bool_and(left, right)
    }

    pub fn bool_xor(&mut self, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        let eq = self.bool_eq(a, b)?;
        self.bool_not(eq)
    }

    pub fn bool_ite(
        &mut self,
        cond: NodeRef,
        then_value: NodeRef,
        else_value: NodeRef,
    ) -> Result<NodeRef> {
        self.expect_bool(cond)?;
        self.expect_bool(then_value)?;
        self.expect_bool(else_value)?;
        let cond_then = self.bool_and(cond, then_value)?;
        let not_cond = self.bool_not(cond)?;
        let else_branch = self.bool_and(not_cond, else_value)?;
        self.bool_or(cond_then, else_branch)
    }

    pub fn bv_rotate_left(&mut self, x: NodeRef, amount: u64) -> Result<NodeRef> {
        let width = self.expect_bv(x)?;
        let amount = amount % u64::from(width);
        if amount == 0 {
            return Ok(x);
        }
        let left_amount = self.bv_const(amount, width)?;
        let right_amount = self.bv_const(u64::from(width) - amount, width)?;
        let left = self.bv_shl(x, left_amount)?;
        let right = self.bv_lshr(x, right_amount)?;
        self.bv_or(left, right)
    }

    pub fn bv_rotate_right(&mut self, x: NodeRef, amount: u64) -> Result<NodeRef> {
        let width = self.expect_bv(x)?;
        let amount = amount % u64::from(width);
        if amount == 0 {
            return Ok(x);
        }
        let right_amount = self.bv_const(amount, width)?;
        let left_amount = self.bv_const(u64::from(width) - amount, width)?;
        let right = self.bv_lshr(x, right_amount)?;
        let left = self.bv_shl(x, left_amount)?;
        self.bv_or(right, left)
    }

    pub fn assert_mutex(&mut self, selectors: &[NodeRef]) -> Result<()> {
        for &selector in selectors {
            self.expect_bool(selector)?;
        }
        for i in 0..selectors.len() {
            for j in (i + 1)..selectors.len() {
                let both = self.bool_and(selectors[i], selectors[j])?;
                let not_both = self.bool_not(both)?;
                self.assert(not_both)?;
            }
        }
        Ok(())
    }

    fn push_blob(&mut self, bytes: &[u8]) -> Result<BlobRef> {
        let offset = u32::try_from(self.blob.len()).map_err(|_| {
            WireError::invalid("blob table", "current blob length exceeds u32::MAX")
        })?;
        let len = u32::try_from(bytes.len())
            .map_err(|_| WireError::invalid("blob table", "blob entry exceeds u32::MAX"))?;
        let end = offset
            .checked_add(len)
            .ok_or(WireError::IntegerOverflow("blob table append"))?;
        if end as usize > u32::MAX as usize {
            return Err(WireError::invalid(
                "blob table",
                "blob table length exceeds u32::MAX",
            ));
        }
        self.blob.extend_from_slice(bytes);
        Ok(BlobRef::new(offset, len))
    }

    fn push_node(
        &mut self,
        tag: Tag,
        width: u32,
        children: &[NodeRef],
        aux_hi: u16,
        aux_lo: u32,
        payload: u64,
    ) -> Result<NodeRef> {
        let arity = u8::try_from(children.len()).map_err(|_| {
            WireError::invalid(
                "node arity",
                format!("{} children exceeds u8::MAX", children.len()),
            )
        })?;
        for child in children {
            self.meta_for(*child)?;
        }
        let child_start = u32::try_from(self.children.len()).map_err(|_| {
            WireError::invalid("child array", "child array length exceeds u32::MAX")
        })?;
        self.children.extend_from_slice(children);
        let index = u32::try_from(self.nodes.len())
            .map_err(|_| WireError::invalid("node array", "node count exceeds u32::MAX"))?;
        let id = NodeRef::new(tag.result_sort(), index)?;
        self.nodes.push(RawNode::new(
            tag.into(),
            arity,
            aux_hi,
            width,
            aux_lo,
            if arity == 0 { 0 } else { child_start },
            payload,
        ));
        self.meta.push(NodeMeta {
            sort: tag.result_sort(),
            width,
        });
        Ok(id)
    }

    fn meta_for(&self, reference: NodeRef) -> Result<NodeMeta> {
        let meta = self
            .meta
            .get(reference.index() as usize)
            .copied()
            .ok_or_else(|| {
                WireError::invalid(
                    "node reference",
                    format!("reference {:#010x} points outside builder", reference.raw()),
                )
            })?;
        if meta.sort != reference.sort() {
            return Err(WireError::invalid(
                "node reference",
                format!(
                    "reference {:#010x} has sort {:?}, node has {:?}",
                    reference.raw(),
                    reference.sort(),
                    meta.sort
                ),
            ));
        }
        Ok(meta)
    }

    fn expect_bv(&self, reference: NodeRef) -> Result<u32> {
        let meta = self.meta_for(reference)?;
        if meta.sort != Sort::Bv {
            return Err(WireError::invalid(
                "sort",
                format!("expected BV reference, got {reference:?}"),
            ));
        }
        Ok(meta.width)
    }

    fn expect_bool(&self, reference: NodeRef) -> Result<()> {
        let meta = self.meta_for(reference)?;
        if meta.sort != Sort::Bool {
            return Err(WireError::invalid(
                "sort",
                format!("expected Bool reference, got {reference:?}"),
            ));
        }
        Ok(())
    }

    fn expect_same_bv_width(&self, a: NodeRef, b: NodeRef, context: &'static str) -> Result<u32> {
        let lhs = self.expect_bv(a)?;
        let rhs = self.expect_bv(b)?;
        if lhs != rhs {
            return Err(WireError::invalid(
                context,
                format!("width mismatch: {lhs} vs {rhs}"),
            ));
        }
        Ok(lhs)
    }

    fn bv_unary(&mut self, tag: Tag, x: NodeRef) -> Result<NodeRef> {
        let width = self.expect_bv(x)?;
        self.push_node(tag, width, &[x], 0, 0, 0)
    }

    fn bv_binary(&mut self, tag: Tag, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        let width = self.expect_same_bv_width(a, b, tag.name())?;
        self.push_node(tag, width, &[a, b], 0, 0, 0)
    }

    fn bv_extend(&mut self, tag: Tag, x: NodeRef, amount: u16) -> Result<NodeRef> {
        let width = self
            .expect_bv(x)?
            .checked_add(u32::from(amount))
            .ok_or(WireError::IntegerOverflow("BV extension width"))?;
        validate_bv_width_value(width, "BV extension width")?;
        self.push_node(tag, width, &[x], amount, 0, 0)
    }

    fn bool_binary(&mut self, tag: Tag, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.expect_bool(a)?;
        self.expect_bool(b)?;
        self.push_node(tag, 0, &[a, b], 0, 0, 0)
    }

    fn bv_comparison(&mut self, tag: Tag, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.expect_same_bv_width(a, b, tag.name())?;
        self.push_node(tag, 0, &[a, b], 0, 0, 0)
    }

    fn overflow_binary(&mut self, tag: Tag, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        self.expect_same_bv_width(a, b, tag.name())?;
        self.push_node(tag, 0, &[a, b], 0, 0, 0)
    }

    fn mark_ref(&self, reference: NodeRef, marked: &mut [bool]) -> Result<()> {
        self.meta_for(reference)?;
        let index = reference.index() as usize;
        if marked[index] {
            return Ok(());
        }
        marked[index] = true;
        let node = self.nodes[index];
        for child_offset in 0..node.arity as usize {
            let child = self.children[node.children as usize + child_offset];
            self.mark_ref(child, marked)?;
        }
        Ok(())
    }
}

fn mask_u64(value: u64, width: u32) -> u64 {
    if width >= 64 {
        value
    } else {
        value & ((1u64 << width) - 1)
    }
}

fn mask_unused_high_bits(bytes: &mut [u8], width: u32) {
    let valid_bits = width % 8;
    if valid_bits == 0 || bytes.is_empty() {
        return;
    }
    let mask = (1u8 << valid_bits) - 1;
    let last = bytes.len() - 1;
    bytes[last] &= mask;
}
