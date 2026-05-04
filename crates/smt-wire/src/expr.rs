use crate::constants::{self, tag, Tag, EXPR_HEADER_LEN, NODE_RECORD_LEN};
use crate::error::{Result, WireError};
use crate::le;
use crate::types::{BlobRef, NodeRef, Sort};

pub const MAX_BV_WIDTH: u32 = 65_536;
pub const MAX_NODE_COUNT: u32 = 1 << 31;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExprHeader {
    pub node_count: u32,
    pub child_count: u32,
    pub blob_len: u32,
}

impl ExprHeader {
    pub fn total_len(self) -> Result<usize> {
        expression_len(self.node_count, self.child_count, self.blob_len)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RawNode {
    pub tag: u8,
    pub arity: u8,
    pub aux_hi: u16,
    pub width: u32,
    pub aux_lo: u32,
    pub children: u32,
    pub payload: u64,
}

impl RawNode {
    pub const fn new(
        tag: u8,
        arity: u8,
        aux_hi: u16,
        width: u32,
        aux_lo: u32,
        children: u32,
        payload: u64,
    ) -> Self {
        Self {
            tag,
            arity,
            aux_hi,
            width,
            aux_lo,
            children,
            payload,
        }
    }

    pub fn decode(bytes: &[u8], offset: usize) -> Result<Self> {
        Ok(Self {
            tag: le::read_u8(bytes, offset, "node tag")?,
            arity: le::read_u8(bytes, offset + 1, "node arity")?,
            aux_hi: le::read_u16(bytes, offset + 2, "node aux_hi")?,
            width: le::read_u32(bytes, offset + 4, "node width")?,
            aux_lo: le::read_u32(bytes, offset + 8, "node aux_lo")?,
            children: le::read_u32(bytes, offset + 12, "node children")?,
            payload: le::read_u64(bytes, offset + 16, "node payload")?,
        })
    }

    pub fn encode(&self, dst: &mut Vec<u8>) {
        le::write_u8(dst, self.tag);
        le::write_u8(dst, self.arity);
        le::write_u16(dst, self.aux_hi);
        le::write_u32(dst, self.width);
        le::write_u32(dst, self.aux_lo);
        le::write_u32(dst, self.children);
        le::write_u64(dst, self.payload);
    }

    pub const fn blob_ref(self) -> BlobRef {
        BlobRef::from_payload(self.payload)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionBuffer {
    bytes: Vec<u8>,
}

impl ExpressionBuffer {
    pub fn empty() -> Self {
        Self::from_parts(&[], &[], &[]).expect("empty expression buffer is always valid")
    }

    pub fn from_parts(nodes: &[RawNode], children: &[NodeRef], blob: &[u8]) -> Result<Self> {
        let node_count = u32::try_from(nodes.len()).map_err(|_| {
            WireError::invalid(
                "expression buffer",
                format!("node count {} exceeds u32::MAX", nodes.len()),
            )
        })?;
        if node_count > MAX_NODE_COUNT {
            return Err(WireError::invalid(
                "expression buffer",
                format!("node count {node_count} exceeds 2^31"),
            ));
        }
        let child_count = u32::try_from(children.len()).map_err(|_| {
            WireError::invalid(
                "expression buffer",
                format!("child count {} exceeds u32::MAX", children.len()),
            )
        })?;
        let blob_len = u32::try_from(blob.len()).map_err(|_| {
            WireError::invalid(
                "expression buffer",
                format!("blob length {} exceeds u32::MAX", blob.len()),
            )
        })?;
        let expected_len = expression_len(node_count, child_count, blob_len)?;
        let mut out = Vec::with_capacity(expected_len);
        out.extend_from_slice(&constants::EXPR_MAGIC);
        le::write_u8(&mut out, constants::VERSION);
        out.extend_from_slice(&[0u8; 3]);
        le::write_u32(&mut out, node_count);
        le::write_u32(&mut out, child_count);
        le::write_u32(&mut out, blob_len);
        out.extend_from_slice(&[0u8; 12]);
        for node in nodes {
            node.encode(&mut out);
        }
        for child in children {
            le::write_u32(&mut out, child.raw());
        }
        out.extend_from_slice(blob);
        debug_assert_eq!(out.len(), expected_len);
        Ok(Self { bytes: out })
    }

    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self> {
        ExprView::parse(&bytes)?;
        Ok(Self { bytes })
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    pub fn view(&self) -> Result<ExprView<'_>> {
        ExprView::parse(&self.bytes)
    }

    pub fn validate(&self) -> Result<()> {
        self.view()?.validate()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExprView<'a> {
    bytes: &'a [u8],
    header: ExprHeader,
    node_offset: usize,
    child_offset: usize,
    blob_offset: usize,
}

impl<'a> ExprView<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self> {
        if bytes.len() < EXPR_HEADER_LEN {
            return Err(WireError::UnexpectedEof {
                context: "expression header",
                needed: EXPR_HEADER_LEN,
                actual: bytes.len(),
            });
        }
        let magic = le::exact_slice(bytes, 0, 4, "expression magic")?;
        if magic != constants::EXPR_MAGIC {
            return Err(WireError::BadMagic {
                context: "expression buffer",
                expected: &constants::EXPR_MAGIC,
                actual: magic.to_vec(),
            });
        }
        let version = le::read_u8(bytes, 4, "expression version")?;
        if version != constants::VERSION {
            return Err(WireError::UnsupportedVersion(version));
        }
        let header = ExprHeader {
            node_count: le::read_u32(bytes, 8, "expression node_count")?,
            child_count: le::read_u32(bytes, 12, "expression child_count")?,
            blob_len: le::read_u32(bytes, 16, "expression blob_len")?,
        };
        if header.node_count > MAX_NODE_COUNT {
            return Err(WireError::invalid(
                "expression node_count",
                format!("{} exceeds 2^31", header.node_count),
            ));
        }
        let expected = header.total_len()?;
        if bytes.len() != expected {
            return Err(WireError::LengthMismatch {
                context: "expression buffer",
                expected,
                actual: bytes.len(),
            });
        }
        let node_offset = EXPR_HEADER_LEN;
        let node_bytes = le::checked_mul(
            header.node_count as usize,
            NODE_RECORD_LEN,
            "expression node array length",
        )?;
        let child_offset = le::checked_add(node_offset, node_bytes, "expression child offset")?;
        let child_bytes = le::checked_mul(
            header.child_count as usize,
            4,
            "expression child array length",
        )?;
        let blob_offset = le::checked_add(child_offset, child_bytes, "expression blob offset")?;
        Ok(Self {
            bytes,
            header,
            node_offset,
            child_offset,
            blob_offset,
        })
    }

    pub fn parse_and_validate(bytes: &'a [u8]) -> Result<Self> {
        let view = Self::parse(bytes)?;
        view.validate()?;
        Ok(view)
    }

    pub const fn header(&self) -> ExprHeader {
        self.header
    }

    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub fn node_count(&self) -> u32 {
        self.header.node_count
    }

    pub fn child_count(&self) -> u32 {
        self.header.child_count
    }

    pub fn blob_len(&self) -> u32 {
        self.header.blob_len
    }

    pub fn node(&self, index: u32) -> Result<RawNode> {
        if index >= self.header.node_count {
            return Err(WireError::invalid(
                "node index",
                format!(
                    "{index} is out of bounds for {} nodes",
                    self.header.node_count
                ),
            ));
        }
        let index_bytes = le::checked_mul(index as usize, NODE_RECORD_LEN, "node offset")?;
        let offset = le::checked_add(self.node_offset, index_bytes, "node offset")?;
        RawNode::decode(self.bytes, offset)
    }

    pub fn child_ref(&self, index: u32) -> Result<NodeRef> {
        if index >= self.header.child_count {
            return Err(WireError::invalid(
                "child index",
                format!(
                    "{index} is out of bounds for {} children",
                    self.header.child_count
                ),
            ));
        }
        let index_bytes = le::checked_mul(index as usize, 4, "child offset")?;
        let offset = le::checked_add(self.child_offset, index_bytes, "child offset")?;
        Ok(NodeRef::from_raw(le::read_u32(
            self.bytes,
            offset,
            "child reference",
        )?))
    }

    pub fn blob(&self) -> &'a [u8] {
        &self.bytes[self.blob_offset..]
    }

    pub fn blob_ref(&self, reference: BlobRef) -> Result<&'a [u8]> {
        let start = reference.offset as usize;
        let len = reference.len as usize;
        let end = start
            .checked_add(len)
            .ok_or(WireError::IntegerOverflow("blob reference"))?;
        if end > self.blob().len() {
            return Err(WireError::invalid(
                "blob reference",
                format!(
                    "offset {} plus length {} exceeds blob length {}",
                    reference.offset,
                    reference.len,
                    self.blob().len()
                ),
            ));
        }
        Ok(&self.blob()[start..end])
    }

    pub fn blob_str(&self, reference: BlobRef, context: &'static str) -> Result<&'a str> {
        let bytes = self.blob_ref(reference)?;
        core::str::from_utf8(bytes).map_err(|_| WireError::InvalidUtf8 {
            context,
            offset: reference.offset,
            len: reference.len,
        })
    }

    pub fn validate(&self) -> Result<()> {
        let mut meta = Vec::with_capacity(self.header.node_count as usize);
        for index in 0..self.header.node_count {
            let node = self.node(index)?;
            let tag = parse_tag(node.tag, index)?;
            validate_arity(index, tag, node.arity)?;
            let sort = tag.result_sort();
            validate_node_width(index, tag, node.width)?;
            if matches!(tag, Tag::BvVar | Tag::BoolVar) {
                self.blob_str(node.blob_ref(), "symbol name")?;
            }
            if matches!(tag, Tag::BvConst) && node.width > 64 {
                let reference = node.blob_ref();
                let expected_len = bytes_for_width(node.width)?;
                if reference.len as usize != expected_len {
                    return Err(WireError::invalid(
                        "wide BV_CONST",
                        format!(
                            "node {index} has blob length {}, expected {expected_len} for width {}",
                            reference.len, node.width
                        ),
                    ));
                }
                self.blob_ref(reference)?;
            }
            meta.push(NodeInfo {
                tag,
                sort,
                width: node.width,
            });
        }

        for index in 0..self.header.node_count {
            let node = self.node(index)?;
            let info = meta[index as usize];
            validate_children_range(self.header.child_count, index, &node)?;
            match info.tag {
                Tag::BvVar | Tag::BvConst | Tag::BoolTrue | Tag::BoolFalse | Tag::BoolVar => {}
                Tag::BvNot | Tag::BvNeg => {
                    let child = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    expect_width(index, info.tag, node.width, child.width, "unary BV result")?;
                }
                Tag::BvAnd
                | Tag::BvOr
                | Tag::BvXor
                | Tag::BvAdd
                | Tag::BvSub
                | Tag::BvMul
                | Tag::BvUdiv
                | Tag::BvUrem
                | Tag::BvSdiv
                | Tag::BvSrem
                | Tag::BvSmod
                | Tag::BvShl
                | Tag::BvLshr
                | Tag::BvAshr => {
                    let lhs = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    let rhs = self.expect_child(&meta, index, &node, 1, Sort::Bv)?;
                    expect_same_child_width(index, info.tag, lhs.width, rhs.width)?;
                    expect_width(index, info.tag, node.width, lhs.width, "binary BV result")?;
                }
                Tag::BvExtract => {
                    let child = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    let lo = node.aux_lo;
                    let hi = u32::from(node.aux_hi);
                    if lo > hi || hi >= child.width {
                        return Err(WireError::invalid(
                            "BV_EXTRACT bounds",
                            format!(
                                "node {index} has lo={lo}, hi={hi}, child width {}",
                                child.width
                            ),
                        ));
                    }
                    let expected = hi - lo + 1;
                    expect_width(index, info.tag, node.width, expected, "extract result")?;
                }
                Tag::BvConcat => {
                    let hi = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    let lo = self.expect_child(&meta, index, &node, 1, Sort::Bv)?;
                    let expected = hi
                        .width
                        .checked_add(lo.width)
                        .ok_or(WireError::IntegerOverflow("BV_CONCAT width"))?;
                    validate_bv_width_value(expected, "BV_CONCAT result")?;
                    expect_width(index, info.tag, node.width, expected, "concat result")?;
                }
                Tag::BvZext | Tag::BvSext => {
                    let child = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    let expected = child
                        .width
                        .checked_add(u32::from(node.aux_hi))
                        .ok_or(WireError::IntegerOverflow("BV_EXT width"))?;
                    validate_bv_width_value(expected, "BV_EXT result")?;
                    expect_width(index, info.tag, node.width, expected, "extension result")?;
                }
                Tag::BvIte => {
                    self.expect_child(&meta, index, &node, 0, Sort::Bool)?;
                    let then_child = self.expect_child(&meta, index, &node, 1, Sort::Bv)?;
                    let else_child = self.expect_child(&meta, index, &node, 2, Sort::Bv)?;
                    expect_same_child_width(index, info.tag, then_child.width, else_child.width)?;
                    expect_width(
                        index,
                        info.tag,
                        node.width,
                        then_child.width,
                        "BV_ITE result",
                    )?;
                }
                Tag::BvSelect => {
                    validate_select_shape(index, &node)?;
                    let pairs = usize::from(node.aux_hi);
                    let default = self.expect_child(&meta, index, &node, pairs * 2, Sort::Bv)?;
                    for pair in 0..pairs {
                        self.expect_child(&meta, index, &node, pair * 2, Sort::Bool)?;
                        let value =
                            self.expect_child(&meta, index, &node, pair * 2 + 1, Sort::Bv)?;
                        expect_same_child_width(index, info.tag, value.width, default.width)?;
                    }
                    expect_width(
                        index,
                        info.tag,
                        node.width,
                        default.width,
                        "BV_SELECT result",
                    )?;
                }
                Tag::BoolNot => {
                    self.expect_child(&meta, index, &node, 0, Sort::Bool)?;
                }
                Tag::BoolAnd | Tag::BoolOr | Tag::BoolImplies => {
                    self.expect_child(&meta, index, &node, 0, Sort::Bool)?;
                    self.expect_child(&meta, index, &node, 1, Sort::Bool)?;
                }
                Tag::BvEq | Tag::BvUlt | Tag::BvUle | Tag::BvSlt | Tag::BvSle => {
                    let lhs = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    let rhs = self.expect_child(&meta, index, &node, 1, Sort::Bv)?;
                    expect_same_child_width(index, info.tag, lhs.width, rhs.width)?;
                }
                Tag::UaddOvf
                | Tag::SaddOvf
                | Tag::UsubOvf
                | Tag::SsubOvf
                | Tag::UmulOvf
                | Tag::SmulOvf
                | Tag::SdivOvf => {
                    let lhs = self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                    let rhs = self.expect_child(&meta, index, &node, 1, Sort::Bv)?;
                    expect_same_child_width(index, info.tag, lhs.width, rhs.width)?;
                }
                Tag::NegOvf => {
                    self.expect_child(&meta, index, &node, 0, Sort::Bv)?;
                }
            }
        }
        Ok(())
    }

    fn expect_child(
        &self,
        meta: &[NodeInfo],
        parent_index: u32,
        parent: &RawNode,
        child_offset: usize,
        expected_sort: Sort,
    ) -> Result<NodeInfo> {
        let child_array_index = parent
            .children
            .checked_add(child_offset as u32)
            .ok_or(WireError::IntegerOverflow("child array index"))?;
        let reference = self.child_ref(child_array_index)?;
        validate_ref(
            meta,
            reference,
            expected_sort,
            Some(parent_index),
            "child reference",
        )
    }
}

#[derive(Debug, Clone, Copy)]
struct NodeInfo {
    tag: Tag,
    sort: Sort,
    width: u32,
}

fn expression_len(node_count: u32, child_count: u32, blob_len: u32) -> Result<usize> {
    let node_bytes = le::checked_mul(
        node_count as usize,
        NODE_RECORD_LEN,
        "expression node array length",
    )?;
    let after_nodes = le::checked_add(EXPR_HEADER_LEN, node_bytes, "expression length")?;
    let child_bytes = le::checked_mul(child_count as usize, 4, "expression child array length")?;
    let after_children = le::checked_add(after_nodes, child_bytes, "expression length")?;
    le::checked_add(after_children, blob_len as usize, "expression length")
}

fn parse_tag(raw: u8, node_index: u32) -> Result<Tag> {
    Tag::try_from(raw).map_err(|_| {
        WireError::invalid(
            "node tag",
            format!("node {node_index} uses unknown v1 tag {raw}"),
        )
    })
}

fn validate_arity(index: u32, tag: Tag, arity: u8) -> Result<()> {
    if let Some(expected) = tag.fixed_arity() {
        if arity != expected {
            return Err(WireError::invalid(
                "node arity",
                format!(
                    "node {index} ({}) has arity {arity}, expected {expected}",
                    tag.name()
                ),
            ));
        }
    } else {
        validate_select_arity(index, arity)?;
    }
    Ok(())
}

fn validate_select_arity(index: u32, arity: u8) -> Result<()> {
    if arity == 0 || arity.is_multiple_of(2) {
        return Err(WireError::invalid(
            "BV_SELECT arity",
            format!("node {index} has arity {arity}, expected odd 2N+1"),
        ));
    }
    Ok(())
}

fn validate_select_shape(index: u32, node: &RawNode) -> Result<()> {
    validate_select_arity(index, node.arity)?;
    let expected_pairs = (u16::from(node.arity) - 1) / 2;
    if node.aux_hi != expected_pairs {
        return Err(WireError::invalid(
            "BV_SELECT aux_hi",
            format!(
                "node {index} has aux_hi {}, expected {expected_pairs}",
                node.aux_hi
            ),
        ));
    }
    Ok(())
}

fn validate_node_width(index: u32, tag: Tag, width: u32) -> Result<()> {
    match tag.result_sort() {
        Sort::Bool => {
            if width != 0 {
                return Err(WireError::invalid(
                    "Bool node width",
                    format!(
                        "node {index} ({}) has width {width}, expected 0",
                        tag.name()
                    ),
                ));
            }
        }
        Sort::Bv => validate_bv_width_value(width, "BV node width").map_err(|_| {
            WireError::invalid(
                "BV node width",
                format!(
                    "node {index} ({}) has width {width}, expected 1..={MAX_BV_WIDTH}",
                    tag.name()
                ),
            )
        })?,
    }
    Ok(())
}

pub(crate) fn validate_bv_width_value(width: u32, context: &'static str) -> Result<()> {
    if !(1..=MAX_BV_WIDTH).contains(&width) {
        return Err(WireError::invalid(
            context,
            format!("width {width} is outside 1..={MAX_BV_WIDTH}"),
        ));
    }
    Ok(())
}

fn validate_children_range(child_count: u32, index: u32, node: &RawNode) -> Result<()> {
    if node.arity == 0 {
        return Ok(());
    }
    let end = node
        .children
        .checked_add(u32::from(node.arity))
        .ok_or(WireError::IntegerOverflow("node child range"))?;
    if end > child_count {
        return Err(WireError::invalid(
            "node child range",
            format!(
                "node {index} children [{}..{}) exceeds child_count {child_count}",
                node.children, end
            ),
        ));
    }
    Ok(())
}

fn validate_ref(
    meta: &[NodeInfo],
    reference: NodeRef,
    expected_sort: Sort,
    parent_index: Option<u32>,
    context: &'static str,
) -> Result<NodeInfo> {
    let index = reference.index();
    if index as usize >= meta.len() {
        return Err(WireError::invalid(
            context,
            format!(
                "reference {:#010x} points outside {} nodes",
                reference.raw(),
                meta.len()
            ),
        ));
    }
    if reference.sort() != expected_sort {
        return Err(WireError::invalid(
            context,
            format!(
                "reference {:#010x} has sort {:?}, expected {:?}",
                reference.raw(),
                reference.sort(),
                expected_sort
            ),
        ));
    }
    let info = meta[index as usize];
    if info.sort != reference.sort() {
        return Err(WireError::invalid(
            context,
            format!(
                "reference {:#010x} sort {:?} does not match node tag sort {:?}",
                reference.raw(),
                reference.sort(),
                info.sort
            ),
        ));
    }
    if let Some(parent) = parent_index {
        if index >= parent {
            return Err(WireError::invalid(
                context,
                format!("parent node {parent} references non-earlier child node {index}"),
            ));
        }
    }
    Ok(info)
}

fn expect_width(
    index: u32,
    tag: Tag,
    actual: u32,
    expected: u32,
    context: &'static str,
) -> Result<()> {
    if actual != expected {
        return Err(WireError::invalid(
            context,
            format!(
                "node {index} ({}) has width {actual}, expected {expected}",
                tag.name()
            ),
        ));
    }
    Ok(())
}

fn expect_same_child_width(index: u32, tag: Tag, lhs: u32, rhs: u32) -> Result<()> {
    if lhs != rhs {
        return Err(WireError::invalid(
            "child widths",
            format!(
                "node {index} ({}) has child widths {lhs} and {rhs}",
                tag.name()
            ),
        ));
    }
    Ok(())
}

pub(crate) fn bytes_for_width(width: u32) -> Result<usize> {
    validate_bv_width_value(width, "scalar width")?;
    Ok((width as usize).div_ceil(8))
}

/// Validate a typed node reference against an already-validated expression view.
pub fn validate_node_ref(
    view: &ExprView<'_>,
    reference: NodeRef,
    expected_sort: Sort,
    context: &'static str,
) -> Result<RawNode> {
    let index = reference.index();
    if index >= view.node_count() {
        return Err(WireError::invalid(
            context,
            format!(
                "reference {:#010x} points outside {} nodes",
                reference.raw(),
                view.node_count()
            ),
        ));
    }
    if reference.sort() != expected_sort {
        return Err(WireError::invalid(
            context,
            format!(
                "reference {:#010x} has sort {:?}, expected {:?}",
                reference.raw(),
                reference.sort(),
                expected_sort
            ),
        ));
    }
    let node = view.node(index)?;
    let tag = parse_tag(node.tag, index)?;
    if tag.result_sort() != reference.sort() {
        return Err(WireError::invalid(
            context,
            format!(
                "reference {:#010x} sort {:?} does not match node tag {}",
                reference.raw(),
                reference.sort(),
                tag.name()
            ),
        ));
    }
    Ok(node)
}

/// Returns true if `node` is a BV or Bool variable node that can appear in a model block.
pub fn is_variable_node(node: RawNode) -> bool {
    matches!(node.tag, tag::BV_VAR | tag::BOOL_VAR)
}
