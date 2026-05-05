use std::collections::HashMap;

use crate::error::{Error, Result};

pub const MAX_BV_WIDTH: u32 = 65_536;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub(crate) u32);

impl TermId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub const fn raw(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    Bv(u32),
}

impl Sort {
    pub const fn is_bool(self) -> bool {
        matches!(self, Sort::Bool)
    }

    pub const fn bv_width(self) -> Option<u32> {
        match self {
            Sort::Bool => None,
            Sort::Bv(width) => Some(width),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    BvConst {
        width: u32,
        bytes: Vec<u8>,
    },
    BvVar {
        width: u32,
        name: String,
        external: Option<u32>,
    },
    BoolConst(bool),
    BoolVar {
        name: String,
        external: Option<u32>,
    },

    BvNot(TermId),
    BvNeg(TermId),
    BvAnd(TermId, TermId),
    BvOr(TermId, TermId),
    BvXor(TermId, TermId),
    BvAdd(TermId, TermId),
    BvSub(TermId, TermId),
    BvMul(TermId, TermId),
    BvUDiv(TermId, TermId),
    BvURem(TermId, TermId),
    BvSDiv(TermId, TermId),
    BvSRem(TermId, TermId),
    BvSMod(TermId, TermId),
    BvShl(TermId, TermId),
    BvLShr(TermId, TermId),
    BvAShr(TermId, TermId),
    BvExtract {
        child: TermId,
        high: u32,
        low: u32,
    },
    BvConcat(TermId, TermId),
    BvZeroExtend {
        child: TermId,
        extra: u32,
    },
    BvSignExtend {
        child: TermId,
        extra: u32,
    },
    BvRepeat {
        child: TermId,
        count: u32,
    },
    BvRotateLeft {
        child: TermId,
        amount: u32,
    },
    BvRotateRight {
        child: TermId,
        amount: u32,
    },
    BvIte {
        cond: TermId,
        then_value: TermId,
        else_value: TermId,
    },
    BvSelect {
        cases: Vec<(TermId, TermId)>,
        default: TermId,
    },

    BoolNot(TermId),
    BoolAnd(TermId, TermId),
    BoolOr(TermId, TermId),
    BoolImplies(TermId, TermId),
    BoolEq(TermId, TermId),
    BoolIte {
        cond: TermId,
        then_value: TermId,
        else_value: TermId,
    },

    BvEq(TermId, TermId),
    BvUlt(TermId, TermId),
    BvUle(TermId, TermId),
    BvSlt(TermId, TermId),
    BvSle(TermId, TermId),

    UAddOverflow(TermId, TermId),
    SAddOverflow(TermId, TermId),
    USubOverflow(TermId, TermId),
    SSubOverflow(TermId, TermId),
    UMulOverflow(TermId, TermId),
    SMulOverflow(TermId, TermId),
    NegOverflow(TermId),
    SDivOverflow(TermId, TermId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct NodeKey {
    kind: NodeKind,
    sort: Sort,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub kind: NodeKind,
    pub sort: Sort,
}

#[derive(Debug, Clone, Default)]
pub struct Arena {
    nodes: Vec<Node>,
    ids: HashMap<NodeKey, TermId>,
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    pub fn node(&self, id: TermId) -> Result<&Node> {
        self.nodes.get(id.index()).ok_or_else(|| {
            Error::invalid(
                "term id",
                format!(
                    "term {} is out of bounds for {} nodes",
                    id.raw(),
                    self.nodes.len()
                ),
            )
        })
    }

    pub fn sort(&self, id: TermId) -> Result<Sort> {
        Ok(self.node(id)?.sort)
    }

    pub fn add(&mut self, kind: NodeKind, sort: Sort) -> Result<TermId> {
        validate_sort(sort)?;
        let key = NodeKey {
            kind: kind.clone(),
            sort,
        };
        if let Some(existing) = self.ids.get(&key) {
            return Ok(*existing);
        }
        let id = TermId(
            u32::try_from(self.nodes.len())
                .map_err(|_| Error::invalid("arena", "node count exceeds u32::MAX"))?,
        );
        self.nodes.push(Node { kind, sort });
        self.ids.insert(key, id);
        Ok(id)
    }

    pub fn expect_bool(&self, id: TermId, context: &'static str) -> Result<()> {
        let sort = self.sort(id)?;
        if sort != Sort::Bool {
            return Err(Error::invalid(
                context,
                format!("expected Bool term, got {sort:?}"),
            ));
        }
        Ok(())
    }

    pub fn expect_bv(&self, id: TermId, context: &'static str) -> Result<u32> {
        match self.sort(id)? {
            Sort::Bv(width) => Ok(width),
            Sort::Bool => Err(Error::invalid(context, "expected BV term, got Bool")),
        }
    }

    pub fn expect_same_bv(&self, a: TermId, b: TermId, context: &'static str) -> Result<u32> {
        let aw = self.expect_bv(a, context)?;
        let bw = self.expect_bv(b, context)?;
        if aw != bw {
            return Err(Error::invalid(
                context,
                format!("BV width mismatch: {aw} vs {bw}"),
            ));
        }
        Ok(aw)
    }
}

pub fn validate_bv_width(width: u32, context: &'static str) -> Result<()> {
    if !(1..=MAX_BV_WIDTH).contains(&width) {
        return Err(Error::invalid(
            context,
            format!("width {width} is outside 1..={MAX_BV_WIDTH}"),
        ));
    }
    Ok(())
}

pub fn validate_sort(sort: Sort) -> Result<()> {
    match sort {
        Sort::Bool => Ok(()),
        Sort::Bv(width) => validate_bv_width(width, "BV sort width"),
    }
}

pub fn bytes_for_width(width: u32) -> Result<usize> {
    validate_bv_width(width, "BV width")?;
    Ok((width as usize).div_ceil(8))
}

pub fn mask_unused_high_bits(bytes: &mut [u8], width: u32) {
    let valid_bits = width % 8;
    if valid_bits == 0 || bytes.is_empty() {
        return;
    }
    let mask = (1u8 << valid_bits) - 1;
    let last = bytes.len() - 1;
    bytes[last] &= mask;
}

pub fn normalized_bytes(bytes: &[u8], width: u32) -> Result<Vec<u8>> {
    let expected = bytes_for_width(width)?;
    if bytes.len() != expected {
        return Err(Error::invalid(
            "BV bytes",
            format!(
                "got {} bytes, expected {expected} for width {width}",
                bytes.len()
            ),
        ));
    }
    let mut out = bytes.to_vec();
    mask_unused_high_bits(&mut out, width);
    Ok(out)
}
