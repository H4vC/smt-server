use crate::error::{Result, WireError};

/// Sort encoded in bit 31 of a typed node reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Bv,
    Bool,
}

impl Sort {
    pub const fn sort_bit(self) -> u32 {
        match self {
            Sort::Bv => 0,
            Sort::Bool => NodeRef::SORT_BIT,
        }
    }
}

/// A typed node reference.
///
/// Bit 31 encodes the sort (`0 = BV`, `1 = Bool`) and bits 0-30 encode the
/// node-array index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeRef(u32);

impl NodeRef {
    pub const SORT_BIT: u32 = 0x8000_0000;
    pub const INDEX_MASK: u32 = 0x7fff_ffff;

    pub fn new(sort: Sort, index: u32) -> Result<Self> {
        if index > Self::INDEX_MASK {
            return Err(WireError::invalid(
                "node reference",
                format!("index {index} exceeds 31-bit node-reference range"),
            ));
        }
        Ok(Self(sort.sort_bit() | index))
    }

    pub fn bv(index: u32) -> Result<Self> {
        Self::new(Sort::Bv, index)
    }

    pub fn bool(index: u32) -> Result<Self> {
        Self::new(Sort::Bool, index)
    }

    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    pub const fn raw(self) -> u32 {
        self.0
    }

    pub const fn index(self) -> u32 {
        self.0 & Self::INDEX_MASK
    }

    pub const fn sort(self) -> Sort {
        if (self.0 & Self::SORT_BIT) == 0 {
            Sort::Bv
        } else {
            Sort::Bool
        }
    }

    pub const fn is_bv(self) -> bool {
        matches!(self.sort(), Sort::Bv)
    }

    pub const fn is_bool(self) -> bool {
        matches!(self.sort(), Sort::Bool)
    }
}

impl From<NodeRef> for u32 {
    fn from(value: NodeRef) -> Self {
        value.raw()
    }
}

/// A `(blob_offset, blob_len)` reference, encoded in node payloads and request
/// name lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlobRef {
    pub offset: u32,
    pub len: u32,
}

impl BlobRef {
    pub const fn new(offset: u32, len: u32) -> Self {
        Self { offset, len }
    }

    pub const fn from_payload(payload: u64) -> Self {
        Self {
            offset: (payload >> 32) as u32,
            len: payload as u32,
        }
    }

    pub const fn to_payload(self) -> u64 {
        ((self.offset as u64) << 32) | (self.len as u64)
    }
}
