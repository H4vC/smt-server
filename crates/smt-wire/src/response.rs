use std::collections::{HashMap, HashSet};

use crate::constants::{response_flags, Status, RESPONSE_ENVELOPE_LEN, RESPONSE_MAGIC};
use crate::error::{Result, WireError};
use crate::expr::{
    bytes_for_width, is_variable_node, validate_node_ref, ExprView, ExpressionBuffer,
};
use crate::le;
use crate::types::{NodeRef, Sort};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResponseEnvelope {
    pub request_id: u32,
    pub status: Status,
    pub flags: u8,
    pub payload_len: u32,
}

impl ResponseEnvelope {
    pub fn encode(&self, dst: &mut Vec<u8>) -> Result<()> {
        validate_response_flags(self.flags)?;
        dst.extend_from_slice(&RESPONSE_MAGIC);
        le::write_u32(dst, self.request_id);
        le::write_u8(dst, self.status.into());
        le::write_u8(dst, self.flags);
        le::write_u32(dst, self.payload_len);
        le::write_u16(dst, 0);
        Ok(())
    }

    pub fn parse(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < RESPONSE_ENVELOPE_LEN {
            return Err(WireError::UnexpectedEof {
                context: "response envelope",
                needed: RESPONSE_ENVELOPE_LEN,
                actual: bytes.len(),
            });
        }
        let magic = le::exact_slice(bytes, 0, 4, "response magic")?;
        if magic != RESPONSE_MAGIC {
            return Err(WireError::BadMagic {
                context: "response envelope",
                expected: &RESPONSE_MAGIC,
                actual: magic.to_vec(),
            });
        }
        let status_raw = le::read_u8(bytes, 8, "response status")?;
        let status = Status::try_from(status_raw).map_err(|_| {
            WireError::invalid("response status", format!("unknown status {status_raw}"))
        })?;
        let flags = le::read_u8(bytes, 9, "response flags")?;
        validate_response_flags(flags)?;
        let reserved = le::read_u16(bytes, 14, "response reserved")?;
        if reserved != 0 {
            return Err(WireError::invalid(
                "response reserved",
                format!("expected 0, got {reserved}"),
            ));
        }
        Ok(Self {
            request_id: le::read_u32(bytes, 4, "response request_id")?,
            status,
            flags,
            payload_len: le::read_u32(bytes, 10, "response payload_len")?,
        })
    }

    pub fn encoded_len(&self) -> Result<usize> {
        le::checked_add(
            RESPONSE_ENVELOPE_LEN,
            self.payload_len as usize,
            "response length",
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryResponse {
    pub envelope: ResponseEnvelope,
    pub payload: Vec<u8>,
}

impl BinaryResponse {
    pub fn new(request_id: u32, status: Status, flags: u8, payload: Vec<u8>) -> Result<Self> {
        validate_response_flags(flags)?;
        let payload_len = u32::try_from(payload.len()).map_err(|_| {
            WireError::invalid(
                "response payload",
                format!("payload length {} exceeds u32::MAX", payload.len()),
            )
        })?;
        let response = Self {
            envelope: ResponseEnvelope {
                request_id,
                status,
                flags,
                payload_len,
            },
            payload,
        };
        response.validate()?;
        Ok(response)
    }

    pub fn simplified(request_id: u32, payload: Vec<u8>, flags: u8) -> Result<Self> {
        Self::new(request_id, Status::Simplified, flags, payload)
    }

    pub fn error(request_id: u32, message: &str) -> Result<Self> {
        Self::new(
            request_id,
            Status::Error,
            response_flags::HAS_MESSAGE,
            message.as_bytes().to_vec(),
        )
    }

    pub fn parse(frame_payload: &[u8]) -> Result<Self> {
        let envelope = ResponseEnvelope::parse(frame_payload)?;
        let expected = envelope.encoded_len()?;
        if frame_payload.len() != expected {
            return Err(WireError::LengthMismatch {
                context: "response frame payload",
                expected,
                actual: frame_payload.len(),
            });
        }
        let payload = frame_payload[RESPONSE_ENVELOPE_LEN..].to_vec();
        let response = Self { envelope, payload };
        response.validate()?;
        Ok(response)
    }

    pub fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let mut out = Vec::with_capacity(self.envelope.encoded_len()?);
        self.envelope.encode(&mut out)?;
        out.extend_from_slice(&self.payload);
        Ok(out)
    }

    pub fn validate(&self) -> Result<()> {
        if self.envelope.payload_len as usize != self.payload.len() {
            return Err(WireError::LengthMismatch {
                context: "response payload length",
                expected: self.envelope.payload_len as usize,
                actual: self.payload.len(),
            });
        }
        match self.envelope.status {
            Status::Error => {
                if self.envelope.flags != response_flags::HAS_MESSAGE {
                    return Err(WireError::invalid(
                        "error response",
                        "ERROR status must use exactly HAS_MESSAGE",
                    ));
                }
                core::str::from_utf8(&self.payload)
                    .map_err(|_| WireError::invalid("error response", "message is not UTF-8"))?;
            }
            Status::Unknown => match self.envelope.flags {
                0 => {
                    if !self.payload.is_empty() {
                        return Err(WireError::invalid(
                            "unknown response",
                            "payload requires HAS_MESSAGE",
                        ));
                    }
                }
                response_flags::HAS_MESSAGE => {
                    core::str::from_utf8(&self.payload).map_err(|_| {
                        WireError::invalid("unknown response", "message is not UTF-8")
                    })?;
                }
                _ => {
                    return Err(WireError::invalid(
                        "unknown response",
                        "UNKNOWN status may only use HAS_MESSAGE",
                    ))
                }
            },
            Status::Sat => {
                let allowed = response_flags::HAS_MODEL | response_flags::HAS_VALUE;
                if (self.envelope.flags & !allowed) != 0 {
                    return Err(WireError::invalid(
                        "sat response",
                        "SAT status may only use HAS_MODEL/HAS_VALUE",
                    ));
                }
                match (
                    (self.envelope.flags & response_flags::HAS_VALUE) != 0,
                    (self.envelope.flags & response_flags::HAS_MODEL) != 0,
                ) {
                    (false, false) => {
                        if !self.payload.is_empty() {
                            return Err(WireError::invalid(
                                "sat response",
                                "payload without flags",
                            ));
                        }
                    }
                    (false, true) => {
                        ModelBlock::decode(&self.payload)?;
                    }
                    (true, has_model) => {
                        OptimizationValueBlock::decode(&self.payload, has_model)?;
                    }
                }
            }
            Status::Unsat => match self.envelope.flags {
                0 => {
                    if !self.payload.is_empty() {
                        return Err(WireError::invalid(
                            "unsat response",
                            "payload without HAS_CORE",
                        ));
                    }
                }
                response_flags::HAS_CORE => {
                    UnsatCoreBlock::decode(&self.payload)?;
                }
                _ => {
                    return Err(WireError::invalid(
                        "unsat response",
                        "UNSAT status may only use HAS_CORE",
                    ))
                }
            },
            Status::Simplified => {
                if self.envelope.flags != response_flags::HAS_EXPR {
                    return Err(WireError::invalid(
                        "simplified response",
                        "SIMPLIFIED status must use exactly HAS_EXPR",
                    ));
                }
                SimplifyBlock::decode(&self.payload)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarValue {
    pub width: u32,
    pub bytes: Vec<u8>,
}

impl ScalarValue {
    pub fn bool(value: bool) -> Self {
        Self {
            width: 0,
            bytes: vec![u8::from(value)],
        }
    }

    pub fn bv(width: u32, bytes: Vec<u8>) -> Result<Self> {
        let expected = bytes_for_width(width)?;
        if bytes.len() != expected {
            return Err(WireError::invalid(
                "scalar BV value",
                format!(
                    "got {} bytes, expected {expected} for width {width}",
                    bytes.len()
                ),
            ));
        }
        ensure_unused_high_bits_zero(width, &bytes, "scalar BV value")?;
        Ok(Self { width, bytes })
    }

    pub fn as_bool(&self) -> Result<bool> {
        self.validate()?;
        if self.width != 0 {
            return Err(WireError::invalid("scalar value", "expected Bool scalar"));
        }
        Ok(self.bytes[0] != 0)
    }

    pub fn as_u128(&self) -> Result<u128> {
        self.validate()?;
        if self.width == 0 {
            return Ok(u128::from(self.bytes[0] != 0));
        }
        if self.bytes.len() > 16 {
            return Err(WireError::invalid(
                "scalar value",
                "BV scalar does not fit in u128",
            ));
        }
        let mut bytes = [0u8; 16];
        bytes[..self.bytes.len()].copy_from_slice(&self.bytes);
        Ok(u128::from_le_bytes(bytes))
    }

    pub fn encode(&self, dst: &mut Vec<u8>) -> Result<()> {
        self.validate()?;
        le::write_u32(dst, self.width);
        le::write_u32(
            dst,
            u32::try_from(self.bytes.len())
                .map_err(|_| WireError::invalid("scalar value", "value length exceeds u32::MAX"))?,
        );
        dst.extend_from_slice(&self.bytes);
        Ok(())
    }

    pub fn decode(bytes: &[u8], offset: &mut usize) -> Result<Self> {
        let width = le::read_u32(bytes, *offset, "scalar width")?;
        let value_len = le::read_u32(bytes, *offset + 4, "scalar value_len")? as usize;
        *offset = le::checked_add(*offset, 8, "scalar offset")?;
        let value = le::exact_slice(bytes, *offset, value_len, "scalar value bytes")?.to_vec();
        *offset = le::checked_add(*offset, value_len, "scalar offset")?;
        let scalar = Self {
            width,
            bytes: value,
        };
        scalar.validate()?;
        Ok(scalar)
    }

    pub fn validate(&self) -> Result<()> {
        if self.width == 0 {
            if self.bytes.len() != 1 || !matches!(self.bytes[0], 0 | 1) {
                return Err(WireError::invalid(
                    "Bool scalar value",
                    "expected value_len=1 and byte 0 or 1",
                ));
            }
            return Ok(());
        }
        let expected = bytes_for_width(self.width)?;
        if self.bytes.len() != expected {
            return Err(WireError::invalid(
                "BV scalar value",
                format!(
                    "got {} bytes, expected {expected} for width {}",
                    self.bytes.len(),
                    self.width
                ),
            ));
        }
        ensure_unused_high_bits_zero(self.width, &self.bytes, "BV scalar value")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelEntry {
    pub node_ref: NodeRef,
    pub value: ScalarValue,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModelBlock {
    pub entries: Vec<ModelEntry>,
}

impl ModelBlock {
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        le::write_u32(
            &mut out,
            u32::try_from(self.entries.len())
                .map_err(|_| WireError::invalid("model block", "entry count exceeds u32::MAX"))?,
        );
        for entry in &self.entries {
            le::write_u32(&mut out, entry.node_ref.raw());
            entry.value.encode(&mut out)?;
        }
        Ok(out)
    }

    pub fn decode(payload: &[u8]) -> Result<Self> {
        let mut offset = 0;
        let block = Self::decode_from(payload, &mut offset)?;
        if offset != payload.len() {
            return Err(WireError::LengthMismatch {
                context: "model block",
                expected: offset,
                actual: payload.len(),
            });
        }
        Ok(block)
    }

    pub fn decode_from(bytes: &[u8], offset: &mut usize) -> Result<Self> {
        let entry_count = le::read_u32(bytes, *offset, "model entry_count")?;
        *offset = le::checked_add(*offset, 4, "model offset")?;
        let remaining = bytes.len().checked_sub(*offset).ok_or_else(|| {
            WireError::invalid("model block", "entry offset is past end of payload")
        })?;
        if entry_count as usize > remaining / 12 {
            return Err(WireError::invalid(
                "model block",
                format!(
                    "entry_count {entry_count} cannot fit in remaining {remaining} payload bytes"
                ),
            ));
        }
        let mut entries = Vec::with_capacity(entry_count as usize);
        for _ in 0..entry_count {
            let node_ref = NodeRef::from_raw(le::read_u32(bytes, *offset, "model node_ref")?);
            *offset = le::checked_add(*offset, 4, "model offset")?;
            let value = ScalarValue::decode(bytes, offset)?;
            entries.push(ModelEntry { node_ref, value });
        }
        Ok(Self { entries })
    }

    pub fn validate_against_expr(&self, expr: &ExprView<'_>) -> Result<()> {
        let mut seen_refs = HashSet::with_capacity(self.entries.len());
        let mut symbol_values = HashMap::<(String, Sort, u32), ScalarValue>::new();
        for entry in &self.entries {
            if !seen_refs.insert(entry.node_ref) {
                return Err(WireError::invalid(
                    "model node_ref",
                    format!("duplicate model entry for node {}", entry.node_ref.index()),
                ));
            }
            let expected_sort = if entry.node_ref.is_bool() {
                Sort::Bool
            } else {
                Sort::Bv
            };
            let node = validate_node_ref(expr, entry.node_ref, expected_sort, "model node_ref")?;
            if !is_variable_node(node) {
                return Err(WireError::invalid(
                    "model node_ref",
                    format!("node {} is not a variable", entry.node_ref.index()),
                ));
            }
            let (symbol_sort, symbol_width, name_context) = match entry.node_ref.sort() {
                Sort::Bool => {
                    if entry.value.width != 0 {
                        return Err(WireError::invalid(
                            "model value",
                            "Bool variable has non-Bool scalar value",
                        ));
                    }
                    (Sort::Bool, 0, "Bool variable")
                }
                Sort::Bv => {
                    if entry.value.width != node.width {
                        return Err(WireError::invalid(
                            "model value",
                            format!(
                                "BV variable width {} but scalar width {}",
                                node.width, entry.value.width
                            ),
                        ));
                    }
                    (Sort::Bv, node.width, "BV variable")
                }
            };
            let name = expr.blob_str(node.blob_ref(), name_context)?.to_owned();
            let key = (name, symbol_sort, symbol_width);
            if let Some(existing) = symbol_values.insert(key, entry.value.clone()) {
                if existing != entry.value {
                    return Err(WireError::invalid(
                        "model value",
                        "same symbol appears with inconsistent values",
                    ));
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnsatCoreBlock {
    pub names: Vec<String>,
}

impl UnsatCoreBlock {
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        le::write_u32(
            &mut out,
            u32::try_from(self.names.len()).map_err(|_| {
                WireError::invalid("unsat core block", "name count exceeds u32::MAX")
            })?,
        );
        for name in &self.names {
            le::write_u32(
                &mut out,
                u32::try_from(name.len()).map_err(|_| {
                    WireError::invalid("unsat core block", "name length exceeds u32::MAX")
                })?,
            );
            out.extend_from_slice(name.as_bytes());
        }
        Ok(out)
    }

    pub fn decode(payload: &[u8]) -> Result<Self> {
        let mut offset = 0;
        let name_count = le::read_u32(payload, offset, "unsat core name_count")?;
        offset += 4;
        let remaining = payload.len().checked_sub(offset).ok_or_else(|| {
            WireError::invalid("unsat core block", "name offset is past end of payload")
        })?;
        if name_count as usize > remaining / 4 {
            return Err(WireError::invalid(
                "unsat core block",
                format!(
                    "name_count {name_count} cannot fit in remaining {remaining} payload bytes"
                ),
            ));
        }
        let mut names = Vec::with_capacity(name_count as usize);
        for _ in 0..name_count {
            let len = le::read_u32(payload, offset, "unsat core name_len")? as usize;
            offset += 4;
            let bytes = le::exact_slice(payload, offset, len, "unsat core name")?;
            let name = core::str::from_utf8(bytes)
                .map_err(|_| WireError::invalid("unsat core block", "name is not UTF-8"))?
                .to_owned();
            offset += len;
            names.push(name);
        }
        if offset != payload.len() {
            return Err(WireError::LengthMismatch {
                context: "unsat core block",
                expected: offset,
                actual: payload.len(),
            });
        }
        Ok(Self { names })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimplifyBlock {
    pub expression: Vec<u8>,
    pub target_node: NodeRef,
}

impl SimplifyBlock {
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let expr_len = u32::try_from(self.expression.len()).map_err(|_| {
            WireError::invalid("simplify block", "expression length exceeds u32::MAX")
        })?;

        let mut out = Vec::new();
        le::write_u32(&mut out, expr_len);
        le::write_u32(&mut out, self.target_node.raw());
        out.extend_from_slice(&self.expression);
        Ok(out)
    }

    pub fn decode(payload: &[u8]) -> Result<Self> {
        if payload.len() < 8 {
            return Err(WireError::UnexpectedEof {
                context: "simplify block header",
                needed: 8,
                actual: payload.len(),
            });
        }
        let expr_len = le::read_u32(payload, 0, "simplify expr_len")? as usize;
        let target_node = NodeRef::from_raw(le::read_u32(payload, 4, "simplify target_node")?);
        let expected = le::checked_add(8, expr_len, "simplify block length")?;
        if payload.len() != expected {
            return Err(WireError::LengthMismatch {
                context: "simplify block",
                expected,
                actual: payload.len(),
            });
        }
        let expression = payload[8..8 + expr_len].to_vec();
        let block = Self {
            expression,
            target_node,
        };
        block.validate()?;
        Ok(block)
    }

    pub fn validate(&self) -> Result<()> {
        let expr = ExprView::parse_and_validate(&self.expression)?;
        validate_node_ref(
            &expr,
            self.target_node,
            self.target_node.sort(),
            "simplify target_node",
        )?;
        Ok(())
    }

    pub fn expression_buffer(&self) -> Result<ExpressionBuffer> {
        ExpressionBuffer::from_bytes(self.expression.clone())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptimizationValueBlock {
    pub optimum: ScalarValue,
    pub model: Option<ModelBlock>,
}

impl OptimizationValueBlock {
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        self.optimum.encode(&mut out)?;
        if let Some(model) = &self.model {
            out.extend_from_slice(&model.encode()?);
        }
        Ok(out)
    }

    pub fn decode(payload: &[u8], has_model: bool) -> Result<Self> {
        let mut offset = 0;
        let optimum = ScalarValue::decode(payload, &mut offset)?;
        let model = if has_model {
            Some(ModelBlock::decode_from(payload, &mut offset)?)
        } else {
            None
        };
        if offset != payload.len() {
            return Err(WireError::LengthMismatch {
                context: "optimization value block",
                expected: offset,
                actual: payload.len(),
            });
        }
        Ok(Self { optimum, model })
    }
}

pub fn validate_response_flags(flags: u8) -> Result<()> {
    let unknown = flags & !response_flags::ALL;
    if unknown != 0 {
        return Err(WireError::invalid(
            "response flags",
            format!("unknown flag bits {unknown:#04x}"),
        ));
    }
    Ok(())
}

fn ensure_unused_high_bits_zero(width: u32, bytes: &[u8], context: &'static str) -> Result<()> {
    let valid_bits = width % 8;
    if valid_bits == 0 || bytes.is_empty() {
        return Ok(());
    }
    let mask = (1u8 << valid_bits) - 1;
    let last = bytes[bytes.len() - 1];
    if (last & !mask) != 0 {
        return Err(WireError::invalid(
            context,
            format!("unused high bits in final byte are not zero: {last:#04x}"),
        ));
    }
    Ok(())
}
