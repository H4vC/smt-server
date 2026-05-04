use crate::constants::{response_flags, Status, RESPONSE_ENVELOPE_LEN, RESPONSE_MAGIC};
use crate::error::{Result, WireError};
use crate::expr::{
    bytes_for_width, is_variable_node, validate_node_ref, ExprView, ExpressionBuffer,
};
use crate::le;
use crate::types::{BlobRef, NodeRef, Sort};

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

    pub fn ok(request_id: u32, payload: Vec<u8>, flags: u8) -> Result<Self> {
        Self::new(request_id, Status::Ok, flags, payload)
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
        if self.envelope.status == Status::Error {
            if (self.envelope.flags & response_flags::HAS_MESSAGE) == 0 {
                return Err(WireError::invalid(
                    "error response",
                    "HAS_MESSAGE flag must be set",
                ));
            }
            core::str::from_utf8(&self.payload)
                .map_err(|_| WireError::invalid("error response", "message is not UTF-8"))?;
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
        for entry in &self.entries {
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
            match entry.node_ref.sort() {
                Sort::Bool => {
                    if entry.value.width != 0 {
                        return Err(WireError::invalid(
                            "model value",
                            "Bool variable has non-Bool scalar value",
                        ));
                    }
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
    pub assertion_roots: Vec<NodeRef>,
    pub named_assertion_refs: Vec<BlobRef>,
    pub assumption_roots: Vec<NodeRef>,
}

impl SimplifyBlock {
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let expr_len = u32::try_from(self.expression.len()).map_err(|_| {
            WireError::invalid("simplify block", "expression length exceeds u32::MAX")
        })?;
        let assertion_count = u16::try_from(self.assertion_roots.len()).map_err(|_| {
            WireError::invalid("simplify block", "assertion count exceeds u16::MAX")
        })?;
        let named_count = u16::try_from(self.named_assertion_refs.len())
            .map_err(|_| WireError::invalid("simplify block", "named count exceeds u16::MAX"))?;
        let assumption_count = u16::try_from(self.assumption_roots.len()).map_err(|_| {
            WireError::invalid("simplify block", "assumption count exceeds u16::MAX")
        })?;

        let mut out = Vec::new();
        le::write_u32(&mut out, expr_len);
        le::write_u16(&mut out, assertion_count);
        le::write_u16(&mut out, named_count);
        le::write_u16(&mut out, assumption_count);
        le::write_u16(&mut out, 0);
        out.extend_from_slice(&self.expression);
        for root in &self.assertion_roots {
            le::write_u32(&mut out, root.raw());
        }
        for name in &self.named_assertion_refs {
            le::write_u32(&mut out, name.offset);
            le::write_u32(&mut out, name.len);
        }
        for root in &self.assumption_roots {
            le::write_u32(&mut out, root.raw());
        }
        Ok(out)
    }

    pub fn decode(payload: &[u8]) -> Result<Self> {
        if payload.len() < 12 {
            return Err(WireError::UnexpectedEof {
                context: "simplify block header",
                needed: 12,
                actual: payload.len(),
            });
        }
        let expr_len = le::read_u32(payload, 0, "simplify expr_len")? as usize;
        let assertion_count = le::read_u16(payload, 4, "simplify assertion_count")? as usize;
        let named_count = le::read_u16(payload, 6, "simplify named_count")? as usize;
        let assumption_count = le::read_u16(payload, 8, "simplify assumption_count")? as usize;
        if named_count > assertion_count {
            return Err(WireError::invalid(
                "simplify block",
                "named_count exceeds assertion_count",
            ));
        }
        let mut expected = 12usize;
        expected = le::checked_add(expected, expr_len, "simplify block length")?;
        expected = le::checked_add(
            expected,
            le::checked_mul(assertion_count, 4, "simplify assertions length")?,
            "simplify block length",
        )?;
        expected = le::checked_add(
            expected,
            le::checked_mul(named_count, 8, "simplify named refs length")?,
            "simplify block length",
        )?;
        expected = le::checked_add(
            expected,
            le::checked_mul(assumption_count, 4, "simplify assumptions length")?,
            "simplify block length",
        )?;
        if payload.len() != expected {
            return Err(WireError::LengthMismatch {
                context: "simplify block",
                expected,
                actual: payload.len(),
            });
        }
        let mut offset = 12;
        let expression = payload[offset..offset + expr_len].to_vec();
        offset += expr_len;
        let mut assertion_roots = Vec::with_capacity(assertion_count);
        for _ in 0..assertion_count {
            assertion_roots.push(NodeRef::from_raw(le::read_u32(
                payload,
                offset,
                "simplify assertion root",
            )?));
            offset += 4;
        }
        let mut named_assertion_refs = Vec::with_capacity(named_count);
        for _ in 0..named_count {
            named_assertion_refs.push(BlobRef::new(
                le::read_u32(payload, offset, "simplify name offset")?,
                le::read_u32(payload, offset + 4, "simplify name length")?,
            ));
            offset += 8;
        }
        let mut assumption_roots = Vec::with_capacity(assumption_count);
        for _ in 0..assumption_count {
            assumption_roots.push(NodeRef::from_raw(le::read_u32(
                payload,
                offset,
                "simplify assumption root",
            )?));
            offset += 4;
        }
        debug_assert_eq!(offset, expected);
        let block = Self {
            expression,
            assertion_roots,
            named_assertion_refs,
            assumption_roots,
        };
        block.validate()?;
        Ok(block)
    }

    pub fn validate(&self) -> Result<()> {
        if self.named_assertion_refs.len() > self.assertion_roots.len() {
            return Err(WireError::invalid(
                "simplify block",
                "named_count exceeds assertion_count",
            ));
        }
        let expr = ExprView::parse_and_validate(&self.expression)?;
        for root in &self.assertion_roots {
            validate_node_ref(&expr, *root, Sort::Bool, "simplify assertion root")?;
        }
        for root in &self.assumption_roots {
            validate_node_ref(&expr, *root, Sort::Bool, "simplify assumption root")?;
        }
        for name in &self.named_assertion_refs {
            expr.blob_str(*name, "simplify named assertion")?;
        }
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
