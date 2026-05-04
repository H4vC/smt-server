use std::collections::HashSet;

use crate::constants::{request_flags, Command, REQUEST_ENVELOPE_LEN, REQUEST_MAGIC};
use crate::error::{Result, WireError};
use crate::expr::{validate_node_ref, ExprView};
use crate::le;
use crate::types::{BlobRef, NodeRef, Sort};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequestEnvelope {
    pub request_id: u32,
    pub command: Command,
    pub flags: u8,
    pub budget_ms: u32,
    pub expr_len: u32,
    pub assertion_count: u16,
    pub named_count: u16,
    pub assumption_count: u16,
    pub target_node: u32,
}

impl RequestEnvelope {
    pub fn encode(&self, dst: &mut Vec<u8>) -> Result<()> {
        validate_request_flags(self.flags)?;
        dst.extend_from_slice(&REQUEST_MAGIC);
        le::write_u32(dst, self.request_id);
        le::write_u8(dst, self.command.into());
        le::write_u8(dst, self.flags);
        le::write_u32(dst, self.budget_ms);
        le::write_u32(dst, self.expr_len);
        le::write_u16(dst, self.assertion_count);
        le::write_u16(dst, self.named_count);
        le::write_u16(dst, self.assumption_count);
        le::write_u32(dst, self.target_node);
        le::write_u32(dst, 0);
        Ok(())
    }

    pub fn parse(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < REQUEST_ENVELOPE_LEN {
            return Err(WireError::UnexpectedEof {
                context: "request envelope",
                needed: REQUEST_ENVELOPE_LEN,
                actual: bytes.len(),
            });
        }
        let magic = le::exact_slice(bytes, 0, 4, "request magic")?;
        if magic != REQUEST_MAGIC {
            return Err(WireError::BadMagic {
                context: "request envelope",
                expected: &REQUEST_MAGIC,
                actual: magic.to_vec(),
            });
        }
        let command_raw = le::read_u8(bytes, 8, "request command")?;
        let command = Command::try_from(command_raw).map_err(|_| {
            WireError::invalid("request command", format!("unknown command {command_raw}"))
        })?;
        let flags = le::read_u8(bytes, 9, "request flags")?;
        validate_request_flags(flags)?;
        Ok(Self {
            request_id: le::read_u32(bytes, 4, "request id")?,
            command,
            flags,
            budget_ms: le::read_u32(bytes, 10, "request budget")?,
            expr_len: le::read_u32(bytes, 14, "request expr_len")?,
            assertion_count: le::read_u16(bytes, 18, "request assertion_count")?,
            named_count: le::read_u16(bytes, 20, "request named_count")?,
            assumption_count: le::read_u16(bytes, 22, "request assumption_count")?,
            target_node: le::read_u32(bytes, 24, "request target_node")?,
        })
    }

    pub fn encoded_len(&self) -> Result<usize> {
        request_len(
            self.expr_len as usize,
            self.assertion_count as usize,
            self.named_count as usize,
            self.assumption_count as usize,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryRequest {
    pub envelope: RequestEnvelope,
    pub expression: Vec<u8>,
    pub assertion_roots: Vec<NodeRef>,
    pub named_assertion_refs: Vec<BlobRef>,
    pub assumption_roots: Vec<NodeRef>,
}

impl BinaryRequest {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        request_id: u32,
        command: Command,
        flags: u8,
        budget_ms: u32,
        expression: Vec<u8>,
        assertion_roots: Vec<NodeRef>,
        named_assertion_refs: Vec<BlobRef>,
        assumption_roots: Vec<NodeRef>,
        target_node: Option<NodeRef>,
    ) -> Result<Self> {
        validate_request_flags(flags)?;
        if named_assertion_refs.len() > assertion_roots.len() {
            return Err(WireError::invalid(
                "request named assertions",
                format!(
                    "named_count {} exceeds assertion_count {}",
                    named_assertion_refs.len(),
                    assertion_roots.len()
                ),
            ));
        }
        let expr_len = u32::try_from(expression.len()).map_err(|_| {
            WireError::invalid(
                "request expression",
                format!("expression length {} exceeds u32::MAX", expression.len()),
            )
        })?;
        let assertion_count = u16::try_from(assertion_roots.len()).map_err(|_| {
            WireError::invalid("request assertions", "assertion count exceeds u16::MAX")
        })?;
        let named_count = u16::try_from(named_assertion_refs.len()).map_err(|_| {
            WireError::invalid("request named assertions", "named count exceeds u16::MAX")
        })?;
        let assumption_count = u16::try_from(assumption_roots.len()).map_err(|_| {
            WireError::invalid("request assumptions", "assumption count exceeds u16::MAX")
        })?;
        if matches!(command, Command::Minimize | Command::Maximize) && target_node.is_none() {
            return Err(WireError::invalid(
                "request target_node",
                "MINIMIZE/MAXIMIZE require a BV target node",
            ));
        }
        let target_node_raw = target_node.map(NodeRef::raw).unwrap_or(0);
        let request = Self {
            envelope: RequestEnvelope {
                request_id,
                command,
                flags,
                budget_ms,
                expr_len,
                assertion_count,
                named_count,
                assumption_count,
                target_node: target_node_raw,
            },
            expression,
            assertion_roots,
            named_assertion_refs,
            assumption_roots,
        };
        request.validate()?;
        Ok(request)
    }

    pub fn parse(frame_payload: &[u8]) -> Result<Self> {
        let envelope = RequestEnvelope::parse(frame_payload)?;
        if envelope.named_count > envelope.assertion_count {
            return Err(WireError::invalid(
                "request named_count",
                format!(
                    "{} exceeds assertion_count {}",
                    envelope.named_count, envelope.assertion_count
                ),
            ));
        }
        let expected_len = envelope.encoded_len()?;
        if frame_payload.len() != expected_len {
            return Err(WireError::LengthMismatch {
                context: "request frame payload",
                expected: expected_len,
                actual: frame_payload.len(),
            });
        }
        let expr_start = REQUEST_ENVELOPE_LEN;
        let expr_end = expr_start + envelope.expr_len as usize;
        let expression = frame_payload[expr_start..expr_end].to_vec();
        let mut offset = expr_end;
        let mut assertion_roots = Vec::with_capacity(envelope.assertion_count as usize);
        for _ in 0..envelope.assertion_count {
            assertion_roots.push(NodeRef::from_raw(le::read_u32(
                frame_payload,
                offset,
                "assertion root",
            )?));
            offset += 4;
        }
        let mut named_assertion_refs = Vec::with_capacity(envelope.named_count as usize);
        for _ in 0..envelope.named_count {
            let blob_offset = le::read_u32(frame_payload, offset, "named assertion offset")?;
            let blob_len = le::read_u32(frame_payload, offset + 4, "named assertion length")?;
            named_assertion_refs.push(BlobRef::new(blob_offset, blob_len));
            offset += 8;
        }
        let mut assumption_roots = Vec::with_capacity(envelope.assumption_count as usize);
        for _ in 0..envelope.assumption_count {
            assumption_roots.push(NodeRef::from_raw(le::read_u32(
                frame_payload,
                offset,
                "assumption root",
            )?));
            offset += 4;
        }
        debug_assert_eq!(offset, expected_len);
        let request = Self {
            envelope,
            expression,
            assertion_roots,
            named_assertion_refs,
            assumption_roots,
        };
        request.validate()?;
        Ok(request)
    }

    pub fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let mut out = Vec::with_capacity(self.envelope.encoded_len()?);
        self.envelope.encode(&mut out)?;
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

    pub fn validate(&self) -> Result<()> {
        if self.envelope.expr_len as usize != self.expression.len() {
            return Err(WireError::LengthMismatch {
                context: "request expression length",
                expected: self.envelope.expr_len as usize,
                actual: self.expression.len(),
            });
        }
        if self.envelope.assertion_count as usize != self.assertion_roots.len() {
            return Err(WireError::LengthMismatch {
                context: "request assertion_count",
                expected: self.envelope.assertion_count as usize,
                actual: self.assertion_roots.len(),
            });
        }
        if self.envelope.named_count as usize != self.named_assertion_refs.len() {
            return Err(WireError::LengthMismatch {
                context: "request named_count",
                expected: self.envelope.named_count as usize,
                actual: self.named_assertion_refs.len(),
            });
        }
        if self.envelope.assumption_count as usize != self.assumption_roots.len() {
            return Err(WireError::LengthMismatch {
                context: "request assumption_count",
                expected: self.envelope.assumption_count as usize,
                actual: self.assumption_roots.len(),
            });
        }
        if self.named_assertion_refs.len() > self.assertion_roots.len() {
            return Err(WireError::invalid(
                "request named assertions",
                "named_count exceeds assertion_count",
            ));
        }
        let expr = ExprView::parse_and_validate(&self.expression)?;
        for root in &self.assertion_roots {
            validate_node_ref(&expr, *root, Sort::Bool, "assertion root")?;
        }
        for root in &self.assumption_roots {
            validate_node_ref(&expr, *root, Sort::Bool, "assumption root")?;
        }
        for name in &self.named_assertion_refs {
            expr.blob_str(*name, "named assertion")?;
        }
        if (self.envelope.flags & request_flags::WANT_CORE) != 0 {
            let mut names = HashSet::new();
            for name in &self.named_assertion_refs {
                let name = expr.blob_str(*name, "named assertion")?;
                if !names.insert(name.to_owned()) {
                    return Err(WireError::invalid(
                        "named assertions",
                        format!("duplicate assertion name {name:?}"),
                    ));
                }
            }
        }
        match self.envelope.command {
            Command::Minimize | Command::Maximize => {
                validate_node_ref(
                    &expr,
                    NodeRef::from_raw(self.envelope.target_node),
                    Sort::Bv,
                    "target_node",
                )?;
            }
            Command::Solve | Command::Simplify => {}
        }
        Ok(())
    }

    pub fn expression_view(&self) -> Result<ExprView<'_>> {
        ExprView::parse_and_validate(&self.expression)
    }

    pub fn target_ref(&self) -> Option<NodeRef> {
        match self.envelope.command {
            Command::Minimize | Command::Maximize => {
                Some(NodeRef::from_raw(self.envelope.target_node))
            }
            Command::Solve | Command::Simplify => None,
        }
    }
}

pub fn is_binary_request_payload(payload: &[u8]) -> bool {
    payload.len() >= 4 && payload[..4] == REQUEST_MAGIC
}

pub fn validate_request_flags(flags: u8) -> Result<()> {
    let unknown = flags & !request_flags::ALL;
    if unknown != 0 {
        return Err(WireError::invalid(
            "request flags",
            format!("unknown flag bits {unknown:#04x}"),
        ));
    }
    Ok(())
}

fn request_len(
    expr_len: usize,
    assertion_count: usize,
    named_count: usize,
    assumption_count: usize,
) -> Result<usize> {
    let mut total = REQUEST_ENVELOPE_LEN;
    total = le::checked_add(total, expr_len, "request length")?;
    total = le::checked_add(
        total,
        le::checked_mul(assertion_count, 4, "request assertion roots length")?,
        "request length",
    )?;
    total = le::checked_add(
        total,
        le::checked_mul(named_count, 8, "request named refs length")?,
        "request length",
    )?;
    le::checked_add(
        total,
        le::checked_mul(assumption_count, 4, "request assumption roots length")?,
        "request length",
    )
}
