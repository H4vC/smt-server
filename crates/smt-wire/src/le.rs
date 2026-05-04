use crate::error::{Result, WireError};

fn ensure<'a>(
    bytes: &'a [u8],
    offset: usize,
    len: usize,
    context: &'static str,
) -> Result<&'a [u8]> {
    let end = offset
        .checked_add(len)
        .ok_or(WireError::IntegerOverflow(context))?;
    if end > bytes.len() {
        return Err(WireError::UnexpectedEof {
            context,
            needed: end,
            actual: bytes.len(),
        });
    }
    Ok(&bytes[offset..end])
}

pub fn read_u8(bytes: &[u8], offset: usize, context: &'static str) -> Result<u8> {
    Ok(ensure(bytes, offset, 1, context)?[0])
}

pub fn read_u16(bytes: &[u8], offset: usize, context: &'static str) -> Result<u16> {
    let mut arr = [0u8; 2];
    arr.copy_from_slice(ensure(bytes, offset, 2, context)?);
    Ok(u16::from_le_bytes(arr))
}

pub fn read_u32(bytes: &[u8], offset: usize, context: &'static str) -> Result<u32> {
    let mut arr = [0u8; 4];
    arr.copy_from_slice(ensure(bytes, offset, 4, context)?);
    Ok(u32::from_le_bytes(arr))
}

pub fn read_u64(bytes: &[u8], offset: usize, context: &'static str) -> Result<u64> {
    let mut arr = [0u8; 8];
    arr.copy_from_slice(ensure(bytes, offset, 8, context)?);
    Ok(u64::from_le_bytes(arr))
}

pub fn write_u8(dst: &mut Vec<u8>, value: u8) {
    dst.push(value);
}

pub fn write_u16(dst: &mut Vec<u8>, value: u16) {
    dst.extend_from_slice(&value.to_le_bytes());
}

pub fn write_u32(dst: &mut Vec<u8>, value: u32) {
    dst.extend_from_slice(&value.to_le_bytes());
}

pub fn write_u64(dst: &mut Vec<u8>, value: u64) {
    dst.extend_from_slice(&value.to_le_bytes());
}

pub fn checked_add(a: usize, b: usize, context: &'static str) -> Result<usize> {
    a.checked_add(b).ok_or(WireError::IntegerOverflow(context))
}

pub fn checked_mul(a: usize, b: usize, context: &'static str) -> Result<usize> {
    a.checked_mul(b).ok_or(WireError::IntegerOverflow(context))
}

pub fn exact_slice<'a>(
    bytes: &'a [u8],
    offset: usize,
    len: usize,
    context: &'static str,
) -> Result<&'a [u8]> {
    ensure(bytes, offset, len, context)
}

pub fn encode_transport_frame(payload: &[u8]) -> Result<Vec<u8>> {
    let len = u32::try_from(payload.len()).map_err(|_| {
        WireError::invalid(
            "transport frame",
            format!("payload length {} exceeds u32::MAX", payload.len()),
        )
    })?;
    let mut out = Vec::with_capacity(4 + payload.len());
    write_u32(&mut out, len);
    out.extend_from_slice(payload);
    Ok(out)
}

pub fn decode_transport_frame(frame: &[u8]) -> Result<&[u8]> {
    let len = read_u32(frame, 0, "transport frame length")? as usize;
    let expected = checked_add(4, len, "transport frame length")?;
    if frame.len() != expected {
        return Err(WireError::LengthMismatch {
            context: "transport frame",
            expected,
            actual: frame.len(),
        });
    }
    exact_slice(frame, 4, len, "transport frame payload")
}
