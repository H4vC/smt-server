use core::fmt;

/// Errors returned while decoding, validating, or building wire-format data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireError {
    /// A byte slice ended before the requested field could be decoded.
    UnexpectedEof {
        context: &'static str,
        needed: usize,
        actual: usize,
    },
    /// A length derived from headers did not match the enclosing slice length.
    LengthMismatch {
        context: &'static str,
        expected: usize,
        actual: usize,
    },
    /// A magic value did not match the v1 wire contract.
    BadMagic {
        context: &'static str,
        expected: &'static [u8],
        actual: Vec<u8>,
    },
    /// The encoded version is not supported by this crate.
    UnsupportedVersion(u8),
    /// Integer arithmetic overflowed while computing a layout or length.
    IntegerOverflow(&'static str),
    /// A field value is syntactically decoded but semantically invalid.
    InvalidValue {
        context: &'static str,
        message: String,
    },
    /// A byte range that must contain UTF-8 does not.
    InvalidUtf8 {
        context: &'static str,
        offset: u32,
        len: u32,
    },
}

pub type Result<T> = core::result::Result<T, WireError>;

impl WireError {
    pub(crate) fn invalid(context: &'static str, message: impl Into<String>) -> Self {
        WireError::InvalidValue {
            context,
            message: message.into(),
        }
    }
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WireError::UnexpectedEof {
                context,
                needed,
                actual,
            } => write!(
                f,
                "unexpected end of input while reading {context}: needed {needed} bytes, got {actual}"
            ),
            WireError::LengthMismatch {
                context,
                expected,
                actual,
            } => write!(
                f,
                "length mismatch for {context}: expected {expected} bytes, got {actual}"
            ),
            WireError::BadMagic {
                context,
                expected,
                actual,
            } => write!(
                f,
                "bad magic for {context}: expected {:?}, got {:?}",
                expected, actual
            ),
            WireError::UnsupportedVersion(version) => {
                write!(f, "unsupported SMT wire version {version}")
            }
            WireError::IntegerOverflow(context) => {
                write!(f, "integer overflow while computing {context}")
            }
            WireError::InvalidValue { context, message } => {
                write!(f, "invalid {context}: {message}")
            }
            WireError::InvalidUtf8 {
                context,
                offset,
                len,
            } => write!(
                f,
                "invalid UTF-8 in {context} at blob offset {offset} with length {len}"
            ),
        }
    }
}

impl std::error::Error for WireError {}
