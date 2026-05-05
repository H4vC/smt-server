use std::fmt;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Invalid {
        context: &'static str,
        message: String,
    },
    Unsupported(String),
    Parse(String),
    Timeout,
    Internal(String),
}

impl Error {
    pub fn invalid(context: &'static str, message: impl Into<String>) -> Self {
        Self::Invalid {
            context,
            message: message.into(),
        }
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self::Unsupported(message.into())
    }

    pub fn parse(message: impl Into<String>) -> Self {
        Self::Parse(message.into())
    }

    pub fn internal(message: impl Into<String>) -> Self {
        Self::Internal(message.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Invalid { context, message } => write!(f, "invalid {context}: {message}"),
            Error::Unsupported(message) => write!(f, "unsupported feature: {message}"),
            Error::Parse(message) => write!(f, "parse error: {message}"),
            Error::Timeout => write!(f, "timeout"),
            Error::Internal(message) => write!(f, "internal error: {message}"),
        }
    }
}

impl std::error::Error for Error {}
