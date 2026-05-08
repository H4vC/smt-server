use std::fmt;
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::string::FromUtf8Error;
use std::time::Duration;

use crate::response::BinaryResponse;
use crate::WireError;

pub const DEFAULT_MAX_RESPONSE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug)]
pub enum ClientError {
    Io(std::io::Error),
    Wire(WireError),
    Utf8(FromUtf8Error),
    FrameTooLarge(usize),
}

pub type ClientResult<T> = std::result::Result<T, ClientError>;

impl fmt::Display for ClientError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClientError::Io(err) => write!(f, "I/O error: {err}"),
            ClientError::Wire(err) => write!(f, "wire-format error: {err}"),
            ClientError::Utf8(err) => write!(f, "UTF-8 error: {err}"),
            ClientError::FrameTooLarge(len) => {
                write!(f, "frame payload exceeds configured limit: {len} bytes")
            }
        }
    }
}

impl std::error::Error for ClientError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ClientError::Io(err) => Some(err),
            ClientError::Wire(err) => Some(err),
            ClientError::Utf8(err) => Some(err),
            ClientError::FrameTooLarge(_) => None,
        }
    }
}

impl From<std::io::Error> for ClientError {
    fn from(err: std::io::Error) -> Self {
        ClientError::Io(err)
    }
}

impl From<WireError> for ClientError {
    fn from(err: WireError) -> Self {
        ClientError::Wire(err)
    }
}

impl From<FromUtf8Error> for ClientError {
    fn from(err: FromUtf8Error) -> Self {
        ClientError::Utf8(err)
    }
}

pub struct TcpClient {
    stream: TcpStream,
    max_response_bytes: usize,
}

impl TcpClient {
    pub fn connect(addr: impl ToSocketAddrs) -> ClientResult<Self> {
        Ok(Self {
            stream: TcpStream::connect(addr)?,
            max_response_bytes: DEFAULT_MAX_RESPONSE_BYTES,
        })
    }

    pub fn from_stream(stream: TcpStream) -> Self {
        Self {
            stream,
            max_response_bytes: DEFAULT_MAX_RESPONSE_BYTES,
        }
    }

    pub fn set_max_response_bytes(&mut self, max_response_bytes: usize) {
        self.max_response_bytes = max_response_bytes;
    }

    pub fn set_read_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        self.stream.set_read_timeout(timeout)
    }

    pub fn set_write_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        self.stream.set_write_timeout(timeout)
    }

    pub fn send_payload(&mut self, payload: &[u8]) -> ClientResult<Vec<u8>> {
        let len =
            u32::try_from(payload.len()).map_err(|_| ClientError::FrameTooLarge(payload.len()))?;
        self.stream.write_all(&len.to_le_bytes())?;
        self.stream.write_all(payload)?;

        let mut len_bytes = [0u8; 4];
        self.stream.read_exact(&mut len_bytes)?;
        let response_len = u32::from_le_bytes(len_bytes) as usize;
        if response_len > self.max_response_bytes {
            return Err(ClientError::FrameTooLarge(response_len));
        }
        let mut response = vec![0u8; response_len];
        self.stream.read_exact(&mut response)?;
        Ok(response)
    }

    pub fn send_binary_request(&mut self, request: &[u8]) -> ClientResult<BinaryResponse> {
        Ok(BinaryResponse::parse(&self.send_payload(request)?)?)
    }

    pub fn send_text_bytes(&mut self, script: &[u8]) -> ClientResult<Vec<u8>> {
        self.send_payload(script)
    }

    pub fn send_text(&mut self, script: &str) -> ClientResult<String> {
        Ok(String::from_utf8(self.send_text_bytes(script.as_bytes())?)?)
    }
}
