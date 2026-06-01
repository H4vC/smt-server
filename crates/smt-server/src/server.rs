use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use std::thread;
use std::time::Duration;

use smt_wire::raw::{le, BinaryResponse, Status};

use crate::backend::Backend;
use crate::cache::{
    binary_request_id, cache_key_for_payload, rebind_cached_response, ResponseCache,
};
use crate::protocol::handle_binary_frame;
use crate::recording::record_binary_pair;
use crate::smtlib::handle_text_frame_recording;

pub const DEFAULT_MAX_FRAME_BYTES: usize = 64 * 1024 * 1024;
pub const DEFAULT_MAX_RESPONSE_BYTES: usize = 64 * 1024 * 1024;
pub const DEFAULT_MAX_CONNECTIONS: usize = 128;

#[derive(Clone)]
pub struct ServerConfig {
    pub backend: Arc<dyn Backend>,
    pub cache: Option<Arc<ResponseCache>>,
    pub max_frame_bytes: usize,
    pub max_response_bytes: usize,
    pub max_connections: usize,
    pub read_timeout: Option<Duration>,
    pub write_timeout: Option<Duration>,
}

impl ServerConfig {
    pub fn new(backend: Arc<dyn Backend>) -> Self {
        Self {
            backend,
            cache: Some(Arc::new(ResponseCache::new())),
            max_frame_bytes: DEFAULT_MAX_FRAME_BYTES,
            max_response_bytes: DEFAULT_MAX_RESPONSE_BYTES,
            max_connections: DEFAULT_MAX_CONNECTIONS,
            read_timeout: None,
            write_timeout: None,
        }
    }
}

pub fn serve_tcp(addr: impl ToSocketAddrs, config: ServerConfig) -> std::io::Result<()> {
    let listener = TcpListener::bind(addr)?;
    let config = Arc::new(config);
    let active_connections = Arc::new(AtomicUsize::new(0));
    for stream in listener.incoming() {
        let mut stream = stream?;
        apply_stream_timeouts(&stream, &config)?;
        if !try_acquire_connection(&active_connections, config.max_connections) {
            let _ = write_error_frame(&mut stream, "maximum active connections reached");
            continue;
        }
        let config = Arc::clone(&config);
        let active_connections = Arc::clone(&active_connections);
        thread::spawn(move || {
            let _permit = ConnectionPermit { active_connections };
            let _ = handle_connection(stream, config);
        });
    }
    Ok(())
}

fn apply_stream_timeouts(stream: &TcpStream, config: &ServerConfig) -> std::io::Result<()> {
    stream.set_read_timeout(config.read_timeout)?;
    stream.set_write_timeout(config.write_timeout)
}

fn try_acquire_connection(active_connections: &AtomicUsize, max_connections: usize) -> bool {
    if max_connections == 0 {
        return false;
    }
    active_connections
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            (current < max_connections).then_some(current + 1)
        })
        .is_ok()
}

struct ConnectionPermit {
    active_connections: Arc<AtomicUsize>,
}

impl Drop for ConnectionPermit {
    fn drop(&mut self) {
        self.active_connections.fetch_sub(1, Ordering::AcqRel);
    }
}

fn write_error_frame(stream: &mut TcpStream, message: &str) -> std::io::Result<()> {
    let response_payload = binary_error_response(message);
    let frame = le::encode_transport_frame(&response_payload)
        .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err))?;
    stream.write_all(&frame)
}

fn handle_connection(mut stream: TcpStream, config: Arc<ServerConfig>) -> std::io::Result<()> {
    loop {
        let mut len_bytes = [0u8; 4];
        match stream.read_exact(&mut len_bytes) {
            Ok(()) => {}
            Err(err) if err.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(err) => return Err(err),
        }
        let frame_len = u32::from_le_bytes(len_bytes) as usize;
        if frame_len > config.max_frame_bytes {
            write_error_frame(
                &mut stream,
                &format!(
                    "frame payload length {frame_len} exceeds configured maximum {}",
                    config.max_frame_bytes
                ),
            )?;
            return Ok(());
        }
        let mut payload = vec![0u8; frame_len];
        stream.read_exact(&mut payload)?;

        let mut response_payload =
            dispatch_payload_with_cache(&payload, config.backend.as_ref(), config.cache.as_deref());
        if response_payload.len() > config.max_response_bytes {
            response_payload = binary_error_response(&format!(
                "response payload length {} exceeds configured maximum {}",
                response_payload.len(),
                config.max_response_bytes
            ));
        }
        let frame = le::encode_transport_frame(&response_payload)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err))?;
        stream.write_all(&frame)?;
    }
}

pub fn dispatch_payload_with_cache(
    payload: &[u8],
    backend: &dyn Backend,
    cache: Option<&ResponseCache>,
) -> Vec<u8> {
    if let Some(cache) = cache.filter(|cache| {
        smt_wire::raw::request::is_binary_request_payload(payload) && cache.accepts_payload(payload)
    }) {
        let key = cache_key_for_payload(payload);
        let request_id = binary_request_id(payload);
        if let Some(response) = cache.lookup(&key) {
            let response = rebind_cached_response(response, request_id);
            record_binary_pair(payload, &response);
            return response;
        }
        let response = dispatch_payload(payload, backend);
        if is_cacheable_binary_response(&response) {
            cache.insert(key, response.clone());
        }
        return response;
    }
    dispatch_payload(payload, backend)
}

fn is_cacheable_binary_response(response: &[u8]) -> bool {
    BinaryResponse::parse(response)
        .map(|response| {
            matches!(
                response.envelope.status,
                Status::Sat | Status::Unsat | Status::Simplified
            )
        })
        .unwrap_or(false)
}

pub fn dispatch_payload(payload: &[u8], backend: &dyn Backend) -> Vec<u8> {
    if smt_wire::raw::request::is_binary_request_payload(payload) {
        let response =
            match handle_binary_frame(payload, backend).and_then(|response| response.encode()) {
                Ok(bytes) => bytes,
                Err(err) => binary_error_response(&err.to_string()),
            };
        record_binary_pair(payload, &response);
        response
    } else {
        match handle_text_frame_recording(payload, backend) {
            Ok(bytes) => bytes,
            Err(err) => format!("(error {:?})\n", err.to_string()).into_bytes(),
        }
    }
}

fn binary_error_response(message: &str) -> Vec<u8> {
    BinaryResponse::error(0, message)
        .and_then(|response| response.encode())
        .or_else(|_| BinaryResponse::new(0, Status::Unknown, 0, Vec::new())?.encode())
        .unwrap_or_else(|_| b"SMTR\0\0\0\0\x03\0\0\0\0\0\0\0".to_vec())
}
