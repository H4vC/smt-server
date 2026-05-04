use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use std::sync::Arc;
use std::thread;

use smt_wire::{le, BinaryResponse};

use crate::backend::Backend;
use crate::cache::{
    binary_request_id, cache_key_for_payload, rebind_cached_response, ResponseCache,
};
use crate::protocol::handle_binary_frame;
use crate::smtlib::handle_text_frame;

#[derive(Clone)]
pub struct ServerConfig {
    pub backend: Arc<dyn Backend>,
    pub cache: Option<Arc<ResponseCache>>,
}

impl ServerConfig {
    pub fn new(backend: Arc<dyn Backend>) -> Self {
        Self {
            backend,
            cache: Some(Arc::new(ResponseCache::new())),
        }
    }
}

pub fn serve_tcp(addr: impl ToSocketAddrs, config: ServerConfig) -> std::io::Result<()> {
    let listener = TcpListener::bind(addr)?;
    let config = Arc::new(config);
    for stream in listener.incoming() {
        let stream = stream?;
        let config = Arc::clone(&config);
        thread::spawn(move || {
            let _ = handle_connection(stream, config);
        });
    }
    Ok(())
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
        let mut payload = vec![0u8; frame_len];
        stream.read_exact(&mut payload)?;

        let response_payload =
            dispatch_payload_with_cache(&payload, config.backend.as_ref(), config.cache.as_deref());
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
    if let Some(cache) = cache {
        let key = cache_key_for_payload(payload);
        let request_id = binary_request_id(payload);
        if let Some(response) = cache.lookup(&key) {
            return rebind_cached_response(response, request_id);
        }
        let response = dispatch_payload(payload, backend);
        cache.insert(key, response.clone());
        return response;
    }
    dispatch_payload(payload, backend)
}

pub fn dispatch_payload(payload: &[u8], backend: &dyn Backend) -> Vec<u8> {
    if smt_wire::request::is_binary_request_payload(payload) {
        match handle_binary_frame(payload, backend).and_then(|response| response.encode()) {
            Ok(bytes) => bytes,
            Err(err) => binary_error_response(&err.to_string()),
        }
    } else {
        match handle_text_frame(payload, backend) {
            Ok(bytes) => bytes,
            Err(err) => format!("(error {:?})\n", err.to_string()).into_bytes(),
        }
    }
}

fn binary_error_response(message: &str) -> Vec<u8> {
    BinaryResponse::error(0, message)
        .and_then(|response| response.encode())
        .unwrap_or_else(|_| b"SMTR\0\0\0\0\x04\x10\0\0\0\0\0\0".to_vec())
}
