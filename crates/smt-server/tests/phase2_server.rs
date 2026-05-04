use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::Arc;
use std::thread;

use smt_server::{handle_binary_frame, serve_tcp, ExhaustiveBackend, ServerConfig};
use smt_wire::{
    le, response_flags, status, BinaryResponse, ExprBuilder, ModelBlock, NodeRef, Status,
    UnsatCoreBlock,
};

#[test]
fn exhaustive_backend_solves_sat_with_model() {
    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 2).unwrap();
    let one = builder.bv_const(1, 2).unwrap();
    let eq = builder.bv_eq(x, one).unwrap();
    builder.assert(eq).unwrap();
    let request = builder.build_solve_request(11, 0, true, false).unwrap();

    let response = handle_binary_frame(&request, &ExhaustiveBackend::default())
        .unwrap()
        .encode()
        .unwrap();
    let response = BinaryResponse::parse(&response).unwrap();
    assert_eq!(response.envelope.status, Status::Sat);
    assert_eq!(response.envelope.flags, response_flags::HAS_MODEL);
    let model = ModelBlock::decode(&response.payload).unwrap();
    let x_entry = model
        .entries
        .iter()
        .find(|entry| entry.node_ref == NodeRef::bv(0).unwrap())
        .unwrap();
    assert_eq!(x_entry.value.width, 2);
    assert_eq!(x_entry.value.bytes, vec![1]);
}

#[test]
fn exhaustive_backend_solves_unsat_with_named_core() {
    let mut builder = ExprBuilder::new();
    let p = builder.bool_var("p").unwrap();
    let not_p = builder.bool_not(p).unwrap();
    builder.assert_named("p-is-true", p).unwrap();
    builder.assert_named("p-is-false", not_p).unwrap();
    let request = builder.build_solve_request(12, 0, false, true).unwrap();

    let response = handle_binary_frame(&request, &ExhaustiveBackend::default())
        .unwrap()
        .encode()
        .unwrap();
    let response = BinaryResponse::parse(&response).unwrap();
    assert_eq!(response.envelope.status, Status::Unsat);
    assert_eq!(response.envelope.flags, response_flags::HAS_CORE);
    let core = UnsatCoreBlock::decode(&response.payload).unwrap();
    assert_eq!(core.names, vec!["p-is-true", "p-is-false"]);
}

#[test]
fn exhaustive_backend_returns_unknown_when_enumeration_limit_is_exceeded() {
    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 8).unwrap();
    let y = builder.bv_var("y", 8).unwrap();
    let eq = builder.bv_eq(x, y).unwrap();
    builder.assert(eq).unwrap();
    let request = builder.build_solve_request(13, 0, false, false).unwrap();

    let response = handle_binary_frame(&request, &ExhaustiveBackend::new(10))
        .unwrap()
        .encode()
        .unwrap();
    let response = BinaryResponse::parse(&response).unwrap();
    assert_eq!(response.envelope.status, Status::Unknown);
}

#[test]
fn tcp_server_handles_one_binary_frame() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    drop(listener);

    let handle = thread::spawn(move || {
        // The server runs until the client closes; this test relies on process
        // teardown to clean up the background thread after one request.
        let _ = serve_tcp(
            addr,
            ServerConfig::new(Arc::new(ExhaustiveBackend::default())),
        );
    });

    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request = builder.build_solve_request(14, 0, false, false).unwrap();
    let frame = le::encode_transport_frame(&request).unwrap();

    let mut stream = None;
    for _ in 0..100 {
        match std::net::TcpStream::connect(addr) {
            Ok(s) => {
                stream = Some(s);
                break;
            }
            Err(_) => std::thread::sleep(std::time::Duration::from_millis(10)),
        }
    }
    let mut stream = stream.unwrap();
    stream.write_all(&frame).unwrap();
    let mut len = [0u8; 4];
    stream.read_exact(&mut len).unwrap();
    let len = u32::from_le_bytes(len) as usize;
    let mut payload = vec![0u8; len];
    stream.read_exact(&mut payload).unwrap();
    let response = BinaryResponse::parse(&payload).unwrap();
    assert_eq!(response.envelope.request_id, 14);
    assert_eq!(response.envelope.status as u8, status::SAT);
    drop(stream);
    drop(handle);
}
