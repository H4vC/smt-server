use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use smt_server::{
    serve_tcp, BinbitBackend, CommandRouterBackend, RacingBackend, RumbaBackend, ServerConfig,
    Z3Backend,
};
use smt_wire::{response_flags, ExprBuilder, ModelBlock, SimplifyBlock, Status, TcpClient};

fn start_default_test_server() -> SocketAddr {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    drop(listener);

    thread::spawn(move || {
        let solver = Arc::new(RacingBackend::new(vec![
            Arc::new(Z3Backend),
            Arc::new(BinbitBackend),
        ]));
        let backend = Arc::new(CommandRouterBackend::new(Arc::new(RumbaBackend), solver));
        let _ = serve_tcp(addr, ServerConfig::new(backend));
    });

    for _ in 0..100 {
        if TcpStream::connect(addr).is_ok() {
            return addr;
        }
        thread::sleep(Duration::from_millis(10));
    }
    panic!("test server did not start on {addr}");
}

#[test]
fn live_tcp_server_handles_binary_text_and_cached_requests() {
    let addr = start_default_test_server();
    let mut client = TcpClient::connect(addr).unwrap();

    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 4).unwrap();
    let two = builder.bv_const(2, 4).unwrap();
    let eq = builder.bv_eq(x, two).unwrap();
    builder.assert(eq).unwrap();
    let request = builder.build_solve_request(0x1001, 0, true, false).unwrap();

    let response = client.send_binary_request(&request).unwrap();
    assert_eq!(response.envelope.request_id, 0x1001);
    assert_eq!(response.envelope.status, Status::Sat);
    assert_eq!(response.envelope.flags, response_flags::HAS_MODEL);
    let model = ModelBlock::decode(&response.payload).unwrap();
    assert!(model
        .entries
        .iter()
        .any(|entry| entry.value.width == 4 && entry.value.bytes == vec![2]));

    let first_cached = builder
        .build_solve_request(0x2001, 0, false, false)
        .unwrap();
    let second_cached = builder
        .build_solve_request(0x2002, 0, false, false)
        .unwrap();
    let first = client.send_binary_request(&first_cached).unwrap();
    let second = client.send_binary_request(&second_cached).unwrap();
    assert_eq!(first.envelope.request_id, 0x2001);
    assert_eq!(second.envelope.request_id, 0x2002);
    assert_eq!(first.envelope.status, Status::Sat);
    assert_eq!(second.envelope.status, Status::Sat);

    let mut simplify_builder = ExprBuilder::new();
    let sx = simplify_builder.bv_var("v0", 8).unwrap();
    let zero = simplify_builder.bv_const(0, 8).unwrap();
    let simplify_target = simplify_builder.bv_add(sx, zero).unwrap();
    let simplify_request = simplify_builder
        .build_simplify_request(0x3001, simplify_target)
        .unwrap();
    let simplify_response = client.send_binary_request(&simplify_request).unwrap();
    assert_eq!(simplify_response.envelope.status, Status::Ok);
    let simplify_block = SimplifyBlock::decode(&simplify_response.payload).unwrap();
    assert!(simplify_block.target_node.is_bv());
    assert_eq!(
        simplify_block
            .expression_buffer()
            .unwrap()
            .view()
            .unwrap()
            .node_count(),
        1
    );

    let text_script = r#"
        #| yaspar parses block comments in the live text path |#
        (set-logic QF_BV)
        (declare-const |x y| (_ BitVec 2))
        (assert (= |x y| #b11))
        (check-sat)
        (get-value (|x y|))
    "#;
    let text_response = client.send_text(text_script).unwrap();
    assert!(text_response.starts_with("sat\n"), "{text_response}");
    assert!(text_response.contains("(|x y| #b11)"), "{text_response}");
}
