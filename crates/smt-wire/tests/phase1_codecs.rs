use smt_wire::{
    request_flags, response_flags, status, tag, BinaryRequest, BinaryResponse, BlobRef,
    ClientError, Command, ExprBuilder, ExprView, ExpressionBuffer, ModelBlock, ModelEntry, NodeRef,
    OptimizationValueBlock, RawNode, ScalarValue, SimplifyBlock, Sort, Status, TcpClient,
    UnsatCoreBlock,
};

fn hex_bytes(input: &str) -> Vec<u8> {
    let compact = input.split_whitespace().collect::<String>();
    assert_eq!(compact.len() % 2, 0, "hex string must contain whole bytes");
    (0..compact.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&compact[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn simple_sat_request_golden_vector() {
    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 8).unwrap();
    let one = builder.bv_const(1, 8).unwrap();
    let assertion = builder.bv_eq(x, one).unwrap();
    builder.assert(assertion).unwrap();

    let bytes = builder
        .build_solve_request(0x0102_0304, 500, true, false)
        .unwrap();
    let expected = hex_bytes(
        "53 4d 54 51 04 03 02 01 00 01 f4 01 00 00 71 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         53 4d 54 00 01 00 00 00 03 00 00 00 02 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         00 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00 \
         01 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00 \
         1f 02 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         00 00 00 00 01 00 00 00 78 02 00 00 80",
    );
    assert_eq!(bytes, expected);

    let parsed = BinaryRequest::parse(&bytes).unwrap();
    assert_eq!(parsed.envelope.request_id, 0x0102_0304);
    assert_eq!(parsed.envelope.command, Command::Solve);
    assert_eq!(parsed.envelope.flags, request_flags::WANT_MODEL);
    assert_eq!(parsed.envelope.budget_ms, 500);
    assert_eq!(parsed.assertion_roots, vec![NodeRef::bool(2).unwrap()]);
    assert_eq!(parsed.expression_view().unwrap().node_count(), 3);
}

#[test]
fn simple_unsat_request_golden_vector() {
    let mut builder = ExprBuilder::new();
    let false_node = builder.bool_false().unwrap();
    builder.assert(false_node).unwrap();

    let bytes = builder.build_solve_request(5, 0, false, false).unwrap();
    let expected = hex_bytes(
        "53 4d 54 51 05 00 00 00 00 00 00 00 00 00 38 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         53 4d 54 00 01 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         19 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 80",
    );
    assert_eq!(bytes, expected);
    let parsed = BinaryRequest::parse(&bytes).unwrap();
    assert_eq!(parsed.assertion_roots, vec![NodeRef::bool(0).unwrap()]);
}

#[test]
fn wide_constant_golden_vector() {
    let mut builder = ExprBuilder::new();
    builder
        .bv_const_wide(
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
            128,
        )
        .unwrap();
    let bytes = builder.to_bytes().unwrap();
    let expected = hex_bytes(
        "53 4d 54 00 01 00 00 00 01 00 00 00 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         01 00 00 00 80 00 00 00 00 00 00 00 00 00 00 00 10 00 00 00 00 00 00 00 \
         01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f 10",
    );
    assert_eq!(bytes, expected);
    ExprView::parse_and_validate(&bytes).unwrap();
}

#[test]
fn named_assertion_and_unsat_core_golden_vectors() {
    let mut builder = ExprBuilder::new();
    let p = builder.bool_var("p").unwrap();
    builder.assert_named("a0", p).unwrap();
    let bytes = builder.build_solve_request(7, 0, false, true).unwrap();
    let expected_request = hex_bytes(
        "53 4d 54 51 07 00 00 00 00 02 00 00 00 00 3b 00 00 00 01 00 01 00 00 00 00 00 00 00 00 00 00 00 \
         53 4d 54 00 01 00 00 00 01 00 00 00 00 00 00 00 03 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 \
         1a 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00 \
         70 61 30 00 00 00 80 01 00 00 00 02 00 00 00",
    );
    assert_eq!(bytes, expected_request);

    let parsed = BinaryRequest::parse(&bytes).unwrap();
    assert_eq!(parsed.envelope.flags, request_flags::WANT_CORE);
    assert_eq!(parsed.named_assertion_refs, vec![BlobRef::new(1, 2)]);
    assert_eq!(
        parsed
            .expression_view()
            .unwrap()
            .blob_str(parsed.named_assertion_refs[0], "test")
            .unwrap(),
        "a0"
    );

    let core = UnsatCoreBlock {
        names: vec!["a0".to_owned()],
    };
    let response = BinaryResponse::new(
        7,
        Status::Unsat,
        response_flags::HAS_CORE,
        core.encode().unwrap(),
    )
    .unwrap()
    .encode()
    .unwrap();
    let expected_response =
        hex_bytes("53 4d 54 52 07 00 00 00 02 02 0a 00 00 00 00 00 01 00 00 00 02 00 00 00 61 30");
    assert_eq!(response, expected_response);
    let parsed_response = BinaryResponse::parse(&response).unwrap();
    assert_eq!(parsed_response.envelope.status, Status::Unsat);
    assert_eq!(
        UnsatCoreBlock::decode(&parsed_response.payload).unwrap(),
        core
    );
}

#[test]
fn response_payload_codecs_round_trip() {
    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 8).unwrap();
    let p = builder.bool_var("p").unwrap();
    let expr = builder.to_expression_buffer().unwrap();
    let view = expr.view().unwrap();

    let model = ModelBlock {
        entries: vec![
            ModelEntry {
                node_ref: x,
                value: ScalarValue::bv(8, vec![42]).unwrap(),
            },
            ModelEntry {
                node_ref: p,
                value: ScalarValue::bool(true),
            },
        ],
    };
    model.validate_against_expr(&view).unwrap();
    let model_bytes = model.encode().unwrap();
    assert_eq!(ModelBlock::decode(&model_bytes).unwrap(), model);

    let simplify = SimplifyBlock {
        expression: ExpressionBuffer::empty().into_bytes(),
        assertion_roots: vec![],
        named_assertion_refs: vec![],
        assumption_roots: vec![],
    };
    let simplify_bytes = simplify.encode().unwrap();
    assert_eq!(SimplifyBlock::decode(&simplify_bytes).unwrap(), simplify);

    let optimum = OptimizationValueBlock {
        optimum: ScalarValue::bv(8, vec![0x7f]).unwrap(),
        model: Some(model.clone()),
    };
    let opt_bytes = optimum.encode().unwrap();
    assert_eq!(
        OptimizationValueBlock::decode(&opt_bytes, true).unwrap(),
        optimum
    );

    let response = BinaryResponse::new(
        9,
        Status::Sat,
        response_flags::HAS_VALUE | response_flags::HAS_MODEL,
        opt_bytes,
    )
    .unwrap();
    let parsed = BinaryResponse::parse(&response.encode().unwrap()).unwrap();
    assert_eq!(parsed.envelope.status, Status::Sat);
}

#[test]
fn expression_builder_rejects_sort_and_width_errors() {
    let mut builder = ExprBuilder::new();
    let a8 = builder.bv_var("a", 8).unwrap();
    let b16 = builder.bv_var("b", 16).unwrap();
    assert!(builder.bv_add(a8, b16).is_err());

    let p = builder.bool_var("p").unwrap();
    assert!(builder.bool_and(p, a8).is_err());
    assert!(builder.bv_extract(a8, 8, 0).is_err());
    assert!(builder.bv_zext(b16, u16::MAX).is_err());

    let selectors = vec![p; 128];
    let values = vec![a8; 128];
    assert!(builder.bv_select(&selectors, &values, a8).is_err());
}

#[test]
fn malformed_inputs_are_rejected() {
    let bad_magic = [0u8; 32];
    assert!(ExprView::parse(&bad_magic).is_err());

    let unknown_tag =
        ExpressionBuffer::from_parts(&[RawNode::new(250, 0, 0, 0, 0, 0, 0)], &[], &[]).unwrap();
    assert!(ExprView::parse(&unknown_tag.into_bytes())
        .unwrap()
        .validate()
        .is_err());

    let width_mismatch = ExpressionBuffer::from_parts(
        &[
            RawNode::new(tag::BV_CONST, 0, 0, 8, 0, 0, 1),
            RawNode::new(tag::BV_CONST, 0, 0, 16, 0, 0, 1),
            RawNode::new(tag::BV_ADD, 2, 0, 8, 0, 0, 0),
        ],
        &[NodeRef::bv(0).unwrap(), NodeRef::bv(1).unwrap()],
        &[],
    )
    .unwrap();
    assert!(ExprView::parse(&width_mismatch.into_bytes())
        .unwrap()
        .validate()
        .is_err());

    let wrong_root_sort = BinaryRequest::new(
        1,
        Command::Solve,
        0,
        0,
        ExpressionBuffer::from_parts(&[RawNode::new(tag::BV_CONST, 0, 0, 8, 0, 0, 1)], &[], &[])
            .unwrap()
            .into_bytes(),
        vec![NodeRef::bv(0).unwrap()],
        vec![],
        vec![],
        None,
    );
    assert!(wrong_root_sort.is_err());

    let bad_scalar = ScalarValue {
        width: 9,
        bytes: vec![0xff, 0xfe],
    };
    assert!(bad_scalar.validate().is_err());

    let mut truncated_response = BinaryResponse::error(1, "bad").unwrap().encode().unwrap();
    truncated_response.pop();
    assert!(BinaryResponse::parse(&truncated_response).is_err());

    let mut reserved_response = BinaryResponse::new(1, Status::Sat, 0, vec![])
        .unwrap()
        .encode()
        .unwrap();
    reserved_response[14] = 1;
    assert!(BinaryResponse::parse(&reserved_response).is_err());
}

#[test]
fn request_validation_rejects_command_specific_flags() {
    let mut parse_builder = ExprBuilder::new();
    let truth = parse_builder.bool_true().unwrap();
    parse_builder.assert(truth).unwrap();
    let solve = parse_builder
        .build_solve_request(9, 0, false, false)
        .unwrap();
    let mut malformed_solve = solve.clone();
    malformed_solve[9] |= request_flags::SIGNED;
    assert!(BinaryRequest::parse(&malformed_solve).is_err());
    let mut solve_with_target = solve.clone();
    solve_with_target[24..28].copy_from_slice(&1u32.to_le_bytes());
    assert!(BinaryRequest::parse(&solve_with_target).is_err());
    let mut solve_with_reserved = solve;
    solve_with_reserved[28..32].copy_from_slice(&1u32.to_le_bytes());
    assert!(BinaryRequest::parse(&solve_with_reserved).is_err());

    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    let x = builder.bv_var("x", 4).unwrap();
    let expression = builder.to_bytes().unwrap();

    assert!(BinaryRequest::new(
        1,
        Command::Solve,
        request_flags::SIGNED,
        0,
        expression.clone(),
        vec![t],
        vec![],
        vec![],
        None,
    )
    .is_err());
    assert!(BinaryRequest::new(
        2,
        Command::Simplify,
        request_flags::WANT_MODEL,
        0,
        expression.clone(),
        vec![t],
        vec![],
        vec![],
        None,
    )
    .is_err());
    assert!(BinaryRequest::new(
        3,
        Command::Minimize,
        request_flags::WANT_CORE,
        0,
        expression,
        vec![t],
        vec![],
        vec![],
        Some(x),
    )
    .is_err());
}

#[test]
fn request_validation_rejects_duplicate_core_names_and_missing_optimization_target() {
    let mut builder = ExprBuilder::new();
    let p = builder.bool_var("p").unwrap();
    builder.assert_named("dup", p).unwrap();
    builder.assert_named("dup", p).unwrap();
    assert!(builder.build_solve_request(1, 0, false, true).is_err());

    let expr =
        ExpressionBuffer::from_parts(&[RawNode::new(tag::BV_CONST, 0, 0, 8, 0, 0, 1)], &[], &[])
            .unwrap()
            .into_bytes();
    let missing_target = BinaryRequest::new(
        2,
        Command::Minimize,
        0,
        0,
        expr,
        vec![],
        vec![],
        vec![],
        None,
    );
    assert!(missing_target.is_err());
}

#[test]
fn transport_frames_are_little_endian_and_exact_length() {
    let payload = b"SMTQ-example";
    let frame = smt_wire::le::encode_transport_frame(payload).unwrap();
    assert_eq!(&frame[..4], &(payload.len() as u32).to_le_bytes());
    assert_eq!(
        smt_wire::le::decode_transport_frame(&frame).unwrap(),
        payload
    );

    let mut too_long = frame.clone();
    too_long.push(0);
    assert!(smt_wire::le::decode_transport_frame(&too_long).is_err());

    assert_eq!(status::SAT, 1);
    assert_eq!(Sort::Bool.sort_bit(), 0x8000_0000);
}

#[test]
fn tcp_client_rejects_oversized_response_frame_before_allocation() {
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::thread;

    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    let handle = thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        let mut len = [0u8; 4];
        stream.read_exact(&mut len).unwrap();
        let len = u32::from_le_bytes(len) as usize;
        let mut payload = vec![0u8; len];
        stream.read_exact(&mut payload).unwrap();
        stream.write_all(&1024u32.to_le_bytes()).unwrap();
    });

    let mut client = TcpClient::connect(addr).unwrap();
    client.set_max_response_bytes(8);
    let err = client.send_payload(b"ping").unwrap_err();
    assert!(matches!(err, ClientError::FrameTooLarge(1024)));
    handle.join().unwrap();
}
