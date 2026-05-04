use smt_server::{handle_binary_frame, ExhaustiveBackend};
use smt_wire::{
    response_flags, BinaryResponse, ExprBuilder, OptimizationValueBlock, SimplifyBlock, Status,
};

#[test]
fn simplify_returns_simplify_block() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request = builder.build_simplify_request(21).unwrap();
    let response = handle_binary_frame(&request, &ExhaustiveBackend::default())
        .unwrap()
        .encode()
        .unwrap();
    let response = BinaryResponse::parse(&response).unwrap();
    assert_eq!(response.envelope.status, Status::Ok);
    assert_eq!(response.envelope.flags, response_flags::HAS_EXPR);
    let block = SimplifyBlock::decode(&response.payload).unwrap();
    assert_eq!(block.assertion_roots.len(), 1);
    assert_eq!(block.assumption_roots.len(), 0);
}

#[test]
fn unsigned_minimize_and_maximize_return_optimum_values() {
    let mut min_builder = ExprBuilder::new();
    let x = min_builder.bv_var("x", 4).unwrap();
    let three = min_builder.bv_const(3, 4).unwrap();
    let ge = min_builder.bv_uge(x, three).unwrap();
    min_builder.assert(ge).unwrap();
    let request = min_builder
        .build_minimize_request(22, x, false, 0, false)
        .unwrap();
    let response = BinaryResponse::parse(
        &handle_binary_frame(&request, &ExhaustiveBackend::default())
            .unwrap()
            .encode()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(response.envelope.status, Status::Sat);
    assert_eq!(response.envelope.flags, response_flags::HAS_VALUE);
    let optimum = OptimizationValueBlock::decode(&response.payload, false).unwrap();
    assert_eq!(optimum.optimum.width, 4);
    assert_eq!(optimum.optimum.bytes, vec![3]);

    let mut max_builder = ExprBuilder::new();
    let y = max_builder.bv_var("y", 4).unwrap();
    let ten = max_builder.bv_const(10, 4).unwrap();
    let le = max_builder.bv_ule(y, ten).unwrap();
    max_builder.assert(le).unwrap();
    let request = max_builder
        .build_maximize_request(23, y, false, 0, false)
        .unwrap();
    let response = BinaryResponse::parse(
        &handle_binary_frame(&request, &ExhaustiveBackend::default())
            .unwrap()
            .encode()
            .unwrap(),
    )
    .unwrap();
    let optimum = OptimizationValueBlock::decode(&response.payload, false).unwrap();
    assert_eq!(optimum.optimum.bytes, vec![10]);
}

#[test]
fn signed_optimization_uses_signed_ordering_and_can_return_model() {
    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 4).unwrap();
    let request = builder
        .build_minimize_request(24, x, true, 0, true)
        .unwrap();
    let response = BinaryResponse::parse(
        &handle_binary_frame(&request, &ExhaustiveBackend::default())
            .unwrap()
            .encode()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(
        response.envelope.flags,
        response_flags::HAS_VALUE | response_flags::HAS_MODEL
    );
    let optimum = OptimizationValueBlock::decode(&response.payload, true).unwrap();
    // 4-bit signed minimum is -8, encoded as 0b1000.
    assert_eq!(optimum.optimum.bytes, vec![8]);
    assert!(optimum
        .model
        .unwrap()
        .entries
        .iter()
        .any(|entry| entry.value.bytes == vec![8]));

    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 4).unwrap();
    let request = builder
        .build_maximize_request(25, x, true, 0, false)
        .unwrap();
    let response = BinaryResponse::parse(
        &handle_binary_frame(&request, &ExhaustiveBackend::default())
            .unwrap()
            .encode()
            .unwrap(),
    )
    .unwrap();
    let optimum = OptimizationValueBlock::decode(&response.payload, false).unwrap();
    // 4-bit signed maximum is +7.
    assert_eq!(optimum.optimum.bytes, vec![7]);
}
