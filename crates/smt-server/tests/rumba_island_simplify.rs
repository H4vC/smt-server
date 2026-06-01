//! Rumba simplifies MBA islands even when nested under structural operators
//! (`concat`, `ite`, ...). Before island extraction the converter bailed to identity
//! whenever any non-MBA node appeared anywhere in the target.

use smt_server::{handle_binary_frame, RumbaBackend};
use smt_wire::raw::{tag, BinaryResponse, ExprBuilder, SimplifyBlock, Status};

/// Count occurrences of each tag in the simplified result expression.
fn tag_counts(payload: &[u8]) -> Vec<u8> {
    let block = SimplifyBlock::decode(payload).unwrap();
    let buffer = block.expression_buffer().unwrap();
    let view = buffer.view().unwrap();
    let mut tags = Vec::new();
    for index in 0..view.node_count() {
        tags.push(view.node(index).unwrap().tag);
    }
    tags
}

fn simplify(builder: &ExprBuilder, target: smt_wire::raw::NodeRef) -> Vec<u8> {
    let request = builder.build_simplify_request(1, target).unwrap();
    let response = BinaryResponse::parse(
        &handle_binary_frame(&request, &RumbaBackend)
            .unwrap()
            .encode()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(response.envelope.status, Status::Simplified);
    response.payload
}

/// `concat(0xFF, (x^y) + 2*(x&y))` -> the MBA arm must collapse to `x + y`, while the
/// `concat` skeleton is preserved.
#[test]
fn simplifies_mba_island_nested_under_concat() {
    let mut b = ExprBuilder::new();
    let x = b.bv_var("x", 16).unwrap();
    let y = b.bv_var("y", 16).unwrap();
    let two = b.bv_const(2, 16).unwrap();
    let xor = b.bv_xor(x, y).unwrap();
    let and = b.bv_and(x, y).unwrap();
    let mul = b.bv_mul(two, and).unwrap();
    let mba = b.bv_add(xor, mul).unwrap();
    let hi = b.bv_const(0xFF, 16).unwrap();
    let target = b.bv_concat(hi, mba).unwrap();

    let tags = tag_counts(&simplify(&b, target));
    let count = |t: u8| tags.iter().filter(|&&n| n == t).count();
    assert_eq!(count(tag::BV_XOR), 0, "xor not eliminated");
    assert_eq!(count(tag::BV_AND), 0, "and not eliminated");
    assert_eq!(count(tag::BV_MUL), 0, "mul not eliminated");
    assert!(count(tag::BV_ADD) >= 1, "reduced x+y add missing");
    assert_eq!(count(tag::BV_CONCAT), 1, "concat skeleton not preserved");
}

/// `ite(c, (x|(x&y)), x)` -> the taken arm's absorption `x|(x&y)` must collapse to `x`
/// inside the `ite`, leaving an `ite` with no `and`.
#[test]
fn simplifies_mba_island_nested_under_ite() {
    let mut b = ExprBuilder::new();
    let c = b.bool_var("c").unwrap();
    let x = b.bv_var("x", 32).unwrap();
    let y = b.bv_var("y", 32).unwrap();
    let and = b.bv_and(x, y).unwrap();
    let absorb = b.bv_or(x, and).unwrap(); // x | (x & y) == x
    let target = b.bv_ite(c, absorb, x).unwrap();

    let tags = tag_counts(&simplify(&b, target));
    let count = |t: u8| tags.iter().filter(|&&n| n == t).count();
    assert_eq!(count(tag::BV_AND), 0, "absorption under ite not applied");
    assert_eq!(count(tag::BV_OR), 0, "absorption under ite not applied");
    assert_eq!(count(tag::BV_ITE), 1, "ite skeleton not preserved");
}

/// A pure top-level MBA island still simplifies (no regression).
#[test]
fn simplifies_top_level_mba() {
    let mut b = ExprBuilder::new();
    let x = b.bv_var("x", 64).unwrap();
    let y = b.bv_var("y", 64).unwrap();
    let and = b.bv_and(x, y).unwrap();
    let target = b.bv_or(x, and).unwrap(); // x | (x & y) == x

    let tags = tag_counts(&simplify(&b, target));
    // Collapses to the single variable `x`: one BV_VAR node, nothing else.
    assert_eq!(tags, vec![tag::BV_VAR]);
}
