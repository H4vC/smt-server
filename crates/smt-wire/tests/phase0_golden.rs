use smt_wire::raw::{constants::tag, le, ExprView, ExpressionBuffer, NodeRef, RawNode};

#[test]
fn empty_expression_buffer_golden_bytes() {
    let empty = ExpressionBuffer::empty();
    let expected = [
        b'S', b'M', b'T', 0, // magic
        1, 0, 0, 0, // version + pad
        0, 0, 0, 0, // node_count
        0, 0, 0, 0, // child_count
        0, 0, 0, 0, // blob_len
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // reserved
    ];
    assert_eq!(empty.as_bytes(), expected);
    ExprView::parse_and_validate(empty.as_bytes()).unwrap();
}

#[test]
fn simple_expression_buffer_golden_bytes() {
    let nodes = [
        RawNode::new(tag::BV_VAR, 0, 0, 8, 0, 0, 1),
        RawNode::new(tag::BV_EQ, 2, 0, 0, 0, 0, 0),
    ];
    let children = [NodeRef::bv(0).unwrap(), NodeRef::bv(0).unwrap()];
    let expr = ExpressionBuffer::from_parts(&nodes, &children, b"x").unwrap();
    let expected = [
        b'S', b'M', b'T', 0, 1, 0, 0, 0, // header magic/version
        2, 0, 0, 0, // node_count
        2, 0, 0, 0, // child_count
        1, 0, 0, 0, // blob_len
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // reserved
        // node 0: BV_VAR x : (_ BitVec 8), payload = blob ref (0, 1)
        0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        // node 1: BV_EQ node0 node0 -> Bool
        31, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // children
        0, 0, 0, 0, 0, 0, 0, 0, // blob
        b'x',
    ];
    assert_eq!(expr.as_bytes(), expected);
    ExprView::parse_and_validate(expr.as_bytes()).unwrap();
}

#[test]
fn little_endian_decoding_is_explicit() {
    let bytes = [0x34, 0x12, 0xef, 0xcd, 0xab, 0x89, 0x08, 0x07];
    assert_eq!(le::read_u16(&bytes, 0, "u16").unwrap(), 0x1234);
    assert_eq!(le::read_u32(&bytes, 2, "u32").unwrap(), 0x89ab_cdef);
    assert_eq!(
        le::read_u64(&bytes, 0, "u64").unwrap(),
        0x0708_89ab_cdef_1234
    );
}

#[test]
fn malformed_child_index_is_rejected() {
    let nodes = [
        RawNode::new(tag::BV_VAR, 0, 0, 8, 0, 0, 1),
        RawNode::new(tag::BV_EQ, 2, 0, 0, 0, 0, 0),
    ];
    // The first child points at node 1, i.e. the parent itself, which violates
    // the strict bottom-up construction rule.
    let children = [NodeRef::bv(1).unwrap(), NodeRef::bv(0).unwrap()];
    let expr = ExpressionBuffer::from_parts(&nodes, &children, b"x").unwrap();
    assert!(ExprView::parse(&expr.into_bytes())
        .unwrap()
        .validate()
        .is_err());
}
