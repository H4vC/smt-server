use std::collections::HashMap;
use std::panic::{catch_unwind, set_hook, take_hook, AssertUnwindSafe};
use std::sync::Mutex;

use rumba_core::{
    expr::{Expr as RumbaExpr, VarId},
    simplify::simplify_mba,
    varint::make_mask,
};
use smt_wire::raw::{
    tag, BinaryRequest, BlobRef, Command, ExprBuilder, ExprView, NodeRef, RawNode, SimplifyBlock,
    WireError,
};

use crate::backend::{Backend, QueryResult, SolveContext};

const MAX_RUMBA_WIDTH: u32 = 64;
const MAX_RUMBA_VARIABLES: usize = 20;

static RUMBA_PANIC_HOOK_LOCK: Mutex<()> = Mutex::new(());

#[derive(Debug, Clone, Default)]
pub struct RumbaBackend;

impl Backend for RumbaBackend {
    fn name(&self) -> &'static str {
        "rumba"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        match request.envelope.command {
            Command::Simplify => simplify_request(request).map(QueryResult::simplified),
            Command::Solve | Command::Minimize | Command::Maximize => {
                Ok(QueryResult::unknown("rumba only supports SIMPLIFY"))
            }
        }
    }

    fn handle_with_context(
        &self,
        request: &BinaryRequest,
        context: &SolveContext,
    ) -> smt_wire::Result<QueryResult> {
        if context.is_cancelled() {
            return Ok(QueryResult::unknown("rumba request cancelled before start"));
        }
        self.handle(request)
    }
}

fn simplify_request(request: &BinaryRequest) -> smt_wire::Result<SimplifyBlock> {
    let target = request
        .target_ref()
        .ok_or_else(|| WireError::invalid("simplify request", "missing target_node"))?;
    let view = request.expression_view()?;
    let node = view.node(target.index())?;
    if !target.is_bv() || node.width == 0 || node.width > MAX_RUMBA_WIDTH {
        return Ok(identity_simplify(request, target));
    }

    let bits = node.width as u8;
    let mut conversion = RumbaConversion::new(view, node.width);
    let Some(expr) = conversion.convert_ref(target)? else {
        return Ok(identity_simplify(request, target));
    };
    let Some(simplified) = simplify_mba_catching_panic(expr, bits) else {
        return Ok(identity_simplify(request, target));
    };

    let mut builder = ExprBuilder::new();
    let target_node = rumba_to_wire(&simplified, node.width, &conversion.variables, &mut builder)?;
    Ok(SimplifyBlock {
        expression: builder.to_bytes()?,
        target_node,
    })
}

fn identity_simplify(request: &BinaryRequest, target_node: NodeRef) -> SimplifyBlock {
    SimplifyBlock {
        expression: request.expression.clone(),
        target_node,
    }
}

#[derive(Clone)]
struct RumbaVariable {
    name: String,
}

struct RumbaConversion<'a> {
    view: ExprView<'a>,
    width: u32,
    variables: Vec<RumbaVariable>,
    variable_map: HashMap<NodeRef, usize>,
    variable_name_map: HashMap<String, usize>,
}

impl<'a> RumbaConversion<'a> {
    fn new(view: ExprView<'a>, width: u32) -> Self {
        Self {
            view,
            width,
            variables: Vec::new(),
            variable_map: HashMap::new(),
            variable_name_map: HashMap::new(),
        }
    }

    fn convert_ref(&mut self, reference: NodeRef) -> smt_wire::Result<Option<RumbaExpr>> {
        if !reference.is_bv() {
            return Ok(None);
        }
        let node = self.view.node(reference.index())?;
        if node.width != self.width || node.width == 0 || node.width > MAX_RUMBA_WIDTH {
            return Ok(None);
        }
        Ok(match node.tag {
            tag::BV_VAR => self.rumba_var(reference, node)?,
            tag::BV_CONST => Some(RumbaExpr::Const(rumba_core::varint::VarInt::from(
                node.payload & mask_for_width(self.width),
            ))),
            tag::BV_NOT => self.rumba_child(&node, 0)?.map(|x| !x),
            tag::BV_NEG => self.rumba_child(&node, 0)?.map(|x| -x),
            tag::BV_AND => self.rumba_nary(reference, tag::BV_AND)?.map(RumbaExpr::And),
            tag::BV_OR => self.rumba_nary(reference, tag::BV_OR)?.map(RumbaExpr::Or),
            tag::BV_XOR => self.rumba_nary(reference, tag::BV_XOR)?.map(RumbaExpr::Xor),
            tag::BV_ADD => self.rumba_nary(reference, tag::BV_ADD)?.map(RumbaExpr::Add),
            tag::BV_SUB => self.rumba_children2(&node)?.map(|(a, b)| a - b),
            tag::BV_MUL => self.rumba_nary(reference, tag::BV_MUL)?.map(RumbaExpr::Mul),
            _ => None,
        })
    }

    fn rumba_child(
        &mut self,
        node: &RawNode,
        child_offset: usize,
    ) -> smt_wire::Result<Option<RumbaExpr>> {
        let child_index = node
            .children
            .checked_add(child_offset as u32)
            .ok_or(WireError::IntegerOverflow("child array index"))?;
        let child = self.view.child_ref(child_index)?;
        self.convert_ref(child)
    }

    fn rumba_children2(
        &mut self,
        node: &RawNode,
    ) -> smt_wire::Result<Option<(RumbaExpr, RumbaExpr)>> {
        let Some(a) = self.rumba_child(node, 0)? else {
            return Ok(None);
        };
        let Some(b) = self.rumba_child(node, 1)? else {
            return Ok(None);
        };
        Ok(Some((a, b)))
    }

    fn rumba_nary(&mut self, root: NodeRef, tag: u8) -> smt_wire::Result<Option<Vec<RumbaExpr>>> {
        let mut stack = vec![root];
        let mut terms = Vec::new();
        while let Some(reference) = stack.pop() {
            let node = self.view.node(reference.index())?;
            if reference.is_bv() && node.tag == tag && node.width == self.width {
                for offset in (0..node.arity as usize).rev() {
                    let child_index = node
                        .children
                        .checked_add(offset as u32)
                        .ok_or(WireError::IntegerOverflow("child array index"))?;
                    stack.push(self.view.child_ref(child_index)?);
                }
            } else if let Some(term) = self.convert_ref(reference)? {
                terms.push(term);
            } else {
                return Ok(None);
            }
        }
        Ok(Some(terms))
    }

    fn rumba_var(
        &mut self,
        reference: NodeRef,
        node: RawNode,
    ) -> smt_wire::Result<Option<RumbaExpr>> {
        if let Some(id) = self.variable_map.get(&reference).copied() {
            return Ok(Some(RumbaExpr::Var(VarId(id))));
        }
        let name = self
            .view
            .blob_str(BlobRef::from_payload(node.payload), "BV variable")?
            .to_owned();
        if let Some(id) = self.variable_name_map.get(&name).copied() {
            self.variable_map.insert(reference, id);
            return Ok(Some(RumbaExpr::Var(VarId(id))));
        }
        if self.variables.len() >= MAX_RUMBA_VARIABLES {
            return Ok(None);
        }
        let id = self.variables.len();
        self.variables.push(RumbaVariable { name: name.clone() });
        self.variable_map.insert(reference, id);
        self.variable_name_map.insert(name, id);
        Ok(Some(RumbaExpr::Var(VarId(id))))
    }
}

fn rumba_to_wire(
    expr: &RumbaExpr,
    width: u32,
    variables: &[RumbaVariable],
    builder: &mut ExprBuilder,
) -> smt_wire::Result<NodeRef> {
    let mask = mask_for_width(width);
    let mut stack = vec![RumbaFrame::Enter(expr)];
    let mut refs = Vec::<NodeRef>::new();

    while let Some(frame) = stack.pop() {
        match frame {
            RumbaFrame::Enter(expr) => {
                stack.push(RumbaFrame::Exit(expr));
                match expr {
                    RumbaExpr::Var(_) | RumbaExpr::Const(_) => {}
                    RumbaExpr::Not(child) | RumbaExpr::Scale(_, child) => {
                        stack.push(RumbaFrame::Enter(child));
                    }
                    RumbaExpr::And(children)
                    | RumbaExpr::Or(children)
                    | RumbaExpr::Xor(children)
                    | RumbaExpr::Add(children)
                    | RumbaExpr::Mul(children) => {
                        for child in children.iter().rev() {
                            stack.push(RumbaFrame::Enter(child));
                        }
                    }
                }
            }
            RumbaFrame::Exit(expr) => {
                let reference = match expr {
                    RumbaExpr::Var(var) => {
                        let binding = variables.get(var.0).ok_or_else(|| {
                            WireError::invalid(
                                "rumba expression",
                                format!("unknown Rumba variable v{}", var.0),
                            )
                        })?;
                        builder.bv_var(&binding.name, width)?
                    }
                    RumbaExpr::Const(c) => builder.bv_const(c.get(mask), width)?,
                    RumbaExpr::Not(_) => {
                        let child = refs.pop().ok_or_else(|| {
                            WireError::invalid("rumba expression", "missing child")
                        })?;
                        builder.bv_not(child)?
                    }
                    RumbaExpr::Scale(c, _) => {
                        let child = refs.pop().ok_or_else(|| {
                            WireError::invalid("rumba expression", "missing child")
                        })?;
                        let coeff = builder.bv_const(c.get(mask), width)?;
                        builder.bv_mul(coeff, child)?
                    }
                    RumbaExpr::And(children) => fold_child_refs(
                        builder,
                        &mut refs,
                        children.len(),
                        width,
                        mask,
                        ExprBuilder::bv_and,
                    )?,
                    RumbaExpr::Or(children) => fold_child_refs(
                        builder,
                        &mut refs,
                        children.len(),
                        width,
                        0,
                        ExprBuilder::bv_or,
                    )?,
                    RumbaExpr::Xor(children) => fold_child_refs(
                        builder,
                        &mut refs,
                        children.len(),
                        width,
                        0,
                        ExprBuilder::bv_xor,
                    )?,
                    RumbaExpr::Add(children) => fold_child_refs(
                        builder,
                        &mut refs,
                        children.len(),
                        width,
                        0,
                        ExprBuilder::bv_add,
                    )?,
                    RumbaExpr::Mul(children) => fold_child_refs(
                        builder,
                        &mut refs,
                        children.len(),
                        width,
                        1,
                        ExprBuilder::bv_mul,
                    )?,
                };
                refs.push(reference);
            }
        }
    }

    if refs.len() != 1 {
        return Err(WireError::invalid(
            "rumba expression",
            format!("expected one lowered root, got {}", refs.len()),
        ));
    }
    Ok(refs.pop().expect("length checked"))
}

#[derive(Clone, Copy)]
enum RumbaFrame<'a> {
    Enter(&'a RumbaExpr),
    Exit(&'a RumbaExpr),
}

fn fold_child_refs(
    builder: &mut ExprBuilder,
    refs: &mut Vec<NodeRef>,
    len: usize,
    width: u32,
    identity: u64,
    mut op: impl FnMut(&mut ExprBuilder, NodeRef, NodeRef) -> smt_wire::Result<NodeRef>,
) -> smt_wire::Result<NodeRef> {
    if len == 0 {
        return builder.bv_const(identity, width);
    }
    let start = refs
        .len()
        .checked_sub(len)
        .ok_or_else(|| WireError::invalid("rumba expression", "missing child references"))?;
    let children = refs.split_off(start);
    let mut iter = children.into_iter();
    let mut acc = iter
        .next()
        .expect("non-empty child vector after length check");
    for child in iter {
        acc = op(builder, acc, child)?;
    }
    Ok(acc)
}

fn simplify_mba_catching_panic(expr: RumbaExpr, bits: u8) -> Option<RumbaExpr> {
    let _guard = RUMBA_PANIC_HOOK_LOCK.lock().ok()?;
    let previous_hook = take_hook();
    set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(|| simplify_mba(expr, bits))).ok();
    set_hook(previous_hook);
    result
}

fn mask_for_width(width: u32) -> u64 {
    debug_assert!((1..=MAX_RUMBA_WIDTH).contains(&width));
    make_mask(width as u8)
}
