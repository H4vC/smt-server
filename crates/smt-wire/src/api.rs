use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::net::{TcpStream, ToSocketAddrs};
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use crate::builder::{Assertion, ExprBuilder, NodeMeta};
use crate::client::{ClientResult, TcpClient};
use crate::constants::{request_flags, response_flags, Command, Status, Tag};
use crate::error::{Result, WireError};
use crate::expr::{bytes_for_width, validate_bv_width_value, ExprView, RawNode};
use crate::request::BinaryRequest;
use crate::response::{
    BinaryResponse, ModelBlock, OptimizationValueBlock, ScalarValue, SimplifyBlock, UnsatCoreBlock,
};
use crate::types::{BlobRef, NodeRef, Sort};

static NEXT_CONTEXT_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone)]
pub struct Context {
    inner: Rc<RefCell<ContextInner>>,
}

#[derive(Debug)]
struct ContextInner {
    id: u64,
    builder: ExprBuilder,
}

#[derive(Clone)]
pub struct BvTerm {
    ctx: Context,
    reference: NodeRef,
}

#[derive(Clone)]
pub struct BoolTerm {
    ctx: Context,
    reference: NodeRef,
}

#[derive(Clone)]
pub enum Term {
    Bv(BvTerm),
    Bool(BoolTerm),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WalkOrder {
    Pre,
    Post,
}

#[derive(Debug, Clone)]
struct BuiltRequest {
    payload: Vec<u8>,
    context: Context,
    new_to_old: HashMap<NodeRef, NodeRef>,
}

#[derive(Debug, Clone)]
pub struct SolveOptions {
    pub request_id: Option<u32>,
    pub budget_ms: u32,
    pub want_model: bool,
    pub want_core: bool,
}

impl Default for SolveOptions {
    fn default() -> Self {
        Self {
            request_id: None,
            budget_ms: 0,
            want_model: true,
            want_core: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct OptimizeOptions {
    pub request_id: Option<u32>,
    pub signed: bool,
    pub budget_ms: u32,
    pub want_model: bool,
}

impl Default for OptimizeOptions {
    fn default() -> Self {
        Self {
            request_id: None,
            signed: false,
            budget_ms: 0,
            want_model: true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Response {
    pub request_id: u32,
    pub status: Status,
    pub flags: u8,
    pub message: Option<String>,
    pub model: Option<Model>,
    pub core: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct SimplifyResult {
    pub request_id: u32,
    pub status: Status,
    pub message: Option<String>,
    pub context: Option<Context>,
    pub term: Option<Term>,
}

#[derive(Debug, Clone)]
pub struct OptimizationResult {
    pub request_id: u32,
    pub status: Status,
    pub flags: u8,
    pub message: Option<String>,
    pub optimum: Option<ScalarValue>,
    pub model: Option<Model>,
}

#[derive(Clone)]
pub struct Model {
    ctx: Context,
    values: HashMap<NodeRef, ScalarValue>,
}

pub enum BvOperand<'a> {
    Term(&'a BvTerm),
    OwnedTerm(BvTerm),
    Unsigned(u64),
    Signed(i64),
}

impl Context {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(ContextInner {
                id: NEXT_CONTEXT_ID.fetch_add(1, Ordering::Relaxed),
                builder: ExprBuilder::new(),
            })),
        }
    }

    pub fn id(&self) -> u64 {
        self.inner.borrow().id
    }

    pub fn node_count(&self) -> usize {
        self.inner.borrow().builder.node_count()
    }

    pub fn assertion_count(&self) -> usize {
        self.inner.borrow().builder.assertions().len()
    }

    pub fn assertions(&self) -> Result<Vec<BoolTerm>> {
        let roots = self
            .inner
            .borrow()
            .builder
            .assertions
            .iter()
            .map(|a| a.root)
            .collect::<Vec<_>>();
        roots.into_iter().map(|root| self.bool_term(root)).collect()
    }

    pub fn named_assertions(&self) -> Result<Vec<(String, BoolTerm)>> {
        let assertions = self.inner.borrow().builder.assertions.clone();
        let mut out = Vec::new();
        for assertion in assertions {
            if let Some(name_ref) = assertion.name {
                let name = self.blob_str(name_ref)?;
                out.push((name, self.bool_term(assertion.root)?));
            }
        }
        Ok(out)
    }

    pub fn assumptions(&self) -> Result<Vec<BoolTerm>> {
        let roots = self.inner.borrow().builder.assumptions.clone();
        roots.into_iter().map(|root| self.bool_term(root)).collect()
    }

    pub fn reset(&self) {
        self.inner.borrow_mut().builder.reset();
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        self.inner.borrow().builder.to_bytes()
    }

    pub fn bv_var(&self, name: &str, width: u32) -> Result<BvTerm> {
        let reference = self.inner.borrow_mut().builder.bv_var(name, width)?;
        self.bv_term(reference)
    }

    pub fn bool_var(&self, name: &str) -> Result<BoolTerm> {
        let reference = self.inner.borrow_mut().builder.bool_var(name)?;
        self.bool_term(reference)
    }

    pub fn bv_const(&self, value: u64, width: u32) -> Result<BvTerm> {
        let reference = self.inner.borrow_mut().builder.bv_const(value, width)?;
        self.bv_term(reference)
    }

    pub fn bv_const_i64(&self, value: i64, width: u32) -> Result<BvTerm> {
        self.bv_const(value as u64, width)
    }

    pub fn bv_const_wide(&self, bytes: &[u8], width: u32) -> Result<BvTerm> {
        let reference = self
            .inner
            .borrow_mut()
            .builder
            .bv_const_wide(bytes, width)?;
        self.bv_term(reference)
    }

    pub fn bool_const(&self, value: bool) -> Result<BoolTerm> {
        if value {
            self.true_term()
        } else {
            self.false_term()
        }
    }

    pub fn true_term(&self) -> Result<BoolTerm> {
        let reference = self.inner.borrow_mut().builder.bool_true()?;
        self.bool_term(reference)
    }

    pub fn false_term(&self) -> Result<BoolTerm> {
        let reference = self.inner.borrow_mut().builder.bool_false()?;
        self.bool_term(reference)
    }

    pub fn bv_not(&self, x: &BvTerm) -> Result<BvTerm> {
        self.bv_unary(Tag::BvNot, x)
    }

    pub fn bv_neg(&self, x: &BvTerm) -> Result<BvTerm> {
        self.bv_unary(Tag::BvNeg, x)
    }

    pub fn bv_and<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvAnd, a, b)
    }

    pub fn bv_or<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvOr, a, b)
    }

    pub fn bv_xor<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvXor, a, b)
    }

    pub fn bv_add<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvAdd, a, b)
    }

    pub fn bv_sub<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvSub, a, b)
    }

    pub fn bv_mul<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvMul, a, b)
    }

    pub fn bv_udiv<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvUdiv, a, b)
    }

    pub fn bv_urem<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvUrem, a, b)
    }

    pub fn bv_sdiv<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvSdiv, a, b)
    }

    pub fn bv_srem<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvSrem, a, b)
    }

    pub fn bv_smod<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvSmod, a, b)
    }

    pub fn bv_shl<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvShl, a, b)
    }

    pub fn bv_lshr<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvLshr, a, b)
    }

    pub fn bv_ashr<'a, B>(&self, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_binary(Tag::BvAshr, a, b)
    }

    pub fn bv_eq<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::BvEq, a, b)
    }

    pub fn bv_ne<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        let eq = self.bv_eq(a, b)?;
        self.bool_not(&eq)
    }

    pub fn bv_ult<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::BvUlt, a, b)
    }

    pub fn bv_ule<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::BvUle, a, b)
    }

    pub fn bv_ugt<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp_reverse(Tag::BvUlt, a, b)
    }

    pub fn bv_uge<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp_reverse(Tag::BvUle, a, b)
    }

    pub fn bv_slt<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::BvSlt, a, b)
    }

    pub fn bv_sle<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::BvSle, a, b)
    }

    pub fn bv_sgt<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp_reverse(Tag::BvSlt, a, b)
    }

    pub fn bv_sge<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp_reverse(Tag::BvSle, a, b)
    }

    pub fn bv_uadd_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::UaddOvf, a, b)
    }

    pub fn bv_sadd_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::SaddOvf, a, b)
    }

    pub fn bv_usub_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::UsubOvf, a, b)
    }

    pub fn bv_ssub_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::SsubOvf, a, b)
    }

    pub fn bv_umul_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::UmulOvf, a, b)
    }

    pub fn bv_smul_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::SmulOvf, a, b)
    }

    pub fn bv_neg_overflows(&self, x: &BvTerm) -> Result<BoolTerm> {
        self.expect_bv(x, Tag::NegOvf.smt_symbol())?;
        let reference = self.inner.borrow_mut().builder.neg_ovf(x.reference)?;
        self.bool_term(reference)
    }

    pub fn bv_sdiv_overflows<'a, B>(&self, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        self.bv_cmp(Tag::SdivOvf, a, b)
    }

    pub fn bv_extract(&self, x: &BvTerm, hi: u32, lo: u32) -> Result<BvTerm> {
        let x_ref = self.expect_bv(x, "extract")?.0;
        let reference = self.inner.borrow_mut().builder.bv_extract(x_ref, hi, lo)?;
        self.bv_term(reference)
    }

    pub fn bv_concat(&self, high: &BvTerm, low: &BvTerm) -> Result<BvTerm> {
        let h = self.expect_bv(high, "concat")?.0;
        let l = self.expect_bv(low, "concat")?.0;
        let reference = self.inner.borrow_mut().builder.bv_concat(h, l)?;
        self.bv_term(reference)
    }

    pub fn bv_zext(&self, x: &BvTerm, amount: u16) -> Result<BvTerm> {
        let x = self.expect_bv(x, "zero_extend")?.0;
        let reference = self.inner.borrow_mut().builder.bv_zext(x, amount)?;
        self.bv_term(reference)
    }

    pub fn bv_sext(&self, x: &BvTerm, amount: u16) -> Result<BvTerm> {
        let x = self.expect_bv(x, "sign_extend")?.0;
        let reference = self.inner.borrow_mut().builder.bv_sext(x, amount)?;
        self.bv_term(reference)
    }

    pub fn bool_not(&self, x: &BoolTerm) -> Result<BoolTerm> {
        self.expect_bool(x, "not")?;
        let reference = self.inner.borrow_mut().builder.bool_not(x.reference)?;
        self.bool_term(reference)
    }

    pub fn bool_and(&self, a: &BoolTerm, b: &BoolTerm) -> Result<BoolTerm> {
        self.bool_binary(Tag::BoolAnd, a, b)
    }

    pub fn bool_or(&self, a: &BoolTerm, b: &BoolTerm) -> Result<BoolTerm> {
        self.bool_binary(Tag::BoolOr, a, b)
    }

    pub fn bool_implies(&self, a: &BoolTerm, b: &BoolTerm) -> Result<BoolTerm> {
        self.bool_binary(Tag::BoolImplies, a, b)
    }

    pub fn bool_eq(&self, a: &BoolTerm, b: &BoolTerm) -> Result<BoolTerm> {
        self.expect_bool(a, "=")?;
        self.expect_bool(b, "=")?;
        let both_true = self.bool_and(a, b)?;
        let not_a = self.bool_not(a)?;
        let not_b = self.bool_not(b)?;
        let both_false = self.bool_and(&not_a, &not_b)?;
        self.bool_or(&both_true, &both_false)
    }

    pub fn ite(&self, cond: &BoolTerm, then_term: &Term, else_term: &Term) -> Result<Term> {
        self.expect_bool(cond, "ite")?;
        self.expect_term(then_term, "ite")?;
        self.expect_term(else_term, "ite")?;
        match (then_term, else_term) {
            (Term::Bv(t), Term::Bv(e)) => Ok(Term::Bv(self.bv_ite(cond, t, e)?)),
            (Term::Bool(t), Term::Bool(e)) => Ok(Term::Bool(self.bool_ite(cond, t, e)?)),
            _ => Err(WireError::invalid(
                "ite",
                "branch sort mismatch; expected both branches to be BV or both Bool",
            )),
        }
    }

    pub fn bv_ite(
        &self,
        cond: &BoolTerm,
        then_value: &BvTerm,
        else_value: &BvTerm,
    ) -> Result<BvTerm> {
        self.expect_bool(cond, "ite")?;
        let t = self.expect_bv(then_value, "ite")?.0;
        let e = self.expect_bv(else_value, "ite")?.0;
        let reference = self
            .inner
            .borrow_mut()
            .builder
            .bv_ite(cond.reference, t, e)?;
        self.bv_term(reference)
    }

    pub fn bool_ite(
        &self,
        cond: &BoolTerm,
        then_value: &BoolTerm,
        else_value: &BoolTerm,
    ) -> Result<BoolTerm> {
        self.expect_bool(cond, "ite")?;
        self.expect_bool(then_value, "ite")?;
        self.expect_bool(else_value, "ite")?;
        let cond_then = self.bool_and(cond, then_value)?;
        let not_cond = self.bool_not(cond)?;
        let else_branch = self.bool_and(&not_cond, else_value)?;
        self.bool_or(&cond_then, &else_branch)
    }

    pub fn bv_select(
        &self,
        selectors: &[BoolTerm],
        values: &[BvTerm],
        default: &BvTerm,
    ) -> Result<BvTerm> {
        let default_ref = self.expect_bv(default, "select")?.0;
        let selector_refs = selectors
            .iter()
            .map(|s| {
                self.expect_bool(s, "select")?;
                Ok(s.reference)
            })
            .collect::<Result<Vec<_>>>()?;
        let value_refs = values
            .iter()
            .map(|v| Ok(self.expect_bv(v, "select")?.0))
            .collect::<Result<Vec<_>>>()?;
        let reference =
            self.inner
                .borrow_mut()
                .builder
                .bv_select(&selector_refs, &value_refs, default_ref)?;
        self.bv_term(reference)
    }

    pub fn bv_rotate_left(&self, x: &BvTerm, amount: u64) -> Result<BvTerm> {
        let x_ref = self.expect_bv(x, "rotate_left")?.0;
        let reference = self
            .inner
            .borrow_mut()
            .builder
            .bv_rotate_left(x_ref, amount)?;
        self.bv_term(reference)
    }

    pub fn bv_rotate_right(&self, x: &BvTerm, amount: u64) -> Result<BvTerm> {
        let x_ref = self.expect_bv(x, "rotate_right")?.0;
        let reference = self
            .inner
            .borrow_mut()
            .builder
            .bv_rotate_right(x_ref, amount)?;
        self.bv_term(reference)
    }

    pub fn assert_(&self, root: &BoolTerm) -> Result<()> {
        self.expect_bool(root, "assert")?;
        self.inner.borrow_mut().builder.assert(root.reference)
    }

    pub fn assert_named(&self, name: &str, root: &BoolTerm) -> Result<()> {
        self.expect_bool(root, "assert_named")?;
        self.inner
            .borrow_mut()
            .builder
            .assert_named(name, root.reference)
    }

    pub fn assume(&self, root: &BoolTerm) -> Result<()> {
        self.expect_bool(root, "assume")?;
        self.inner.borrow_mut().builder.assume(root.reference)
    }

    pub fn clear_assumptions(&self) {
        self.inner.borrow_mut().builder.clear_assumptions();
    }

    pub fn push(&self) {
        self.inner.borrow_mut().builder.push();
    }

    pub fn pop(&self) -> Result<()> {
        self.inner.borrow_mut().builder.pop()
    }

    pub fn assert_mutex(&self, selectors: &[BoolTerm]) -> Result<()> {
        let refs = selectors
            .iter()
            .map(|s| {
                self.expect_bool(s, "assert_mutex")?;
                Ok(s.reference)
            })
            .collect::<Result<Vec<_>>>()?;
        self.inner.borrow_mut().builder.assert_mutex(&refs)
    }

    pub fn to_smt2(&self) -> Result<String> {
        self.to_smt2_with_options(true, true)
    }

    pub fn to_smt2_with_options(&self, mut check_sat: bool, get_model: bool) -> Result<String> {
        if get_model {
            check_sat = true;
        }
        let inner = self.inner.borrow();
        let mut lines = vec!["(set-logic QF_BV)".to_owned()];
        if get_model {
            lines.push("(set-option :produce-models true)".to_owned());
        }

        let mut declarations = Vec::<(String, NodeMeta)>::new();
        let mut seen = HashMap::<String, NodeMeta>::new();
        for node in &inner.builder.nodes {
            let tag = parse_tag(node.tag)?;
            let entry = match tag {
                Tag::BvVar => Some((
                    blob_str_from_builder(&inner.builder, node.blob_ref())?,
                    NodeMeta {
                        sort: Sort::Bv,
                        width: node.width,
                    },
                )),
                Tag::BoolVar => Some((
                    blob_str_from_builder(&inner.builder, node.blob_ref())?,
                    NodeMeta {
                        sort: Sort::Bool,
                        width: 0,
                    },
                )),
                _ => None,
            };
            if let Some((name, meta)) = entry {
                if let Some(existing) = seen.get(&name) {
                    if *existing != meta {
                        return Err(WireError::invalid(
                            "SMT-LIB declarations",
                            format!("symbol {name:?} has multiple sorts"),
                        ));
                    }
                } else {
                    seen.insert(name.clone(), meta);
                    declarations.push((name, meta));
                }
            }
        }

        for (name, meta) in declarations {
            let symbol = quote_symbol(&name);
            if meta.sort == Sort::Bv {
                lines.push(format!(
                    "(declare-const {symbol} (_ BitVec {}))",
                    meta.width
                ));
            } else {
                lines.push(format!("(declare-const {symbol} Bool)"));
            }
        }

        for assertion in &inner.builder.assertions {
            let expr = render_smt2_from_builder(&inner.builder, assertion.root, None, false)?;
            if let Some(name_ref) = assertion.name {
                let name = quote_symbol(&blob_str_from_builder(&inner.builder, name_ref)?);
                lines.push(format!(
                    "(assert (! {expr} :named {name})) ; #{}",
                    assertion.root.index()
                ));
            } else {
                lines.push(format!("(assert {expr}) ; #{}", assertion.root.index()));
            }
        }
        for root in &inner.builder.assumptions {
            let expr = render_smt2_from_builder(&inner.builder, *root, None, false)?;
            lines.push(format!("(assert {expr}) ; assumption #{}", root.index()));
        }
        if check_sat {
            lines.push("(check-sat)".to_owned());
        }
        if get_model {
            lines.push("(get-model)".to_owned());
        }
        Ok(format!("{}\n", lines.join("\n")))
    }

    pub fn term(&self, reference: NodeRef) -> Result<Term> {
        let meta = self.meta_for_ref(reference)?;
        if meta.sort == Sort::Bool {
            Ok(Term::Bool(self.bool_term(reference)?))
        } else {
            Ok(Term::Bv(self.bv_term(reference)?))
        }
    }

    pub fn from_expression_bytes(bytes: Vec<u8>) -> Result<Self> {
        let view = ExprView::parse_and_validate(&bytes)?;
        let ctx = Self::new();
        {
            let mut inner = ctx.inner.borrow_mut();
            inner.builder.nodes.clear();
            inner.builder.children.clear();
            inner.builder.blob.clear();
            inner.builder.meta.clear();
            inner.builder.assertions.clear();
            inner.builder.assumptions.clear();
            inner.builder.scopes.clear();
            inner.builder.bv_vars.clear();
            inner.builder.bool_vars.clear();
            inner.builder.symbols.clear();

            for i in 0..view.node_count() {
                let node = view.node(i)?;
                let tag = parse_tag(node.tag)?;
                inner.builder.nodes.push(node);
                inner.builder.meta.push(NodeMeta {
                    sort: tag.result_sort(),
                    width: node.width,
                });
            }
            for i in 0..view.child_count() {
                inner.builder.children.push(view.child_ref(i)?);
            }
            inner.builder.blob.extend_from_slice(view.blob());

            for i in 0..inner.builder.nodes.len() {
                let node = inner.builder.nodes[i];
                let tag = parse_tag(node.tag)?;
                if matches!(tag, Tag::BvVar | Tag::BoolVar) {
                    let name = blob_str_from_builder(&inner.builder, node.blob_ref())?;
                    let meta = NodeMeta {
                        sort: tag.result_sort(),
                        width: node.width,
                    };
                    inner.builder.symbols.insert(name.clone(), meta);
                    let reference = NodeRef::new(meta.sort, i as u32)?;
                    if meta.sort == Sort::Bv {
                        inner.builder.bv_vars.insert((name, meta.width), reference);
                    } else {
                        inner.builder.bool_vars.insert(name, reference);
                    }
                }
            }
        }
        Ok(ctx)
    }

    pub fn build_solve_request(
        &self,
        request_id: u32,
        budget_ms: u32,
        want_model: bool,
        want_core: bool,
    ) -> Result<Vec<u8>> {
        Ok(self
            .build_solve_request_context(request_id, budget_ms, want_model, want_core)?
            .payload)
    }

    fn build_solve_request_context(
        &self,
        request_id: u32,
        budget_ms: u32,
        want_model: bool,
        want_core: bool,
    ) -> Result<BuiltRequest> {
        let mut flags = 0;
        if want_model {
            flags |= request_flags::WANT_MODEL;
        }
        if want_core {
            flags |= request_flags::WANT_CORE;
        }
        self.build_request(request_id, Command::Solve, flags, budget_ms, None)
    }

    fn build_simplify_request(&self, request_id: u32, target: &Term) -> Result<BuiltRequest> {
        self.expect_term(target, "simplify")?;
        self.build_request(
            request_id,
            Command::Simplify,
            0,
            0,
            Some(target.reference()),
        )
    }

    fn build_minimize_request(
        &self,
        request_id: u32,
        target: &BvTerm,
        signed: bool,
        budget_ms: u32,
        want_model: bool,
    ) -> Result<BuiltRequest> {
        self.expect_bv(target, "minimize")?;
        let mut flags = 0;
        if signed {
            flags |= request_flags::SIGNED;
        }
        if want_model {
            flags |= request_flags::WANT_MODEL;
        }
        self.build_request(
            request_id,
            Command::Minimize,
            flags,
            budget_ms,
            Some(target.reference),
        )
    }

    fn build_maximize_request(
        &self,
        request_id: u32,
        target: &BvTerm,
        signed: bool,
        budget_ms: u32,
        want_model: bool,
    ) -> Result<BuiltRequest> {
        self.expect_bv(target, "maximize")?;
        let mut flags = 0;
        if signed {
            flags |= request_flags::SIGNED;
        }
        if want_model {
            flags |= request_flags::WANT_MODEL;
        }
        self.build_request(
            request_id,
            Command::Maximize,
            flags,
            budget_ms,
            Some(target.reference),
        )
    }

    fn build_request(
        &self,
        request_id: u32,
        command: Command,
        flags: u8,
        budget_ms: u32,
        target: Option<NodeRef>,
    ) -> Result<BuiltRequest> {
        let inner = self.inner.borrow();
        let (ordered_assertions, named_refs, assumptions) = if matches!(command, Command::Simplify)
        {
            (
                Vec::<Assertion>::new(),
                Vec::<BlobRef>::new(),
                Vec::<NodeRef>::new(),
            )
        } else {
            let mut named = Vec::new();
            let mut unnamed = Vec::new();
            for assertion in &inner.builder.assertions {
                if assertion.name.is_some() {
                    named.push(*assertion);
                } else {
                    unnamed.push(*assertion);
                }
            }
            let ordered = named
                .iter()
                .copied()
                .chain(unnamed.iter().copied())
                .collect::<Vec<_>>();
            let names = named.iter().filter_map(|a| a.name).collect::<Vec<_>>();
            (ordered, names, inner.builder.assumptions.clone())
        };
        let mut roots = ordered_assertions
            .iter()
            .map(|a| a.root)
            .collect::<Vec<_>>();
        roots.extend(assumptions.iter().copied());
        if let Some(target) = target {
            roots.push(target);
        }
        let compacted = inner.builder.compact(&roots)?;
        let assertion_roots = ordered_assertions
            .iter()
            .map(|a| compacted.remap_ref(a.root))
            .collect::<Result<Vec<_>>>()?;
        let assumption_roots = assumptions
            .iter()
            .map(|r| compacted.remap_ref(*r))
            .collect::<Result<Vec<_>>>()?;
        let target_ref = target.map(|r| compacted.remap_ref(r)).transpose()?;
        let new_to_old = compacted.new_to_old().clone();
        let request = BinaryRequest::new(
            request_id,
            command,
            flags,
            budget_ms,
            compacted.into_bytes(),
            assertion_roots,
            named_refs,
            assumption_roots,
            target_ref,
        )?;
        Ok(BuiltRequest {
            payload: request.encode()?,
            context: self.clone(),
            new_to_old,
        })
    }

    fn bv_unary(&self, tag: Tag, x: &BvTerm) -> Result<BvTerm> {
        let x_ref = self.expect_bv(x, tag.smt_symbol())?.0;
        let reference = match tag {
            Tag::BvNot => self.inner.borrow_mut().builder.bv_not(x_ref)?,
            Tag::BvNeg => self.inner.borrow_mut().builder.bv_neg(x_ref)?,
            _ => {
                return Err(WireError::invalid(
                    "BV unary",
                    format!("unsupported tag {}", tag.name()),
                ))
            }
        };
        self.bv_term(reference)
    }

    fn bv_binary<'a, B>(&self, tag: Tag, a: &BvTerm, b: B) -> Result<BvTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        let (a_ref, width) = self.expect_bv(a, tag.smt_symbol())?;
        let b = self.coerce_bv_operand(b.into(), width, tag.smt_symbol())?;
        let reference = match tag {
            Tag::BvAnd => self.inner.borrow_mut().builder.bv_and(a_ref, b.reference)?,
            Tag::BvOr => self.inner.borrow_mut().builder.bv_or(a_ref, b.reference)?,
            Tag::BvXor => self.inner.borrow_mut().builder.bv_xor(a_ref, b.reference)?,
            Tag::BvAdd => self.inner.borrow_mut().builder.bv_add(a_ref, b.reference)?,
            Tag::BvSub => self.inner.borrow_mut().builder.bv_sub(a_ref, b.reference)?,
            Tag::BvMul => self.inner.borrow_mut().builder.bv_mul(a_ref, b.reference)?,
            Tag::BvUdiv => self
                .inner
                .borrow_mut()
                .builder
                .bv_udiv(a_ref, b.reference)?,
            Tag::BvUrem => self
                .inner
                .borrow_mut()
                .builder
                .bv_urem(a_ref, b.reference)?,
            Tag::BvSdiv => self
                .inner
                .borrow_mut()
                .builder
                .bv_sdiv(a_ref, b.reference)?,
            Tag::BvSrem => self
                .inner
                .borrow_mut()
                .builder
                .bv_srem(a_ref, b.reference)?,
            Tag::BvSmod => self
                .inner
                .borrow_mut()
                .builder
                .bv_smod(a_ref, b.reference)?,
            Tag::BvShl => self.inner.borrow_mut().builder.bv_shl(a_ref, b.reference)?,
            Tag::BvLshr => self
                .inner
                .borrow_mut()
                .builder
                .bv_lshr(a_ref, b.reference)?,
            Tag::BvAshr => self
                .inner
                .borrow_mut()
                .builder
                .bv_ashr(a_ref, b.reference)?,
            _ => {
                return Err(WireError::invalid(
                    "BV binary",
                    format!("unsupported tag {}", tag.name()),
                ))
            }
        };
        self.bv_term(reference)
    }

    fn bv_cmp<'a, B>(&self, tag: Tag, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        let (a_ref, width) = self.expect_bv(a, tag.smt_symbol())?;
        let b = self.coerce_bv_operand(b.into(), width, tag.smt_symbol())?;
        let reference = self.push_bv_cmp(tag, a_ref, b.reference)?;
        self.bool_term(reference)
    }

    fn bv_cmp_reverse<'a, B>(&self, tag: Tag, a: &BvTerm, b: B) -> Result<BoolTerm>
    where
        B: Into<BvOperand<'a>>,
    {
        let (_a_ref, width) = self.expect_bv(a, tag.smt_symbol())?;
        let b = self.coerce_bv_operand(b.into(), width, tag.smt_symbol())?;
        let reference = self.push_bv_cmp(tag, b.reference, a.reference)?;
        self.bool_term(reference)
    }

    fn push_bv_cmp(&self, tag: Tag, a: NodeRef, b: NodeRef) -> Result<NodeRef> {
        let mut builder = self.inner.borrow_mut();
        match tag {
            Tag::BvEq => builder.builder.bv_eq(a, b),
            Tag::BvUlt => builder.builder.bv_ult(a, b),
            Tag::BvUle => builder.builder.bv_ule(a, b),
            Tag::BvSlt => builder.builder.bv_slt(a, b),
            Tag::BvSle => builder.builder.bv_sle(a, b),
            Tag::UaddOvf => builder.builder.uadd_ovf(a, b),
            Tag::SaddOvf => builder.builder.sadd_ovf(a, b),
            Tag::UsubOvf => builder.builder.usub_ovf(a, b),
            Tag::SsubOvf => builder.builder.ssub_ovf(a, b),
            Tag::UmulOvf => builder.builder.umul_ovf(a, b),
            Tag::SmulOvf => builder.builder.smul_ovf(a, b),
            Tag::SdivOvf => builder.builder.sdiv_ovf(a, b),
            _ => Err(WireError::invalid(
                "BV comparison",
                format!("unsupported tag {}", tag.name()),
            )),
        }
    }

    fn bool_binary(&self, tag: Tag, a: &BoolTerm, b: &BoolTerm) -> Result<BoolTerm> {
        self.expect_bool(a, tag.smt_symbol())?;
        self.expect_bool(b, tag.smt_symbol())?;
        let reference = match tag {
            Tag::BoolAnd => self
                .inner
                .borrow_mut()
                .builder
                .bool_and(a.reference, b.reference)?,
            Tag::BoolOr => self
                .inner
                .borrow_mut()
                .builder
                .bool_or(a.reference, b.reference)?,
            Tag::BoolImplies => self
                .inner
                .borrow_mut()
                .builder
                .bool_implies(a.reference, b.reference)?,
            _ => {
                return Err(WireError::invalid(
                    "Bool binary",
                    format!("unsupported tag {}", tag.name()),
                ))
            }
        };
        self.bool_term(reference)
    }

    fn coerce_bv_operand(
        &self,
        value: BvOperand<'_>,
        width: u32,
        op: &'static str,
    ) -> Result<BvTerm> {
        match value {
            BvOperand::Term(term) => {
                let actual = self.expect_bv(term, op)?.1;
                if actual != width {
                    return Err(WireError::invalid(
                        op,
                        format!("BV width mismatch ({width} vs {actual})"),
                    ));
                }
                Ok(term.clone())
            }
            BvOperand::OwnedTerm(term) => {
                let actual = self.expect_bv(&term, op)?.1;
                if actual != width {
                    return Err(WireError::invalid(
                        op,
                        format!("BV width mismatch ({width} vs {actual})"),
                    ));
                }
                Ok(term)
            }
            BvOperand::Unsigned(value) => self.bv_const(value, width),
            BvOperand::Signed(value) => self.bv_const(value as u64, width),
        }
    }

    fn bv_term(&self, reference: NodeRef) -> Result<BvTerm> {
        let meta = self.meta_for_ref(reference)?;
        if meta.sort != Sort::Bv {
            return Err(WireError::invalid("term reference", "expected BV term"));
        }
        Ok(BvTerm {
            ctx: self.clone(),
            reference,
        })
    }

    fn bool_term(&self, reference: NodeRef) -> Result<BoolTerm> {
        let meta = self.meta_for_ref(reference)?;
        if meta.sort != Sort::Bool {
            return Err(WireError::invalid("term reference", "expected Bool term"));
        }
        Ok(BoolTerm {
            ctx: self.clone(),
            reference,
        })
    }

    fn meta_for_ref(&self, reference: NodeRef) -> Result<NodeMeta> {
        let inner = self.inner.borrow();
        let meta = inner
            .builder
            .meta
            .get(reference.index() as usize)
            .copied()
            .ok_or_else(|| {
                WireError::invalid(
                    "node reference",
                    format!(
                        "reference {:#010x} points outside {} nodes",
                        reference.raw(),
                        inner.builder.meta.len()
                    ),
                )
            })?;
        if meta.sort != reference.sort() {
            return Err(WireError::invalid(
                "node reference",
                format!(
                    "reference sort {:?} does not match node sort {:?}",
                    reference.sort(),
                    meta.sort
                ),
            ));
        }
        Ok(meta)
    }

    fn node_for_ref(&self, reference: NodeRef) -> Result<RawNode> {
        self.meta_for_ref(reference)?;
        Ok(self.inner.borrow().builder.nodes[reference.index() as usize])
    }

    fn blob_str(&self, reference: BlobRef) -> Result<String> {
        blob_str_from_builder(&self.inner.borrow().builder, reference)
    }

    fn expect_term(&self, term: &Term, op: &'static str) -> Result<()> {
        match term {
            Term::Bv(t) => {
                self.expect_bv(t, op)?;
            }
            Term::Bool(t) => {
                self.expect_bool(t, op)?;
            }
        }
        Ok(())
    }

    fn expect_bv(&self, term: &BvTerm, op: &'static str) -> Result<(NodeRef, u32)> {
        if !Rc::ptr_eq(&self.inner, &term.ctx.inner) {
            return Err(WireError::invalid(
                op,
                format!("term from {}, expected {}", term.ctx, self),
            ));
        }
        let meta = self.meta_for_ref(term.reference)?;
        if meta.sort != Sort::Bv {
            return Err(WireError::invalid(op, "expected BV term"));
        }
        Ok((term.reference, meta.width))
    }

    fn expect_bool(&self, term: &BoolTerm, op: &'static str) -> Result<()> {
        if !Rc::ptr_eq(&self.inner, &term.ctx.inner) {
            return Err(WireError::invalid(
                op,
                format!("term from {}, expected {}", term.ctx, self),
            ));
        }
        let meta = self.meta_for_ref(term.reference)?;
        if meta.sort != Sort::Bool {
            return Err(WireError::invalid(op, "expected Bool term"));
        }
        Ok(())
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Context#{}", self.id())
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = self.inner.borrow();
        write!(
            f,
            "Context#{}(nodes={}, assertions={})",
            inner.id,
            inner.builder.node_count(),
            inner.builder.assertions.len()
        )
    }
}

impl BvTerm {
    pub fn context(&self) -> Context {
        self.ctx.clone()
    }
    pub fn id(&self) -> u32 {
        self.reference.index()
    }
    pub fn raw_ref(&self) -> NodeRef {
        self.reference
    }
    pub fn width(&self) -> Result<u32> {
        Ok(self.ctx.meta_for_ref(self.reference)?.width)
    }
    pub fn as_term(&self) -> Term {
        Term::Bv(self.clone())
    }
    pub fn op(&self) -> Result<Tag> {
        Term::Bv(self.clone()).op()
    }
    pub fn children(&self) -> Result<Vec<Term>> {
        Term::Bv(self.clone()).children()
    }
    pub fn name(&self) -> Result<String> {
        Term::Bv(self.clone()).name()
    }
    pub fn value_u128(&self) -> Result<u128> {
        Term::Bv(self.clone()).value_u128()
    }
    pub fn value_bytes_le(&self) -> Result<Vec<u8>> {
        Term::Bv(self.clone()).value_bytes_le()
    }
    pub fn params(&self) -> Result<Vec<u32>> {
        Term::Bv(self.clone()).params()
    }
    pub fn to_smt2(&self, depth: isize) -> Result<String> {
        Term::Bv(self.clone()).to_smt2(depth)
    }
    pub fn walk(&self, order: WalkOrder, unique: bool) -> Result<Vec<Term>> {
        Term::Bv(self.clone()).walk(order, unique)
    }
}

impl BoolTerm {
    pub fn context(&self) -> Context {
        self.ctx.clone()
    }
    pub fn id(&self) -> u32 {
        self.reference.index()
    }
    pub fn raw_ref(&self) -> NodeRef {
        self.reference
    }
    pub fn as_term(&self) -> Term {
        Term::Bool(self.clone())
    }
    pub fn op(&self) -> Result<Tag> {
        Term::Bool(self.clone()).op()
    }
    pub fn children(&self) -> Result<Vec<Term>> {
        Term::Bool(self.clone()).children()
    }
    pub fn name(&self) -> Result<String> {
        Term::Bool(self.clone()).name()
    }
    pub fn bool_value(&self) -> Result<bool> {
        Term::Bool(self.clone()).bool_value()
    }
    pub fn params(&self) -> Result<Vec<u32>> {
        Term::Bool(self.clone()).params()
    }
    pub fn to_smt2(&self, depth: isize) -> Result<String> {
        Term::Bool(self.clone()).to_smt2(depth)
    }
    pub fn walk(&self, order: WalkOrder, unique: bool) -> Result<Vec<Term>> {
        Term::Bool(self.clone()).walk(order, unique)
    }
}

impl Term {
    pub fn context(&self) -> Context {
        match self {
            Term::Bv(t) => t.context(),
            Term::Bool(t) => t.context(),
        }
    }

    pub fn id(&self) -> u32 {
        self.reference().index()
    }
    pub fn raw_ref(&self) -> NodeRef {
        self.reference()
    }
    pub fn sort(&self) -> Sort {
        self.reference().sort()
    }

    pub fn op(&self) -> Result<Tag> {
        parse_tag(self.context().node_for_ref(self.reference())?.tag)
    }

    pub fn children(&self) -> Result<Vec<Term>> {
        let ctx = self.context();
        let node = ctx.node_for_ref(self.reference())?;
        let inner = ctx.inner.borrow();
        let start = node.children as usize;
        let refs = inner.builder.children[start..start + node.arity as usize].to_vec();
        drop(inner);
        refs.into_iter().map(|r| ctx.term(r)).collect()
    }

    pub fn name(&self) -> Result<String> {
        let ctx = self.context();
        let node = ctx.node_for_ref(self.reference())?;
        let tag = parse_tag(node.tag)?;
        if !matches!(tag, Tag::BvVar | Tag::BoolVar) {
            return Err(WireError::invalid(
                "term name",
                format!("term #{} is not a variable", self.id()),
            ));
        }
        ctx.blob_str(node.blob_ref())
    }

    pub fn value_u128(&self) -> Result<u128> {
        let bytes = self.value_bytes_le()?;
        if bytes.len() > 16 {
            return Err(WireError::invalid(
                "BV constant",
                "constant does not fit in u128",
            ));
        }
        let mut arr = [0u8; 16];
        arr[..bytes.len()].copy_from_slice(&bytes);
        Ok(u128::from_le_bytes(arr))
    }

    pub fn value_bytes_le(&self) -> Result<Vec<u8>> {
        let ctx = self.context();
        let node = ctx.node_for_ref(self.reference())?;
        let tag = parse_tag(node.tag)?;
        if tag != Tag::BvConst {
            return Err(WireError::invalid(
                "BV constant",
                format!("term #{} is not a BV constant", self.id()),
            ));
        }
        let len = bytes_for_width(node.width)?;
        if node.width <= 64 {
            let mask = if node.width == 64 {
                u64::MAX
            } else {
                (1u64 << node.width) - 1
            };
            let value = node.payload & mask;
            let mut bytes = value.to_le_bytes().to_vec();
            bytes.truncate(len);
            Ok(bytes)
        } else {
            Ok(ctx
                .inner
                .borrow()
                .builder
                .blob_ref(node.blob_ref())?
                .to_vec())
        }
    }

    pub fn bool_value(&self) -> Result<bool> {
        let tag = self.op()?;
        match tag {
            Tag::BoolTrue => Ok(true),
            Tag::BoolFalse => Ok(false),
            _ => Err(WireError::invalid(
                "Bool constant",
                format!("term #{} is not a Bool constant", self.id()),
            )),
        }
    }

    pub fn params(&self) -> Result<Vec<u32>> {
        let ctx = self.context();
        let node = ctx.node_for_ref(self.reference())?;
        Ok(match parse_tag(node.tag)? {
            Tag::BvExtract => vec![u32::from(node.aux_hi), node.aux_lo],
            Tag::BvZext | Tag::BvSext | Tag::BvSelect => vec![u32::from(node.aux_hi)],
            _ => Vec::new(),
        })
    }

    pub fn to_smt2(&self, depth: isize) -> Result<String> {
        if depth < -1 {
            return Err(WireError::invalid(
                "SMT-LIB depth",
                "depth must be -1 or non-negative",
            ));
        }
        let ctx = self.context();
        let inner = ctx.inner.borrow();
        let rendered = render_smt2_from_builder(
            &inner.builder,
            self.reference(),
            if depth == -1 { None } else { Some(depth) },
            true,
        )?;
        Ok(format!("{rendered} ; #{}", self.id()))
    }

    pub fn walk(&self, order: WalkOrder, unique: bool) -> Result<Vec<Term>> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        self.walk_into(order, unique, &mut seen, &mut out)?;
        Ok(out)
    }

    pub fn visit<R: Clone, F>(&self, f: &mut F) -> Result<R>
    where
        F: FnMut(&Term, Vec<R>) -> Result<R>,
    {
        fn go<R: Clone, F>(term: &Term, f: &mut F, memo: &mut HashMap<NodeRef, R>) -> Result<R>
        where
            F: FnMut(&Term, Vec<R>) -> Result<R>,
        {
            if let Some(value) = memo.get(&term.reference()).cloned() {
                return Ok(value);
            }
            let mut args = Vec::new();
            for child in term.children()? {
                args.push(go(&child, f, memo)?);
            }
            let value = f(term, args)?;
            memo.insert(term.reference(), value.clone());
            Ok(value)
        }
        go(self, f, &mut HashMap::new())
    }

    fn walk_into(
        &self,
        order: WalkOrder,
        unique: bool,
        seen: &mut HashSet<NodeRef>,
        out: &mut Vec<Term>,
    ) -> Result<()> {
        if unique && !seen.insert(self.reference()) {
            return Ok(());
        }
        if order == WalkOrder::Pre {
            out.push(self.clone());
        }
        for child in self.children()? {
            child.walk_into(order, unique, seen, out)?;
        }
        if order == WalkOrder::Post {
            out.push(self.clone());
        }
        Ok(())
    }

    fn reference(&self) -> NodeRef {
        match self {
            Term::Bv(t) => t.reference,
            Term::Bool(t) => t.reference,
        }
    }
}

impl PartialEq for BvTerm {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.ctx.inner, &other.ctx.inner) && self.reference == other.reference
    }
}
impl Eq for BvTerm {}
impl Hash for BvTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.ctx.inner).hash(state);
        self.reference.hash(state);
    }
}

impl PartialEq for BoolTerm {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.ctx.inner, &other.ctx.inner) && self.reference == other.reference
    }
}
impl Eq for BoolTerm {}
impl Hash for BoolTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.ctx.inner).hash(state);
        self.reference.hash(state);
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.context().inner, &other.context().inner)
            && self.reference() == other.reference()
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.context().inner).hash(state);
        self.reference().hash(state);
    }
}

impl fmt::Debug for BvTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.width() {
            Ok(width) => write!(f, "BvTerm({}#{}: BV{})", self.ctx, self.id(), width),
            Err(_) => write!(f, "BvTerm({}#{})", self.ctx, self.id()),
        }
    }
}

impl fmt::Debug for BoolTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BoolTerm({}#{})", self.ctx, self.id())
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Bv(t) => t.fmt(f),
            Term::Bool(t) => t.fmt(f),
        }
    }
}

impl<'a> From<&'a BvTerm> for BvOperand<'a> {
    fn from(value: &'a BvTerm) -> Self {
        BvOperand::Term(value)
    }
}
impl<'a> From<BvTerm> for BvOperand<'a> {
    fn from(value: BvTerm) -> Self {
        BvOperand::OwnedTerm(value)
    }
}
impl<'a> From<u64> for BvOperand<'a> {
    fn from(value: u64) -> Self {
        BvOperand::Unsigned(value)
    }
}
impl<'a> From<u32> for BvOperand<'a> {
    fn from(value: u32) -> Self {
        BvOperand::Unsigned(u64::from(value))
    }
}
impl<'a> From<u16> for BvOperand<'a> {
    fn from(value: u16) -> Self {
        BvOperand::Unsigned(u64::from(value))
    }
}
impl<'a> From<u8> for BvOperand<'a> {
    fn from(value: u8) -> Self {
        BvOperand::Unsigned(u64::from(value))
    }
}
impl<'a> From<usize> for BvOperand<'a> {
    fn from(value: usize) -> Self {
        BvOperand::Unsigned(value as u64)
    }
}
impl<'a> From<i64> for BvOperand<'a> {
    fn from(value: i64) -> Self {
        BvOperand::Signed(value)
    }
}
impl<'a> From<i32> for BvOperand<'a> {
    fn from(value: i32) -> Self {
        BvOperand::Signed(i64::from(value))
    }
}
impl<'a> From<i16> for BvOperand<'a> {
    fn from(value: i16) -> Self {
        BvOperand::Signed(i64::from(value))
    }
}
impl<'a> From<i8> for BvOperand<'a> {
    fn from(value: i8) -> Self {
        BvOperand::Signed(i64::from(value))
    }
}
impl<'a> From<isize> for BvOperand<'a> {
    fn from(value: isize) -> Self {
        BvOperand::Signed(value as i64)
    }
}

pub struct Client {
    transport: TcpClient,
    next_request_id: u32,
}

impl Client {
    pub fn connect(addr: impl ToSocketAddrs) -> ClientResult<Self> {
        Ok(Self {
            transport: TcpClient::connect(addr)?,
            next_request_id: 1,
        })
    }

    pub fn from_stream(stream: TcpStream) -> Self {
        Self {
            transport: TcpClient::from_stream(stream),
            next_request_id: 1,
        }
    }

    pub fn from_transport(transport: TcpClient) -> Self {
        Self {
            transport,
            next_request_id: 1,
        }
    }

    pub fn set_max_response_bytes(&mut self, max_response_bytes: usize) {
        self.transport.set_max_response_bytes(max_response_bytes);
    }

    pub fn set_read_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        self.transport.set_read_timeout(timeout)
    }

    pub fn set_write_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        self.transport.set_write_timeout(timeout)
    }

    pub fn solve(&mut self, ctx: &Context) -> ClientResult<Response> {
        self.solve_with_options(ctx, SolveOptions::default())
    }

    pub fn solve_with_options(
        &mut self,
        ctx: &Context,
        options: SolveOptions,
    ) -> ClientResult<Response> {
        let request_id = self.request_id(options.request_id)?;
        let request = ctx.build_solve_request_context(
            request_id,
            options.budget_ms,
            options.want_model,
            options.want_core,
        )?;
        let raw = self.transport.send_binary_request(&request.payload)?;
        self.solve_response(raw, request)
    }

    pub fn simplify(&mut self, term: &Term) -> ClientResult<SimplifyResult> {
        self.simplify_with_request_id(term, None)
    }

    pub fn simplify_with_request_id(
        &mut self,
        term: &Term,
        request_id: Option<u32>,
    ) -> ClientResult<SimplifyResult> {
        let request_id = self.request_id(request_id)?;
        let request = term.context().build_simplify_request(request_id, term)?;
        let raw = self.transport.send_binary_request(&request.payload)?;
        self.simplify_response(raw)
    }

    pub fn minimize(&mut self, target: &BvTerm) -> ClientResult<OptimizationResult> {
        self.minimize_with_options(target, OptimizeOptions::default())
    }

    pub fn minimize_with_options(
        &mut self,
        target: &BvTerm,
        options: OptimizeOptions,
    ) -> ClientResult<OptimizationResult> {
        let request_id = self.request_id(options.request_id)?;
        let request = target.context().build_minimize_request(
            request_id,
            target,
            options.signed,
            options.budget_ms,
            options.want_model,
        )?;
        let raw = self.transport.send_binary_request(&request.payload)?;
        self.optimization_response(raw, request)
    }

    pub fn maximize(&mut self, target: &BvTerm) -> ClientResult<OptimizationResult> {
        self.maximize_with_options(target, OptimizeOptions::default())
    }

    pub fn maximize_with_options(
        &mut self,
        target: &BvTerm,
        options: OptimizeOptions,
    ) -> ClientResult<OptimizationResult> {
        let request_id = self.request_id(options.request_id)?;
        let request = target.context().build_maximize_request(
            request_id,
            target,
            options.signed,
            options.budget_ms,
            options.want_model,
        )?;
        let raw = self.transport.send_binary_request(&request.payload)?;
        self.optimization_response(raw, request)
    }

    pub fn smt2(&mut self, script: &str) -> ClientResult<String> {
        self.transport.send_text(script)
    }

    fn request_id(&mut self, requested: Option<u32>) -> ClientResult<u32> {
        if let Some(id) = requested {
            return Ok(id);
        }
        let id = self.next_request_id;
        self.next_request_id = self.next_request_id.checked_add(1).unwrap_or(1);
        Ok(id)
    }

    fn solve_response(&self, raw: BinaryResponse, request: BuiltRequest) -> ClientResult<Response> {
        let request_id = raw.envelope.request_id;
        let status = raw.envelope.status;
        let flags = raw.envelope.flags;
        match status {
            Status::Error => Ok(Response {
                request_id,
                status,
                flags,
                message: Some(message_from_payload(&raw.payload)?),
                model: None,
                core: None,
            }),
            Status::Unknown => Ok(Response {
                request_id,
                status,
                flags,
                message: message_if_present(flags, &raw.payload)?,
                model: None,
                core: None,
            }),
            Status::Sat => {
                if (flags & response_flags::HAS_VALUE) != 0 {
                    return Err(WireError::invalid(
                        "solve response",
                        "unexpected optimization value",
                    )
                    .into());
                }
                let model = if (flags & response_flags::HAS_MODEL) != 0 {
                    Some(self.model_from_block(ModelBlock::decode(&raw.payload)?, &request)?)
                } else {
                    None
                };
                Ok(Response {
                    request_id,
                    status,
                    flags,
                    message: None,
                    model,
                    core: None,
                })
            }
            Status::Unsat => {
                let core = if (flags & response_flags::HAS_CORE) != 0 {
                    Some(UnsatCoreBlock::decode(&raw.payload)?.names)
                } else {
                    None
                };
                Ok(Response {
                    request_id,
                    status,
                    flags,
                    message: None,
                    model: None,
                    core,
                })
            }
            Status::Simplified => {
                Err(WireError::invalid("solve response", "unexpected SIMPLIFIED status").into())
            }
        }
    }

    fn simplify_response(&self, raw: BinaryResponse) -> ClientResult<SimplifyResult> {
        let request_id = raw.envelope.request_id;
        let status = raw.envelope.status;
        match status {
            Status::Error => Ok(SimplifyResult {
                request_id,
                status,
                message: Some(message_from_payload(&raw.payload)?),
                context: None,
                term: None,
            }),
            Status::Unknown => Ok(SimplifyResult {
                request_id,
                status,
                message: message_if_present(raw.envelope.flags, &raw.payload)?,
                context: None,
                term: None,
            }),
            Status::Simplified => {
                let block = SimplifyBlock::decode(&raw.payload)?;
                let ctx = Context::from_expression_bytes(block.expression)?;
                let term = ctx.term(block.target_node)?;
                Ok(SimplifyResult {
                    request_id,
                    status,
                    message: None,
                    context: Some(ctx),
                    term: Some(term),
                })
            }
            _ => Err(WireError::invalid(
                "simplify response",
                format!("unexpected status {:?}", status),
            )
            .into()),
        }
    }

    fn optimization_response(
        &self,
        raw: BinaryResponse,
        request: BuiltRequest,
    ) -> ClientResult<OptimizationResult> {
        let request_id = raw.envelope.request_id;
        let status = raw.envelope.status;
        let flags = raw.envelope.flags;
        match status {
            Status::Error => Ok(OptimizationResult {
                request_id,
                status,
                flags,
                message: Some(message_from_payload(&raw.payload)?),
                optimum: None,
                model: None,
            }),
            Status::Unknown => Ok(OptimizationResult {
                request_id,
                status,
                flags,
                message: message_if_present(flags, &raw.payload)?,
                optimum: None,
                model: None,
            }),
            Status::Unsat => Ok(OptimizationResult {
                request_id,
                status,
                flags,
                message: None,
                optimum: None,
                model: None,
            }),
            Status::Sat => {
                if (flags & response_flags::HAS_VALUE) == 0 {
                    return Err(WireError::invalid(
                        "optimization response",
                        "SAT response missing value",
                    )
                    .into());
                }
                let block = OptimizationValueBlock::decode(
                    &raw.payload,
                    (flags & response_flags::HAS_MODEL) != 0,
                )?;
                let model = block
                    .model
                    .map(|model| self.model_from_block(model, &request))
                    .transpose()?;
                Ok(OptimizationResult {
                    request_id,
                    status,
                    flags,
                    message: None,
                    optimum: Some(block.optimum),
                    model,
                })
            }
            Status::Simplified => Err(WireError::invalid(
                "optimization response",
                "unexpected SIMPLIFIED status",
            )
            .into()),
        }
    }

    fn model_from_block(&self, block: ModelBlock, request: &BuiltRequest) -> ClientResult<Model> {
        let mut values = HashMap::new();
        for entry in block.entries {
            let old_ref = request
                .new_to_old
                .get(&entry.node_ref)
                .copied()
                .ok_or_else(|| {
                    WireError::invalid(
                        "model",
                        format!("unknown compacted node ref {:#010x}", entry.node_ref.raw()),
                    )
                })?;
            let node = request.context.node_for_ref(old_ref)?;
            let tag = parse_tag(node.tag)?;
            match old_ref.sort() {
                Sort::Bool => {
                    if tag != Tag::BoolVar || entry.value.width != 0 {
                        return Err(WireError::invalid(
                            "model",
                            "Bool entry does not match a Bool variable",
                        )
                        .into());
                    }
                }
                Sort::Bv => {
                    if tag != Tag::BvVar || entry.value.width != node.width {
                        return Err(WireError::invalid(
                            "model",
                            "BV entry does not match a BV variable",
                        )
                        .into());
                    }
                }
            }
            values.insert(old_ref, entry.value);
        }
        Ok(Model {
            ctx: request.context.clone(),
            values,
        })
    }
}

impl Model {
    pub fn context(&self) -> Context {
        self.ctx.clone()
    }
    pub fn len(&self) -> usize {
        self.values.len()
    }
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn contains(&self, term: &Term) -> bool {
        Rc::ptr_eq(&self.ctx.inner, &term.context().inner)
            && self.values.contains_key(&term.raw_ref())
    }

    pub fn get(&self, term: &Term) -> Option<&ScalarValue> {
        if !Rc::ptr_eq(&self.ctx.inner, &term.context().inner) {
            return None;
        }
        self.values.get(&term.raw_ref())
    }

    pub fn get_bv(&self, term: &BvTerm) -> Option<&ScalarValue> {
        if !Rc::ptr_eq(&self.ctx.inner, &term.ctx.inner) {
            return None;
        }
        self.values.get(&term.reference)
    }

    pub fn get_bool(&self, term: &BoolTerm) -> Option<&ScalarValue> {
        if !Rc::ptr_eq(&self.ctx.inner, &term.ctx.inner) {
            return None;
        }
        self.values.get(&term.reference)
    }

    pub fn iter(&self) -> impl Iterator<Item = (Term, &ScalarValue)> {
        self.values.iter().filter_map(|(reference, value)| {
            self.ctx.term(*reference).ok().map(|term| (term, value))
        })
    }
}

impl fmt::Debug for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Model({}, entries={})", self.ctx, self.values.len())
    }
}

fn message_from_payload(payload: &[u8]) -> ClientResult<String> {
    Ok(String::from_utf8(payload.to_vec())?)
}

fn message_if_present(flags: u8, payload: &[u8]) -> ClientResult<Option<String>> {
    if (flags & response_flags::HAS_MESSAGE) != 0 {
        Ok(Some(message_from_payload(payload)?))
    } else {
        Ok(None)
    }
}

fn parse_tag(raw: u8) -> Result<Tag> {
    Tag::try_from(raw).map_err(|_| WireError::invalid("node tag", format!("unknown tag {raw}")))
}

fn blob_ref_payload(offset: u32, len: u32) -> u64 {
    ((offset as u64) << 32) | len as u64
}

trait BuilderBlobExt {
    fn blob_ref(&self, reference: BlobRef) -> Result<&[u8]>;
}

impl BuilderBlobExt for ExprBuilder {
    fn blob_ref(&self, reference: BlobRef) -> Result<&[u8]> {
        let start = reference.offset as usize;
        let end = start
            .checked_add(reference.len as usize)
            .ok_or(WireError::IntegerOverflow("blob reference"))?;
        if end > self.blob.len() {
            return Err(WireError::invalid(
                "blob reference",
                "offset plus length exceeds blob length",
            ));
        }
        Ok(&self.blob[start..end])
    }
}

fn blob_str_from_builder(builder: &ExprBuilder, reference: BlobRef) -> Result<String> {
    let bytes = builder.blob_ref(reference)?;
    let s = core::str::from_utf8(bytes).map_err(|_| WireError::InvalidUtf8 {
        context: "blob string",
        offset: reference.offset,
        len: reference.len,
    })?;
    Ok(s.to_owned())
}

fn render_smt2_from_builder(
    builder: &ExprBuilder,
    reference: NodeRef,
    remaining: Option<isize>,
    root: bool,
) -> Result<String> {
    let idx = reference.index() as usize;
    let node = *builder.nodes.get(idx).ok_or_else(|| {
        WireError::invalid(
            "SMT-LIB rendering",
            format!("reference #{} out of range", reference.index()),
        )
    })?;
    let tag = parse_tag(node.tag)?;
    if remaining.is_some_and(|r| !root && r < 0 && !is_atom(tag)) {
        return Ok(format!("|#{}|", reference.index()));
    }
    let next_remaining = remaining.map(|r| r - 1);
    let mut children = Vec::new();
    for i in 0..node.arity as usize {
        let child = builder.children[node.children as usize + i];
        children.push(render_smt2_from_builder(
            builder,
            child,
            next_remaining,
            false,
        )?);
    }
    Ok(match tag {
        Tag::BvVar | Tag::BoolVar => {
            quote_symbol(&blob_str_from_builder(builder, node.blob_ref())?)
        }
        Tag::BvConst => format_bv_const(builder, node)?,
        Tag::BoolTrue => "true".to_owned(),
        Tag::BoolFalse => "false".to_owned(),
        Tag::BvExtract => format!(
            "((_ extract {} {}) {})",
            node.aux_hi, node.aux_lo, children[0]
        ),
        Tag::BvConcat => format!("(concat {} {})", children[0], children[1]),
        Tag::BvZext => format!("((_ zero_extend {}) {})", node.aux_hi, children[0]),
        Tag::BvSext => format!("((_ sign_extend {}) {})", node.aux_hi, children[0]),
        Tag::BvIte => format!("(ite {} {} {})", children[0], children[1], children[2]),
        Tag::BvSelect => {
            let mut expr = children.last().cloned().unwrap_or_default();
            for i in (0..node.aux_hi as usize).rev() {
                expr = format!("(ite {} {} {})", children[2 * i], children[2 * i + 1], expr);
            }
            expr
        }
        _ if node.arity == 1 => format!("({} {})", tag.smt_symbol(), children[0]),
        _ if node.arity == 2 => format!("({} {} {})", tag.smt_symbol(), children[0], children[1]),
        _ => format!("(|tag#{}| {})", node.tag, children.join(" ")),
    })
}

fn is_atom(tag: Tag) -> bool {
    matches!(
        tag,
        Tag::BvVar | Tag::BvConst | Tag::BoolTrue | Tag::BoolFalse | Tag::BoolVar
    )
}

fn format_bv_const(builder: &ExprBuilder, node: RawNode) -> Result<String> {
    let bytes = if node.width <= 64 {
        let len = bytes_for_width(node.width)?;
        let mask = if node.width == 64 {
            u64::MAX
        } else {
            (1u64 << node.width) - 1
        };
        let mut bytes = (node.payload & mask).to_le_bytes().to_vec();
        bytes.truncate(len);
        bytes
    } else {
        builder.blob_ref(node.blob_ref())?.to_vec()
    };
    if node.width.is_multiple_of(4) {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut out = String::from("#x");
        for nibble in (0..node.width / 4).rev() {
            let bit = nibble * 4;
            let byte = bytes[(bit / 8) as usize];
            let value = if bit % 8 == 0 {
                byte & 0x0f
            } else {
                (byte >> 4) & 0x0f
            };
            out.push(HEX[value as usize] as char);
        }
        Ok(out)
    } else {
        let mut out = String::from("#b");
        for bit in (0..node.width).rev() {
            let byte = bytes[(bit / 8) as usize];
            out.push(if (byte & (1u8 << (bit % 8))) != 0 {
                '1'
            } else {
                '0'
            });
        }
        Ok(out)
    }
}

fn quote_symbol(name: &str) -> String {
    fn simple_start(c: char) -> bool {
        c.is_ascii_alphabetic() || "_~!@$%^&*+=<>.?/-".contains(c)
    }
    fn simple_rest(c: char) -> bool {
        c.is_ascii_alphanumeric() || "_~!@$%^&*+=<>.?/-".contains(c)
    }
    const RESERVED: &[&str] = &[
        "let", "par", "forall", "exists", "match", "_", "!", "as", "true", "false",
    ];
    let mut chars = name.chars();
    let simple = chars.next().is_some_and(simple_start)
        && chars.all(simple_rest)
        && !RESERVED.contains(&name)
        && !name.starts_with('#');
    if simple {
        name.to_owned()
    } else {
        format!("|{}|", name.replace('\\', "\\\\").replace('|', "\\|"))
    }
}

#[allow(dead_code)]
fn normalize_bv_bytes(mut bytes: Vec<u8>, width: u32) -> Result<Vec<u8>> {
    validate_bv_width_value(width, "BV width")?;
    let expected = bytes_for_width(width)?;
    if bytes.len() != expected {
        return Err(WireError::invalid(
            "BV bytes",
            format!("got {}, expected {expected}", bytes.len()),
        ));
    }
    let valid = width % 8;
    if valid != 0 {
        let mask = (1u8 << valid) - 1;
        let last = bytes.len() - 1;
        bytes[last] &= mask;
    }
    Ok(bytes)
}

#[allow(dead_code)]
fn blob_payload(reference: BlobRef) -> u64 {
    blob_ref_payload(reference.offset, reference.len)
}
