//! Signed reciprocal kernels projected onto an explicit 8/16/32-bit word.
//!
//! Projection commutes with ring operations, masks retaining all word bits and
//! extension from at least that width. It does not commute with right shifts.
//! The latter require an explicit signed input and a full signed product.
use super::pure_expression::Work;
use super::reciprocal_bounds::SignedReciprocal;
use crate::model::ir::{BinaryOp as B, Expr, UnaryOp as U, Width};

pub use super::pure_expression::{MAX_DEPTH, MAX_NODES, MAX_WORK};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation {
    Quotient,
    Remainder,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Evidence {
    pub multiplier: u64,
    pub shift: u32,
    pub excess: u64,
    pub positive_bound: u128,
    pub negative_bound: u128,
}

/// Source keys remain typed: expression references or block-local value IDs.
#[derive(Clone, Copy, Debug)]
pub struct WordView<K> {
    pub value: K,
    /// Exact full product supplying the signed high word.
    pub product: K,
    pub width: Width,
    pub divisor: i64,
    pub operation: Operation,
    pub evidence: Evidence,
}
pub type View<'a> = WordView<&'a Expr>;
mod matcher;
mod ring;
mod source;

pub fn recognize(expression: &Expr) -> Option<View<'_>> {
    let source = source::Raw::new(expression);
    let mut work = Work::new();
    let view = matcher::recognize(&source, expression, &mut work)?;
    validate(expression, &view).then_some(view)
}
pub fn validate(expression: &Expr, view: &View<'_>) -> bool {
    matcher::validate(
        &source::Raw::new(expression),
        expression,
        view,
        &mut Work::new(),
    )
}

pub(crate) fn recognize_value(
    block: &crate::dataflow::value_graph::BlockValues,
    id: crate::dataflow::value_graph::ValueId,
    outer: &mut crate::dataflow::value_graph::Work,
) -> Option<Option<WordView<crate::dataflow::value_graph::ValueId>>> {
    let source = source::Graph(block);
    let mut work = Work::new();
    let view = matcher::recognize(&source, id, &mut work);
    outer.spend(work.used())?;
    let Some(view) = view else { return Some(None) };
    let mut work = Work::new();
    let valid = matcher::validate(&source, id, &view, &mut work);
    outer.spend(work.used())?;
    Some(valid.then_some(view))
}
pub(crate) fn same_value_word(
    block: &crate::dataflow::value_graph::BlockValues,
    a: crate::dataflow::value_graph::ValueId,
    b: crate::dataflow::value_graph::ValueId,
    width: Width,
    outer: &mut crate::dataflow::value_graph::Work,
) -> Option<bool> {
    let mut work = Work::new();
    let equal = matcher::same_word(&source::Graph(block), a, b, width, &mut work);
    outer.spend(work.used())?;
    equal
}

pub const DIVIDE_HELPER: &str = r#"
static inline uint64_t nirvana_sdiv_word(uint64_t value, int64_t divisor, unsigned bits) {
    uint64_t mask = (UINT64_C(1) << bits) - UINT64_C(1);
    uint64_t sign = (value >> (bits - 1)) & UINT64_C(1);
    uint64_t d = (uint64_t)divisor;
    uint64_t magnitude = (sign ? UINT64_C(0) - value : value) & mask;
    uint64_t denominator = divisor < 0 ? UINT64_C(0) - d : d;
    uint64_t q = denominator == UINT64_C(0) ? UINT64_MAX : magnitude / denominator;
    return ((sign ^ (d >> 63)) ? UINT64_C(0) - q : q) & mask;
}
"#;
pub const REMAINDER_HELPER: &str = r#"
static inline uint64_t nirvana_srem_word(uint64_t value, int64_t divisor, unsigned bits) {
    return (value - nirvana_sdiv_word(value, divisor, bits) * (uint64_t)divisor) & ((UINT64_C(1) << bits) - UINT64_C(1));
}
"#;
