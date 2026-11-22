//! Word equations over immutable values. A live representative may differ in
//! upper bits: the canonical operation observes only the declared low word.
use super::*;
use crate::model::ir::{BinaryOp as B, UnaryOp};
use crate::transform::word_signed_division::{self as word, Operation};

pub(super) fn has_kernel(source: &Program) -> bool {
    source.uses_operator(B::Mul)
        && [Width::U8, Width::U16, Width::U32]
            .into_iter()
            .any(|w| source.uses_unary_operator(UnaryOp::SignExtend(w)))
}
pub(super) fn collect(
    source: &Program,
    graph: &ValueGraph,
    work: &mut Work,
) -> Option<Vec<Equation>> {
    let mut result = Vec::new();
    if !has_kernel(source) {
        return Some(result);
    }
    for block in graph.blocks() {
        for (id, node) in block.nodes() {
            work.spend(1)?;
            use crate::dataflow::value_graph::ValueNode;
            let (root, extended) = match node {
                ValueNode::Binary(B::And, ..)
                | ValueNode::Unary(UnaryOp::Extract { start: 0, .. }, _) => (id, None),
                ValueNode::Unary(UnaryOp::SignExtend(w), inner) if w != Width::U64 => {
                    (inner, Some(w))
                }
                _ => continue,
            };
            let Some(view) = word::recognize_value(block, root, work)? else {
                continue;
            };
            if extended.is_some_and(|w| w != view.width) {
                continue;
            }
            let point = block.origin(id)?;
            let input_point = block.origin(view.product)?;
            if block.order(input_point)? > block.order(point)? {
                continue;
            }
            // Prefer an actual live word representative. This admits a truncated
            // EAX value after the original full RAX value has been overwritten.
            let mut input = view.value;
            for index in 0..source.register_count() {
                work.spend(1)?;
                let available = block.value_before(Reg(index), input_point)?;
                if word::same_value_word(block, available, view.value, view.width, work)? {
                    input = available;
                    break;
                }
            }
            let evidence = view.evidence;
            result.push(Equation {
                block: block.start(),
                result: id,
                point,
                input,
                input_point,
                kind: match (view.operation, extended.is_some()) {
                    (Operation::Quotient, false) => ArithmeticKind::SignedDivide(view.width),
                    (Operation::Remainder, false) => ArithmeticKind::SignedRemainder(view.width),
                    (Operation::Quotient, true) => ArithmeticKind::SignedDivideExtended(view.width),
                    (Operation::Remainder, true) => {
                        ArithmeticKind::SignedRemainderExtended(view.width)
                    }
                },
                divisor: view.divisor,
                evidence: SignedDivisionEvidence {
                    multiplier: evidence.multiplier,
                    shift: evidence.shift,
                    excess: evidence.excess,
                    positive_bound: evidence.positive_bound,
                    negative_bound: evidence.negative_bound,
                },
            });
            if result.len() > MAX_CAPTURES {
                return None;
            }
        }
    }
    result.sort_by_key(|e| (e.block, e.result));
    Some(result)
}
