//! Signed reciprocal equations over source value identities, not storage names.
use super::*;
use crate::dataflow::value_graph::ValueNode;
use crate::model::ir::BinaryOp as B;
use crate::transform::signed_division_expr;

#[derive(Clone, Copy)]
struct Quotient {
    equation: Equation,
    estimate: ValueId,
    sign: ValueId,
}

pub(super) fn collect(graph: &ValueGraph, work: &mut Work) -> Option<Vec<Equation>> {
    let mut result = Vec::new();
    for block in graph.blocks() {
        let mut quotients = Vec::new();
        let mut seen = BTreeSet::new();
        for (id, node) in block.nodes() {
            work.spend(1)?;
            let ValueNode::Binary(B::Sub, a, b) = node else {
                continue;
            };
            for (estimate, sign, negative) in [(a, b, false), (b, a, true)] {
                let Some(q) = quotient(block, id, estimate, sign, negative, work)? else {
                    continue;
                };
                if seen.insert(id) {
                    quotients.push(q);
                    result.push(q.equation);
                }
            }
        }
        for (id, node) in block.nodes() {
            work.spend(1)?;
            let ValueNode::Binary(B::Sub, input, product) = node else {
                continue;
            };
            if seen.contains(&id) {
                continue;
            }
            for q in &quotients {
                work.spend(1)?;
                if input != q.equation.input {
                    continue;
                }
                let Some((a, b)) = linear(
                    block,
                    product,
                    q.estimate,
                    q.sign,
                    0,
                    &mut BTreeMap::new(),
                    work,
                )?
                else {
                    continue;
                };
                let magnitude = q.equation.divisor.unsigned_abs();
                if a != magnitude || b != 0u64.wrapping_sub(magnitude) {
                    continue;
                }
                let point = block.origin(id)?;
                if block.order(q.equation.input_point)? > block.order(point)? {
                    continue;
                }
                result.push(Equation {
                    result: id,
                    point,
                    kind: ArithmeticKind::SignedRemainder64,
                    ..q.equation
                });
                break;
            }
        }
        if result.len() > MAX_CAPTURES {
            return None;
        }
    }
    result.sort_by_key(|e| (e.block, e.result));
    Some(result)
}

fn constant(block: &BlockValues, id: ValueId) -> Option<u64> {
    if let Some(ValueNode::Constant(n)) = block.node(id) {
        Some(n)
    } else {
        None
    }
}

fn quotient(
    block: &BlockValues,
    result: ValueId,
    estimate: ValueId,
    sign: ValueId,
    negative: bool,
    work: &mut Work,
) -> Option<Option<Quotient>> {
    work.spend(1)?;
    let Some(ValueNode::Binary(B::AShr, input, count)) = block.node(sign) else {
        return Some(None);
    };
    if constant(block, count) != Some(63) {
        return Some(None);
    }
    let (product, shift) = match block.node(estimate)? {
        ValueNode::Binary(B::AShr, product, count) => match constant(block, count) {
            Some(s @ 0..=63) => (product, s as u32),
            _ => return Some(None),
        },
        _ => (estimate, 0),
    };
    let terms = match block.node(product)? {
        ValueNode::Binary(B::Add, a, b) => vec![(a, Some(b)), (b, Some(a))],
        _ => vec![(product, None)],
    };
    for (high, add) in terms {
        let Some(ValueNode::Binary(B::SMulHigh, a, b)) = block.node(high) else {
            continue;
        };
        for (value, factor) in [(a, b), (b, a)] {
            work.spend(1)?;
            let Some(m) = constant(block, factor) else {
                continue;
            };
            if value != input || (m >> 63 != 0) != add.is_some() || add.is_some_and(|a| a != input)
            {
                continue;
            }
            let Some((d, evidence)) = signed_division_expr::infer_evidence(m, shift) else {
                continue;
            };
            let point = block.origin(result)?;
            let input_point = block.origin(high)?;
            if block.order(input_point)? > block.order(point)? {
                continue;
            }
            let divisor = if negative { -d } else { d };
            return Some(Some(Quotient {
                equation: Equation {
                    block: block.start(),
                    result,
                    point,
                    input,
                    input_point,
                    kind: ArithmeticKind::SignedDivide64,
                    divisor,
                    evidence,
                },
                estimate,
                sign,
            }));
        }
    }
    Some(None)
}

/// Homogeneous coefficients of estimate and sign, in the 64-bit residue ring.
/// This handles strength-reduced q*d and negative-divisor remainder sharing.
fn linear(
    block: &BlockValues,
    id: ValueId,
    estimate: ValueId,
    sign: ValueId,
    depth: usize,
    memo: &mut BTreeMap<ValueId, Option<(u64, u64)>>,
    work: &mut Work,
) -> Option<Option<(u64, u64)>> {
    work.spend(1)?;
    if depth > value_graph::MAX_DEPTH {
        return Some(None);
    }
    if id == estimate {
        return Some(Some((1, 0)));
    }
    if id == sign {
        return Some(Some((0, 1)));
    }
    if let Some(value) = memo.get(&id) {
        return Some(*value);
    }
    let next = depth + 1;
    let result = match block.node(id)? {
        ValueNode::Constant(0) => Some((0, 0)),
        ValueNode::Binary(op @ (B::Add | B::Sub), a, b) => {
            match (
                linear(block, a, estimate, sign, next, memo, work)?,
                linear(block, b, estimate, sign, next, memo, work)?,
            ) {
                (Some((a, b)), Some((c, d))) => Some(if op == B::Add {
                    (a.wrapping_add(c), b.wrapping_add(d))
                } else {
                    (a.wrapping_sub(c), b.wrapping_sub(d))
                }),
                _ => None,
            }
        }
        ValueNode::Binary(B::Mul, a, b) => {
            let terms = match (constant(block, a), constant(block, b)) {
                (Some(n), _) => Some((b, n)),
                (_, Some(n)) => Some((a, n)),
                _ => None,
            };
            if let Some((value, n)) = terms {
                linear(block, value, estimate, sign, next, memo, work)?
                    .map(|(a, b)| (a.wrapping_mul(n), b.wrapping_mul(n)))
            } else {
                None
            }
        }
        ValueNode::Binary(B::Shl, a, b) => {
            if let Some(n) = constant(block, b) {
                linear(block, a, estimate, sign, next, memo, work)?.map(|(a, b)| {
                    (
                        a.wrapping_shl((n & 63) as u32),
                        b.wrapping_shl((n & 63) as u32),
                    )
                })
            } else {
                None
            }
        }
        ValueNode::Binary(B::And, a, b) if constant(block, a) == Some(u64::MAX) => {
            linear(block, b, estimate, sign, next, memo, work)?
        }
        ValueNode::Binary(B::And, a, b) if constant(block, b) == Some(u64::MAX) => {
            linear(block, a, estimate, sign, next, memo, work)?
        }
        ValueNode::Binary(B::Or | B::Xor, a, b) if constant(block, a) == Some(0) => {
            linear(block, b, estimate, sign, next, memo, work)?
        }
        ValueNode::Binary(B::Or | B::Xor, a, b) if constant(block, b) == Some(0) => {
            linear(block, a, estimate, sign, next, memo, work)?
        }
        _ => None,
    };
    memo.insert(id, result);
    Some(result)
}
