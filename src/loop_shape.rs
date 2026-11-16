//! Borrow a conservative while header without rewriting the structured tree.
//!
//! Setup assignments must still execute on every header visit, including the
//! final visit and visits reached by `continue`. A C renderer can join them with
//! comma operators before the condition, preserving their original order.

use crate::ir::{BinaryOp, Expr, Place};
use crate::structure::Node;

pub const MAX_SETUP_ASSIGNMENTS: usize = 16;
pub const MAX_HEADER_EXPRESSION_DEPTH: usize = 128;
pub const MAX_HEADER_EXPRESSION_NODES: usize = 65_536;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhileHeader<'a> {
    /// Original steps, including their addresses and assignment positions.
    pub setup: &'a [Node],
    /// Nonzero means execute the body; zero means leave the loop.
    pub condition: Expr,
    pub body: &'a [Node],
}

/// Recognize only leading register-only steps followed immediately by an if
/// whose sole effect is to break on one arm. No nested control flow is scanned.
///
/// Every setup RHS and the guard may contain at most one syntactic load. This
/// excludes nested address loads and multiple possibly unordered reads, while
/// retaining single reads in lazy select arms. Returning this borrowed view
/// does not erase or move steps in the structured AST.
pub fn while_header(body: &[Node]) -> Option<WhileHeader<'_>> {
    let mut prefix = 0;
    let mut assignment_count = 0;
    for node in body {
        let Node::Step { assignments, .. } = node else {
            break;
        };
        for assignment in assignments {
            assignment_count += 1;
            if assignment_count > MAX_SETUP_ASSIGNMENTS
                || !matches!(assignment.destination, Place::Register(_))
                || !header_expression(&assignment.value)
            {
                return None;
            }
        }
        prefix += 1;
    }
    let Node::If {
        condition,
        taken,
        not_taken,
    } = body.get(prefix)?
    else {
        return None;
    };
    let break_when_taken = if matches!(taken.as_slice(), [Node::Break]) && not_taken.is_empty() {
        true
    } else if taken.is_empty() && matches!(not_taken.as_slice(), [Node::Break]) {
        false
    } else {
        return None;
    };
    if !header_expression(condition) {
        return None;
    }
    let condition = if break_when_taken {
        // Equality with zero inverts truth for every u64, not just booleans.
        // Keep the entire operand, including any faulting or lazy memory read.
        Expr::binary(BinaryOp::Eq, condition.clone(), Expr::Const(0))
    } else {
        condition.clone()
    };
    Some(WhileHeader {
        setup: &body[..prefix],
        condition,
        body: &body[prefix + 1..],
    })
}

// Validate iteratively before cloning the guard so deeply nested frontend
// expressions can fall back to a general loop without overflowing the stack.
fn header_expression(expression: &Expr) -> bool {
    let mut pending = vec![(expression, 1)];
    let mut nodes = 0;
    let mut loads = 0;
    while let Some((expression, depth)) = pending.pop() {
        nodes += 1;
        if depth > MAX_HEADER_EXPRESSION_DEPTH || nodes > MAX_HEADER_EXPRESSION_NODES {
            return false;
        }
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, left, right) => {
                pending.push((right, depth + 1));
                pending.push((left, depth + 1));
            }
            Expr::Load { address, .. } => {
                loads += 1;
                if loads > 1 {
                    return false;
                }
                pending.push((address, depth + 1));
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push((not_taken, depth + 1));
                pending.push((taken, depth + 1));
                pending.push((condition, depth + 1));
            }
        }
    }
    true
}
