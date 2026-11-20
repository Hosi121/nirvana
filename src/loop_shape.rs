//! Borrow conservative loop headers without rewriting the structured tree.
//!
//! Setup assignments must still execute on every header visit, including the
//! final visit and visits reached by `continue`. A C renderer can emit them at
//! the top of an unconditional loop, followed by an explicit exit guard.

use crate::ir::{BinaryOp, Expr, Place};
use crate::structure::Node;

pub const MAX_SETUP_ASSIGNMENTS: usize = 16;
pub const MAX_HEADER_EXPRESSION_DEPTH: usize = 128;
pub const MAX_HEADER_EXPRESSION_NODES: usize = 65_536;
pub const MAX_POST_TEST_NODES: usize = 4096;
pub const MAX_POST_TEST_NODE_DEPTH: usize = 64;
pub const MAX_POST_TEST_WORK: usize = 100_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhileHeader<'a> {
    /// Original steps, including their addresses and assignment positions.
    pub setup: &'a [Node],
    /// Nonzero means execute the body; zero means leave the loop.
    pub condition: Expr,
    pub body: &'a [Node],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PostTest<'a> {
    pub condition: &'a Expr,
    /// Nonzero continues when true; zero continues when false.
    pub continue_when: bool,
    /// Original prefix, including every step's address and assignment index.
    pub body: &'a [Node],
}

/// Borrow a post-test loop ending in an exact Continue/Break or empty/Break
/// conditional, in either direction. Both-backedge shapes are not recognized:
/// the condition must remain evaluated even when neither branch exits.
///
/// A prefix continue targeting this loop would gain a condition evaluation in
/// do-while form and is rejected. Current-loop breaks and function returns skip
/// the condition in both forms; nested local transfers retain their targets.
/// All nonlocal transfers and syntactic loads in the condition are rejected.
pub fn post_test(nodes: &[Node]) -> Option<PostTest<'_>> {
    let mut work = PostTestWork(MAX_POST_TEST_WORK);
    post_test_bounds(nodes, &mut work)?;
    // An explicit terminal backedge follows the latch test in some structured
    // CFGs. Unlike an earlier continue, it never bypasses that test.
    work.spend()?;
    let nodes = if matches!(nodes.last(), Some(Node::Continue)) {
        &nodes[..nodes.len() - 1]
    } else {
        nodes
    };
    let (last, body) = nodes.split_last()?;
    let Node::If {
        condition,
        taken,
        not_taken,
    } = last
    else {
        return None;
    };
    let continue_when = match (taken.as_slice(), not_taken.as_slice()) {
        ([], [Node::Break]) | ([Node::Continue], [Node::Break]) => true,
        ([Node::Break], []) | ([Node::Break], [Node::Continue]) => false,
        _ => return None,
    };
    let mut expressions = vec![condition];
    while let Some(expression) = expressions.pop() {
        work.spend()?;
        match expression {
            Expr::Load { .. } => return None,
            Expr::Binary(_, a, b) => expressions.extend([&**a, &**b]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => expressions.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    // The whole tree and all expression depths were bounded above. This pass
    // tracks lexical targets only; it propagates no first-iteration facts.
    let mut pending: Vec<_> = body.iter().map(|node| (node, 0usize)).collect();
    while let Some((node, inner_loops)) = pending.pop() {
        work.spend()?;
        match node {
            Node::Continue if inner_loops == 0 => return None,
            Node::BreakOuter { .. } | Node::ContinueOuter { .. } => return None,
            Node::If {
                taken, not_taken, ..
            } => pending.extend(
                taken
                    .iter()
                    .chain(not_taken)
                    .map(|node| (node, inner_loops)),
            ),
            Node::Loop(body) => pending.extend(body.iter().map(|node| (node, inner_loops + 1))),
            _ => {}
        }
    }
    Some(PostTest {
        condition,
        continue_when,
        body,
    })
}

struct PostTestWork(usize);
impl PostTestWork {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
}

fn post_test_bounds(nodes: &[Node], work: &mut PostTestWork) -> Option<()> {
    if nodes.len() > MAX_POST_TEST_NODES {
        return None;
    }
    let mut count = 0usize;
    let mut expressions = 0usize;
    let mut pending: Vec<_> = nodes.iter().map(|node| (node, 1usize)).collect();
    while let Some((node, depth)) = pending.pop() {
        work.spend()?;
        count += 1;
        if count > MAX_POST_TEST_NODES || depth > MAX_POST_TEST_NODE_DEPTH {
            return None;
        }
        match node {
            Node::Step { assignments, .. } => {
                if assignments.len() > MAX_HEADER_EXPRESSION_NODES {
                    return None;
                }
                for assignment in assignments {
                    work.spend()?;
                    expressions += 1;
                    if expressions > MAX_HEADER_EXPRESSION_NODES {
                        return None;
                    }
                    if let Place::Memory { address, .. } = &assignment.destination {
                        post_test_expression_bounds(address, &mut expressions, work)?;
                    }
                    post_test_expression_bounds(&assignment.value, &mut expressions, work)?;
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                post_test_expression_bounds(condition, &mut expressions, work)?;
                let children = taken.len().checked_add(not_taken.len())?;
                if count.checked_add(pending.len())?.checked_add(children)? > MAX_POST_TEST_NODES {
                    return None;
                }
                pending.extend(taken.iter().chain(not_taken).map(|node| (node, depth + 1)));
            }
            Node::Loop(body) => {
                if count.checked_add(pending.len())?.checked_add(body.len())? > MAX_POST_TEST_NODES
                {
                    return None;
                }
                pending.extend(body.iter().map(|node| (node, depth + 1)));
            }
            Node::Evaluate(value) | Node::Return(value) => {
                post_test_expression_bounds(value, &mut expressions, work)?;
            }
            _ => {}
        }
    }
    Some(())
}

fn post_test_expression_bounds(
    value: &Expr,
    count: &mut usize,
    work: &mut PostTestWork,
) -> Option<()> {
    let mut pending = vec![(value, 1usize)];
    while let Some((value, depth)) = pending.pop() {
        work.spend()?;
        *count += 1;
        if *count > MAX_HEADER_EXPRESSION_NODES || depth > MAX_HEADER_EXPRESSION_DEPTH {
            return None;
        }
        match value {
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**condition, depth + 1),
                (&**taken, depth + 1),
                (&**not_taken, depth + 1),
            ]),
            _ => {}
        }
    }
    Some(())
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
