//! Borrow a post-test loop and a returning exit tail without moving operations.
//!
//! A current-loop continue in the prefix would gain a condition evaluation in
//! do-while form, and a current-loop break would start executing the exit tail.
//! Both are rejected. Nested local transfers and early function returns retain
//! their targets. This is a presentation view, not a rewritten executable AST.

use crate::control_flow::structure::Node;
use crate::model::ir::{Expr, Place};

pub const MAX_NODES: usize = 4096;
pub const MAX_NODE_DEPTH: usize = 64;
pub const MAX_EXPRESSION_NODES: usize = 65_536;
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_WORK: usize = 100_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExitLoop<'a> {
    pub condition: &'a Expr,
    /// Nonzero continues when true; zero continues when false.
    pub continue_when: bool,
    pub body: &'a [Node],
    pub exit: &'a [Node],
}

/// Recognize the body of one Node::Loop ending in `If([Continue], tail)` or
/// its reverse, including a flattened `If([Continue], [])` followed by tail.
/// `tail` must be Step/Evaluate* followed by exactly one Return.
/// All bounds are checked over the entire input before returning any view.
pub fn recover(nodes: &[Node]) -> Option<ExitLoop<'_>> {
    let mut work = Work(MAX_WORK);
    bounded(nodes, &mut work)?;
    let (condition, continue_when, body, exit) = shape(nodes, &mut work)?;
    let (last, setup) = exit.split_last()?;
    if !matches!(last, Node::Return(_)) {
        return None;
    }
    for node in setup {
        work.spend()?;
        if !matches!(node, Node::Step { .. } | Node::Evaluate(_)) {
            return None;
        }
    }
    pure(condition, &mut work)?;
    let mut pending: Vec<_> = body.iter().map(|node| (node, 0usize)).collect();
    while let Some((node, inner_loops)) = pending.pop() {
        work.spend()?;
        match node {
            Node::Break | Node::Continue if inner_loops == 0 => return None,
            Node::BreakOuter { .. } | Node::ContinueOuter { .. } => return None,
            Node::If {
                taken, not_taken, ..
            } => {
                pending.extend(
                    taken
                        .iter()
                        .chain(not_taken)
                        .map(|node| (node, inner_loops)),
                );
            }
            Node::Loop(nodes) => pending.extend(nodes.iter().map(|node| (node, inner_loops + 1))),
            _ => {}
        }
    }
    Some(ExitLoop {
        condition,
        continue_when,
        body,
        exit,
    })
}

fn shape<'a>(
    nodes: &'a [Node],
    work: &mut Work,
) -> Option<(&'a Expr, bool, &'a [Node], &'a [Node])> {
    let (last, body) = nodes.split_last()?;
    if let Node::If {
        condition,
        taken,
        not_taken,
    } = last
    {
        if matches!(taken.as_slice(), [Node::Continue]) {
            return Some((condition, true, body, not_taken));
        }
        if matches!(not_taken.as_slice(), [Node::Continue]) {
            return Some((condition, false, body, taken));
        }
        return None;
    }
    if !matches!(last, Node::Return(_)) {
        return None;
    }
    // compact() can move the returning arm after a one-arm continue guard.
    // Borrow that suffix in place; no operation or program point is rebuilt.
    let mut index = None;
    for (candidate, node) in body.iter().enumerate().rev() {
        work.spend()?;
        if !matches!(node, Node::Step { .. } | Node::Evaluate(_)) {
            index = Some(candidate);
            break;
        }
    }
    let index = index?;
    let Node::If {
        condition,
        taken,
        not_taken,
    } = &nodes[index]
    else {
        return None;
    };
    let continue_when = if matches!(taken.as_slice(), [Node::Continue]) && not_taken.is_empty() {
        true
    } else if taken.is_empty() && matches!(not_taken.as_slice(), [Node::Continue]) {
        false
    } else {
        return None;
    };
    Some((
        condition,
        continue_when,
        &nodes[..index],
        &nodes[index + 1..],
    ))
}

struct Work(usize);
impl Work {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
}
struct Bounds {
    nodes: usize,
    expressions: usize,
}
fn expression(value: &Expr, bounds: &mut Bounds, work: &mut Work) -> Option<()> {
    let mut pending = vec![(value, 1usize)];
    while let Some((value, depth)) = pending.pop() {
        work.spend()?;
        bounds.expressions += 1;
        if bounds.expressions > MAX_EXPRESSION_NODES || depth > MAX_EXPRESSION_DEPTH {
            return None;
        }
        match value {
            Expr::Const(_) | Expr::Register(_) => {}
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
        }
    }
    Some(())
}
fn bounded(nodes: &[Node], work: &mut Work) -> Option<()> {
    if nodes.len() > MAX_NODES {
        return None;
    }
    let mut bounds = Bounds {
        nodes: 0,
        expressions: 0,
    };
    let mut pending: Vec<_> = nodes.iter().map(|node| (node, 1usize)).collect();
    while let Some((node, depth)) = pending.pop() {
        work.spend()?;
        bounds.nodes += 1;
        if bounds.nodes > MAX_NODES || depth > MAX_NODE_DEPTH {
            return None;
        }
        let mut children = None;
        match node {
            Node::Step { assignments, .. } => {
                if assignments.len() > MAX_EXPRESSION_NODES {
                    return None;
                }
                for assignment in assignments {
                    work.spend()?;
                    bounds.expressions += 1;
                    if bounds.expressions > MAX_EXPRESSION_NODES {
                        return None;
                    }
                    if let Place::Memory { address, .. } = &assignment.destination {
                        expression(address, &mut bounds, work)?;
                    }
                    expression(&assignment.value, &mut bounds, work)?;
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                expression(condition, &mut bounds, work)?;
                let count = taken.len().checked_add(not_taken.len())?;
                if bounds
                    .nodes
                    .checked_add(pending.len())?
                    .checked_add(count)?
                    > MAX_NODES
                {
                    return None;
                }
                pending.extend(taken.iter().chain(not_taken).map(|node| (node, depth + 1)));
            }
            Node::Loop(body) => children = Some(body),
            Node::Evaluate(value) | Node::Return(value) => expression(value, &mut bounds, work)?,
            _ => {}
        }
        if let Some(children) = children {
            if bounds
                .nodes
                .checked_add(pending.len())?
                .checked_add(children.len())?
                > MAX_NODES
            {
                return None;
            }
            pending.extend(children.iter().map(|node| (node, depth + 1)));
        }
    }
    Some(())
}
fn pure(value: &Expr, work: &mut Work) -> Option<()> {
    // Depth and size were validated before this second, nonrecursive walk.
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        work.spend()?;
        match value {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Load { .. } => return None,
        }
    }
    Some(())
}
