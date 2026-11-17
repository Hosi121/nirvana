//! Factor exact common branch suffixes as a bounded C presentation pass.
//! Instruction PCs, assignment order, expression effects, and lexical loop
//! depth are preserved. The executable IR and its structure evidence are not
//! changed by this owned presentation tree.

use crate::ir::{Assignment, Expr, Place};
use crate::structure::Node;

pub const MAX_ITEMS: usize = 65_536;
pub const MAX_NODE_DEPTH: usize = 64;
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_COMPARISON_WORK: usize = 262_144;

/// Recursively factor the longest exact common suffix from each If. Even an
/// empty/pure condition stays as Evaluate when both arm prefixes disappear.
/// Whole-input validation precedes every clone and structural equality check;
/// exceeding any limit returns None without exposing a partial result.
pub fn factor(nodes: &[Node]) -> Option<Vec<Node>> {
    measure(nodes)?;
    let mut work = MAX_COMPARISON_WORK;
    transform(nodes, &mut work)
}

fn transform(nodes: &[Node], work: &mut usize) -> Option<Vec<Node>> {
    let mut output = Vec::new();
    for node in nodes {
        match node {
            Node::Loop(body) => output.push(Node::Loop(transform(body, work)?)),
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                let mut taken = transform(taken, work)?;
                let mut not_taken = transform(not_taken, work)?;
                let mut common = 0;
                while common < taken.len().min(not_taken.len()) {
                    let left = &taken[taken.len() - 1 - common];
                    let right = &not_taken[not_taken.len() - 1 - common];
                    // Derived equality visits at most this bounded left tree:
                    // differing Vec lengths or variant fields stop it earlier.
                    let cost = measure(std::slice::from_ref(left))?;
                    *work = work.checked_sub(cost)?;
                    if left != right {
                        break;
                    }
                    common += 1;
                }
                let tail = taken.split_off(taken.len() - common);
                not_taken.truncate(not_taken.len() - common);
                if taken.is_empty() && not_taken.is_empty() {
                    output.push(Node::Evaluate(condition.clone()));
                } else {
                    output.push(Node::If {
                        condition: condition.clone(),
                        taken,
                        not_taken,
                    });
                }
                output.extend(tail);
            }
            _ => output.push(node.clone()),
        }
    }
    Some(output)
}

enum Item<'a> {
    Node(&'a Node, usize),
    Assignment(&'a Assignment),
    Expression(&'a Expr, usize),
}

fn push<'a>(pending: &mut Vec<Item<'a>>, count: &mut usize, item: Item<'a>) -> Option<()> {
    *count = count.checked_add(1)?;
    if *count > MAX_ITEMS {
        return None;
    }
    pending.push(item);
    Some(())
}

// Count every Node, assignment, and Expr before recursive clone/equality or
// transformation. Enqueued items count immediately, bounding wide/deep pending
// lists even before their elements are popped. No input expression is evaluated.
fn measure(nodes: &[Node]) -> Option<usize> {
    if nodes.len() > MAX_ITEMS {
        return None;
    }
    let mut count = nodes.len();
    let mut pending: Vec<_> = nodes.iter().map(|node| Item::Node(node, 1)).collect();
    while let Some(item) = pending.pop() {
        match item {
            Item::Node(node, depth) => {
                if depth > MAX_NODE_DEPTH {
                    return None;
                }
                match node {
                    Node::Evaluate(expression) | Node::Return(expression) => {
                        push(&mut pending, &mut count, Item::Expression(expression, 1))?
                    }
                    Node::Step { assignments, .. } => {
                        for assignment in assignments {
                            push(&mut pending, &mut count, Item::Assignment(assignment))?;
                        }
                    }
                    Node::If {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        push(&mut pending, &mut count, Item::Expression(condition, 1))?;
                        for node in taken.iter().chain(not_taken) {
                            push(&mut pending, &mut count, Item::Node(node, depth + 1))?;
                        }
                    }
                    Node::Loop(body) => {
                        for node in body {
                            push(&mut pending, &mut count, Item::Node(node, depth + 1))?;
                        }
                    }
                    _ => {}
                }
            }
            Item::Assignment(assignment) => {
                push(
                    &mut pending,
                    &mut count,
                    Item::Expression(&assignment.value, 1),
                )?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    push(&mut pending, &mut count, Item::Expression(address, 1))?;
                }
            }
            Item::Expression(expression, depth) => {
                if depth > MAX_EXPRESSION_DEPTH {
                    return None;
                }
                match expression {
                    Expr::Const(_) | Expr::Register(_) => {}
                    Expr::Load { address, .. } => push(
                        &mut pending,
                        &mut count,
                        Item::Expression(address, depth + 1),
                    )?,
                    Expr::Binary(_, left, right) => {
                        push(&mut pending, &mut count, Item::Expression(left, depth + 1))?;
                        push(&mut pending, &mut count, Item::Expression(right, depth + 1))?;
                    }
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        for expression in [&**condition, &**taken, &**not_taken] {
                            push(
                                &mut pending,
                                &mut count,
                                Item::Expression(expression, depth + 1),
                            )?;
                        }
                    }
                }
            }
        }
    }
    Some(count)
}
