//! Conservative borrowed for-loop presentation, preserving every operation.
//!
//! Setup remains in the condition and runs on the final header visit. The
//! update is an unchanged trailing step slice. Local break/return can bypass it;
//! earlier continues and nonlocal transfers are rejected rather than retargeted.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{Assignment, BinaryOp, Expr, Place, Reg};
use crate::loop_shape::while_header;
use crate::structure::Node;

pub const MAX_UPDATE_ASSIGNMENTS: usize = 16;
pub const MAX_UPDATE_STEPS: usize = 16;
pub const MAX_BODY_NODES: usize = 4_096;
pub const MAX_BODY_DEPTH: usize = 64;
pub const MAX_EXPRESSION_NODES: usize = 65_536;
pub const MAX_EXPRESSION_DEPTH: usize = 128;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForLoop<'a> {
    pub setup: &'a [Node],
    pub condition: Expr,
    pub body: &'a [Node],
    pub update: &'a [Node],
}

/// Recognize a pre-test loop with an affine counter update in its minimal
/// trailing step suffix. `slot` identifies the final C storage name, so distinct
/// virtual registers may be the same counter. Copyback steps remain in order.
/// A memory store of `condition_slot +/- nonzero_constant` may also anchor the
/// suffix; this is a presentation hint, not a proof of counter-address aliasing.
pub fn recover(body: &[Node], slot: impl Fn(Reg) -> Option<usize>) -> Option<ForLoop<'_>> {
    bounded_body(body)?;
    let header = while_header(body)?;
    let end = header.body.len() - usize::from(matches!(header.body.last(), Some(Node::Continue)));
    let nodes = &header.body[..end];
    no_early_transfer(nodes)?;
    let condition_slots = registers(&header.condition)
        .into_iter()
        .filter_map(|index| slot(Reg(index)))
        .collect::<BTreeSet<_>>();
    if condition_slots.is_empty() {
        return None;
    }
    // Track which original condition slots a trailing copy will receive. This
    // recognizes tmp = counter + 1; counter = tmp without treating an unrelated
    // limit = counter + 1 as a self update.
    let mut feeds: BTreeMap<_, BTreeSet<_>> = condition_slots
        .iter()
        .map(|&s| (s, BTreeSet::from([s])))
        .collect();
    let mut assignments = 0;
    let mut start = end;
    let mut found = false;
    while start > 0 && end - start < MAX_UPDATE_STEPS {
        let Node::Step {
            assignments: step, ..
        } = &nodes[start - 1]
        else {
            break;
        };
        assignments += step.len();
        if assignments > MAX_UPDATE_ASSIGNMENTS || !movable(step) {
            return None;
        }
        start -= 1;
        for assignment in step.iter().rev() {
            let source = affine_source(&assignment.value).and_then(&slot);
            match assignment.destination {
                Place::Memory { .. } => {
                    if source.is_some_and(|s| condition_slots.contains(&s)) {
                        found = true;
                    }
                }
                Place::Register(destination) => {
                    if let Some(destination) = slot(destination) {
                        let targets = feeds.remove(&destination).unwrap_or_default();
                        if source.is_some_and(|s| targets.contains(&s)) {
                            found = true;
                        }
                        if let Expr::Register(source) = assignment.value
                            && let Some(source) = slot(source)
                        {
                            feeds.entry(source).or_default().extend(targets);
                        }
                    }
                }
            }
        }
        if found {
            break;
        }
    }
    if !found {
        return None;
    }

    // Include only adjacent register definitions needed by the chosen suffix,
    // such as the reload immediately before a memory-counter increment. Stop at
    // the first unrelated step/control node instead of swallowing the body.
    let mut needed = BTreeSet::new();
    for node in nodes[start..].iter().rev() {
        let Node::Step { assignments, .. } = node else {
            return None;
        };
        dependencies(assignments, &slot, &mut needed);
    }
    while start > 0 && end - start < MAX_UPDATE_STEPS {
        let Node::Step {
            assignments: step, ..
        } = &nodes[start - 1]
        else {
            break;
        };
        let defines_needed = step.iter().any(|assignment| {
            matches!(assignment.destination, Place::Register(reg) if needed.contains(&key(reg, &slot)))
        });
        if !defines_needed {
            break;
        }
        // These adjacent definitions can safely remain in the body if moving
        // them would exceed the clause budget or require statement sequencing.
        if assignments + step.len() > MAX_UPDATE_ASSIGNMENTS || !movable(step) {
            break;
        }
        assignments += step.len();
        start -= 1;
        dependencies(step, &slot, &mut needed);
    }
    Some(ForLoop {
        setup: header.setup,
        condition: header.condition,
        body: &nodes[..start],
        update: &nodes[start..],
    })
}

fn affine_source(expression: &Expr) -> Option<Reg> {
    match expression {
        Expr::Binary(BinaryOp::Add | BinaryOp::Sub, left, right) => match (&**left, &**right) {
            (Expr::Register(source), Expr::Const(value)) if *value != 0 => Some(*source),
            (Expr::Const(value), Expr::Register(source))
                if *value != 0 && matches!(expression, Expr::Binary(BinaryOp::Add, ..)) =>
            {
                Some(*source)
            }
            _ => None,
        },
        _ => None,
    }
}

fn movable(assignments: &[Assignment]) -> bool {
    assignments
        .iter()
        .all(|assignment| match &assignment.destination {
            Place::Register(_) => loads(&assignment.value) <= 1,
            Place::Memory { address, .. } => loads(address) == 0 && loads(&assignment.value) == 0,
        })
}

fn loads(expression: &Expr) -> usize {
    let mut pending = vec![expression];
    let mut count = 0;
    while let Some(expression) = pending.pop() {
        if matches!(expression, Expr::Load { .. }) {
            count += 1;
            if count > 1 {
                break;
            }
        }
        children(expression, &mut pending);
    }
    count
}

fn registers(expression: &Expr) -> BTreeSet<usize> {
    let mut pending = vec![expression];
    let mut registers = BTreeSet::new();
    while let Some(expression) = pending.pop() {
        if let Expr::Register(reg) = expression {
            registers.insert(reg.0);
        }
        children(expression, &mut pending);
    }
    registers
}

fn children<'a>(expression: &'a Expr, pending: &mut Vec<&'a Expr>) {
    match expression {
        Expr::Binary(_, left, right) => pending.extend([&**right, &**left]),
        Expr::Load { address, .. } => pending.push(address),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => pending.extend([&**not_taken, &**taken, &**condition]),
        _ => {}
    }
}

// A slot key models coalesced aliases; unnamed registers retain individual keys
// for dependency discovery without becoming counter-anchor candidates.
fn key(reg: Reg, slot: &impl Fn(Reg) -> Option<usize>) -> (bool, usize) {
    slot(reg).map(|s| (true, s)).unwrap_or((false, reg.0))
}

fn dependencies(
    assignments: &[Assignment],
    slot: &impl Fn(Reg) -> Option<usize>,
    needed: &mut BTreeSet<(bool, usize)>,
) {
    for assignment in assignments.iter().rev() {
        match &assignment.destination {
            Place::Register(reg) => {
                needed.remove(&key(*reg, slot));
            }
            Place::Memory { address, .. } => {
                needed.extend(registers(address).into_iter().map(|r| key(Reg(r), slot)));
            }
        }
        needed.extend(
            registers(&assignment.value)
                .into_iter()
                .map(|r| key(Reg(r), slot)),
        );
    }
}

fn no_early_transfer(nodes: &[Node]) -> Option<()> {
    let mut pending: Vec<_> = nodes.iter().collect();
    while let Some(node) = pending.pop() {
        match node {
            Node::Continue
            | Node::ContinueOuter { .. }
            | Node::BreakOuter { .. }
            | Node::Loop(_) => return None,
            Node::If {
                taken, not_taken, ..
            } => pending.extend(taken.iter().chain(not_taken)),
            _ => {}
        }
    }
    Some(())
}

fn bounded_body(nodes: &[Node]) -> Option<()> {
    if nodes.len() > MAX_BODY_NODES {
        return None;
    }
    let mut pending: Vec<_> = nodes.iter().map(|n| (n, 1)).collect();
    let mut node_count = 0;
    let mut expression_count = 0;
    while let Some((node, depth)) = pending.pop() {
        node_count += 1;
        if node_count > MAX_BODY_NODES || depth > MAX_BODY_DEPTH {
            return None;
        }
        let mut expressions = Vec::new();
        match node {
            Node::Evaluate(expression) | Node::Return(expression) => expressions.push(expression),
            Node::Step { assignments, .. } => {
                if assignments.len() > MAX_EXPRESSION_NODES {
                    return None;
                }
                for assignment in assignments {
                    expressions.push(&assignment.value);
                    if let Place::Memory { address, .. } = &assignment.destination {
                        expressions.push(address);
                    }
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                if taken.len().checked_add(not_taken.len())? > MAX_BODY_NODES {
                    return None;
                }
                expressions.push(condition);
                pending.extend(taken.iter().chain(not_taken).map(|n| (n, depth + 1)));
            }
            Node::Loop(body) => {
                if body.len() > MAX_BODY_NODES {
                    return None;
                }
                pending.extend(body.iter().map(|n| (n, depth + 1)));
            }
            _ => {}
        }
        let mut expressions: Vec<_> = expressions.into_iter().map(|e| (e, 1)).collect();
        while let Some((expression, depth)) = expressions.pop() {
            expression_count += 1;
            if expression_count > MAX_EXPRESSION_NODES || depth > MAX_EXPRESSION_DEPTH {
                return None;
            }
            let mut next = Vec::new();
            children(expression, &mut next);
            expressions.extend(next.into_iter().map(|e| (e, depth + 1)));
        }
    }
    Some(())
}
