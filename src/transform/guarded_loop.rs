//! Fold a pure entry guard around a post-test loop using bounded initial facts.
//! Facts prove only the first test. The returned condition retains the original
//! registers and expression so subsequent iterations use their current values.
//! A final register-only step may prove a copied alias for a latch temporary;
//! that unchanged copy stays in the body and its source remains used.

use std::collections::{BTreeMap, BTreeSet};

use crate::control_flow::structure::Node;
use crate::model::ir::{BinaryOp, Expr, Place, Reg};

pub const MAX_SLOTS: usize = 4_096;
pub const MAX_NODES: usize = 4_096;
pub const MAX_EXPRESSIONS: usize = 65_536;
pub const MAX_DEPTH: usize = 64;
pub const MAX_FACT_WORK: usize = 1_000_000;

#[derive(Clone, Debug)]
pub struct Facts {
    initialized: BTreeSet<usize>,
    constants: BTreeMap<usize, u64>,
    remaining: usize,
    valid: bool,
}

impl Facts {
    pub fn new(initialized: &[usize]) -> Self {
        let valid = initialized.len() <= MAX_SLOTS;
        Self {
            initialized: if valid {
                initialized.iter().copied().collect()
            } else {
                BTreeSet::new()
            },
            constants: BTreeMap::new(),
            remaining: MAX_FACT_WORK,
            valid,
        }
    }

    /// Observe execution reaching the end of a node. A conditional or loop does
    /// not establish any new initialized slots. All of its possible register
    /// writes invalidate constants, including writes through coalesced aliases.
    pub fn observe(&mut self, node: &Node, slot: impl Fn(Reg) -> Option<usize>) {
        if !self.valid {
            return;
        }
        let Some(summary) = inspect(std::slice::from_ref(node), &slot) else {
            self.invalidate();
            return;
        };
        if !self.spend(summary.work) {
            return;
        }
        if let Node::Step { assignments, .. } = node {
            for assignment in assignments {
                let Place::Register(reg) = assignment.destination else {
                    continue;
                };
                let Some(destination) = slot(reg) else {
                    continue;
                };
                // Evaluate against the pre-assignment constants, including the
                // previous destination value in an affine self update.
                let constant = raw_slots(&assignment.value, &slot)
                    .filter(|reads| reads.is_subset(&self.initialized))
                    .and_then(|_| substitute(&assignment.value, self, &slot))
                    .and_then(|expression| {
                        match crate::transform::simplify::simplify(&expression) {
                            Expr::Const(value) => Some(value),
                            _ => None,
                        }
                    });
                self.constants.remove(&destination);
                // Reaching the next node establishes initialization even when
                // the assigned value is unknown or came from a checked load.
                self.initialized.insert(destination);
                if let Some(value) = constant {
                    self.constants.insert(destination, value);
                }
                if self.initialized.len() > MAX_SLOTS {
                    self.invalidate();
                    return;
                }
            }
        } else {
            self.kill(&summary.writes);
        }
    }

    /// Facts valid at every visit inside a loop, before visiting its first node.
    /// Never propagate an entry-only constant across a loop-carried assignment.
    pub fn enter_loop(&self, body: &[Node], slot: impl Fn(Reg) -> Option<usize>) -> Self {
        let mut result = self.clone();
        if !result.valid {
            return result;
        }
        let Some(summary) = inspect(body, &slot) else {
            result.invalidate();
            return result;
        };
        if result.spend(summary.work) {
            result.kill(&summary.writes);
        }
        result
    }

    fn kill(&mut self, writes: &BTreeSet<usize>) {
        for slot in writes {
            self.constants.remove(slot);
        }
    }
    fn invalidate(&mut self) {
        self.valid = false;
        self.initialized.clear();
        self.constants.clear();
    }
    fn spend(&mut self, work: usize) -> bool {
        if let Some(remaining) = self.remaining.checked_sub(work) {
            self.remaining = remaining;
            true
        } else {
            self.invalidate();
            false
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardedLoop<'a> {
    pub body: &'a [Node],
    pub condition: Expr,
}

pub fn recover<'a>(
    condition: &Expr,
    taken: &'a [Node],
    not_taken: &[Node],
    facts: &Facts,
    slot: impl Fn(Reg) -> Option<usize>,
) -> Option<GuardedLoop<'a>> {
    if !facts.valid || !not_taken.is_empty() {
        return None;
    }
    let [Node::Loop(nodes)] = taken else {
        return None;
    };
    let summary = inspect(taken, &slot)?;
    let entry_work = expression_size(condition)?;
    if summary.work.checked_add(entry_work)? > facts.remaining {
        return None;
    }
    let (latch, prefix) = nodes.split_last()?;
    let Node::If {
        condition: latch,
        taken,
        not_taken,
    } = latch
    else {
        return None;
    };
    let reversed = if matches!(taken.as_slice(), [Node::Continue])
        && matches!(not_taken.as_slice(), [Node::Break])
    {
        false
    } else if matches!(taken.as_slice(), [Node::Break])
        && matches!(not_taken.as_slice(), [Node::Continue])
    {
        true
    } else {
        return None;
    };
    let mut pending: Vec<_> = prefix.iter().collect();
    while let Some(node) = pending.pop() {
        match node {
            Node::Loop(_)
            | Node::Continue
            | Node::ContinueOuter { .. }
            | Node::BreakOuter { .. } => return None,
            Node::If {
                taken, not_taken, ..
            } => pending.extend(taken.iter().chain(not_taken)),
            _ => {}
        }
    }
    let entry_slots = raw_slots(condition, &slot)?;
    let latch = initialized_latch(latch, condition, prefix, facts, &slot)?;
    let latch_slots = raw_slots(&latch, &slot)?;
    if !latch_slots.is_subset(&facts.initialized) || !entry_slots.is_subset(&latch_slots) {
        return None;
    }
    let continuing = if reversed {
        Expr::binary(BinaryOp::Eq, latch, Expr::Const(0))
    } else {
        latch
    };
    let entry = truth(condition, facts, &slot)?;
    let initial_latch = truth(&continuing, facts, &slot)?;
    (entry == initial_latch).then_some(GuardedLoop {
        body: prefix,
        condition: continuing,
    })
}

fn truth(expression: &Expr, facts: &Facts, slot: &impl Fn(Reg) -> Option<usize>) -> Option<Expr> {
    let expression = substitute(expression, facts, slot)?;
    let expression = crate::transform::simplify::simplify(&Expr::binary(
        BinaryOp::Ne,
        expression,
        Expr::Const(0),
    ));
    Some(canonical(expression))
}

// Only pure expressions can participate in a proof. Canonical registers denote
// C slots, while the returned loop condition keeps the original raw registers.
fn substitute(
    expression: &Expr,
    facts: &Facts,
    slot: &impl Fn(Reg) -> Option<usize>,
) -> Option<Expr> {
    Some(match expression {
        Expr::Const(value) => Expr::Const(*value),
        Expr::Unary(op, value) => canonical(Expr::unary(*op, substitute(value, facts, slot)?)),
        Expr::Register(reg) => {
            let slot = slot(*reg)?;
            facts
                .constants
                .get(&slot)
                .copied()
                .map(Expr::Const)
                .unwrap_or(Expr::Register(Reg(slot)))
        }
        Expr::Load { .. } => return None,
        Expr::Binary(op, left, right) => canonical(Expr::binary(
            *op,
            substitute(left, facts, slot)?,
            substitute(right, facts, slot)?,
        )),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            substitute(condition, facts, slot)?,
            substitute(taken, facts, slot)?,
            substitute(not_taken, facts, slot)?,
        ),
    })
}

fn initialized_latch(
    latch: &Expr,
    entry: &Expr,
    prefix: &[Node],
    facts: &Facts,
    slot: &impl Fn(Reg) -> Option<usize>,
) -> Option<Expr> {
    let reads = raw_slots(latch, slot)?;
    if reads.is_subset(&facts.initialized) {
        return Some(latch.clone());
    }
    let mut entry_registers = BTreeMap::new();
    let mut pending = vec![entry];
    while let Some(expression) = pending.pop() {
        if let Expr::Register(reg) = expression {
            let s = slot(*reg)?;
            if facts.initialized.contains(&s) {
                entry_registers.entry(s).or_insert(*reg);
            }
        }
        children(expression, &mut pending);
    }
    let copies = prefix.iter().rev().find_map(|node| match node {
        Node::Step { assignments, .. } if assignments.is_empty() => None,
        node => Some(node),
    })?;
    let Node::Step { assignments, .. } = copies else {
        return None;
    };
    if assignments.len() > 16 {
        return None;
    }
    // Initial tokens denote values at entry to this final step. Other writes
    // receive fresh tokens; later scalar/copy writes correctly break equality.
    let mut values = BTreeMap::new();
    let mut sources = BTreeSet::new();
    for (index, assignment) in assignments.iter().enumerate() {
        let Place::Register(destination) = &assignment.destination else {
            return None;
        };
        let Some(destination) = slot(*destination) else {
            continue;
        };
        let value = if let Expr::Register(source) = &assignment.value
            && let Some(source) = slot(*source)
        {
            sources.insert(source);
            values.get(&source).copied().unwrap_or((false, source))
        } else {
            (true, index)
        };
        values.insert(destination, value);
    }
    let mut replacements = BTreeMap::new();
    for read in reads.difference(&facts.initialized) {
        // Keeping this RHS read keeps the original temporary used after
        // removing its occurrence in the latch.
        if !sources.contains(read) {
            return None;
        }
        let value = values.get(read).copied().unwrap_or((false, *read));
        let replacement = entry_registers.iter().find_map(|(&s, &reg)| {
            (values.get(&s).copied().unwrap_or((false, s)) == value).then_some(reg)
        })?;
        replacements.insert(*read, replacement);
    }
    fn replace(
        expression: &Expr,
        replacements: &BTreeMap<usize, Reg>,
        slot: &impl Fn(Reg) -> Option<usize>,
    ) -> Option<Expr> {
        Some(match expression {
            Expr::Unary(op, value) => Expr::unary(*op, replace(value, replacements, slot)?),
            Expr::Register(reg) => {
                Expr::Register(replacements.get(&slot(*reg)?).copied().unwrap_or(*reg))
            }
            Expr::Const(value) => Expr::Const(*value),
            Expr::Load { .. } => return None,
            Expr::Binary(op, left, right) => Expr::binary(
                *op,
                replace(left, replacements, slot)?,
                replace(right, replacements, slot)?,
            ),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Expr::select(
                replace(condition, replacements, slot)?,
                replace(taken, replacements, slot)?,
                replace(not_taken, replacements, slot)?,
            ),
        })
    }
    replace(latch, &replacements, slot)
}

fn canonical(mut expression: Expr) -> Expr {
    if let Expr::Binary(BinaryOp::Eq | BinaryOp::Ne, left, right) = &mut expression
        && ((matches!(**left, Expr::Const(_)) && !matches!(**right, Expr::Const(_)))
            || matches!((&**left, &**right), (Expr::Register(a), Expr::Register(b)) if a.0 > b.0))
    {
        std::mem::swap(left, right);
    }
    expression
}

fn raw_slots(expression: &Expr, slot: &impl Fn(Reg) -> Option<usize>) -> Option<BTreeSet<usize>> {
    let mut pending = vec![expression];
    let mut slots = BTreeSet::new();
    while let Some(expression) = pending.pop() {
        if let Expr::Register(reg) = expression {
            slots.insert(slot(*reg)?);
        }
        children(expression, &mut pending);
    }
    Some(slots)
}

fn children<'a>(expression: &'a Expr, pending: &mut Vec<&'a Expr>) {
    match expression {
        Expr::Unary(_, value) => pending.push(value),
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

fn expression_size(expression: &Expr) -> Option<usize> {
    let mut pending = vec![(expression, 1)];
    let mut count = 0;
    while let Some((expression, depth)) = pending.pop() {
        count += 1;
        if count > MAX_EXPRESSIONS || depth > MAX_DEPTH {
            return None;
        }
        let mut next = Vec::new();
        children(expression, &mut next);
        pending.extend(next.into_iter().map(|e| (e, depth + 1)));
    }
    Some(count)
}

struct Summary {
    writes: BTreeSet<usize>,
    work: usize,
}
fn inspect(nodes: &[Node], slot: &impl Fn(Reg) -> Option<usize>) -> Option<Summary> {
    if nodes.len() > MAX_NODES {
        return None;
    }
    let mut pending: Vec<_> = nodes.iter().map(|n| (n, 1)).collect();
    let mut summary = Summary {
        writes: BTreeSet::new(),
        work: 0,
    };
    let mut node_count = 0;
    while let Some((node, depth)) = pending.pop() {
        node_count += 1;
        if node_count > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        summary.work += 1;
        let mut expressions = Vec::new();
        match node {
            Node::Step { assignments, .. } => {
                if assignments.len() > MAX_EXPRESSIONS {
                    return None;
                }
                for assignment in assignments {
                    expressions.push(&assignment.value);
                    match &assignment.destination {
                        Place::Register(reg) => {
                            if let Some(s) = slot(*reg) {
                                summary.writes.insert(s);
                            }
                        }
                        Place::Memory { address, .. } => expressions.push(address),
                    }
                }
            }
            Node::Evaluate(expression) | Node::Return(expression) => expressions.push(expression),
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                if taken.len().checked_add(not_taken.len())? > MAX_NODES {
                    return None;
                }
                expressions.push(condition);
                pending.extend(taken.iter().chain(not_taken).map(|n| (n, depth + 1)));
            }
            Node::Loop(body) => {
                if body.len() > MAX_NODES {
                    return None;
                }
                pending.extend(body.iter().map(|n| (n, depth + 1)));
            }
            _ => {}
        }
        for expression in expressions {
            summary.work = summary.work.checked_add(expression_size(expression)?)?;
            if summary.work > MAX_EXPRESSIONS {
                return None;
            }
        }
        if summary.writes.len() > MAX_SLOTS {
            return None;
        }
    }
    Some(summary)
}
