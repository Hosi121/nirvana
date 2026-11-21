//! Bounded, borrowed targets for lexical loop transfers in C presentation.
//!
//! IDs follow preorder (taken branch before not-taken branch). Identity queries
//! accept only nodes from the analyzed tree; borrowed slices keep that identity,
//! while cloned/rebuilt candidates need their own plan. No IR or AST is changed.

use std::collections::BTreeMap;
use std::fmt;

use crate::control_flow::structure::Node;
use crate::model::ir::{Expr, Place};

pub const MAX_NODES: usize = 100_000;
pub const MAX_DEPTH: usize = 256;
pub const MAX_EXPRESSION_NODES: usize = 100_000;
pub const MAX_EXPRESSION_DEPTH: usize = 256;
pub const MAX_WORK: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LoopId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TransferKind {
    Continue,
    Break,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TransferTarget {
    pub loop_id: LoopId,
    pub kind: TransferKind,
}
impl TransferTarget {
    pub fn label(self) -> String {
        self.to_string()
    }
}
impl fmt::Display for TransferTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            TransferKind::Continue => "continue",
            TransferKind::Break => "break",
        };
        write!(f, "nirvana_loop_{}_{kind}", self.loop_id.0)
    }
}

#[derive(Default)]
struct Used {
    again: bool,
    after: bool,
}

pub struct LoopLabels<'a> {
    _nodes: &'a [Node],
    loops: BTreeMap<usize, LoopId>,
    transfers: BTreeMap<usize, TransferTarget>,
    used: Vec<Used>,
}

impl<'a> LoopLabels<'a> {
    /// Validate bounds over the entire tree and all expressions first. Both
    /// local and outer transfers must have a lexical target. Outer levels are
    /// positive: one names the parent, and levels must be below loop nesting.
    /// Invalid transfers or any exhausted budget return a whole-pass None.
    pub fn analyze(nodes: &'a [Node]) -> Option<Self> {
        let mut work = Work(MAX_WORK);
        bounded(nodes, &mut work)?;
        let mut plan = Self {
            _nodes: nodes,
            loops: BTreeMap::new(),
            transfers: BTreeMap::new(),
            used: Vec::new(),
        };
        enum Visit<'a> {
            Node(&'a Node),
            LeaveLoop,
        }
        let mut pending: Vec<_> = nodes.iter().rev().map(Visit::Node).collect();
        let mut enclosing = Vec::new();
        while let Some(visit) = pending.pop() {
            work.spend()?;
            let Visit::Node(node) = visit else {
                enclosing.pop()?;
                continue;
            };
            match node {
                Node::Loop(body) => {
                    let id = LoopId(plan.used.len());
                    plan.loops.insert(key(node), id);
                    plan.used.push(Used::default());
                    enclosing.push(id);
                    pending.push(Visit::LeaveLoop);
                    pending.extend(body.iter().rev().map(Visit::Node));
                }
                Node::If {
                    taken, not_taken, ..
                } => {
                    pending.extend(not_taken.iter().rev().map(Visit::Node));
                    pending.extend(taken.iter().rev().map(Visit::Node));
                }
                Node::Break | Node::Continue if enclosing.is_empty() => return None,
                Node::BreakOuter { levels } | Node::ContinueOuter { levels } => {
                    if *levels == 0 || *levels >= enclosing.len() {
                        return None;
                    }
                    let id = enclosing[enclosing.len() - 1 - levels];
                    let kind = if matches!(node, Node::ContinueOuter { .. }) {
                        plan.used[id.0].again = true;
                        TransferKind::Continue
                    } else {
                        plan.used[id.0].after = true;
                        TransferKind::Break
                    };
                    plan.transfers
                        .insert(key(node), TransferTarget { loop_id: id, kind });
                }
                _ => {}
            }
        }
        Some(plan)
    }

    pub fn loop_count(&self) -> usize {
        self.used.len()
    }
    pub fn has_transfers(&self) -> bool {
        !self.transfers.is_empty()
    }
    pub fn loop_id(&self, node: &Node) -> Option<LoopId> {
        self.loops.get(&key(node)).copied()
    }
    /// A target for an Outer transfer; ordinary local control stays break /
    /// continue in C. A missing node must cause atomic rendering fallback.
    pub fn target(&self, node: &Node) -> Option<TransferTarget> {
        self.transfers.get(&key(node)).copied()
    }
    /// Place immediately before the target's semantic loop header, so a jump
    /// repeats header setup/test and skips any factored trailing update.
    pub fn continue_label(&self, node: &Node) -> Option<TransferTarget> {
        let id = self.loop_id(node)?;
        self.used[id.0].again.then_some(TransferTarget {
            loop_id: id,
            kind: TransferKind::Continue,
        })
    }
    /// Place immediately after the complete target loop. Emit `label: ;` so a
    /// following C declaration is portable C11, including at a block's end.
    pub fn break_label(&self, node: &Node) -> Option<TransferTarget> {
        let id = self.loop_id(node)?;
        self.used[id.0].after.then_some(TransferTarget {
            loop_id: id,
            kind: TransferKind::Break,
        })
    }
}

fn key(node: &Node) -> usize {
    node as *const Node as usize
}

struct Work(usize);
impl Work {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
}

fn bounded<'a>(nodes: &'a [Node], work: &mut Work) -> Option<()> {
    if nodes.len() > MAX_NODES {
        return None;
    }
    let mut remaining_nodes = MAX_NODES - nodes.len();
    let mut remaining_expressions = MAX_EXPRESSION_NODES;
    let mut pending: Vec<_> = nodes.iter().rev().map(|n| (n, 1usize)).collect();
    while let Some((node, depth)) = pending.pop() {
        work.spend()?;
        if depth > MAX_DEPTH {
            return None;
        }
        let mut push = |children: &'a [Node]| -> Option<()> {
            remaining_nodes = remaining_nodes.checked_sub(children.len())?;
            pending.extend(children.iter().rev().map(|n| (n, depth + 1)));
            Some(())
        };
        match node {
            Node::Loop(body) => push(body)?,
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                push(not_taken)?;
                push(taken)?;
                expression(condition, &mut remaining_expressions, work)?;
            }
            Node::Step { assignments, .. } => {
                if assignments.len() > MAX_WORK {
                    return None;
                }
                for assignment in assignments {
                    work.spend()?;
                    if let Place::Memory { address, .. } = &assignment.destination {
                        expression(address, &mut remaining_expressions, work)?;
                    }
                    expression(&assignment.value, &mut remaining_expressions, work)?;
                }
            }
            Node::Evaluate(value) | Node::Return(value) => {
                expression(value, &mut remaining_expressions, work)?
            }
            _ => {}
        }
    }
    Some(())
}

fn expression(value: &Expr, remaining: &mut usize, work: &mut Work) -> Option<()> {
    let mut pending = vec![(value, 1usize)];
    while let Some((value, depth)) = pending.pop() {
        work.spend()?;
        *remaining = remaining.checked_sub(1)?;
        if depth > MAX_EXPRESSION_DEPTH {
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
