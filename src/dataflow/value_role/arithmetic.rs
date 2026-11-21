//! Optional naming evidence for final C slots, after grouping has finished.
use std::collections::{BTreeMap, BTreeSet};

use super::{MAX_SLOTS, spend};
use crate::control_flow::structure::Node;
use crate::model::ir::{BinaryOp as B, Expr, Place, Reg};

// The caller already validated the complete AST and every expression. This
// separate work/map budget can fail without losing any canonical old role.
const MAX_WORK: usize = 65_536;

#[derive(Default)]
struct State {
    read: bool,
    written: bool,
    first_valid: bool,
    clean: bool,
    division: bool,
}
struct Scan<'a, F> {
    slot: &'a F,
    states: BTreeMap<usize, State>,
    work: usize,
}
impl<F: Fn(Reg) -> Option<usize>> Scan<'_, F> {
    fn slot(&mut self, reg: Reg) -> Option<Option<usize>> {
        spend(&mut self.work, 1)?;
        Some((self.slot)(reg))
    }
    fn state(&mut self, slot: usize) -> Option<&mut State> {
        spend(&mut self.work, 1)?;
        if !self.states.contains_key(&slot) && self.states.len() >= MAX_SLOTS {
            return None;
        }
        Some(self.states.entry(slot).or_default())
    }
    fn reads(&mut self, expression: &Expr) -> Option<usize> {
        let mut pending = vec![expression];
        let mut nodes = 0usize;
        while let Some(expression) = pending.pop() {
            spend(&mut self.work, 1)?;
            nodes += 1;
            match expression {
                Expr::Register(reg) => {
                    if let Some(slot) = self.slot(*reg)? {
                        self.state(slot)?.read = true;
                    }
                }
                Expr::Const(_) => {}
                Expr::Unary(_, value) => pending.push(value),
                Expr::Binary(_, a, b) => pending.extend([&**b, &**a]),
                Expr::Load { address, .. } => pending.push(address),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**not_taken, &**taken, &**condition]),
            }
        }
        Some(nodes)
    }
}

pub(super) fn quotients(
    nodes: &[Node],
    slot: &impl Fn(Reg) -> Option<usize>,
    blocked: &BTreeSet<usize>,
) -> Option<BTreeSet<usize>> {
    let mut scan = Scan {
        slot,
        states: BTreeMap::new(),
        work: MAX_WORK,
    };
    let prefix = nodes
        .iter()
        .take_while(|node| matches!(node, Node::Step { .. }))
        .count();
    let mut pending: Vec<_> = nodes
        .iter()
        .enumerate()
        .rev()
        .map(|(index, node)| (node, index < prefix))
        .collect();
    while let Some((node, entry_prefix)) = pending.pop() {
        spend(&mut scan.work, 1)?;
        match node {
            Node::Step { assignments, .. } => {
                for assignment in assignments {
                    spend(&mut scan.work, 1)?;
                    // Reads precede definition, including destination addresses
                    // and the first definition's own RHS through any slot alias.
                    if let Place::Memory { address, .. } = &assignment.destination {
                        scan.reads(address)?;
                    }
                    let expression_nodes = scan.reads(&assignment.value)?;
                    let Place::Register(reg) = assignment.destination else {
                        continue;
                    };
                    let Some(destination) = scan.slot(reg)? else {
                        continue;
                    };
                    // Charge an upper bound for all three possible pure-tree scans
                    // and their constant-sized certificate arithmetic.
                    spend(
                        &mut scan.work,
                        expression_nodes.checked_mul(3)?.checked_add(128)?,
                    )?;
                    let mut division =
                        matches!(assignment.value, Expr::Binary(B::UDiv | B::SDiv, ..))
                            || crate::transform::division_expr::recognize(&assignment.value)
                                .is_some();
                    // The reciprocal-add recognizer may recheck three copies
                    // of its dividend. Charge its extra bounded scans first.
                    if !division
                        && crate::transform::add_division_expr::has_kernel_shape(&assignment.value)
                    {
                        spend(
                            &mut scan.work,
                            expression_nodes.checked_mul(16)?.checked_add(512)?,
                        )?;
                        division =
                            crate::transform::add_division_expr::recognize(&assignment.value)
                                .is_some();
                    }
                    let copy = if let Expr::Register(source) = assignment.value {
                        scan.slot(source)? == Some(destination)
                    } else {
                        false
                    };
                    let state = scan.state(destination)?;
                    if !state.written {
                        state.first_valid = entry_prefix && !state.read;
                        state.clean = true;
                    }
                    state.written = true;
                    state.clean &= division || copy;
                    state.division |= division;
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                scan.reads(condition)?;
                pending.extend(not_taken.iter().rev().map(|node| (node, false)));
                pending.extend(taken.iter().rev().map(|node| (node, false)));
            }
            Node::Loop(body) => pending.extend(body.iter().rev().map(|node| (node, false))),
            Node::Evaluate(expression) | Node::Return(expression) => {
                scan.reads(expression)?;
            }
            _ => {}
        }
    }
    Some(
        scan.states
            .into_iter()
            .filter_map(|(slot, state)| {
                (state.written
                    && state.first_valid
                    && state.clean
                    && state.division
                    && !blocked.contains(&slot))
                .then_some(slot)
            })
            .collect(),
    )
}
