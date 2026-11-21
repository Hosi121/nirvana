//! Refine C storage colors using bounded value-lineage syntax.
//!
//! A group is always a subset of one supplied color. Connections describe
//! copies and arithmetic roots, not reaching definitions, source variables,
//! pointer types, or equivalence of values. This does not validate the original
//! allocation or split different definitions of a single virtual register.

use std::collections::BTreeMap;

use crate::model::ir::{BinaryOp, Control, Expr, Place, Program, Reg};

const MAX_REGISTERS: usize = 4096;
const MAX_POINTS: usize = 100_000;
const MAX_DEPTH: usize = 128;
const MAX_WORK: usize = 1_000_000;

#[derive(Clone, Debug)]
pub struct LocalIdentities {
    by_register: BTreeMap<usize, usize>,
    count: usize,
}

impl LocalIdentities {
    pub fn group(&self, register: Reg) -> Option<usize> {
        self.by_register.get(&register.0).copied()
    }

    pub fn groups(&self) -> usize {
        self.count
    }
}

/// Partition exactly the supplied distinct, valid registers. Labels are dense
/// and deterministic in ascending register order, independent of input order.
/// Every validation/resource failure discards the entire candidate.
pub fn refine(program: &Program, storage: &[(Reg, usize)]) -> Option<LocalIdentities> {
    if storage.len() > MAX_REGISTERS {
        return None;
    }
    let mut indices = BTreeMap::new();
    for &(reg, color) in storage {
        if reg.0 >= program.register_count() || indices.insert(reg.0, (color, 0)).is_some() {
            return None;
        }
    }
    let mut work = MAX_WORK;
    validate(program, &mut work)?;
    for (index, (_, position)) in indices.values_mut().enumerate() {
        *position = index;
    }
    let mut groups = Groups {
        parent: (0..indices.len()).collect(),
    };
    for id in program.cfg().reachable_blocks() {
        for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()] {
            spend(&mut work)?;
            for assignment in &instruction.assignments {
                spend(&mut work)?;
                if let Place::Register(destination) = assignment.destination
                    && let Some(&(color, index)) = indices.get(&destination.0)
                {
                    connect(
                        &assignment.value,
                        color,
                        index,
                        &indices,
                        &mut groups,
                        &mut work,
                    )?;
                }
            }
        }
    }
    let mut labels = BTreeMap::new();
    let mut by_register = BTreeMap::new();
    for (reg, (_, index)) in indices {
        let root = groups.root(index, &mut work)?;
        let next = labels.len();
        let label = *labels.entry(root).or_insert(next);
        by_register.insert(reg, label);
    }
    Some(LocalIdentities {
        by_register,
        count: labels.len(),
    })
}

fn spend(work: &mut usize) -> Option<()> {
    *work = work.checked_sub(1)?;
    Some(())
}

// Validate every expression, even unreachable instructions, memory destinations,
// and values assigned to excluded registers, before recursive root traversal.
fn validate(program: &Program, work: &mut usize) -> Option<()> {
    let mut points = 0usize;
    for instruction in program.instructions() {
        points = points
            .checked_add(instruction.assignments.len())?
            .checked_add(1)?;
        if points > MAX_POINTS {
            return None;
        }
        spend(work)?;
        for assignment in &instruction.assignments {
            spend(work)?;
            if let Place::Memory { address, .. } = &assignment.destination {
                expression(address, work)?;
            }
            expression(&assignment.value, work)?;
        }
        match &instruction.control {
            Control::Branch { condition, .. } => expression(condition, work)?,
            Control::Return(value) => expression(value, work)?,
            _ => {}
        }
    }
    Some(())
}

fn expression(expression: &Expr, work: &mut usize) -> Option<()> {
    let mut pending = vec![(expression, 1)];
    while let Some((expr, depth)) = pending.pop() {
        spend(work)?;
        if depth > MAX_DEPTH {
            return None;
        }
        match expr {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, a, b) => {
                pending.push((b, depth + 1));
                pending.push((a, depth + 1));
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
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
    Some(())
}

struct Groups {
    parent: Vec<usize>,
}
impl Groups {
    fn root(&mut self, mut index: usize, work: &mut usize) -> Option<usize> {
        while self.parent[index] != index {
            spend(work)?;
            self.parent[index] = self.parent[self.parent[index]];
            index = self.parent[index];
        }
        spend(work)?;
        Some(index)
    }

    fn join(&mut self, a: usize, b: usize, work: &mut usize) -> Option<()> {
        let a = self.root(a, work)?;
        let b = self.root(b, work)?;
        self.parent[a.max(b)] = a.min(b);
        Some(())
    }
}

fn connect(
    expr: &Expr,
    color: usize,
    destination: usize,
    indices: &BTreeMap<usize, (usize, usize)>,
    groups: &mut Groups,
    work: &mut usize,
) -> Option<()> {
    spend(work)?;
    match expr {
        Expr::Unary(_, value) => connect(value, color, destination, indices, groups, work)?,
        Expr::Register(reg) => {
            if let Some(&(source_color, source)) = indices.get(&reg.0)
                && source_color == color
            {
                groups.join(destination, source, work)?;
            }
        }
        Expr::Binary(
            BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor,
            a,
            b,
        ) => {
            connect(a, color, destination, indices, groups, work)?;
            connect(b, color, destination, indices, groups, work)?;
        }
        Expr::Binary(BinaryOp::Sub | BinaryOp::Shl | BinaryOp::Shr, a, _) => {
            connect(a, color, destination, indices, groups, work)?
        }
        // In particular, never treat a Load address or a Select arm as a data
        // predecessor. Comparisons and control/memory uses create no edges.
        _ => {}
    }
    Some(())
}
