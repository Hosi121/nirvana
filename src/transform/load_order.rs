//! Shared bounded layout and occurrence checks for load folding.
use crate::model::ir::{Assignment, Control, Expr, Place, Program, Reg};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
pub const MAX_REGISTERS: usize = 65_536;
pub const MAX_INSTRUCTIONS: usize = 32_768;
pub const MAX_ASSIGNMENTS: usize = 32_768;
pub const MAX_BLOCKS: usize = 4096;
pub const MAX_NODES: usize = 250_000;
pub const MAX_DEPTH: usize = 128;
pub const MAX_FOLDS: usize = 64;
pub const MAX_WORK: usize = 2_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    InvalidParameters,
    ShapeMismatch,
    UnsupportedChange,
    InvalidTemporary,
    ResourceLimit,
}
impl Error {
    pub const fn is_resource_limit(self) -> bool {
        matches!(self, Self::ResourceLimit)
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidParameters => "invalid or repeated load-fold parameter",
            Self::ShapeMismatch => "load-fold program layout changed",
            Self::UnsupportedChange => "change is outside the load-fold schema",
            Self::InvalidTemporary => "load-fold temporary is not a unique local use",
            Self::ResourceLimit => "load-fold resource limit",
        })
    }
}
impl std::error::Error for Error {}

pub(super) struct Work(pub(super) usize);
impl Work {
    pub(super) fn charge(&mut self, n: usize) -> Result<(), Error> {
        self.0 = self.0.checked_sub(n).ok_or(Error::ResourceLimit)?;
        Ok(())
    }
}

// This validates the entire input before any expression clone or equality.
pub(super) fn bounded(
    program: &Program,
    parameters: &[Reg],
    work: &mut Work,
) -> Result<usize, Error> {
    if program.register_count() > MAX_REGISTERS
        || program.instructions().len() > MAX_INSTRUCTIONS
        || program.cfg().blocks().len() > MAX_BLOCKS
    {
        return Err(Error::ResourceLimit);
    }
    let mut distinct = BTreeSet::new();
    if parameters.len() > MAX_REGISTERS {
        return Err(Error::ResourceLimit);
    }
    for reg in parameters {
        work.charge(1)?;
        if reg.0 >= program.register_count() || !distinct.insert(reg.0) {
            return Err(Error::InvalidParameters);
        }
    }
    let mut assignments = 0usize;
    let mut nodes = 0usize;
    for instruction in program.instructions() {
        work.charge(1)?;
        assignments = assignments
            .checked_add(instruction.assignments.len())
            .ok_or(Error::ResourceLimit)?;
        if assignments > MAX_ASSIGNMENTS {
            return Err(Error::ResourceLimit);
        }
        let mut roots = Vec::new();
        for assignment in &instruction.assignments {
            roots.push(&assignment.value);
            if let Place::Memory { address, .. } = &assignment.destination {
                roots.push(address);
            }
        }
        match &instruction.control {
            Control::Branch { condition, .. } | Control::Return(condition) => roots.push(condition),
            _ => {}
        }
        for root in roots {
            let mut pending = vec![(root, 1usize)];
            while let Some((expression, depth)) = pending.pop() {
                work.charge(1)?;
                nodes += 1;
                if nodes > MAX_NODES || depth > MAX_DEPTH {
                    return Err(Error::ResourceLimit);
                }
                match expression {
                    Expr::Const(_) | Expr::Register(_) => {}
                    Expr::Unary(_, value) => pending.push((value, depth + 1)),
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
        }
    }
    Ok(nodes + assignments + program.instructions().len())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Point {
    pub(super) instruction: usize,
    pub(super) assignment: usize,
    pub(super) block: usize,
}
impl Point {
    pub(super) fn precedes(self, other: Self) -> bool {
        self.block == other.block
            && (self.instruction, self.assignment) < (other.instruction, other.assignment)
    }
}

#[derive(Default)]
pub(super) struct Uses {
    pub(super) definitions: u8,
    pub(super) reads: u8,
    pub(super) assignment_read: Option<Point>,
}

fn proposed_reads(
    expression: &Expr,
    point: Option<Point>,
    uses: &mut BTreeMap<usize, Uses>,
    work: &mut Work,
) -> Result<(), Error> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        work.charge(1)?;
        match expression {
            Expr::Register(reg) => {
                let value = uses.entry(reg.0).or_default();
                value.reads = value.reads.saturating_add(1).min(2);
                value.assignment_read = point;
            }
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Const(_) => {}
        }
    }
    Ok(())
}

pub(super) fn same(a: &Expr, b: &Expr, work: &mut Work) -> Result<bool, Error> {
    let mut pending = vec![(a, b)];
    while let Some((a, b)) = pending.pop() {
        work.charge(1)?;
        match (a, b) {
            (Expr::Const(a), Expr::Const(b)) if a == b => {}
            (Expr::Register(a), Expr::Register(b)) if a == b => {}
            (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => pending.push((x, y)),
            (Expr::Binary(a, al, ar), Expr::Binary(b, bl, br)) if a == b => {
                pending.extend([(&**al, &**bl), (&**ar, &**br)])
            }
            (
                Expr::Load {
                    address: a,
                    width: aw,
                },
                Expr::Load {
                    address: b,
                    width: bw,
                },
            ) if aw == bw => pending.push((a, b)),
            (
                Expr::Select {
                    condition: a,
                    taken: at,
                    not_taken: an,
                },
                Expr::Select {
                    condition: b,
                    taken: bt,
                    not_taken: bn,
                },
            ) => pending.extend([(&**a, &**b), (&**at, &**bt), (&**an, &**bn)]),
            _ => return Ok(false),
        }
    }
    Ok(true)
}

pub(super) fn same_control(a: &Control, b: &Control, work: &mut Work) -> Result<bool, Error> {
    Ok(match (a, b) {
        (Control::Next, Control::Next) => true,
        (Control::Jump(a), Control::Jump(b)) => a == b,
        (
            Control::Branch {
                condition: a,
                target: at,
            },
            Control::Branch {
                condition: b,
                target: bt,
            },
        ) => at == bt && same(a, b, work)?,
        (Control::Return(a), Control::Return(b)) => same(a, b, work)?,
        _ => false,
    })
}

pub(super) fn collect_uses(
    program: &Program,
    work: &mut Work,
) -> Result<BTreeMap<usize, Uses>, Error> {
    let mut uses = BTreeMap::<usize, Uses>::new();
    for block in program.cfg().blocks() {
        for i in block.instructions.clone() {
            let instruction = &program.instructions()[i];
            for (a, assignment) in instruction.assignments.iter().enumerate() {
                work.charge(1)?;
                let point = Point {
                    instruction: i,
                    assignment: a,
                    block: block.id.index(),
                };
                if let Place::Register(reg) = assignment.destination {
                    let count = &mut uses.entry(reg.0).or_default().definitions;
                    *count = count.saturating_add(1).min(2);
                } else if let Place::Memory { ref address, .. } = assignment.destination {
                    proposed_reads(address, Some(point), &mut uses, work)?;
                }
                proposed_reads(&assignment.value, Some(point), &mut uses, work)?;
            }
            if let Control::Branch { ref condition, .. } | Control::Return(ref condition) =
                instruction.control
            {
                proposed_reads(condition, None, &mut uses, work)?;
            }
        }
    }
    Ok(uses)
}
pub(super) fn unique_private(
    source: &Program,
    temps: impl IntoIterator<Item = usize>,
    work: &mut Work,
) -> Result<(), Error> {
    let mut counts: BTreeMap<usize, (u8, u8)> =
        temps.into_iter().map(|reg| (reg, (0, 0))).collect();
    for instruction in source.instructions() {
        work.charge(1)?;
        let mut pending = Vec::new();
        for Assignment { destination, value } in &instruction.assignments {
            match destination {
                Place::Register(reg) => {
                    if let Some((definitions, _)) = counts.get_mut(&reg.0) {
                        *definitions = definitions.saturating_add(1).min(2);
                    }
                }
                Place::Memory { address, .. } => pending.push(address),
            }
            pending.push(value);
        }
        match &instruction.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                pending.push(condition)
            }
            _ => {}
        }
        while let Some(expression) = pending.pop() {
            work.charge(1)?;
            match expression {
                Expr::Register(reg) => {
                    if let Some((_, reads)) = counts.get_mut(&reg.0) {
                        *reads = reads.saturating_add(1).min(2);
                    }
                }
                Expr::Unary(_, value) => pending.push(value),
                Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
                Expr::Load { address, .. } => pending.push(address),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**condition, &**taken, &**not_taken]),
                Expr::Const(_) => {}
            }
        }
    }
    if counts.values().any(|count| *count != (1, 1)) {
        return Err(Error::InvalidTemporary);
    }
    Ok(())
}

pub(super) type ChangedAssignment<'a> = (Point, Reg, &'a Expr, &'a Expr);
pub(super) fn changed_assignments<'a>(
    original: &'a Program,
    candidate: &'a Program,
    work: &mut Work,
) -> Result<Vec<ChangedAssignment<'a>>, Error> {
    if original.register_count() != candidate.register_count()
        || original.cfg().instructions() != candidate.cfg().instructions()
        || original.cfg().block(original.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
    {
        return Err(Error::ShapeMismatch);
    }
    let reachable: BTreeSet<_> = original.cfg().reachable_blocks().into_iter().collect();
    let mut changed = Vec::new();
    for block in original.cfg().blocks() {
        for i in block.instructions.clone() {
            work.charge(1)?;
            let a = &original.instructions()[i];
            let b = &candidate.instructions()[i];
            if a.assignments.len() != b.assignments.len()
                || !same_control(&a.control, &b.control, work)?
            {
                return Err(Error::ShapeMismatch);
            }
            for (j, (a, b)) in a.assignments.iter().zip(&b.assignments).enumerate() {
                work.charge(1)?;
                let register = match (&a.destination, &b.destination) {
                    (Place::Register(a), Place::Register(b)) if a == b => Some(*a),
                    (
                        Place::Memory {
                            address: a,
                            width: aw,
                        },
                        Place::Memory {
                            address: b,
                            width: bw,
                        },
                    ) if aw == bw && same(a, b, work)? => None,
                    _ => return Err(Error::ShapeMismatch),
                };
                if same(&a.value, &b.value, work)? {
                    continue;
                }
                let destination = register.ok_or(Error::UnsupportedChange)?;
                if !reachable.contains(&block.id) {
                    return Err(Error::UnsupportedChange);
                }
                if changed.len() == MAX_FOLDS * 2 {
                    return Err(Error::ResourceLimit);
                }
                changed.push((
                    Point {
                        instruction: i,
                        assignment: j,
                        block: block.id.index(),
                    },
                    destination,
                    &a.value,
                    &b.value,
                ));
            }
        }
    }
    Ok(changed)
}
