//! Optional display-only load masks, with a separate exact-schema validator.
//!
//! `T = load(A); ...; D = T & M` becomes `T = load(A) & M; ...; D = T`.
//! Every assignment destination, program point, control, and raw load subtree
//! stays in place. The sole changed temporary is neither an input nor read
//! anywhere else. Final internal registers are outside this pass's contract.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::model::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg, UnaryOp};

pub const MAX_REGISTERS: usize = 65_536;
pub const MAX_INSTRUCTIONS: usize = 32_768;
pub const MAX_ASSIGNMENTS: usize = 32_768;
pub const MAX_BLOCKS: usize = 4096;
pub const MAX_NODES: usize = 250_000;
pub const MAX_DEPTH: usize = 128;
pub const MAX_FOLDS: usize = 64;
pub const MAX_WORK: usize = 2_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadMaskFold {
    pub load_instruction: u64,
    pub load_assignment: usize,
    pub consumer_instruction: u64,
    pub consumer_assignment: usize,
    pub temporary: Reg,
    pub destination: Reg,
    pub mask: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadMaskEvidence {
    pub folds: Vec<LoadMaskFold>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LoadMaskError {
    InvalidParameters,
    ShapeMismatch,
    UnsupportedChange,
    InvalidTemporary,
    ResourceLimit,
}
impl LoadMaskError {
    pub const fn is_resource_limit(self) -> bool {
        matches!(self, Self::ResourceLimit)
    }
}
impl fmt::Display for LoadMaskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidParameters => "invalid or repeated load-mask parameter",
            Self::ShapeMismatch => "load-mask program layout changed",
            Self::UnsupportedChange => "change is outside the load-mask schema",
            Self::InvalidTemporary => "load-mask temporary is not a unique local use",
            Self::ResourceLimit => "load-mask resource limit",
        })
    }
}
impl std::error::Error for LoadMaskError {}

struct Work(usize);
impl Work {
    fn charge(&mut self, n: usize) -> Result<(), LoadMaskError> {
        self.0 = self.0.checked_sub(n).ok_or(LoadMaskError::ResourceLimit)?;
        Ok(())
    }
}

// This validates the entire input before any expression clone or equality.
fn bounded(program: &Program, parameters: &[Reg], work: &mut Work) -> Result<usize, LoadMaskError> {
    if program.register_count() > MAX_REGISTERS
        || program.instructions().len() > MAX_INSTRUCTIONS
        || program.cfg().blocks().len() > MAX_BLOCKS
    {
        return Err(LoadMaskError::ResourceLimit);
    }
    let mut distinct = BTreeSet::new();
    if parameters.len() > MAX_REGISTERS {
        return Err(LoadMaskError::ResourceLimit);
    }
    for reg in parameters {
        work.charge(1)?;
        if reg.0 >= program.register_count() || !distinct.insert(reg.0) {
            return Err(LoadMaskError::InvalidParameters);
        }
    }
    let mut assignments = 0usize;
    let mut nodes = 0usize;
    for instruction in program.instructions() {
        work.charge(1)?;
        assignments = assignments
            .checked_add(instruction.assignments.len())
            .ok_or(LoadMaskError::ResourceLimit)?;
        if assignments > MAX_ASSIGNMENTS {
            return Err(LoadMaskError::ResourceLimit);
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
                    return Err(LoadMaskError::ResourceLimit);
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
struct Point {
    instruction: usize,
    assignment: usize,
    block: usize,
}
impl Point {
    fn precedes(self, other: Self) -> bool {
        self.block == other.block
            && (self.instruction, self.assignment) < (other.instruction, other.assignment)
    }
}

#[derive(Default)]
struct Uses {
    definitions: u8,
    reads: u8,
    assignment_read: Option<Point>,
}

fn proposed_reads(
    expression: &Expr,
    point: Option<Point>,
    uses: &mut BTreeMap<usize, Uses>,
    work: &mut Work,
) -> Result<(), LoadMaskError> {
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

fn mask_register(expression: &Expr) -> Option<(Reg, u64)> {
    match expression {
        Expr::Unary(UnaryOp::Extract { start: 0, width }, value) => {
            if let Expr::Register(reg) = **value {
                Some((reg, width.mask()))
            } else {
                None
            }
        }
        Expr::Binary(BinaryOp::And, a, b) => match (&**a, &**b) {
            (Expr::Register(reg), Expr::Const(mask)) | (Expr::Const(mask), Expr::Register(reg)) => {
                Some((*reg, *mask))
            }
            _ => None,
        },
        _ => None,
    }
}

// Wrapping the original root increases its depth by one. No select from that
// load (including its address) is admitted by this deliberately small schema.
fn wrappable_load(expression: &Expr, work: &mut Work) -> Result<bool, LoadMaskError> {
    if !matches!(expression, Expr::Load { .. }) {
        return Ok(false);
    }
    let mut pending = vec![(expression, 1usize)];
    while let Some((expression, depth)) = pending.pop() {
        work.charge(1)?;
        if depth >= MAX_DEPTH {
            return Ok(false);
        }
        match expression {
            Expr::Select { .. } => return Ok(false),
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            _ => {}
        }
    }
    Ok(true)
}

/// Propose only the small paired rewrite. Call `validate` before adoption.
/// None means no useful fold, invalid input, or unavailable resources; no
/// partially transformed program is returned. Parameters keep their identity.
pub fn propose(program: &Program, parameters: &[Reg]) -> Option<Program> {
    let mut work = Work(MAX_WORK);
    let clone_cost = bounded(program, parameters, &mut work).ok()?;
    let mut uses = BTreeMap::<usize, Uses>::new();
    for block in program.cfg().blocks() {
        for i in block.instructions.clone() {
            let instruction = &program.instructions()[i];
            for (a, assignment) in instruction.assignments.iter().enumerate() {
                work.charge(1).ok()?;
                let point = Point {
                    instruction: i,
                    assignment: a,
                    block: block.id.index(),
                };
                if let Place::Register(reg) = assignment.destination {
                    let count = &mut uses.entry(reg.0).or_default().definitions;
                    *count = count.saturating_add(1).min(2);
                } else if let Place::Memory { ref address, .. } = assignment.destination {
                    proposed_reads(address, Some(point), &mut uses, &mut work).ok()?;
                }
                proposed_reads(&assignment.value, Some(point), &mut uses, &mut work).ok()?;
            }
            if let Control::Branch { ref condition, .. } | Control::Return(ref condition) =
                instruction.control
            {
                proposed_reads(condition, None, &mut uses, &mut work).ok()?;
            }
        }
    }
    let parameters: BTreeSet<_> = parameters.iter().map(|reg| reg.0).collect();
    let mut folds = Vec::new();
    for id in program.cfg().reachable_blocks() {
        let block = program.cfg().block(id);
        for i in block.instructions.clone() {
            for (a, assignment) in program.instructions()[i].assignments.iter().enumerate() {
                work.charge(1).ok()?;
                let Place::Register(temp) = assignment.destination else {
                    continue;
                };
                let use_info = &uses[&temp.0];
                if use_info.definitions != 1 || use_info.reads != 1 || parameters.contains(&temp.0)
                {
                    continue;
                }
                let Some(consumer) = use_info.assignment_read else {
                    continue;
                };
                let load = Point {
                    instruction: i,
                    assignment: a,
                    block: id.index(),
                };
                if !load.precedes(consumer) {
                    continue;
                }
                let use_assignment =
                    &program.instructions()[consumer.instruction].assignments[consumer.assignment];
                let Place::Register(destination) = use_assignment.destination else {
                    continue;
                };
                let Some((source, mask)) = mask_register(&use_assignment.value) else {
                    continue;
                };
                if source != temp
                    || destination == temp
                    || mask == u64::MAX
                    || !wrappable_load(&assignment.value, &mut work).ok()?
                {
                    continue;
                }
                if folds.len() == MAX_FOLDS {
                    return None;
                }
                folds.push((load, consumer, temp, mask));
            }
        }
    }
    if folds.is_empty() {
        return None;
    }
    // All resource failures happen before the sole candidate clone.
    work.charge(clone_cost).ok()?;
    let mut instructions = program.instructions().to_vec();
    for (load, consumer, temp, mask) in folds {
        let value = &mut instructions[load.instruction].assignments[load.assignment].value;
        let original = std::mem::replace(value, Expr::Const(0));
        *value = Expr::binary(BinaryOp::And, original, Expr::Const(mask));
        instructions[consumer.instruction].assignments[consumer.assignment].value =
            Expr::Register(temp);
    }
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        program.register_count(),
        instructions,
    )
    .ok()
}

fn same(a: &Expr, b: &Expr, work: &mut Work) -> Result<bool, LoadMaskError> {
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

fn same_control(a: &Control, b: &Control, work: &mut Work) -> Result<bool, LoadMaskError> {
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

/// Independently validate the *actual paired IR*, without calling the proposer
/// or trusting its discovered sites. No solver, alias assumption, or initial
/// temporary value is used. Unrelated code must match literally, including
/// unreachable instructions. This proves the schema, not C compilation.
pub fn validate(
    original: &Program,
    candidate: &Program,
    parameters: &[Reg],
) -> Result<LoadMaskEvidence, LoadMaskError> {
    let mut work = Work(MAX_WORK);
    bounded(original, parameters, &mut work)?;
    bounded(candidate, parameters, &mut work)?;
    if original.register_count() != candidate.register_count()
        || original.cfg().instructions() != candidate.cfg().instructions()
        || original.cfg().block(original.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
    {
        return Err(LoadMaskError::ShapeMismatch);
    }
    let mut producers = BTreeMap::<usize, (Point, u64)>::new();
    let mut consumers = BTreeMap::<usize, (Point, Reg, u64)>::new();
    let reachable: BTreeSet<_> = original.cfg().reachable_blocks().into_iter().collect();
    for block in original.cfg().blocks() {
        for i in block.instructions.clone() {
            work.charge(1)?;
            let a = &original.instructions()[i];
            let b = &candidate.instructions()[i];
            if a.assignments.len() != b.assignments.len()
                || !same_control(&a.control, &b.control, &mut work)?
            {
                return Err(LoadMaskError::ShapeMismatch);
            }
            for (j, (a, b)) in a.assignments.iter().zip(&b.assignments).enumerate() {
                work.charge(1)?;
                let destination = match (&a.destination, &b.destination) {
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
                    ) if aw == bw && same(a, b, &mut work)? => None,
                    _ => return Err(LoadMaskError::ShapeMismatch),
                };
                if same(&a.value, &b.value, &mut work)? {
                    continue;
                }
                let reg = destination.ok_or(LoadMaskError::UnsupportedChange)?;
                if !reachable.contains(&block.id) {
                    return Err(LoadMaskError::UnsupportedChange);
                }
                let point = Point {
                    instruction: i,
                    assignment: j,
                    block: block.id.index(),
                };
                // Producer and consumer classification deliberately does not
                // use the proposer's register-mask parser or occurrence data.
                if matches!(a.value, Expr::Load { .. }) {
                    let Expr::Binary(BinaryOp::And, left, right) = &b.value else {
                        return Err(LoadMaskError::UnsupportedChange);
                    };
                    let (load, mask) = match (&**left, &**right) {
                        (load, Expr::Const(mask)) if matches!(load, Expr::Load { .. }) => {
                            (load, *mask)
                        }
                        (Expr::Const(mask), load) if matches!(load, Expr::Load { .. }) => {
                            (load, *mask)
                        }
                        _ => return Err(LoadMaskError::UnsupportedChange),
                    };
                    if !same(&a.value, load, &mut work)?
                        || !wrappable_load(&a.value, &mut work)?
                        || producers.insert(reg.0, (point, mask)).is_some()
                    {
                        return Err(LoadMaskError::UnsupportedChange);
                    }
                } else {
                    let Expr::Register(temp) = b.value else {
                        return Err(LoadMaskError::UnsupportedChange);
                    };
                    let mask = match &a.value {
                        Expr::Binary(BinaryOp::And, left, right) => match (&**left, &**right) {
                            (Expr::Register(read), Expr::Const(mask))
                            | (Expr::Const(mask), Expr::Register(read))
                                if *read == temp =>
                            {
                                *mask
                            }
                            _ => return Err(LoadMaskError::UnsupportedChange),
                        },
                        Expr::Unary(UnaryOp::Extract { start: 0, width }, value) if matches!(&**value, Expr::Register(read) if *read == temp) => {
                            width.mask()
                        }
                        _ => return Err(LoadMaskError::UnsupportedChange),
                    };
                    if reg == temp || consumers.insert(temp.0, (point, reg, mask)).is_some() {
                        return Err(LoadMaskError::InvalidTemporary);
                    }
                }
                if producers.len() > MAX_FOLDS || consumers.len() > MAX_FOLDS {
                    return Err(LoadMaskError::ResourceLimit);
                }
            }
        }
    }
    if producers.len() != consumers.len() {
        return Err(LoadMaskError::UnsupportedChange);
    }
    let parameters: BTreeSet<_> = parameters.iter().map(|reg| reg.0).collect();
    let mut folds = Vec::new();
    for (temp, (load, mask)) in &producers {
        let (consumer, destination, consumer_mask) = consumers
            .get(temp)
            .ok_or(LoadMaskError::UnsupportedChange)?;
        if mask != consumer_mask || !load.precedes(*consumer) || parameters.contains(temp) {
            return Err(LoadMaskError::InvalidTemporary);
        }
        folds.push(LoadMaskFold {
            load_instruction: original.instructions()[load.instruction].address,
            load_assignment: load.assignment,
            consumer_instruction: original.instructions()[consumer.instruction].address,
            consumer_assignment: consumer.assignment,
            temporary: Reg(*temp),
            destination: *destination,
            mask: *mask,
        });
    }
    // A second, validator-owned traversal counts individual register leaves,
    // including both lazy arms, nested addresses, stores, and controls. It does
    // not reuse the proposal's uses map or count one read per expression.
    let mut counts: BTreeMap<usize, (u8, u8)> =
        producers.keys().map(|reg| (*reg, (0, 0))).collect();
    for instruction in original.instructions() {
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
        return Err(LoadMaskError::InvalidTemporary);
    }
    folds.sort_by_key(|fold| (fold.load_instruction, fold.load_assignment));
    Ok(LoadMaskEvidence { folds })
}
