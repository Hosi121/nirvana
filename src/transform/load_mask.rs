//! Optional display-only load masks, with a separate exact-schema validator.
//!
//! `T = load(A); ...; D = T & M` becomes `T = load(A) & M; ...; D = T`.
//! Every assignment destination, program point, control, and raw load subtree
//! stays in place. The sole changed temporary is neither an input nor read
//! anywhere else. Final internal registers are outside this pass's contract.

use std::collections::{BTreeMap, BTreeSet};

use crate::model::ir::{BinaryOp, Expr, Place, Program, Reg, UnaryOp};

pub use super::load_order::{
    Error as LoadMaskError, MAX_ASSIGNMENTS, MAX_BLOCKS, MAX_DEPTH, MAX_FOLDS, MAX_INSTRUCTIONS,
    MAX_NODES, MAX_REGISTERS, MAX_WORK,
};
use super::load_order::{
    Point, Work, bounded, changed_assignments, collect_uses, same, unique_private,
};
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
    let uses = collect_uses(program, &mut work).ok()?;
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
    for (point, reg, old, new) in changed_assignments(original, candidate, &mut work)? {
        // Producer and consumer classification deliberately does not
        // use the proposer's register-mask parser or occurrence data.
        if matches!(old, Expr::Load { .. }) {
            let Expr::Binary(BinaryOp::And, left, right) = new else {
                return Err(LoadMaskError::UnsupportedChange);
            };
            let (load, mask) = match (&**left, &**right) {
                (load, Expr::Const(mask)) if matches!(load, Expr::Load { .. }) => (load, *mask),
                (Expr::Const(mask), load) if matches!(load, Expr::Load { .. }) => (load, *mask),
                _ => return Err(LoadMaskError::UnsupportedChange),
            };
            if !same(old, load, &mut work)?
                || !wrappable_load(old, &mut work)?
                || producers.insert(reg.0, (point, mask)).is_some()
            {
                return Err(LoadMaskError::UnsupportedChange);
            }
        } else {
            let Expr::Register(temp) = *new else {
                return Err(LoadMaskError::UnsupportedChange);
            };
            let mask = match old {
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
    unique_private(original, producers.keys().copied(), &mut work)?;
    folds.sort_by_key(|fold| (fold.load_instruction, fold.load_assignment));
    Ok(LoadMaskEvidence { folds })
}
