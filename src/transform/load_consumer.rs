//! Fuse strict, single-input computations at their original load site.
//!
//! T=load(A); ...; D=f(T) becomes T=f(load(A)); ...; D=T. Only the
//! uniquely private temporary changes contents. The contract is
//! return, all RAM and first fault, with original load evaluation order.
use super::load_order::*;
use crate::model::ir::{Expr, Place, Program, Reg};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

pub use super::load_order::{
    Error, MAX_ASSIGNMENTS, MAX_BLOCKS, MAX_DEPTH, MAX_FOLDS, MAX_INSTRUCTIONS, MAX_NODES,
    MAX_REGISTERS, MAX_WORK,
};
pub const MODEL_ID: &str = "checked-strict-load-consumer-v1";
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fold {
    pub load_instruction: u64,
    pub load_assignment: usize,
    pub consumer_instruction: u64,
    pub consumer_assignment: usize,
    pub temporary: Reg,
    pub destination: Reg,
    pub expression: Expr,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evidence {
    pub folds: Vec<Fold>,
}

/// Retain the source before presentation changes and the checked paired IR.
/// Control recovery can consume the source while C consumes the lowering.
#[derive(Clone, Debug)]
pub struct Lowering {
    source: Arc<Program>,
    program: Arc<Program>,
    parameters: Vec<Reg>,
    evidence: Evidence,
}
impl Lowering {
    pub fn source(&self) -> &Program {
        &self.source
    }
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn parameters(&self) -> &[Reg] {
        &self.parameters
    }
    pub fn evidence(&self) -> &Evidence {
        &self.evidence
    }
    pub(crate) fn shared_source(&self) -> Arc<Program> {
        Arc::clone(&self.source)
    }
    pub fn validate(&self) -> Result<(), Error> {
        let actual = validate(&self.source, &self.program, &self.parameters)?;
        if actual != self.evidence {
            return Err(Error::UnsupportedChange);
        }
        Ok(())
    }
}
pub fn lower(source: &Program, parameters: &[Reg]) -> Option<Lowering> {
    let candidate = propose(source, parameters)?;
    let evidence = validate(source, &candidate, parameters).ok()?;
    Some(Lowering {
        source: Arc::new(source.clone()),
        program: Arc::new(candidate),
        parameters: parameters.to_vec(),
        evidence,
    })
}

// Strict operators always evaluate the unique hole. Select outside the raw
// load is excluded: inserting the load in a lazy arm could discard its fault.
fn substitute(
    e: &Expr,
    temp: Reg,
    load: &Expr,
    work: &mut Work,
    depth: usize,
    holes: &mut usize,
) -> Result<Expr, Error> {
    work.charge(1)?;
    if depth > MAX_DEPTH {
        return Err(Error::ResourceLimit);
    }
    Ok(match e {
        Expr::Const(n) => Expr::Const(*n),
        Expr::Register(r) if *r == temp => {
            *holes += 1;
            if *holes > 1 {
                return Err(Error::InvalidTemporary);
            }
            load.clone()
        }
        Expr::Unary(op, x) => Expr::unary(*op, substitute(x, temp, load, work, depth + 1, holes)?),
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            substitute(a, temp, load, work, depth + 1, holes)?,
            substitute(b, temp, load, work, depth + 1, holes)?,
        ),
        _ => return Err(Error::UnsupportedChange),
    })
}
pub fn propose(source: &Program, parameters: &[Reg]) -> Option<Program> {
    let mut work = Work(MAX_WORK);
    let clone_cost = bounded(source, parameters, &mut work).ok()?;
    let uses = collect_uses(source, &mut work).ok()?;
    let parameters: BTreeSet<_> = parameters.iter().map(|r| r.0).collect();
    let mut folds = Vec::new();
    for id in source.cfg().reachable_blocks() {
        let block = source.cfg().block(id);
        for i in block.instructions.clone() {
            for (a, assignment) in source.instructions()[i].assignments.iter().enumerate() {
                work.charge(1).ok()?;
                let Place::Register(temp) = assignment.destination else {
                    continue;
                };
                if !matches!(assignment.value, Expr::Load { .. }) || parameters.contains(&temp.0) {
                    continue;
                }
                let use_info = uses.get(&temp.0)?;
                if use_info.definitions != 1 || use_info.reads != 1 {
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
                    &source.instructions()[consumer.instruction].assignments[consumer.assignment];
                let Place::Register(destination) = use_assignment.destination else {
                    continue;
                };
                if destination == temp || use_assignment.value == Expr::Register(temp) {
                    continue;
                }
                let mut holes = 0;
                let expression = match substitute(
                    &use_assignment.value,
                    temp,
                    &assignment.value,
                    &mut work,
                    1,
                    &mut holes,
                ) {
                    Ok(value) => value,
                    Err(Error::ResourceLimit) => return None,
                    Err(_) => continue,
                };
                if holes != 1 {
                    continue;
                }
                if folds.len() == MAX_FOLDS {
                    return None;
                }
                folds.push((load, consumer, temp, expression));
            }
        }
    }
    if folds.is_empty() {
        return None;
    }
    work.charge(clone_cost).ok()?;
    let mut instructions = source.instructions().to_vec();
    for (load, consumer, temp, expression) in folds {
        instructions[load.instruction].assignments[load.assignment].value = expression;
        instructions[consumer.instruction].assignments[consumer.assignment].value =
            Expr::Register(temp);
    }
    let candidate = Program::new(
        source.cfg().block(source.cfg().entry()).start,
        source.register_count(),
        instructions,
    )
    .ok()?;
    // Bound the composed context+original load before handing it to clients.
    bounded(&candidate, &[], &mut work).ok()?;
    Some(candidate)
}

// Verifier-owned context reconstruction: the one exact original load subtree
// is the hole; all other leaves are literal constants. This does not call the
// proposer's substitution walker or consume its occurrence map.
fn context(
    original_load: &Expr,
    actual: &Expr,
    temp: Reg,
    work: &mut Work,
    holes: &mut usize,
) -> Result<Expr, Error> {
    work.charge(1)?;
    if matches!(actual, Expr::Load { .. }) {
        if !same(original_load, actual, work)? {
            return Err(Error::UnsupportedChange);
        }
        *holes += 1;
        if *holes > 1 {
            return Err(Error::InvalidTemporary);
        }
        return Ok(Expr::Register(temp));
    }
    Ok(match actual {
        Expr::Const(n) => Expr::Const(*n),
        Expr::Unary(op, x) => Expr::unary(*op, context(original_load, x, temp, work, holes)?),
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            context(original_load, a, temp, work, holes)?,
            context(original_load, b, temp, work, holes)?,
        ),
        _ => return Err(Error::UnsupportedChange),
    })
}
pub fn validate(
    source: &Program,
    candidate: &Program,
    parameters: &[Reg],
) -> Result<Evidence, Error> {
    let mut work = Work(MAX_WORK);
    bounded(source, parameters, &mut work)?;
    bounded(candidate, parameters, &mut work)?;
    let changes = changed_assignments(source, candidate, &mut work)?;
    let mut producers = BTreeMap::new();
    let mut consumers = BTreeMap::new();
    for (point, destination, old, new) in changes {
        if matches!(old, Expr::Load { .. }) {
            let mut holes = 0;
            let expression = context(old, new, destination, &mut work, &mut holes)?;
            if holes != 1
                || producers
                    .insert(destination.0, (point, expression))
                    .is_some()
            {
                return Err(Error::InvalidTemporary);
            }
        } else {
            let Expr::Register(temp) = new else {
                return Err(Error::UnsupportedChange);
            };
            if *temp == destination
                || consumers
                    .insert(temp.0, (point, destination, old))
                    .is_some()
            {
                return Err(Error::InvalidTemporary);
            }
        }
        if producers.len() > MAX_FOLDS || consumers.len() > MAX_FOLDS {
            return Err(Error::ResourceLimit);
        }
    }
    if producers.is_empty() || producers.len() != consumers.len() {
        return Err(Error::UnsupportedChange);
    }
    let parameters: BTreeSet<_> = parameters.iter().map(|r| r.0).collect();
    let mut folds = Vec::new();
    for (temp, (load, expression)) in &producers {
        let (consumer, destination, original) =
            consumers.get(temp).ok_or(Error::UnsupportedChange)?;
        if !load.precedes(*consumer)
            || parameters.contains(temp)
            || !same(expression, original, &mut work)?
        {
            return Err(Error::InvalidTemporary);
        }
        folds.push(Fold {
            load_instruction: source.instructions()[load.instruction].address,
            load_assignment: load.assignment,
            consumer_instruction: source.instructions()[consumer.instruction].address,
            consumer_assignment: consumer.assignment,
            temporary: Reg(*temp),
            destination: *destination,
            expression: expression.clone(),
        });
    }
    unique_private(source, producers.keys().copied(), &mut work)?;
    folds.sort_by_key(|f| (f.load_instruction, f.load_assignment));
    Ok(Evidence { folds })
}
