//! Fuse single-use loaded values into strict computations at the load site.
//!
//! T=load(A); ...; D=f(T) becomes T=f(load(A)); ...; D=T. Only the
//! uniquely private temporary changes contents. The contract is
//! return, all RAM and first fault, with original load evaluation order.
//! The stable-input API also admits register leaves with no intervening
//! definitions. The constant-only API retains its original v1 contract.
use super::load_order::*;
use crate::model::ir::{Expr, Place, Program, Reg};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

pub use super::load_order::{
    Error, MAX_ASSIGNMENTS, MAX_BLOCKS, MAX_DEPTH, MAX_FOLDS, MAX_INSTRUCTIONS, MAX_NODES,
    MAX_REGISTERS, MAX_WORK,
};
pub const MODEL_ID: &str = "checked-strict-load-consumer-v1";
pub const STABLE_MODEL_ID: &str = "checked-stable-load-consumer-v2";
pub const MAX_CONTEXT_INPUTS: usize = 64;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ContextKind {
    Constants,
    StableInputs,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fold {
    pub load_instruction: u64,
    pub load_assignment: usize,
    pub consumer_instruction: u64,
    pub consumer_assignment: usize,
    pub temporary: Reg,
    pub destination: Reg,
    pub expression: Expr,
    pub inputs: Vec<Reg>,
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
    context: ContextKind,
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
    pub fn model_id(&self) -> &'static str {
        match self.context {
            ContextKind::Constants => MODEL_ID,
            ContextKind::StableInputs => STABLE_MODEL_ID,
        }
    }
    pub(crate) fn shared_source(&self) -> Arc<Program> {
        Arc::clone(&self.source)
    }
    pub fn validate(&self) -> Result<(), Error> {
        let actual = match self.context {
            ContextKind::Constants => validate(&self.source, &self.program, &self.parameters)?,
            ContextKind::StableInputs => {
                validate_with_stable_inputs(&self.source, &self.program, &self.parameters)?
            }
        };
        if actual != self.evidence {
            return Err(Error::UnsupportedChange);
        }
        Ok(())
    }
}
pub fn lower(source: &Program, parameters: &[Reg]) -> Option<Lowering> {
    lower_kind(source, parameters, ContextKind::Constants)
}
pub fn lower_with_stable_inputs(source: &Program, parameters: &[Reg]) -> Option<Lowering> {
    lower_kind(source, parameters, ContextKind::StableInputs)
}
fn lower_kind(source: &Program, parameters: &[Reg], context: ContextKind) -> Option<Lowering> {
    let candidate = propose_kind(source, parameters, context)?;
    let evidence = validate_kind(source, &candidate, parameters, context).ok()?;
    let context = if evidence.folds.iter().all(|f| f.inputs.is_empty()) {
        ContextKind::Constants
    } else {
        context
    };
    Some(Lowering {
        source: Arc::new(source.clone()),
        program: Arc::new(candidate),
        parameters: parameters.to_vec(),
        evidence,
        context,
    })
}

#[derive(Default)]
struct ProposedContext {
    holes: usize,
    inputs: BTreeSet<usize>,
}

// Strict operators always evaluate the unique hole. Select outside the raw
// load is excluded: inserting the load in a lazy arm could discard its fault.
fn substitute(
    e: &Expr,
    temp: Reg,
    load: &Expr,
    work: &mut Work,
    depth: usize,
    kind: ContextKind,
    context: &mut ProposedContext,
) -> Result<Expr, Error> {
    work.charge(1)?;
    if depth > MAX_DEPTH {
        return Err(Error::ResourceLimit);
    }
    Ok(match e {
        Expr::Const(n) => Expr::Const(*n),
        Expr::Register(r) if *r == temp => {
            context.holes += 1;
            if context.holes > 1 {
                return Err(Error::InvalidTemporary);
            }
            load.clone()
        }
        Expr::Register(r) if kind == ContextKind::StableInputs => {
            context.inputs.insert(r.0);
            if context.inputs.len() > MAX_CONTEXT_INPUTS {
                return Err(Error::ResourceLimit);
            }
            Expr::Register(*r)
        }
        Expr::Unary(op, x) => Expr::unary(
            *op,
            substitute(x, temp, load, work, depth + 1, kind, context)?,
        ),
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            substitute(a, temp, load, work, depth + 1, kind, context)?,
            substitute(b, temp, load, work, depth + 1, kind, context)?,
        ),
        _ => return Err(Error::UnsupportedChange),
    })
}

// Proposer scans forward from the load, excluding both endpoint assignments.
// Memory effects keep their exact place and never modify scalar registers.
fn proposed_stability(
    source: &Program,
    load: Point,
    consumer: Point,
    inputs: &BTreeSet<usize>,
    work: &mut Work,
) -> Result<bool, Error> {
    if inputs.is_empty() {
        return Ok(true);
    }
    for i in load.instruction..=consumer.instruction {
        work.charge(1)?;
        let assignments = &source.instructions()[i].assignments;
        let begin = if i == load.instruction {
            load.assignment + 1
        } else {
            0
        };
        let end = if i == consumer.instruction {
            consumer.assignment
        } else {
            assignments.len()
        };
        for a in &assignments[begin..end] {
            work.charge(1)?;
            if matches!(a.destination, Place::Register(r) if inputs.contains(&r.0)) {
                return Ok(false);
            }
        }
    }
    Ok(true)
}
pub fn propose(source: &Program, parameters: &[Reg]) -> Option<Program> {
    propose_kind(source, parameters, ContextKind::Constants)
}
pub fn propose_with_stable_inputs(source: &Program, parameters: &[Reg]) -> Option<Program> {
    propose_kind(source, parameters, ContextKind::StableInputs)
}
fn propose_kind(source: &Program, parameters: &[Reg], kind: ContextKind) -> Option<Program> {
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
                let mut context = ProposedContext::default();
                let expression = match substitute(
                    &use_assignment.value,
                    temp,
                    &assignment.value,
                    &mut work,
                    1,
                    kind,
                    &mut context,
                ) {
                    Ok(value) => value,
                    Err(Error::ResourceLimit) => return None,
                    Err(_) => continue,
                };
                if context.holes != 1
                    || !proposed_stability(source, load, consumer, &context.inputs, &mut work)
                        .ok()?
                {
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

#[derive(Default)]
struct CheckedContext {
    holes: usize,
    inputs: BTreeSet<usize>,
}

// Verifier-owned context reconstruction: the one exact original load subtree
// is the hole. Other leaves are literals or separately checked stable input
// registers. This does not call the proposer's substitution walker or use map.
fn context(
    original_load: &Expr,
    actual: &Expr,
    temp: Reg,
    work: &mut Work,
    kind: ContextKind,
    context_inputs: &mut CheckedContext,
) -> Result<Expr, Error> {
    work.charge(1)?;
    if matches!(actual, Expr::Load { .. }) {
        if !same(original_load, actual, work)? {
            return Err(Error::UnsupportedChange);
        }
        context_inputs.holes += 1;
        if context_inputs.holes > 1 {
            return Err(Error::InvalidTemporary);
        }
        return Ok(Expr::Register(temp));
    }
    Ok(match actual {
        Expr::Const(n) => Expr::Const(*n),
        Expr::Register(r) if kind == ContextKind::StableInputs && *r != temp => {
            context_inputs.inputs.insert(r.0);
            if context_inputs.inputs.len() > MAX_CONTEXT_INPUTS {
                return Err(Error::ResourceLimit);
            }
            Expr::Register(*r)
        }
        Expr::Unary(op, x) => Expr::unary(
            *op,
            context(original_load, x, temp, work, kind, context_inputs)?,
        ),
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            context(original_load, a, temp, work, kind, context_inputs)?,
            context(original_load, b, temp, work, kind, context_inputs)?,
        ),
        _ => return Err(Error::UnsupportedChange),
    })
}

// Verifier scans original assignments backwards. No proposer use map, input
// set or forward-frame result is accepted as evidence.
fn check_stability(
    source: &Program,
    load: Point,
    consumer: Point,
    inputs: &BTreeSet<usize>,
    work: &mut Work,
) -> Result<(), Error> {
    if inputs.is_empty() {
        return Ok(());
    }
    for i in (load.instruction..=consumer.instruction).rev() {
        work.charge(1)?;
        for (a, assignment) in source.instructions()[i]
            .assignments
            .iter()
            .enumerate()
            .rev()
        {
            work.charge(1)?;
            if (i, a) <= (load.instruction, load.assignment)
                || (i, a) >= (consumer.instruction, consumer.assignment)
            {
                continue;
            }
            if let Place::Register(r) = assignment.destination
                && inputs.contains(&r.0)
            {
                return Err(Error::UnsupportedChange);
            }
        }
    }
    Ok(())
}
pub fn validate(
    source: &Program,
    candidate: &Program,
    parameters: &[Reg],
) -> Result<Evidence, Error> {
    validate_kind(source, candidate, parameters, ContextKind::Constants)
}
pub fn validate_with_stable_inputs(
    source: &Program,
    candidate: &Program,
    parameters: &[Reg],
) -> Result<Evidence, Error> {
    validate_kind(source, candidate, parameters, ContextKind::StableInputs)
}
fn validate_kind(
    source: &Program,
    candidate: &Program,
    parameters: &[Reg],
    kind: ContextKind,
) -> Result<Evidence, Error> {
    let mut work = Work(MAX_WORK);
    bounded(source, parameters, &mut work)?;
    bounded(candidate, parameters, &mut work)?;
    let changes = changed_assignments(source, candidate, &mut work)?;
    let mut producers = BTreeMap::new();
    let mut consumers = BTreeMap::new();
    for (point, destination, old, new) in changes {
        if matches!(old, Expr::Load { .. }) {
            let mut checked = CheckedContext::default();
            let expression = context(old, new, destination, &mut work, kind, &mut checked)?;
            if checked.holes != 1
                || producers
                    .insert(destination.0, (point, expression, checked.inputs))
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
    for (temp, (load, expression, inputs)) in &producers {
        let (consumer, destination, original) =
            consumers.get(temp).ok_or(Error::UnsupportedChange)?;
        if !load.precedes(*consumer)
            || parameters.contains(temp)
            || !same(expression, original, &mut work)?
        {
            return Err(Error::InvalidTemporary);
        }
        check_stability(source, *load, *consumer, inputs, &mut work)?;
        if inputs.iter().any(|reg| producers.contains_key(reg)) {
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
            inputs: inputs.iter().copied().map(Reg).collect(),
        });
    }
    unique_private(source, producers.keys().copied(), &mut work)?;
    folds.sort_by_key(|f| (f.load_instruction, f.load_assignment));
    Ok(Evidence { folds })
}
