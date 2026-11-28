use super::super::load_order::*;
use super::*;
use crate::model::ir::Place;
use std::collections::{BTreeMap, BTreeSet};

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
    with_kind(source, candidate, parameters, ContextKind::Constants)
}
pub fn validate_with_stable_inputs(
    source: &Program,
    candidate: &Program,
    parameters: &[Reg],
) -> Result<Evidence, Error> {
    with_kind(source, candidate, parameters, ContextKind::StableInputs)
}
pub(super) fn with_kind(
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
