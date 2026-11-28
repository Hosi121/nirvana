use super::super::load_order::*;
use super::*;
use crate::model::ir::Place;
use std::collections::BTreeSet;

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
        Expr::Register(r) if kind != ContextKind::Constants => {
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
// Proposal-only effect scan. The verifier inspects the source independently.
fn proposed_producer(e: &Expr, kind: ContextKind, work: &mut Work) -> Result<bool, Error> {
    if matches!(e, Expr::Load { .. }) {
        return Ok(true);
    }
    if kind != ContextKind::MemoryValues {
        return Ok(false);
    }
    let mut pending = vec![e];
    while let Some(e) = pending.pop() {
        work.charge(1)?;
        match e {
            Expr::Load { .. } => return Ok(true),
            Expr::Unary(_, x) => pending.push(x),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    Ok(false)
}
pub fn propose_memory_values(source: &Program, parameters: &[Reg]) -> Option<Program> {
    with_kind(source, parameters, ContextKind::MemoryValues)
}
pub fn propose(source: &Program, parameters: &[Reg]) -> Option<Program> {
    with_kind(source, parameters, ContextKind::Constants)
}
pub fn propose_with_stable_inputs(source: &Program, parameters: &[Reg]) -> Option<Program> {
    with_kind(source, parameters, ContextKind::StableInputs)
}
pub(super) fn with_kind(
    source: &Program,
    parameters: &[Reg],
    kind: ContextKind,
) -> Option<Program> {
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
                if !proposed_producer(&assignment.value, kind, &mut work).ok()?
                    || parameters.contains(&temp.0)
                {
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
