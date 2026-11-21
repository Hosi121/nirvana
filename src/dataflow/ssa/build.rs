//! Pruned register SSA. Phis deliberately remain unsimplified, including on
//! single-predecessor edges, so every live block-entry value has a local name.
use super::*;
use crate::model::ir::Place;
use std::collections::VecDeque;

pub(super) fn build(source: &Program) -> Option<SsaFunction> {
    construct(source).ok()
}

fn construct(source: &Program) -> Result<SsaFunction, SsaError> {
    let mut budget = Budget::new();
    preflight(source, &mut budget)?;
    let cfg = source.cfg();
    let ids: Vec<_> = cfg.reachable_blocks().into_iter().collect();
    let mut indices = vec![usize::MAX; cfg.blocks().len()];
    for (i, id) in ids.iter().enumerate() {
        indices[id.index()] = i;
    }
    let mut successors = vec![Vec::new(); ids.len()];
    let mut predecessors = vec![Vec::new(); ids.len()];
    for (i, id) in ids.iter().enumerate() {
        for edge in &cfg.block(*id).successors {
            budget.spend(1)?;
            let Target::Block(target) = edge.target else {
                return Err(SsaError::Unavailable("unresolved edge"));
            };
            let target = indices[target.index()];
            if !successors[i].contains(&target) {
                successors[i].push(target);
            }
        }
        successors[i].sort_unstable();
        for predecessor in &cfg.block(*id).predecessors {
            budget.spend(1)?;
            let predecessor = indices[predecessor.index()];
            if predecessor != usize::MAX {
                predecessors[i].push(predecessor);
            }
        }
    }

    // Only syntactically active registers consume block-state storage. This
    // includes dead RHSs and the non-selected arm of a Select expression.
    let mut active = vec![false; source.register_count()];
    for id in &ids {
        for ins in &source.instructions()[cfg.block(*id).instructions.clone()] {
            for assignment in &ins.assignments {
                assignment_reads(assignment, &mut budget, &mut |reg| {
                    active[reg.0] = true;
                    Ok(())
                })?;
                if let Place::Register(reg) = assignment.destination {
                    active[reg.0] = true;
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) = &ins.control {
                reads(condition, &mut budget, &mut |reg| {
                    active[reg.0] = true;
                    Ok(())
                })?;
            }
        }
    }
    let registers: Vec<_> = active
        .iter()
        .enumerate()
        .filter_map(|(i, used)| used.then_some(Reg(i)))
        .collect();
    let count = registers.len();
    // Four block matrices, the renaming state, and the raw-to-active mapping.
    // Check the product before allocating any block/register matrix.
    let cells = ids
        .len()
        .checked_mul(count)
        .and_then(|n| n.checked_mul(4))
        .and_then(|n| n.checked_add(count))
        .and_then(|n| n.checked_add(source.register_count()))
        .ok_or(SsaError::Unavailable("state size"))?;
    if cells > MAX_STATE_CELLS {
        return Err(SsaError::Unavailable("state size"));
    }
    budget.spend(cells)?;
    let mut slots = vec![usize::MAX; source.register_count()];
    for (slot, reg) in registers.iter().enumerate() {
        slots[reg.0] = slot;
    }
    let mut used = vec![vec![false; count]; ids.len()];
    let mut defined = vec![vec![false; count]; ids.len()];
    let mut live_in = vec![vec![false; count]; ids.len()];
    let mut live_out = vec![vec![false; count]; ids.len()];
    for (i, id) in ids.iter().enumerate() {
        for ins in &source.instructions()[cfg.block(*id).instructions.clone()] {
            for assignment in &ins.assignments {
                assignment_reads(assignment, &mut budget, &mut |reg| {
                    let slot = slots[reg.0];
                    used[i][slot] |= !defined[i][slot];
                    Ok(())
                })?;
                if let Place::Register(reg) = assignment.destination {
                    defined[i][slots[reg.0]] = true;
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) = &ins.control {
                reads(condition, &mut budget, &mut |reg| {
                    let slot = slots[reg.0];
                    used[i][slot] |= !defined[i][slot];
                    Ok(())
                })?;
            }
        }
    }
    // A predecessor is revisited only when its successor's live-in changes.
    let mut queue: VecDeque<_> = (0..ids.len()).rev().collect();
    let mut queued = vec![true; ids.len()];
    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        budget.spend(
            1 + count
                .checked_mul(successors[i].len() + 1)
                .ok_or(SsaError::Unavailable("work"))?,
        )?;
        let mut changed = false;
        for slot in 0..count {
            let outgoing = successors[i].iter().any(|next| live_in[*next][slot]);
            let incoming = used[i][slot] || (outgoing && !defined[i][slot]);
            live_out[i][slot] = outgoing;
            changed |= incoming != live_in[i][slot];
            live_in[i][slot] = incoming;
        }
        if changed {
            for predecessor in &predecessors[i] {
                budget.spend(1)?;
                if !queued[*predecessor] {
                    queued[*predecessor] = true;
                    queue.push_back(*predecessor);
                }
            }
        }
    }

    let entry = cfg.block(cfg.entry()).start;
    let mut values = Vec::new();
    let mut initial = Vec::new();
    for register in &registers {
        initial.push(value(
            &mut values,
            Definition::Initial {
                register: *register,
            },
            &mut budget,
        )?);
    }
    let mut blocks = Vec::with_capacity(ids.len());
    for (i, id) in ids.iter().enumerate() {
        let start = cfg.block(*id).start;
        let mut phis = Vec::new();
        budget.spend(count)?;
        for (slot, register) in registers.iter().enumerate() {
            if live_in[i][slot] {
                phis.push(value(
                    &mut values,
                    Definition::Phi {
                        block: start,
                        register: *register,
                        inputs: Vec::new(),
                    },
                    &mut budget,
                )?);
            }
        }
        blocks.push(SsaBlock {
            start,
            phis,
            points: Vec::new(),
            exit_values: Vec::new(),
        });
    }
    let mut point_count = 0usize;
    let mut read_count = 0usize;
    for (i, id) in ids.iter().enumerate() {
        let mut current = vec![None; count];
        for phi in &blocks[i].phis {
            let Definition::Phi { register, .. } = values[phi.0] else {
                unreachable!()
            };
            current[slots[register.0]] = Some(*phi);
        }
        for ins in &source.instructions()[cfg.block(*id).instructions.clone()] {
            for (assignment_index, assignment) in ins.assignments.iter().enumerate() {
                cap(&mut point_count, MAX_NODES, "points", &mut budget)?;
                let site = Site {
                    instruction: ins.address,
                    assignment: Some(assignment_index),
                };
                let mut point_reads = Vec::new();
                assignment_reads(assignment, &mut budget, &mut |reg| {
                    record_read(&mut point_reads, reg, &slots, &current, &mut read_count)
                })?;
                let definition = if let Place::Register(register) = assignment.destination {
                    let id = value(
                        &mut values,
                        Definition::Assignment { site, register },
                        &mut budget,
                    )?;
                    current[slots[register.0]] = Some(id);
                    Some(id)
                } else {
                    None
                };
                blocks[i].points.push(PointValues {
                    site,
                    definition,
                    reads: point_reads,
                });
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) = &ins.control {
                cap(&mut point_count, MAX_NODES, "points", &mut budget)?;
                let mut point_reads = Vec::new();
                reads(condition, &mut budget, &mut |reg| {
                    record_read(&mut point_reads, reg, &slots, &current, &mut read_count)
                })?;
                blocks[i].points.push(PointValues {
                    site: Site {
                        instruction: ins.address,
                        assignment: None,
                    },
                    definition: None,
                    reads: point_reads,
                });
            }
        }
        budget.spend(count)?;
        for (slot, register) in registers.iter().enumerate() {
            if live_out[i][slot] {
                blocks[i].exit_values.push(RegisterValue {
                    register: *register,
                    value: current[slot].ok_or(SsaError::Malformed("missing live exit"))?,
                });
            }
        }
    }
    // All predecessor exits now exist, regardless of block order or cycles.
    let mut input_count = 0usize;
    for (i, block) in blocks.iter().enumerate() {
        for phi in &block.phis {
            let Definition::Phi { register, .. } = values[phi.0] else {
                unreachable!()
            };
            let mut inputs = Vec::new();
            if block.start == entry {
                cap(&mut input_count, MAX_PHI_INPUTS, "phi inputs", &mut budget)?;
                inputs.push(PhiInput {
                    predecessor: None,
                    value: initial[slots[register.0]],
                });
            }
            for predecessor in &predecessors[i] {
                cap(&mut input_count, MAX_PHI_INPUTS, "phi inputs", &mut budget)?;
                let pred = &blocks[*predecessor];
                budget.spend(
                    usize::BITS as usize - pred.exit_values.len().leading_zeros() as usize,
                )?;
                let slot = pred
                    .exit_values
                    .binary_search_by_key(&register.0, |rv| rv.register.0)
                    .map_err(|_| SsaError::Malformed("missing phi source"))?;
                inputs.push(PhiInput {
                    predecessor: Some(pred.start),
                    value: pred.exit_values[slot].value,
                });
            }
            let Definition::Phi { inputs: stored, .. } = &mut values[phi.0] else {
                unreachable!()
            };
            *stored = inputs;
        }
    }
    Ok(SsaFunction {
        entry,
        register_count: source.register_count(),
        values,
        blocks,
    })
}

fn value(
    values: &mut Vec<Definition>,
    definition: Definition,
    budget: &mut Budget,
) -> Result<ValueId, SsaError> {
    budget.spend(1)?;
    if values.len() >= MAX_VALUES {
        return Err(SsaError::Unavailable("values"));
    }
    let id = ValueId(values.len());
    values.push(definition);
    Ok(id)
}
fn cap(
    count: &mut usize,
    limit: usize,
    label: &'static str,
    budget: &mut Budget,
) -> Result<(), SsaError> {
    budget.spend(1)?;
    if *count >= limit {
        return Err(SsaError::Unavailable(label));
    }
    *count += 1;
    Ok(())
}
fn record_read(
    output: &mut Vec<RegisterValue>,
    reg: Reg,
    slots: &[usize],
    current: &[Option<ValueId>],
    count: &mut usize,
) -> Result<(), SsaError> {
    if *count >= MAX_NODES {
        return Err(SsaError::Unavailable("register reads"));
    }
    let value = current[slots[reg.0]].ok_or(SsaError::Malformed("missing read definition"))?;
    *count += 1;
    output.push(RegisterValue {
        register: reg,
        value,
    });
    Ok(())
}
fn assignment_reads(
    assignment: &crate::model::ir::Assignment,
    budget: &mut Budget,
    visit: &mut impl FnMut(Reg) -> Result<(), SsaError>,
) -> Result<(), SsaError> {
    if let Place::Memory { address, .. } = &assignment.destination {
        reads(address, budget, visit)?;
    }
    reads(&assignment.value, budget, visit)
}
fn reads(
    expr: &Expr,
    budget: &mut Budget,
    visit: &mut impl FnMut(Reg) -> Result<(), SsaError>,
) -> Result<(), SsaError> {
    budget.spend(1)?;
    match expr {
        Expr::Register(reg) => visit(*reg)?,
        Expr::Const(_) => {}
        Expr::Binary(_, left, right) => {
            reads(left, budget, visit)?;
            reads(right, budget, visit)?;
        }
        Expr::Load { address, .. } => reads(address, budget, visit)?,
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            reads(condition, budget, visit)?;
            reads(taken, budget, visit)?;
            reads(not_taken, budget, visit)?;
        }
    }
    Ok(())
}
