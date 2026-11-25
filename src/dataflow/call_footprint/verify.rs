//! Source-bound checking of closed register contracts, independent of `Local`.
//!
//! The trusted stack boundary is StackAnalysis on the conservative projection
//! built here: ordered original assignments, unknown divide/call outputs, and
//! normal-call RSP restoration. Each assumed restoration is justified by the
//! closed-callee equations and original return/store checks below. Recursive
//! contracts use induction on finite successful calls, not termination claims.
//! IR layout validation and resource/syntax guards are shared infrastructure.
//! Neither the producer's CFG walk, local rejection flags nor propagation is
//! consulted. Source successors include both branch arms and the entry itself,
//! including when a backedge returns to that virtual entry boundary.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    Analysis, MAX_FUNCTION_INSTRUCTIONS, MAX_FUNCTIONS, MAX_INSTRUCTIONS, MAX_STACK_OFFSET, RSP,
    Registers, Work, preflight,
};
use crate::dataflow::stack::StackAnalysis;
use crate::model::ir::{
    AccessKind, Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use crate::model::module_ir::{self, Instruction, Target};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValidationEvidence {
    pub functions: usize,
    pub closed_functions: usize,
    pub reachable_instructions: usize,
    pub call_edges: usize,
}

/// Check claimed closed summaries against original reachable instructions.
///
/// Reads include writes conservatively. Callees are exact direct entry targets;
/// register sets obey local-union-callee equations, with preserved the exact
/// complement of clobbers. These equations certify a sound solution, including
/// recursive SCCs; they do not certify the producer's least fixed point. Opaque
/// functions retain the canonical all-register fallback. Resource exhaustion or
/// any invalid closed claim returns an error atomically, with no evidence.
pub fn validate(
    program: &module_ir::Program,
    candidate: &Analysis,
) -> Result<ValidationEvidence, String> {
    if program.functions().len() > MAX_FUNCTIONS
        || program.instructions().len() > MAX_INSTRUCTIONS
        || candidate.functions.len() != program.functions().len()
        || program.register_count() != module_ir::REGISTER_COUNT
    {
        return Err("call footprint validation source/summary size".into());
    }
    let functions: BTreeMap<_, _> = program.functions().iter().map(|f| (f.address, f)).collect();
    if functions.len() != program.functions().len()
        || functions
            .keys()
            .copied()
            .ne(candidate.functions.iter().map(|f| f.address))
    {
        return Err("call footprint validation function entries".into());
    }
    let mut work = Work::default();
    let mut evidence = ValidationEvidence {
        functions: functions.len(),
        closed_functions: 0,
        reachable_instructions: 0,
        call_edges: 0,
    };
    let all = (1 << module_ir::REGISTER_COUNT) - 1;
    for summary in &candidate.functions {
        let claimed_reads = register_bits(&summary.reads)?;
        let claimed_clobbers = register_bits(&summary.clobbers)?;
        let preserved = register_bits(&summary.preserved)?;
        if summary.callees.windows(2).any(|w| w[0] >= w[1])
            || summary.callees.iter().any(|a| !functions.contains_key(a))
        {
            return Err("call footprint validation callee entries".into());
        }
        if !summary.closed {
            if summary.reason.is_none()
                || claimed_reads != all
                || claimed_clobbers != all
                || preserved != 0
            {
                return Err("call footprint validation opaque fallback".into());
            }
            continue;
        }
        if summary.reason.is_some()
            || preserved != all & !claimed_clobbers
            || claimed_clobbers & (1 << RSP.0) != 0
        {
            return Err("call footprint validation preservation partition".into());
        }
        let function = functions[&summary.address];
        let end = function
            .address
            .checked_add(function.size)
            .ok_or("call footprint validation function overflow")?;
        let instructions = program.instructions();
        let source = &instructions[instructions.partition_point(|i| i.address() < function.address)
            ..instructions.partition_point(|i| i.address() < end)];
        if source.len() > MAX_FUNCTION_INSTRUCTIONS {
            return Err("call footprint validation function size".into());
        }
        preflight(source, module_ir::REGISTER_COUNT, &mut work)?;
        let projected = stack_program(source, function.address, &mut work)?;
        let stack = StackAnalysis::try_analyze(&projected, RSP)
            .ok_or("call footprint validation stack unavailable")?;
        let sites: BTreeMap<_, _> = source.iter().map(|i| (i.address(), i)).collect();
        let mut visited = BTreeSet::new();
        let mut pending = vec![function.address];
        let mut callees = BTreeSet::new();
        let (mut observed_reads, mut writes) = (0, 0);
        while let Some(address) = pending.pop() {
            if !visited.insert(address) {
                continue;
            }
            let instruction = sites
                .get(&address)
                .ok_or("call footprint validation missing original successor")?;
            let next = address
                .checked_add(u64::from(instruction.size()))
                .ok_or("call footprint validation next PC overflow")?;
            let assignments = match instruction {
                Instruction::Core(i) => {
                    match &i.control {
                        Control::Next => pending.push(next),
                        Control::Jump(target) => pending.push(*target),
                        Control::Branch { condition, target } => {
                            observed_reads |= expression_reads(condition);
                            pending.extend([next, *target]);
                        }
                        Control::Return(_) => {
                            return Err("call footprint validation scalar return".into());
                        }
                    }
                    &i.assignments[..]
                }
                Instruction::Vector(i) => {
                    pending.push(next);
                    if let Some(memory) = &i.memory {
                        observed_reads |= expression_reads(&memory.address);
                        if memory.access == AccessKind::Write {
                            check_store(
                                &stack,
                                address,
                                0,
                                &memory.address,
                                u64::from(memory.width),
                                &mut work,
                            )?;
                        }
                    }
                    &i.assignments[..]
                }
                Instruction::Divide { source, width, .. } => {
                    pending.push(next);
                    observed_reads |= expression_reads(source);
                    writes |= 1 << crate::binary::x86::RAX;
                    if *width != Width::U8 {
                        writes |= 1 << crate::binary::x86::RDX;
                    }
                    &[]
                }
                Instruction::Transfer { target, link, .. } => {
                    observed_reads |= 1 << RSP.0;
                    let Target::Value(Expr::Const(callee)) = target else {
                        return Err("call footprint validation unknown call target".into());
                    };
                    if candidate.at(*callee).is_none_or(|s| !s.closed) {
                        return Err("call footprint validation open callee".into());
                    }
                    callees.insert(*callee);
                    let offset = work.offset(&stack, address, 0, &Expr::Register(RSP))?;
                    match link {
                        Some(link)
                            if *link == next
                                && offset.is_some_and(|o| (-MAX_STACK_OFFSET..=0).contains(&o)) =>
                        {
                            pending.push(*link)
                        }
                        None if offset == Some(0) => {}
                        _ => return Err("call footprint validation call link/stack".into()),
                    }
                    &[]
                }
                Instruction::Return { extra_pop, .. } => {
                    observed_reads |= 1 << RSP.0;
                    if *extra_pop != 0
                        || work.offset(&stack, address, 0, &Expr::Register(RSP))? != Some(0)
                    {
                        return Err("call footprint validation return stack".into());
                    }
                    &[]
                }
                Instruction::StoreString { .. } | Instruction::MoveString { .. } => {
                    return Err("call footprint validation unknown memory effect".into());
                }
            };
            for (index, assignment) in assignments.iter().enumerate() {
                observed_reads |= expression_reads(&assignment.value);
                match &assignment.destination {
                    Place::Register(reg) => writes |= 1 << reg.0,
                    Place::Memory {
                        address: destination,
                        width,
                    } => {
                        observed_reads |= expression_reads(destination);
                        check_store(
                            &stack,
                            address,
                            index,
                            destination,
                            width.bytes() as u64,
                            &mut work,
                        )?;
                    }
                }
            }
        }
        observed_reads |= writes;
        writes &= !(1 << RSP.0);
        if callees.iter().copied().ne(summary.callees.iter().copied()) {
            return Err("call footprint validation missing/extra direct callee".into());
        }
        for callee in &callees {
            let summary = candidate
                .at(*callee)
                .ok_or("call footprint validation missing callee")?;
            observed_reads |= register_bits(&summary.reads)?;
            writes |= register_bits(&summary.clobbers)?;
        }
        if claimed_reads != observed_reads || claimed_clobbers != writes {
            return Err("call footprint validation register equations".into());
        }
        evidence.closed_functions += 1;
        evidence.reachable_instructions += visited.len();
        evidence.call_edges += callees.len();
    }
    Ok(evidence)
}

fn register_bits(registers: &[Reg]) -> Result<Registers, String> {
    if registers.iter().any(|r| r.0 >= module_ir::REGISTER_COUNT)
        || registers.windows(2).any(|w| w[0].0 >= w[1].0)
    {
        return Err("call footprint validation register set".into());
    }
    Ok(registers.iter().fold(0, |bits, r| bits | (1 << r.0)))
}

// Expressions have already passed the iterative syntax/depth/work guard.
fn expression_reads(expression: &Expr) -> Registers {
    let mut pending = vec![expression];
    let mut bits = 0;
    while let Some(expression) = pending.pop() {
        match expression {
            Expr::Register(reg) => bits |= 1 << reg.0,
            Expr::Unary(_, value) | Expr::Load { address: value, .. } => pending.push(value),
            Expr::Binary(_, a, b) => pending.extend([a.as_ref(), b.as_ref()]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([condition.as_ref(), taken.as_ref(), not_taken.as_ref()]),
            Expr::Const(_) => {}
        }
    }
    bits
}

fn check_store(
    stack: &StackAnalysis,
    instruction: u64,
    assignment: usize,
    address: &Expr,
    width: u64,
    work: &mut Work,
) -> Result<(), String> {
    let offset = work.offset(stack, instruction, assignment, address)?;
    if !offset.is_some_and(|o| {
        (-MAX_STACK_OFFSET..0).contains(&o) && width > 0 && i128::from(o) + i128::from(width) <= 0
    }) {
        return Err("call footprint validation store touches return slot/unknown memory".into());
    }
    Ok(())
}

// A separate source projection for the shared affine stack analysis. Callee
// register summaries are deliberately not used to invent stack pointer facts.
fn stack_program(source: &[Instruction], entry: u64, work: &mut Work) -> Result<Program, String> {
    let guests = module_ir::REGISTER_COUNT;
    let unknown = Expr::Register(Reg(guests));
    let mut projected = Vec::with_capacity(source.len());
    for original in source {
        let mut instruction = IrInstruction {
            address: original.address(),
            size: original.size(),
            assignments: Vec::new(),
            control: Control::Return(Expr::Const(0)),
        };
        match original {
            Instruction::Core(i) => instruction = i.clone(),
            Instruction::Vector(i) => {
                instruction.assignments = i.assignments.clone();
                instruction.control = Control::Next;
            }
            Instruction::Divide { width, .. } => {
                instruction.assignments.push(Assignment {
                    destination: Reg(crate::binary::x86::RAX).into(),
                    value: unknown.clone(),
                });
                if *width != Width::U8 {
                    instruction.assignments.push(Assignment {
                        destination: Reg(crate::binary::x86::RDX).into(),
                        value: unknown.clone(),
                    });
                }
                instruction.control = Control::Next;
            }
            Instruction::Transfer {
                link: Some(link), ..
            } => {
                instruction.assignments = (0..guests)
                    .filter(|r| *r != RSP.0)
                    .map(|r| Assignment {
                        destination: Reg(r).into(),
                        value: unknown.clone(),
                    })
                    .collect();
                instruction.control = Control::Jump(*link);
            }
            _ => {}
        }
        work.charge(instruction.assignments.len() + 1, "projection")?;
        projected.push(instruction);
    }
    Program::new(entry, guests + 1, projected)
        .map_err(|e| format!("call footprint validation stack control: {e}"))
}

#[cfg(test)]
mod tests;
