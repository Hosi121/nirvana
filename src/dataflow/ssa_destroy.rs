//! Checked phi destruction with canonical register mirrors and original steps.
//!
//! Local storage is additional to the original register file. Every successful
//! source register assignment updates its canonical register immediately. Edge
//! copies are pure assignments on the existing predecessor instruction. Branch
//! conditions are captured before predicated copies, retaining checked memory
//! order, lazy expressions, fault state and instruction budgets.

use std::collections::{BTreeMap, BTreeSet};

use crate::dataflow::parallel_copy::{self, Copy, Schedule};
use crate::dataflow::ssa::{Definition, PointValues, Site, SsaFunction};
use crate::dataflow::ssa_locals;
use crate::model::ir::{self, Assignment, Control, Expr, IrInstruction, Place, Program, Reg};

const MAX_EDGE_COPIES: usize = 524_288;
const MAX_LOWERED_ASSIGNMENTS: usize = 1_048_576;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EdgeCopies {
    pub from: Option<u64>,
    pub to: u64,
    pub parallel: Vec<Copy>,
    pub schedule: Schedule,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Stats {
    pub ssa_values: usize,
    pub locals: usize,
    pub phi_inputs: usize,
    pub edge_copies: usize,
    pub temporary_edges: usize,
    pub eliminated_local_copies: usize,
    pub mirrored_register_writes: usize,
}

#[derive(Clone, Debug)]
pub struct Recovery {
    pub plan: ssa_locals::Plan,
    pub edges: Vec<EdgeCopies>,
    pub stats: Stats,
}

#[derive(Clone, Debug)]
pub struct LoweredFunction {
    program: Program,
    raw_registers: usize,
    initializations: Vec<(usize, Reg)>,
    plan: ssa_locals::Plan,
    edges: Vec<EdgeCopies>,
    entry: u64,
    stats: Stats,
}

impl LoweredFunction {
    /// Additional registers require `initial_state` before direct IR execution.
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn plan(&self) -> &ssa_locals::Plan {
        &self.plan
    }
    pub fn edges(&self) -> &[EdgeCopies] {
        &self.edges
    }
    pub fn stats(&self) -> Stats {
        self.stats
    }
    pub fn into_recovery(self) -> Recovery {
        Recovery {
            plan: self.plan,
            edges: self.edges,
            stats: self.stats,
        }
    }

    pub fn initial_state(&self, input: &[u64]) -> Result<Vec<u64>, ir::ExecutionError> {
        if input.len() != self.raw_registers {
            return Err(ir::ExecutionError::RegisterCount {
                expected: self.raw_registers,
                actual: input.len(),
            });
        }
        let mut state = vec![0; self.program.register_count()];
        state[..input.len()].copy_from_slice(input);
        for &(local, register) in &self.initializations {
            state[self.raw_registers + local] = input[register.0];
        }
        if let Some(edge) = self
            .edges
            .iter()
            .find(|e| e.from.is_none() && e.to == self.entry)
        {
            for copy in &edge.schedule.copies {
                state[self.raw_registers + copy.destination] =
                    state[self.raw_registers + copy.source];
            }
        }
        Ok(state)
    }

    /// Execute lowered storage while returning exactly the canonical source
    /// registers, RAM, first fault, instruction position and original trace.
    pub fn run_with_memory(
        &self,
        input: &[u64],
        base: u64,
        memory: &[u8],
        steps: usize,
    ) -> Result<ir::RunReport, ir::ExecutionError> {
        let state = self.initial_state(input)?;
        let mut report = self.program.run_with_memory(&state, base, memory, steps)?;
        report.state.registers.truncate(self.raw_registers);
        Ok(report)
    }

    pub(crate) fn source_register_count(&self) -> usize {
        self.raw_registers
    }

    pub(crate) fn initializations(&self) -> &[(usize, Reg)] {
        &self.initializations
    }

    pub(crate) fn entry(&self) -> u64 {
        self.entry
    }
}

pub fn lower(
    source: &Program,
    graph: &SsaFunction,
    excluded_copies: &BTreeSet<Site>,
) -> Result<LoweredFunction, String> {
    let plan = ssa_locals::analyze(source, graph, excluded_copies).map_err(|e| e.to_string())?;
    lower_with_plan(source, graph, plan)
}

pub fn lower_with_plan(
    source: &Program,
    graph: &SsaFunction,
    plan: ssa_locals::Plan,
) -> Result<LoweredFunction, String> {
    ssa_locals::validate(source, graph, &plan).map_err(|e| e.to_string())?;
    let raw = source.register_count();
    let entry = graph.entry;
    let mut stats = Stats {
        ssa_values: graph.values.len(),
        locals: plan.local_count,
        ..Default::default()
    };
    let mut parallel: BTreeMap<(Option<u64>, u64), Vec<Copy>> = BTreeMap::new();
    parallel.insert((None, entry), Vec::new());
    let mut initializations = Vec::new();
    for (id, definition) in graph.values.iter().enumerate() {
        match definition {
            Definition::Initial { register } => {
                initializations.push((plan.by_value[id], *register))
            }
            Definition::Phi { block, inputs, .. } => {
                stats.phi_inputs += inputs.len();
                for input in inputs {
                    let destination = plan.by_value[id];
                    let source = plan.by_value[input.value.0];
                    if destination != source {
                        parallel
                            .entry((input.predecessor, *block))
                            .or_default()
                            .push(Copy {
                                destination,
                                source,
                            });
                    }
                }
            }
            _ => {}
        }
    }
    let mut edges = Vec::new();
    for ((from, to), mut parallel) in parallel {
        parallel.sort_unstable_by_key(|c| c.destination);
        let schedule = parallel_copy::schedule(plan.local_count, &parallel)?;
        parallel_copy::validate(plan.local_count, &parallel, &schedule.copies)?;
        stats.edge_copies = stats
            .edge_copies
            .checked_add(schedule.copies.len())
            .filter(|n| *n <= MAX_EDGE_COPIES)
            .ok_or("phi edge-copy limit")?;
        stats.temporary_edges += usize::from(schedule.uses_temporary);
        edges.push(EdgeCopies {
            from,
            to,
            parallel,
            schedule,
        });
    }
    let edge_map: BTreeMap<_, _> = edges.iter().map(|e| ((e.from, e.to), e)).collect();
    let point_map: BTreeMap<_, _> = graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect();
    let reachable: BTreeSet<_> = source
        .cfg()
        .reachable_blocks()
        .iter()
        .flat_map(|id| source.cfg().block(*id).instructions.clone())
        .collect();
    let mut owners = vec![0; source.instructions().len()];
    let mut last = vec![false; source.instructions().len()];
    for block in source.cfg().blocks() {
        for index in block.instructions.clone() {
            owners[index] = block.start;
        }
        last[block.instructions.end - 1] = true;
    }
    let mut instructions = Vec::new();
    let mut assignment_count = 0usize;
    for (index, instruction) in source.instructions().iter().enumerate() {
        if !reachable.contains(&index) {
            instructions.push(instruction.clone());
            continue;
        }
        let mut assignments = Vec::new();
        for (ordinal, original) in instruction.assignments.iter().enumerate() {
            let site = Site {
                instruction: instruction.address,
                assignment: Some(ordinal),
            };
            let point = point_map.get(&site).ok_or("missing SSA assignment")?;
            let mut reads = Reads {
                point,
                at: 0,
                raw,
                plan: &plan,
            };
            match &original.destination {
                Place::Register(register) => {
                    let destination =
                        Reg(raw
                            + plan.by_value[point.definition.ok_or("missing SSA definition")?.0]);
                    let value = reads.expression(&original.value)?;
                    if value == Expr::Register(destination) {
                        stats.eliminated_local_copies += 1;
                    } else {
                        assignments.push(Assignment {
                            destination: destination.into(),
                            value,
                        });
                    }
                    assignments.push(Assignment {
                        destination: (*register).into(),
                        value: Expr::Register(destination),
                    });
                    stats.mirrored_register_writes += 1;
                }
                Place::Memory { address, width } => assignments.push(Assignment {
                    destination: Place::Memory {
                        address: reads.expression(address)?,
                        width: *width,
                    },
                    value: reads.expression(&original.value)?,
                }),
            }
            if reads.at != point.reads.len() {
                return Err("unconsumed SSA assignment reads".into());
            }
        }
        let mut control = match &instruction.control {
            Control::Return(value)
            | Control::Branch {
                condition: value, ..
            } => {
                let site = Site {
                    instruction: instruction.address,
                    assignment: None,
                };
                let point = point_map.get(&site).ok_or("missing SSA control")?;
                let mut reads = Reads {
                    point,
                    at: 0,
                    raw,
                    plan: &plan,
                };
                let value = reads.expression(value)?;
                if reads.at != point.reads.len() {
                    return Err("unconsumed SSA control reads".into());
                }
                match instruction.control {
                    Control::Return(_) => Control::Return(value),
                    Control::Branch { target, .. } => Control::Branch {
                        condition: value,
                        target,
                    },
                    _ => unreachable!(),
                }
            }
            other => other.clone(),
        };
        if last[index] {
            let from = Some(owners[index]);
            match control {
                Control::Branch { condition, target } => {
                    let condition_register = Reg(raw + plan.local_count + 1);
                    assignments.push(Assignment {
                        destination: condition_register.into(),
                        value: condition,
                    });
                    let not_taken = instruction.address + u64::from(instruction.size);
                    if target == not_taken {
                        append_edge(
                            &mut assignments,
                            edge_map.get(&(from, target)).copied(),
                            raw,
                            None,
                        );
                    } else {
                        append_edge(
                            &mut assignments,
                            edge_map.get(&(from, target)).copied(),
                            raw,
                            Some((condition_register, true)),
                        );
                        append_edge(
                            &mut assignments,
                            edge_map.get(&(from, not_taken)).copied(),
                            raw,
                            Some((condition_register, false)),
                        );
                    }
                    control = Control::Branch {
                        condition: Expr::Register(condition_register),
                        target,
                    };
                }
                Control::Jump(target) => append_edge(
                    &mut assignments,
                    edge_map.get(&(from, target)).copied(),
                    raw,
                    None,
                ),
                Control::Next => {
                    let target = instruction.address + u64::from(instruction.size);
                    append_edge(
                        &mut assignments,
                        edge_map.get(&(from, target)).copied(),
                        raw,
                        None,
                    );
                }
                Control::Return(_) => {}
            }
        }
        assignment_count = assignment_count
            .checked_add(assignments.len())
            .filter(|n| *n <= MAX_LOWERED_ASSIGNMENTS)
            .ok_or("SSA lowering assignment limit")?;
        instructions.push(IrInstruction {
            address: instruction.address,
            size: instruction.size,
            assignments,
            control,
        });
    }
    let program =
        Program::new(entry, raw + plan.local_count + 2, instructions).map_err(|e| e.to_string())?;
    Ok(LoweredFunction {
        program,
        raw_registers: raw,
        initializations,
        plan,
        edges,
        entry,
        stats,
    })
}

fn append_edge(
    out: &mut Vec<Assignment>,
    edge: Option<&EdgeCopies>,
    raw: usize,
    guard: Option<(Reg, bool)>,
) {
    if let Some(edge) = edge {
        for copy in &edge.schedule.copies {
            let destination = Reg(raw + copy.destination);
            let value = Expr::Register(Reg(raw + copy.source));
            let value = match guard {
                Some((condition, true)) => Expr::select(
                    Expr::Register(condition),
                    value,
                    Expr::Register(destination),
                ),
                Some((condition, false)) => Expr::select(
                    Expr::Register(condition),
                    Expr::Register(destination),
                    value,
                ),
                None => value,
            };
            out.push(Assignment {
                destination: destination.into(),
                value,
            });
        }
    }
}

struct Reads<'a> {
    point: &'a PointValues,
    at: usize,
    raw: usize,
    plan: &'a ssa_locals::Plan,
}
impl Reads<'_> {
    fn expression(&mut self, expression: &Expr) -> Result<Expr, String> {
        Ok(match expression {
            Expr::Const(value) => Expr::Const(*value),
            Expr::Register(register) => {
                let read = self.point.reads.get(self.at).ok_or("missing SSA read")?;
                self.at += 1;
                if read.register != *register {
                    return Err("SSA read order mismatch".into());
                }
                Expr::Register(Reg(self.raw + self.plan.by_value[read.value.0]))
            }
            Expr::Binary(op, a, b) => Expr::binary(*op, self.expression(a)?, self.expression(b)?),
            Expr::Load { address, width } => Expr::load(self.expression(address)?, *width),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Expr::select(
                self.expression(condition)?,
                self.expression(taken)?,
                self.expression(not_taken)?,
            ),
        })
    }
}
