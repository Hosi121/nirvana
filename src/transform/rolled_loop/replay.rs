//! Confirm a DAG witness against both actual source control-flow regions.
use super::*;
use crate::model::ir::{BlockExit, MemoryFault, RunReport, RunStatus};
use extraction::live_out::ContinuationOutputs;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplayExit {
    Continuation(u64),
    Returned(u64),
    Fault(MemoryFault),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Replay {
    pub exit: ReplayExit,
    pub registers: Vec<u64>,
    pub memory: Vec<u8>,
    pub trace: Vec<u64>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Counterexample {
    pub dag: Box<region::Counterexample>,
    pub before: Replay,
    pub after: Replay,
}
fn run(
    program: &Program,
    entry: u64,
    stops: &[u64],
    input: &[u64],
    base: u64,
    memory: &[u8],
    rounds: usize,
) -> Result<Replay, UnknownReason> {
    let mut registers = input[..program.register_count()].to_vec();
    let mut memory = memory.to_vec();
    let mut trace = Vec::new();
    let mut pc = entry;
    let limit = program.instructions().len().saturating_mul(rounds + 2);
    for _ in 0..limit {
        let report = program
            .run_block_with_memory(pc, &registers, base, &memory)
            .map_err(|_| UnknownReason::InvalidCounterexample)?;
        registers = report.state.registers;
        memory = report.state.memory;
        trace.extend(report.state.trace);
        let exit = match report.exit {
            BlockExit::Next(next) if stops.contains(&next) => ReplayExit::Continuation(next),
            BlockExit::Next(next) => {
                pc = next;
                continue;
            }
            BlockExit::Returned(value) => ReplayExit::Returned(value),
            BlockExit::Fault(fault) => ReplayExit::Fault(fault),
        };
        return Ok(Replay {
            exit,
            registers,
            memory,
            trace,
        });
    }
    Err(UnknownReason::ReplayLimit)
}
fn matches(
    replay: &Replay,
    dag: &RunReport,
    stops: &[u64],
    capture: Reg,
    outputs: &ContinuationOutputs,
) -> bool {
    if replay.memory != dag.state.memory {
        return false;
    }
    let (tag, captured) = match (&replay.exit, &dag.status) {
        (ReplayExit::Fault(left), RunStatus::Fault(right)) => return left == right,
        (ReplayExit::Continuation(pc), RunStatus::Returned(tag)) => {
            if stops.get(*tag as usize) != Some(pc) {
                return false;
            }
            (*tag, 0)
        }
        (ReplayExit::Returned(value), RunStatus::Returned(tag)) if *tag == stops.len() as u64 => {
            (*tag, *value)
        }
        _ => return false,
    };
    let Some(row) = outputs.returns().iter().find(|row| row.value == tag) else {
        return false;
    };
    row.registers.iter().all(|reg| {
        let value = if *reg == capture {
            Some(&captured)
        } else {
            replay.registers.get(reg.0)
        };
        value == dag.state.registers.get(reg.0)
    })
}
pub(super) fn check(
    proposal: &Proposal,
    dag: Box<region::Counterexample>,
    outputs: &ContinuationOutputs,
) -> Result<Counterexample, UnknownReason> {
    let count = proposal.padded.register_count();
    if dag.before_registers.len() < count || dag.after_registers.len() < count {
        return Err(UnknownReason::InvalidCounterexample);
    }
    let mut input = dag.before_registers.clone();
    for (value, &bits) in input.iter_mut().zip(proposal.before.input_bit_caps()) {
        if bits < 64 {
            *value &= (1u64 << bits) - 1;
        }
    }
    let stops = proposal.envelope.stops();
    let before = run(
        &proposal.padded,
        proposal.envelope.header,
        &stops,
        &input,
        dag.memory_base,
        &dag.memory,
        proposal.rounds,
    )?;
    let after = run(
        &proposal.program,
        proposal.envelope.header,
        &stops,
        &dag.after_registers,
        dag.memory_base,
        &dag.memory,
        proposal.rounds,
    )?;
    if !matches(
        &before,
        &dag.before,
        &stops,
        proposal.before.return_register(),
        outputs,
    ) || !matches(
        &after,
        &dag.after,
        &stops,
        proposal.before.return_register(),
        outputs,
    ) {
        return Err(UnknownReason::InvalidCounterexample);
    }
    Ok(Counterexample { dag, before, after })
}
