//! Repeat a checked one-iteration region and certify that its bound is complete.
use super::*;
use crate::model::ir::BlockExit;
use crate::verification::block_verify::region::{self, Counterexample, Query, Verdict};
use crate::verification::verify::{Solver, UnknownReason};

pub const MODEL_ID: &str = "checked-region-feedback-completion-v1";

mod check;
mod prefix;
pub use prefix::Prefixed;
#[cfg(test)]
mod tests;

/// Bounded copies retain a visible exhaustion path. This value alone certifies
/// projection only; Complete is the additional solver-backed termination gate.
#[derive(Clone, Debug)]
pub struct Unfolding {
    region: Region,
    rounds: usize,
    program: Program,
    copies: Vec<BTreeMap<u64, u64>>,
    flag: Reg,
    exhaustion: u64,
}

/// A checked unfolding whose exhaustion path is unreachable under the region
/// model. Execution ends at a non-feedback continuation, a function Return or
/// the first fault. It certifies this region boundary, not the whole function.
#[derive(Clone, Debug)]
pub struct Complete {
    data: Box<CompleteData>,
}
#[derive(Clone, Debug)]
struct CompleteData {
    program: Program,
    source: Region,
    rounds: usize,
}
impl Complete {
    fn new(program: &Program, source: &Region, rounds: usize) -> Self {
        Self {
            data: Box::new(CompleteData {
                program: program.clone(),
                source: source.clone(),
                rounds,
            }),
        }
    }
    pub fn program(&self) -> &Program {
        &self.data.program
    }
    pub fn source_region(&self) -> &Region {
        &self.data.source
    }
    pub fn rounds(&self) -> usize {
        self.data.rounds
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceReplay {
    pub initial_registers: Vec<u64>,
    pub registers: Vec<u64>,
    pub memory: Vec<u8>,
    pub trace: Vec<u64>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Exhaustion {
    pub witness: Box<Counterexample>,
    pub source: SourceReplay,
    pub rounds: usize,
}
#[derive(Clone, Debug)]
pub enum Completion {
    Complete(Complete),
    BoundExceeded(Box<Exhaustion>),
    Unknown(UnknownReason),
}

impl Unfolding {
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn rounds(&self) -> usize {
        self.rounds
    }
    pub fn source_region(&self) -> &Region {
        &self.region
    }
    pub fn exhaustion_register(&self) -> Reg {
        self.flag
    }
    pub fn validate(&self) -> Result<(), ExtractionError> {
        check::validate(self)
    }
    /// Compare only the fresh flag with an identical DAG whose last mark is 0.
    /// UNSAT means no normal path reaches exhaustion; all fault paths retain
    /// the same effects and first fault. Unknown never creates a Complete.
    pub fn completion_query(&self) -> Result<Query, ExtractionError> {
        self.validate()?;
        flagged_query(&self.program, self.flag, self.exhaustion)
    }

    pub fn check_complete(&self, solver: &Solver) -> Completion {
        let query = match self.completion_query() {
            Ok(query) => query,
            Err(ExtractionError::Region(Error::Limit)) => {
                return Completion::Unknown(UnknownReason::ResourceLimit);
            }
            Err(_) => return Completion::Unknown(UnknownReason::BoundaryMapping),
        };
        match query.check(solver) {
            Verdict::EquivalentUnderModel => {
                Completion::Complete(Complete::new(&self.program, &self.region, self.rounds))
            }
            Verdict::Unknown(reason) => Completion::Unknown(reason),
            Verdict::Counterexample(witness) => match self.replay_source(&witness) {
                Ok(source) => Completion::BoundExceeded(Box::new(Exhaustion {
                    witness,
                    source,
                    rounds: self.rounds,
                })),
                Err(reason) => Completion::Unknown(reason),
            },
        }
    }
    fn replay_source(&self, witness: &Counterexample) -> Result<SourceReplay, UnknownReason> {
        let invalid = || UnknownReason::InvalidCounterexample;
        if witness.before.state.registers[self.flag.0] != 1 {
            return Err(invalid());
        }
        let source = &self.region.source;
        let mut registers = witness.before_registers[..source.register_count()].to_vec();
        for (value, &bits) in registers.iter_mut().zip(&self.region.caps) {
            if bits < 64 {
                *value &= (1u64 << bits) - 1;
            }
        }
        let initial_registers = registers.clone();
        let mut memory = witness.memory.clone();
        let mut trace = Vec::new();
        for _ in 0..self.rounds {
            let mut pc = self.region.entry;
            let mut reached_feedback = false;
            for _ in 0..source.instructions().len() {
                let report = source
                    .run_block_with_memory(pc, &registers, witness.memory_base, &memory)
                    .map_err(|_| invalid())?;
                registers = report.state.registers;
                memory = report.state.memory;
                trace.extend(report.state.trace);
                match report.exit {
                    BlockExit::Next(next) if next == self.region.entry => {
                        reached_feedback = true;
                        break;
                    }
                    BlockExit::Next(next) if !self.region.stops.contains(&next) => pc = next,
                    BlockExit::Next(_) | BlockExit::Returned(_) | BlockExit::Fault(_) => {
                        return Err(invalid());
                    }
                }
            }
            if !reached_feedback {
                return Err(invalid());
            }
        }
        if witness.before.state.registers[..source.register_count()] != registers
            || witness.before.state.memory != memory
        {
            return Err(invalid());
        }
        Ok(SourceReplay {
            initial_registers,
            registers,
            memory,
            trace,
        })
    }
}

/// Compose one-iteration projections at their entry feedback. The prefix and
/// its checked input masks execute once. Later rounds preserve every value
/// carried by the feedback edge. Other continuations and actual Returns keep
/// the original region's disjoint tags and captured return register.
pub fn unfold(region: &Region, rounds: usize) -> Result<Unfolding, ExtractionError> {
    region.validate()?;
    if !region.stops.contains(&region.entry) {
        return Err(ExtractionError::Boundary);
    }
    let count = region.program.register_count();
    let body_count = region.program.instructions().len() - 1;
    if count >= MAX_REGISTERS
        || rounds > region::MAX_INSTRUCTIONS
        || body_count
            .checked_mul(rounds)
            .and_then(|n| n.checked_add(1))
            .is_none_or(|n| n > region::MAX_INSTRUCTIONS)
    {
        return Err(Error::Limit.into());
    }
    let flag = Reg(count);
    let body: Vec<_> = region
        .program
        .instructions()
        .iter()
        .filter(|i| i.address != 0)
        .collect();
    let copies: Vec<BTreeMap<_, _>> = (0..rounds)
        .map(|round| {
            body.iter()
                .enumerate()
                .map(|(n, i)| (i.address, 2 + 2 * (round * body_count + n) as u64))
                .collect()
        })
        .collect();
    let feedback = region.terminals[&region.entry];
    let root = region.body[&region.entry];
    let tag = region
        .stops
        .iter()
        .position(|&pc| pc == region.entry)
        .unwrap() as u64;
    let mut prefix = region.program.instructions()[0].assignments.clone();
    prefix.push(Assignment {
        destination: flag.into(),
        value: Expr::Const(0),
    });
    let first = if rounds == 0 {
        prefix.push(Assignment {
            destination: flag.into(),
            value: Expr::Const(1),
        });
        Control::Return(Expr::Const(tag))
    } else {
        Control::Jump(copies[0][&root])
    };
    let mut instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: prefix,
        control: first,
    }];
    let exhaustion = if rounds == 0 {
        0
    } else {
        copies[rounds - 1][&feedback]
    };
    for (round, copy) in copies.iter().enumerate() {
        for original in &body {
            let mut assignments = original.assignments.clone();
            let control = if original.address == feedback {
                if let Some(next) = copies.get(round + 1) {
                    Control::Jump(next[&root])
                } else {
                    assignments.push(Assignment {
                        destination: flag.into(),
                        value: Expr::Const(1),
                    });
                    original.control.clone()
                }
            } else {
                match &original.control {
                    Control::Jump(to) => Control::Jump(copy[to]),
                    Control::Branch { condition, target } => Control::Branch {
                        condition: condition.clone(),
                        target: copy[target],
                    },
                    Control::Return(value) => Control::Return(value.clone()),
                    Control::Next => return Err(ExtractionError::Projection),
                }
            };
            instructions.push(IrInstruction {
                address: copy[&original.address],
                size: 2,
                assignments,
                control,
            });
        }
    }
    let program =
        Program::new(0, count + 1, instructions).map_err(|_| ExtractionError::Projection)?;
    let result = Unfolding {
        region: region.clone(),
        rounds,
        program,
        copies,
        flag,
        exhaustion,
    };
    result.validate()?;
    Ok(result)
}

/// Both callers check their source correspondence before this bounded clone.
fn flagged_query(program: &Program, flag: Reg, exhaustion: u64) -> Result<Query, ExtractionError> {
    shape::inspect(program)?;
    let mut cleared = program.instructions().to_vec();
    let marker = cleared
        .iter_mut()
        .find(|i| i.address == exhaustion)
        .and_then(|i| i.assignments.last_mut())
        .ok_or(ExtractionError::Projection)?;
    if marker.destination != flag.into() || marker.value != Expr::Const(1) {
        return Err(ExtractionError::Projection);
    }
    marker.value = Expr::Const(0);
    let cleared = Program::new(0, program.register_count(), cleared)
        .map_err(|_| ExtractionError::Projection)?;
    let shared: Vec<_> = (0..program.register_count()).map(Reg).collect();
    Ok(region::query(program, &cleared, &shared, &[flag])?)
}
