//! Preserve entry relations by composing the real prefix with feedback unfolding.
use super::*;
mod check;
#[cfg(test)]
mod tests;
/// An actual source entry prefix followed by a bounded feedback region.
/// Both projections belong to exactly the same Program and terminal interface.
/// The feedback projection accepts arbitrary inputs; the source prefix itself
/// retains initializer, branch, memory and fault semantics on entering it.
#[derive(Clone, Debug)]
pub struct Prefixed {
    prefix: Region,
    repeated: Unfolding,
    program: Program,
    prefix_offset: u64,
    loop_offset: u64,
}
fn relocated(i: &IrInstruction, offset: u64) -> IrInstruction {
    IrInstruction {
        address: i.address + offset,
        size: i.size,
        assignments: i.assignments.clone(),
        control: match &i.control {
            Control::Next => Control::Next,
            Control::Jump(to) => Control::Jump(to + offset),
            Control::Branch { condition, target } => Control::Branch {
                condition: condition.clone(),
                target: target + offset,
            },
            Control::Return(value) => Control::Return(value.clone()),
        },
    }
}
impl Prefixed {
    pub fn new(prefix: &Region, repeated: &Unfolding) -> Result<Self, ExtractionError> {
        prefix.validate()?;
        repeated.validate()?;
        if !prefix.belongs_to(&repeated.region.source)
            || prefix.stops != repeated.region.stops
            || prefix.entry == repeated.region.entry
            || repeated.region.caps.iter().any(|&bits| bits != 64)
        {
            return Err(ExtractionError::Boundary);
        }
        if prefix.program.instructions().len() + repeated.program.instructions().len() + 1
            > region::MAX_INSTRUCTIONS
        {
            return Err(Error::Limit.into());
        }
        let prefix_offset = 1;
        let loop_offset = prefix
            .program
            .instructions()
            .iter()
            .map(|i| i.address + u64::from(i.size))
            .max()
            .unwrap()
            + 2;
        let feedback = prefix.terminals[&repeated.region.entry];
        let mut instructions = vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: repeated.flag.into(),
                value: Expr::Const(0),
            }],
            control: Control::Jump(prefix_offset),
        }];
        for i in prefix.program.instructions() {
            let mut moved = relocated(i, prefix_offset);
            if i.address == feedback {
                moved.control = Control::Jump(loop_offset);
            }
            instructions.push(moved);
        }
        instructions.extend(
            repeated
                .program
                .instructions()
                .iter()
                .map(|i| relocated(i, loop_offset)),
        );
        let program = Program::new(0, repeated.program.register_count(), instructions)
            .map_err(|_| ExtractionError::Projection)?;
        let result = Self {
            prefix: prefix.clone(),
            repeated: repeated.clone(),
            program,
            prefix_offset,
            loop_offset,
        };
        result.validate()?;
        Ok(result)
    }
    pub fn validate(&self) -> Result<(), ExtractionError> {
        check::validate(self)
    }
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn source_region(&self) -> &Region {
        &self.prefix
    }
    pub fn feedback_region(&self) -> &Region {
        &self.repeated.region
    }
    pub fn rounds(&self) -> usize {
        self.repeated.rounds
    }
    pub fn completion_query(&self) -> Result<Query, ExtractionError> {
        self.validate()?;
        flagged_query(
            &self.program,
            self.repeated.flag,
            self.loop_offset + self.repeated.exhaustion,
        )
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
                Completion::Complete(Complete::new(&self.program, &self.prefix, self.rounds()))
            }
            Verdict::Unknown(reason) => Completion::Unknown(reason),
            Verdict::Counterexample(witness) => match self.replay(&witness) {
                Ok(source) => Completion::BoundExceeded(Box::new(Exhaustion {
                    witness,
                    source,
                    rounds: self.rounds(),
                })),
                Err(reason) => Completion::Unknown(reason),
            },
        }
    }
    fn replay(&self, witness: &Counterexample) -> Result<SourceReplay, UnknownReason> {
        let invalid = || UnknownReason::InvalidCounterexample;
        let source = &self.prefix.source;
        let mut registers = witness.before_registers[..source.register_count()].to_vec();
        for (v, &bits) in registers.iter_mut().zip(&self.prefix.caps) {
            if bits < 64 {
                *v &= (1u64 << bits) - 1;
            }
        }
        let initial_registers = registers.clone();
        let mut memory = witness.memory.clone();
        let mut trace = Vec::new();
        let mut pc = self.prefix.entry;
        let mut reached = false;
        for _ in 0..source.instructions().len() {
            let report = source
                .run_block_with_memory(pc, &registers, witness.memory_base, &memory)
                .map_err(|_| invalid())?;
            registers = report.state.registers;
            memory = report.state.memory;
            trace.extend(report.state.trace);
            match report.exit {
                BlockExit::Next(next) if next == self.repeated.region.entry => {
                    reached = true;
                    break;
                }
                BlockExit::Next(next) if !self.prefix.stops.contains(&next) => pc = next,
                _ => return Err(invalid()),
            }
        }
        if !reached {
            return Err(invalid());
        }
        let mut adjusted = witness.clone();
        adjusted.memory = memory;
        adjusted.before_registers[..source.register_count()].copy_from_slice(&registers);
        let mut replay = self.repeated.replay_source(&adjusted)?;
        trace.extend(replay.trace);
        replay.trace = trace;
        replay.initial_registers = initial_registers;
        Ok(replay)
    }
}
