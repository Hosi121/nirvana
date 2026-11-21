//! Completed observations for the explicit puts outcome model.
use crate::model::effects::{Report, Status};
use crate::model::observe::Difference as CoreDifference;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Contract {
    full: bool,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Difference {
    Status {
        left: Status,
        right: Status,
    },
    Core(CoreDifference),
    OutputByte {
        index: usize,
        left: Option<u8>,
        right: Option<u8>,
    },
    Consumed {
        left: usize,
        right: usize,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Comparison {
    MatchForInput,
    Counterexample(Difference),
    Inconclusive { left: Status, right: Status },
}
impl Contract {
    pub const fn return_memory_output() -> Self {
        Self { full: false }
    }
    pub const fn full_ir_state() -> Self {
        Self { full: true }
    }
    pub const fn id(self) -> &'static str {
        if self.full {
            "puts-full-ir-state-output-v1"
        } else {
            "puts-return-memory-output-v1"
        }
    }
    /// Compare corresponding initial states with the same import identity and
    /// outcome tape. Budgets, invalid/missing outcomes and unmodeled targets
    /// leave the final observation inconclusive, even if both stops agree.
    pub fn compare(self, left: &Report, right: &Report) -> Comparison {
        if !matches!(left.status, Status::Returned(_) | Status::Fault(_))
            || !matches!(right.status, Status::Returned(_) | Status::Fault(_))
        {
            return Comparison::Inconclusive {
                left: left.status.clone(),
                right: right.status.clone(),
            };
        }
        if left.status != right.status {
            return Comparison::Counterexample(Difference::Status {
                left: left.status.clone(),
                right: right.status.clone(),
            });
        }
        // Borrow state directly rather than copying RAM to adapt report types.
        let a = &left.state;
        let b = &right.state;
        let difference = if a.memory_layout != b.memory_layout {
            Some(CoreDifference::MemoryMappings {
                left: a.memory_layout.clone(),
                right: b.memory_layout.clone(),
            })
        } else if a.memory_base != b.memory_base || a.memory.len() != b.memory.len() {
            Some(CoreDifference::MemoryLayout {
                left_base: a.memory_base,
                right_base: b.memory_base,
                left_size: a.memory.len(),
                right_size: b.memory.len(),
            })
        } else if let Some(offset) = a.memory.iter().zip(&b.memory).position(|(a, b)| a != b) {
            Some(CoreDifference::MemoryByte {
                offset,
                left: a.memory[offset],
                right: b.memory[offset],
            })
        } else if self.full && a.registers.len() != b.registers.len() {
            Some(CoreDifference::RegisterCount {
                left: a.registers.len(),
                right: b.registers.len(),
            })
        } else if self.full
            && let Some(index) = a
                .registers
                .iter()
                .zip(&b.registers)
                .position(|(a, b)| a != b)
        {
            Some(CoreDifference::Register {
                index,
                left: a.registers[index],
                right: b.registers[index],
            })
        } else if self.full && a.trace != b.trace {
            let index = a
                .trace
                .iter()
                .zip(&b.trace)
                .position(|(a, b)| a != b)
                .unwrap_or(a.trace.len().min(b.trace.len()));
            Some(CoreDifference::InstructionTrace {
                index,
                left: a.trace.get(index).copied(),
                right: b.trace.get(index).copied(),
            })
        } else {
            None
        };
        if let Some(difference) = difference {
            return Comparison::Counterexample(Difference::Core(difference));
        }
        if left.output != right.output {
            let index = left
                .output
                .iter()
                .zip(&right.output)
                .position(|(a, b)| a != b)
                .unwrap_or(left.output.len().min(right.output.len()));
            return Comparison::Counterexample(Difference::OutputByte {
                index,
                left: left.output.get(index).copied(),
                right: right.output.get(index).copied(),
            });
        }
        if left.consumed != right.consumed {
            return Comparison::Counterexample(Difference::Consumed {
                left: left.consumed,
                right: right.consumed,
            });
        }
        Comparison::MatchForInput
    }
}
