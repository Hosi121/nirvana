//! Versioned concrete observation contracts. A matching run is evidence for
//! one corresponding input, never a universal equivalence certificate.

use crate::model::ir::{RunReport, RunStatus};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Profile {
    FullIrState,
    ReturnMemory,
    ReturnMemoryTrace,
}

/// Every profile observes complete guest memory and exact modeled faults.
/// There is intentionally no option to ignore memory regions or faults.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Contract {
    profile: Profile,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Comparison {
    MatchForInput,
    Counterexample(Difference),
    Inconclusive {
        left_suspended: bool,
        right_suspended: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Difference {
    MemoryMappings {
        left: Option<crate::model::memory::Layout>,
        right: Option<crate::model::memory::Layout>,
    },
    Status {
        left: RunStatus,
        right: RunStatus,
    },
    MemoryLayout {
        left_base: u64,
        right_base: u64,
        left_size: usize,
        right_size: usize,
    },
    MemoryByte {
        offset: usize,
        left: u8,
        right: u8,
    },
    RegisterCount {
        left: usize,
        right: usize,
    },
    Register {
        index: usize,
        left: u64,
        right: u64,
    },
    InstructionTrace {
        index: usize,
        left: Option<u64>,
        right: Option<u64>,
    },
}

impl Contract {
    pub const fn full_ir_state() -> Self {
        Self {
            profile: Profile::FullIrState,
        }
    }
    pub const fn return_memory() -> Self {
        Self {
            profile: Profile::ReturnMemory,
        }
    }
    pub const fn with_instruction_trace(self) -> Self {
        match self.profile {
            Profile::ReturnMemory => Self {
                profile: Profile::ReturnMemoryTrace,
            },
            _ => self,
        }
    }
    pub const fn id(self) -> &'static str {
        match self.profile {
            Profile::FullIrState => "full-ir-state-v1",
            Profile::ReturnMemory => "return-memory-v1",
            Profile::ReturnMemoryTrace => "return-memory-trace-v1",
        }
    }

    /// The caller must supply runs from corresponding initial states.
    /// A budget cutoff on either side is inconclusive: a different intermediate
    /// state alone is not a counterexample to final-state equivalence.
    pub fn compare(self, left: &RunReport, right: &RunReport) -> Comparison {
        let left_suspended = left.status == RunStatus::Suspended;
        let right_suspended = right.status == RunStatus::Suspended;
        if left_suspended || right_suspended {
            return Comparison::Inconclusive {
                left_suspended,
                right_suspended,
            };
        }
        let difference = if left.status != right.status {
            Some(Difference::Status {
                left: left.status.clone(),
                right: right.status.clone(),
            })
        } else if left.state.memory_layout != right.state.memory_layout {
            Some(Difference::MemoryMappings {
                left: left.state.memory_layout.clone(),
                right: right.state.memory_layout.clone(),
            })
        } else if left.state.memory_base != right.state.memory_base
            || left.state.memory.len() != right.state.memory.len()
        {
            Some(Difference::MemoryLayout {
                left_base: left.state.memory_base,
                right_base: right.state.memory_base,
                left_size: left.state.memory.len(),
                right_size: right.state.memory.len(),
            })
        } else if let Some(offset) = left
            .state
            .memory
            .iter()
            .zip(&right.state.memory)
            .position(|(l, r)| l != r)
        {
            Some(Difference::MemoryByte {
                offset,
                left: left.state.memory[offset],
                right: right.state.memory[offset],
            })
        } else if self.profile == Profile::FullIrState
            && left.state.registers.len() != right.state.registers.len()
        {
            Some(Difference::RegisterCount {
                left: left.state.registers.len(),
                right: right.state.registers.len(),
            })
        } else if self.profile == Profile::FullIrState
            && let Some(index) = left
                .state
                .registers
                .iter()
                .zip(&right.state.registers)
                .position(|(l, r)| l != r)
        {
            Some(Difference::Register {
                index,
                left: left.state.registers[index],
                right: right.state.registers[index],
            })
        } else if self.profile != Profile::ReturnMemory && left.state.trace != right.state.trace {
            let index = left
                .state
                .trace
                .iter()
                .zip(&right.state.trace)
                .position(|(l, r)| l != r)
                .unwrap_or(left.state.trace.len().min(right.state.trace.len()));
            Some(Difference::InstructionTrace {
                index,
                left: left.state.trace.get(index).copied(),
                right: right.state.trace.get(index).copied(),
            })
        } else {
            None
        };
        match difference {
            Some(difference) => Comparison::Counterexample(difference),
            None => Comparison::MatchForInput,
        }
    }
}
