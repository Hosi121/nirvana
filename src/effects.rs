//! Explicit external calls over the checked integer IR.
//!
//! A puts stub is a guest address, never a host function pointer. Its output,
//! return bits, volatile registers and flags come from the supplied outcome
//! tape; in particular, this model does not assume a particular libc return.

use std::fmt;

use crate::cfg::Cfg;
use crate::ir::{Control, Expr, IrInstruction, Place, ProgramError, Reg};

mod run;

pub const MODEL_ID: &str = "puts-byte-output-tape-v1";

pub const VOLATILE_REGISTERS: [usize; 14] = [0, 1, 2, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20];

const MAX_INSTRUCTIONS: usize = 16_384;
const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 128;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallTarget {
    Direct(u64),
    Register(Reg),
    /// Read a little-endian target pointer from this guest address.
    Memory(u64),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallInstruction {
    pub address: u64,
    pub size: u32,
    pub target: CallTarget,
    pub tail: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Instruction {
    Core(IrInstruction),
    Call(CallInstruction),
}

impl Instruction {
    pub fn address(&self) -> u64 {
        match self {
            Self::Core(instruction) => instruction.address,
            Self::Call(instruction) => instruction.address,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    instructions: Vec<Instruction>,
    // This is a validation/control skeleton. Calls remain explicit above;
    // executing this private skeleton would discard their effects.
    shape: crate::ir::Program,
    entry: u64,
    puts_address: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    RegisterCount { count: usize },
    InstructionLimit { count: usize, maximum: usize },
    NodeLimit { maximum: usize },
    DepthLimit { maximum: usize },
    Program(ProgramError),
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegisterCount { count } => {
                write!(f, "effects require 21..=4096 registers, got {count}")
            }
            Self::InstructionLimit { count, maximum } => {
                write!(f, "effects instruction count {count} exceeds {maximum}")
            }
            Self::NodeLimit { maximum } => write!(f, "effects syntax exceeds {maximum} nodes"),
            Self::DepthLimit { maximum } => {
                write!(f, "effects expression depth exceeds {maximum}")
            }
            Self::Program(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for BuildError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Output {
    All,
    Prefix(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PutsOutcome {
    /// In VOLATILE_REGISTERS order, including full RAX and five Boolean flags.
    pub registers: [u64; 14],
    pub output: Output,
}

impl PutsOutcome {
    /// An explicit input convenience, not an assumption about libc behavior.
    pub fn success(result: u64) -> Self {
        let mut registers = [0; 14];
        registers[0] = result;
        Self {
            registers,
            output: Output::All,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    pub instructions: usize,
    pub external_reads: usize,
    pub output_bytes: usize,
    pub calls: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            instructions: 100_000,
            external_reads: 1_048_576,
            output_bytes: 1_048_576,
            calls: 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Suspend {
    Instructions,
    Reads,
    Output,
    Calls,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Status {
    Returned(u64),
    Fault(crate::ir::MemoryFault),
    UnknownTarget(u64),
    EnvironmentExhausted,
    InvalidOutcome,
    /// Budget exhaustion is an incomplete observation, not a return or proof.
    Suspended(Suspend),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Report {
    pub status: Status,
    pub state: crate::ir::Snapshot,
    pub output: Vec<u8>,
    pub consumed: usize,
}

impl Program {
    pub fn new(
        entry: u64,
        register_count: usize,
        mut instructions: Vec<Instruction>,
        puts_address: u64,
    ) -> Result<Self, BuildError> {
        // Never clone or recursively inspect unbounded caller syntax. On
        // rejection, dismantle it iteratively as well (even a Drop can recurse).
        if let Err(error) = validate_syntax(register_count, &instructions) {
            discard(instructions);
            return Err(error);
        }
        let skeleton = instructions
            .iter()
            .map(|instruction| match instruction {
                Instruction::Core(instruction) => instruction.clone(),
                Instruction::Call(call) => IrInstruction {
                    address: call.address,
                    size: call.size,
                    assignments: Vec::new(),
                    control: if call.tail {
                        Control::Return(Expr::Register(Reg(0)))
                    } else {
                        Control::Next
                    },
                },
            })
            .collect();
        let shape = crate::ir::Program::new(entry, register_count, skeleton)
            .map_err(BuildError::Program)?;
        instructions.sort_by_key(Instruction::address);
        Ok(Self {
            instructions,
            shape,
            entry,
            puts_address,
        })
    }

    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }

    pub fn cfg(&self) -> &Cfg {
        self.shape().cfg()
    }

    pub fn register_count(&self) -> usize {
        self.shape().register_count()
    }

    pub fn entry(&self) -> u64 {
        self.entry
    }

    pub fn puts_address(&self) -> u64 {
        self.puts_address
    }

    pub(crate) fn shape(&self) -> &crate::ir::Program {
        &self.shape
    }
}

fn validate_syntax(count: usize, instructions: &[Instruction]) -> Result<(), BuildError> {
    if !(21..=4096).contains(&count) {
        return Err(BuildError::RegisterCount { count });
    }
    if instructions.len() > MAX_INSTRUCTIONS {
        return Err(BuildError::InstructionLimit {
            count: instructions.len(),
            maximum: MAX_INSTRUCTIONS,
        });
    }
    let mut nodes = instructions.len();
    let mut expressions = Vec::new();
    for instruction in instructions {
        let address = instruction.address();
        let check_register = |register: Reg| {
            if register.0 >= count {
                Err(BuildError::Program(ProgramError::InvalidRegister {
                    address,
                    register,
                    count,
                }))
            } else {
                Ok(())
            }
        };
        match instruction {
            Instruction::Call(call) => {
                if let CallTarget::Register(register) = call.target {
                    check_register(register)?;
                }
            }
            Instruction::Core(instruction) => {
                for assignment in &instruction.assignments {
                    nodes += 1;
                    if nodes > MAX_NODES {
                        return Err(BuildError::NodeLimit { maximum: MAX_NODES });
                    }
                    match &assignment.destination {
                        Place::Register(register) => check_register(*register)?,
                        Place::Memory { address, .. } => expressions.push((address, 1)),
                    }
                    expressions.push((&assignment.value, 1));
                }
                match &instruction.control {
                    Control::Branch { condition, .. } => expressions.push((condition, 1)),
                    Control::Return(value) => expressions.push((value, 1)),
                    _ => {}
                }
            }
        }
        while let Some((expression, depth)) = expressions.pop() {
            nodes += 1;
            if nodes > MAX_NODES {
                return Err(BuildError::NodeLimit { maximum: MAX_NODES });
            }
            if depth > MAX_DEPTH {
                return Err(BuildError::DepthLimit { maximum: MAX_DEPTH });
            }
            match expression {
                Expr::Const(_) => {}
                Expr::Register(register) => check_register(*register)?,
                Expr::Binary(_, left, right) => {
                    expressions.push((left, depth + 1));
                    expressions.push((right, depth + 1));
                }
                Expr::Load { address, .. } => expressions.push((address, depth + 1)),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    expressions.push((condition, depth + 1));
                    expressions.push((taken, depth + 1));
                    expressions.push((not_taken, depth + 1));
                }
            }
        }
    }
    Ok(())
}

fn discard(instructions: Vec<Instruction>) {
    let mut expressions = Vec::new();
    for instruction in instructions {
        if let Instruction::Core(instruction) = instruction {
            for assignment in instruction.assignments {
                if let Place::Memory { address, .. } = assignment.destination {
                    expressions.push(address);
                }
                expressions.push(assignment.value);
            }
            match instruction.control {
                Control::Branch { condition, .. } => expressions.push(condition),
                Control::Return(value) => expressions.push(value),
                _ => {}
            }
        }
    }
    while let Some(expression) = expressions.pop() {
        match expression {
            Expr::Binary(_, left, right) => {
                expressions.push(*left);
                expressions.push(*right);
            }
            Expr::Load { address, .. } => expressions.push(*address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                expressions.push(*condition);
                expressions.push(*taken);
                expressions.push(*not_taken);
            }
            _ => {}
        }
    }
}
