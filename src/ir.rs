//! An executable, unsigned-64-bit IR for checking control-flow recovery.
//! Arithmetic wraps modulo 2^64. Shift counts are masked with 63. Expressions
//! may read a checked little-endian byte memory. Calls are not modeled yet.

use std::fmt;

use crate::analysis::{ControlFlowAnalysis, UnresolvedControlFlow};
use crate::cfg::{Address, BuildError, Cfg, Flow, Instruction};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Reg(pub usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Ult,
    Ule,
    UMulHigh,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Width {
    U8,
    U16,
    U32,
    U64,
}

impl Width {
    pub const fn bytes(self) -> usize {
        match self {
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
        }
    }
    pub const fn bits(self) -> u32 {
        self.bytes() as u32 * 8
    }
    pub const fn mask(self) -> u64 {
        u64::MAX >> (64 - self.bits())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    Const(u64),
    Register(Reg),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Load {
        address: Box<Expr>,
        width: Width,
    },
    Select {
        condition: Box<Expr>,
        taken: Box<Expr>,
        not_taken: Box<Expr>,
    },
}

impl Expr {
    pub fn binary(op: BinaryOp, left: Self, right: Self) -> Self {
        Self::Binary(op, Box::new(left), Box::new(right))
    }

    pub fn load(address: Self, width: Width) -> Self {
        Self::Load {
            address: Box::new(address),
            width,
        }
    }
    pub fn select(condition: Self, taken: Self, not_taken: Self) -> Self {
        Self::Select {
            condition: Box::new(condition),
            taken: Box::new(taken),
            not_taken: Box::new(not_taken),
        }
    }

    pub(crate) fn evaluate(&self, machine: &Machine) -> Result<u64, MemoryFault> {
        Ok(match self {
            Self::Const(value) => *value,
            Self::Register(Reg(index)) => machine.registers[*index],
            Self::Load { address, width } => machine.load(address.evaluate(machine)?, *width)?,
            Self::Select {
                condition,
                taken,
                not_taken,
            } => {
                if condition.evaluate(machine)? != 0 {
                    taken.evaluate(machine)?
                } else {
                    not_taken.evaluate(machine)?
                }
            }
            Self::Binary(op, left, right) => {
                let left = left.evaluate(machine)?;
                let right = right.evaluate(machine)?;
                match op {
                    BinaryOp::Add => left.wrapping_add(right),
                    BinaryOp::Sub => left.wrapping_sub(right),
                    BinaryOp::Mul => left.wrapping_mul(right),
                    BinaryOp::And => left & right,
                    BinaryOp::Or => left | right,
                    BinaryOp::Xor => left ^ right,
                    BinaryOp::Shl => left.wrapping_shl((right & 63) as u32),
                    BinaryOp::Shr => left.wrapping_shr((right & 63) as u32),
                    BinaryOp::Eq => u64::from(left == right),
                    BinaryOp::Ne => u64::from(left != right),
                    BinaryOp::Ult => u64::from(left < right),
                    BinaryOp::Ule => u64::from(left <= right),
                    BinaryOp::UMulHigh => ((u128::from(left) * u128::from(right)) >> 64) as u64,
                }
            }
        })
    }

    fn invalid_register(&self, count: usize) -> Option<Reg> {
        match self {
            Self::Const(_) => None,
            Self::Register(reg) => (reg.0 >= count).then_some(*reg),
            Self::Binary(_, left, right) => left
                .invalid_register(count)
                .or_else(|| right.invalid_register(count)),
            Self::Load { address, .. } => address.invalid_register(count),
            Self::Select {
                condition,
                taken,
                not_taken,
            } => condition
                .invalid_register(count)
                .or_else(|| taken.invalid_register(count))
                .or_else(|| not_taken.invalid_register(count)),
        }
    }

    pub(crate) fn uses_memory(&self) -> bool {
        match self {
            Self::Load { .. } => true,
            Self::Binary(_, left, right) => left.uses_memory() || right.uses_memory(),
            Self::Select {
                condition,
                taken,
                not_taken,
            } => condition.uses_memory() || taken.uses_memory() || not_taken.uses_memory(),
            _ => false,
        }
    }

    pub(crate) fn uses_high_multiply(&self) -> bool {
        match self {
            Self::Binary(op, left, right) => {
                *op == BinaryOp::UMulHigh || left.uses_high_multiply() || right.uses_high_multiply()
            }
            Self::Load { address, .. } => address.uses_high_multiply(),
            Self::Select {
                condition,
                taken,
                not_taken,
            } => {
                condition.uses_high_multiply()
                    || taken.uses_high_multiply()
                    || not_taken.uses_high_multiply()
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Place {
    Register(Reg),
    Memory { address: Expr, width: Width },
}

impl From<Reg> for Place {
    fn from(reg: Reg) -> Self {
        Self::Register(reg)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Assignment {
    pub destination: Place,
    pub value: Expr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Control {
    Next,
    Jump(Address),
    Branch { condition: Expr, target: Address },
    Return(Expr),
}

impl Control {
    fn flow(&self) -> Flow {
        match self {
            Self::Next => Flow::Next,
            Self::Jump(target) => Flow::Jump(*target),
            Self::Branch { target, .. } => Flow::Branch(*target),
            Self::Return(_) => Flow::Return,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IrInstruction {
    pub address: Address,
    pub size: u32,
    /// Sequential assignments, evaluated before control transfer.
    pub assignments: Vec<Assignment>,
    pub control: Control,
}

#[derive(Clone, Debug)]
pub struct Program {
    cfg: Cfg,
    instructions: Vec<IrInstruction>,
    register_count: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramError {
    Layout(BuildError),
    Unresolved(UnresolvedControlFlow),
    InvalidRegister {
        address: Address,
        register: Reg,
        count: usize,
    },
}

impl fmt::Display for ProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Layout(error) => error.fmt(f),
            Self::Unresolved(error) => error.fmt(f),
            Self::InvalidRegister {
                address,
                register,
                count,
            } => write!(
                f,
                "instruction at {address:#x} uses r{} with only {count} registers",
                register.0
            ),
        }
    }
}

impl std::error::Error for ProgramError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Execution {
    pub value: u64,
    pub registers: Vec<u64>,
    /// Original instruction addresses, including branch and jump instructions.
    pub trace: Vec<Address>,
    /// Final checked guest-memory bytes. Empty for register-only executions.
    pub memory: Vec<u8>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AccessKind {
    Read,
    Write,
}

/// A fault in the checked guest-memory model, not a host CPU exception.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemoryFault {
    pub access: AccessKind,
    pub address: u64,
    pub width: Width,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunStatus {
    Returned(u64),
    Fault(MemoryFault),
    /// The observation budget ran out. This does not establish divergence.
    Suspended,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Snapshot {
    pub registers: Vec<u64>,
    pub memory_base: u64,
    pub memory: Vec<u8>,
    /// Instructions started, including an instruction which faulted midway.
    pub trace: Vec<Address>,
    /// Current/faulting instruction, or the next attempted step on suspension.
    pub instruction: Option<Address>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunReport {
    pub status: RunStatus,
    pub state: Snapshot,
}

impl RunReport {
    /// Compatibility projection. Use the report itself to inspect partial state.
    pub fn into_execution(self) -> Result<Execution, ExecutionError> {
        match self.status {
            RunStatus::Returned(value) => Ok(Execution {
                value,
                registers: self.state.registers,
                memory: self.state.memory,
                trace: self.state.trace,
            }),
            RunStatus::Fault(fault) => Err(ExecutionError::MemoryAccess {
                address: fault.address,
                width: fault.width,
            }),
            RunStatus::Suspended => Err(ExecutionError::StepLimit),
        }
    }
}

pub(crate) enum Stop {
    Fault(MemoryFault),
    Limit,
}

impl From<MemoryFault> for Stop {
    fn from(fault: MemoryFault) -> Self {
        Self::Fault(fault)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionError {
    RegisterCount { expected: usize, actual: usize },
    StepLimit,
    MemoryAccess { address: u64, width: Width },
}

impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegisterCount { expected, actual } => {
                write!(f, "expected {expected} input registers, got {actual}")
            }
            Self::StepLimit => f.write_str("instruction step limit exhausted"),
            Self::MemoryAccess { address, width } => write!(
                f,
                "out-of-bounds {}-byte memory access at {address:#x}",
                width.bytes()
            ),
        }
    }
}

impl std::error::Error for ExecutionError {}

pub(crate) struct Machine {
    pub registers: Vec<u64>,
    trace: Vec<Address>,
    remaining: usize,
    memory: Vec<u8>,
    memory_base: u64,
    instruction: Option<Address>,
}

impl Machine {
    pub fn new(count: usize, input: &[u64], limit: usize) -> Result<Self, ExecutionError> {
        if input.len() != count {
            return Err(ExecutionError::RegisterCount {
                expected: count,
                actual: input.len(),
            });
        }
        Ok(Self {
            registers: input.to_vec(),
            trace: Vec::new(),
            remaining: limit,
            memory: Vec::new(),
            memory_base: 0,
            instruction: None,
        })
    }

    pub fn with_memory(
        count: usize,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        limit: usize,
    ) -> Result<Self, ExecutionError> {
        let mut machine = Self::new(count, input, limit)?;
        machine.memory_base = memory_base;
        machine.memory = memory.to_vec();
        Ok(machine)
    }

    fn offset(&self, address: u64, width: Width, access: AccessKind) -> Result<usize, MemoryFault> {
        if address.checked_add(width.bytes() as u64 - 1).is_none() {
            return Err(MemoryFault {
                access,
                address,
                width,
            });
        }
        let offset = address
            .checked_sub(self.memory_base)
            .and_then(|value| usize::try_from(value).ok());
        offset
            .filter(|&offset| {
                offset
                    .checked_add(width.bytes())
                    .is_some_and(|end| end <= self.memory.len())
            })
            .ok_or(MemoryFault {
                access,
                address,
                width,
            })
    }

    fn load(&self, address: u64, width: Width) -> Result<u64, MemoryFault> {
        let offset = self.offset(address, width, AccessKind::Read)?;
        let mut bytes = [0; 8];
        bytes[..width.bytes()].copy_from_slice(&self.memory[offset..offset + width.bytes()]);
        Ok(u64::from_le_bytes(bytes))
    }

    pub fn step(&mut self, address: Address, assignments: &[Assignment]) -> Result<(), Stop> {
        self.instruction = Some(address);
        if self.remaining == 0 {
            return Err(Stop::Limit);
        }
        self.remaining -= 1;
        self.trace.push(address);
        for assignment in assignments {
            match &assignment.destination {
                Place::Register(reg) => self.registers[reg.0] = assignment.value.evaluate(self)?,
                Place::Memory { address, width } => {
                    let address = address.evaluate(self)?;
                    let offset = self.offset(address, *width, AccessKind::Write)?;
                    let value = assignment.value.evaluate(self)?.to_le_bytes();
                    self.memory[offset..offset + width.bytes()]
                        .copy_from_slice(&value[..width.bytes()]);
                }
            }
        }
        Ok(())
    }

    pub fn finish(self, result: Result<u64, Stop>) -> RunReport {
        let status = match result {
            Ok(value) => RunStatus::Returned(value),
            Err(Stop::Fault(fault)) => RunStatus::Fault(fault),
            Err(Stop::Limit) => RunStatus::Suspended,
        };
        RunReport {
            status,
            state: Snapshot {
                registers: self.registers,
                trace: self.trace,
                memory: self.memory,
                memory_base: self.memory_base,
                instruction: self.instruction,
            },
        }
    }
}

impl Program {
    pub fn new(
        entry: Address,
        register_count: usize,
        mut instructions: Vec<IrInstruction>,
    ) -> Result<Self, ProgramError> {
        let cfg = Cfg::build(
            entry,
            instructions
                .iter()
                .map(|instruction| {
                    Instruction::new(
                        instruction.address,
                        instruction.size,
                        instruction.control.flow(),
                    )
                })
                .collect(),
        )
        .map_err(ProgramError::Layout)?;
        ControlFlowAnalysis::compute(&cfg).map_err(ProgramError::Unresolved)?;
        for instruction in &instructions {
            let invalid = instruction
                .assignments
                .iter()
                .find_map(|assignment| {
                    let destination = match &assignment.destination {
                        Place::Register(reg) => (reg.0 >= register_count).then_some(*reg),
                        Place::Memory { address, .. } => address.invalid_register(register_count),
                    };
                    destination.or_else(|| assignment.value.invalid_register(register_count))
                })
                .or_else(|| match &instruction.control {
                    Control::Branch { condition, .. } => condition.invalid_register(register_count),
                    Control::Return(value) => value.invalid_register(register_count),
                    _ => None,
                });
            if let Some(register) = invalid {
                return Err(ProgramError::InvalidRegister {
                    address: instruction.address,
                    register,
                    count: register_count,
                });
            }
        }
        instructions.sort_by_key(|instruction| instruction.address);
        Ok(Self {
            cfg,
            instructions,
            register_count,
        })
    }

    pub fn cfg(&self) -> &Cfg {
        &self.cfg
    }
    pub fn instructions(&self) -> &[IrInstruction] {
        &self.instructions
    }
    pub fn register_count(&self) -> usize {
        self.register_count
    }

    pub fn execute(&self, input: &[u64], step_limit: usize) -> Result<Execution, ExecutionError> {
        self.execute_with_memory(input, 0, &[], step_limit)
    }

    pub fn uses_memory(&self) -> bool {
        self.instructions.iter().any(|instruction| {
            instruction.assignments.iter().any(|assignment| {
                matches!(assignment.destination, Place::Memory { .. })
                    || assignment.value.uses_memory()
            }) || match &instruction.control {
                Control::Branch { condition, .. } => condition.uses_memory(),
                Control::Return(value) => value.uses_memory(),
                _ => false,
            }
        })
    }

    pub fn uses_high_multiply(&self) -> bool {
        self.instructions.iter().any(|instruction| {
            instruction.assignments.iter().any(|assignment| {
                assignment.value.uses_high_multiply()
                    || match &assignment.destination {
                        Place::Memory { address, .. } => address.uses_high_multiply(),
                        _ => false,
                    }
            }) || match &instruction.control {
                Control::Branch { condition, .. } => condition.uses_high_multiply(),
                Control::Return(value) => value.uses_high_multiply(),
                _ => false,
            }
        })
    }

    pub fn execute_with_memory(
        &self,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        step_limit: usize,
    ) -> Result<Execution, ExecutionError> {
        self.run_with_memory(input, memory_base, memory, step_limit)?
            .into_execution()
    }

    /// Retain complete state at return, memory fault, or budget exhaustion.
    /// An outer error denotes an invalid invocation (input-register count).
    pub fn run_with_memory(
        &self,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        step_limit: usize,
    ) -> Result<RunReport, ExecutionError> {
        let mut machine =
            Machine::with_memory(self.register_count, input, memory_base, memory, step_limit)?;
        let mut address = self.cfg.block(self.cfg.entry()).start;
        let result = (|| -> Result<u64, Stop> {
            loop {
                let index = self
                    .instructions
                    .binary_search_by_key(&address, |instruction| instruction.address)
                    .expect("validated reachable instruction");
                let instruction = &self.instructions[index];
                machine.step(address, &instruction.assignments)?;
                address = match &instruction.control {
                    Control::Next => address + u64::from(instruction.size),
                    Control::Jump(target) => *target,
                    Control::Branch { condition, target } => {
                        if condition.evaluate(&machine)? != 0 {
                            *target
                        } else {
                            address + u64::from(instruction.size)
                        }
                    }
                    Control::Return(value) => {
                        let value = value.evaluate(&machine)?;
                        return Ok(value);
                    }
                };
            }
        })();
        Ok(machine.finish(result))
    }
}
