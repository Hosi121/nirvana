//! An executable, 64-bit bit-vector IR for checking control-flow recovery.
//! Arithmetic wraps modulo 2^64. Shift counts are masked with 63. Expressions
//! may read a checked little-endian byte memory. Explicit external calls use
//! the effect IR in `crate::model::effects` and reuse this core machine.

use std::fmt;

use crate::control_flow::analysis::{ControlFlowAnalysis, UnresolvedControlFlow};
use crate::control_flow::cfg::{Address, BuildError, Cfg, Flow, Instruction};

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
    /// High 64 bits of a signed, full 128-bit product.
    SMulHigh,
    /// Sign-filling right shift; the count is masked with 63.
    AShr,
    /// Total SMT-LIB unsigned quotient; zero divisor yields all one bits.
    UDiv,
    /// Total unsigned remainder; zero divisor yields the dividend.
    URem,
    /// Total signed quotient, truncated toward zero. MIN/-1 wraps to MIN;
    /// division by zero yields 1 for a negative input and all ones otherwise.
    SDiv,
    /// Total signed remainder; its sign follows the dividend. A zero divisor
    /// yields the dividend. Hardware divide faults live in module effects.
    SRem,
}

impl BinaryOp {
    /// Total scalar semantics on bit patterns. Signed operations interpret
    /// their operands locally; they do not establish a source-language type.
    pub fn evaluate(self, left: u64, right: u64) -> u64 {
        match self {
            Self::Add => left.wrapping_add(right),
            Self::Sub => left.wrapping_sub(right),
            Self::Mul => left.wrapping_mul(right),
            Self::And => left & right,
            Self::Or => left | right,
            Self::Xor => left ^ right,
            Self::Shl => left.wrapping_shl((right & 63) as u32),
            Self::Shr => left.wrapping_shr((right & 63) as u32),
            Self::AShr => ((left as i64) >> (right & 63)) as u64,
            Self::Eq => u64::from(left == right),
            Self::Ne => u64::from(left != right),
            Self::Ult => u64::from(left < right),
            Self::Ule => u64::from(left <= right),
            Self::UMulHigh => ((u128::from(left) * u128::from(right)) >> 64) as u64,
            Self::SMulHigh => ((i128::from(left as i64) * i128::from(right as i64)) >> 64) as u64,
            Self::UDiv => left.checked_div(right).unwrap_or(u64::MAX),
            Self::URem => {
                if right == 0 {
                    left
                } else {
                    left % right
                }
            }
            Self::SDiv => {
                if right == 0 {
                    if left >> 63 != 0 { 1 } else { u64::MAX }
                } else {
                    (i128::from(left as i64) / i128::from(right as i64)) as u64
                }
            }
            Self::SRem => {
                if right == 0 {
                    left
                } else {
                    (i128::from(left as i64) % i128::from(right as i64)) as u64
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Width {
    U8,
    U16,
    U32,
    U64,
}

/// Total operations on a single 64-bit bit pattern. Width is part of the
/// operation, independent of any source-language type assigned to its input.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UnaryOp {
    SignExtend(Width),
    /// Read a static bit slice, zero extending its result to 64 bits. Bits
    /// beyond the source word are zero; `start` is never reduced modulo 64.
    Extract {
        start: u8,
        width: Width,
    },
}

impl UnaryOp {
    pub(crate) fn is_identity(self) -> bool {
        matches!(
            self,
            Self::SignExtend(Width::U64)
                | Self::Extract {
                    start: 0,
                    width: Width::U64
                }
        )
    }
    pub fn evaluate(self, value: u64) -> u64 {
        match self {
            Self::SignExtend(width) => {
                let sign = 1u64 << (width.bits() - 1);
                ((value & width.mask()) ^ sign).wrapping_sub(sign)
            }
            Self::Extract { start, width } => {
                value.checked_shr(u32::from(start)).unwrap_or(0) & width.mask()
            }
        }
    }

    /// Unsigned bit-length bound for every input covered by `input_bits`.
    pub(crate) fn result_bits(self, input_bits: u8) -> u8 {
        let input_bits = input_bits.min(64);
        match self {
            Self::SignExtend(width) => {
                if input_bits < width.bits() as u8 {
                    input_bits
                } else {
                    64
                }
            }
            Self::Extract { start, width } => {
                input_bits.saturating_sub(start).min(width.bits() as u8)
            }
        }
    }
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
    Unary(UnaryOp, Box<Expr>),
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
    pub fn unary(op: UnaryOp, value: Self) -> Self {
        Self::Unary(op, Box::new(value))
    }
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
            Self::Unary(op, value) => op.evaluate(value.evaluate(machine)?),
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
                op.evaluate(left, right)
            }
        })
    }

    fn invalid_register(&self, count: usize) -> Option<Reg> {
        match self {
            Self::Const(_) => None,
            Self::Register(reg) => (reg.0 >= count).then_some(*reg),
            Self::Unary(_, value) => value.invalid_register(count),
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
            Self::Unary(_, value) => value.uses_memory(),
            Self::Binary(_, left, right) => left.uses_memory() || right.uses_memory(),
            Self::Select {
                condition,
                taken,
                not_taken,
            } => condition.uses_memory() || taken.uses_memory() || not_taken.uses_memory(),
            _ => false,
        }
    }

    pub(crate) fn uses_operator(&self, operator: BinaryOp) -> bool {
        match self {
            Self::Unary(_, value) => value.uses_operator(operator),
            Self::Binary(op, left, right) => {
                *op == operator || left.uses_operator(operator) || right.uses_operator(operator)
            }
            Self::Load { address, .. } => address.uses_operator(operator),
            Self::Select {
                condition,
                taken,
                not_taken,
            } => {
                condition.uses_operator(operator)
                    || taken.uses_operator(operator)
                    || not_taken.uses_operator(operator)
            }
            _ => false,
        }
    }

    pub(crate) fn uses_unary_operator(&self, operator: UnaryOp) -> bool {
        match self {
            Self::Unary(op, value) => *op == operator || value.uses_unary_operator(operator),
            Self::Binary(_, a, b) => {
                a.uses_unary_operator(operator) || b.uses_unary_operator(operator)
            }
            Self::Load { address, .. } => address.uses_unary_operator(operator),
            Self::Select {
                condition,
                taken,
                not_taken,
            } => {
                condition.uses_unary_operator(operator)
                    || taken.uses_unary_operator(operator)
                    || not_taken.uses_unary_operator(operator)
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
    pub memory_layout: Option<crate::model::memory::Layout>,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BlockExit {
    Next(Address),
    Returned(u64),
    Fault(MemoryFault),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockReport {
    pub exit: BlockExit,
    pub state: Snapshot,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BlockError {
    UnknownBlock(Address),
    Input(ExecutionError),
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
    MemoryLayout,
}

impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegisterCount { expected, actual } => {
                write!(f, "expected {expected} input registers, got {actual}")
            }
            Self::StepLimit => f.write_str("instruction step limit exhausted"),
            Self::MemoryLayout => {
                f.write_str("memory base or backing size disagrees with sparse layout")
            }
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
    memory_layout: Option<crate::model::memory::Layout>,
    instruction: Option<Address>,
}

impl Machine {
    pub(crate) fn checked_range(
        &self,
        address: u64,
        width: usize,
        access: AccessKind,
    ) -> Option<usize> {
        crate::model::memory::View {
            base: self.memory_base,
            bytes: &self.memory,
            layout: self.memory_layout.as_ref(),
        }
        .offset(
            address,
            width,
            match access {
                AccessKind::Read => crate::model::memory::READ,
                AccessKind::Write => crate::model::memory::WRITE,
            },
        )
    }
    pub(crate) fn set_memory_layout(
        &mut self,
        layout: &crate::model::memory::Layout,
    ) -> Result<(), ExecutionError> {
        if layout.size() != self.memory.len() || layout.regions()[0].address != self.memory_base {
            return Err(ExecutionError::MemoryLayout);
        }
        self.memory_layout = Some(layout.clone());
        Ok(())
    }
    pub(crate) fn checked_bytes(&self, address: u64, width: usize) -> Option<&[u8]> {
        let offset = self.checked_range(address, width, AccessKind::Read)?;
        self.memory.get(offset..offset.checked_add(width)?)
    }

    pub(crate) fn checked_bytes_mut(&mut self, address: u64, width: usize) -> Option<&mut [u8]> {
        let offset = self.checked_range(address, width, AccessKind::Write)?;
        self.memory.get_mut(offset..offset.checked_add(width)?)
    }
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
            memory_layout: None,
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
        self.checked_range(address, width.bytes(), access)
            .ok_or(MemoryFault {
                access,
                address,
                width,
            })
    }

    pub(crate) fn load(&self, address: u64, width: Width) -> Result<u64, MemoryFault> {
        let offset = self.offset(address, width, AccessKind::Read)?;
        let mut bytes = [0; 8];
        bytes[..width.bytes()].copy_from_slice(&self.memory[offset..offset + width.bytes()]);
        Ok(u64::from_le_bytes(bytes))
    }

    /// Commit a checked store atomically, retaining RAM on a failed access.
    pub(crate) fn store(
        &mut self,
        address: u64,
        width: Width,
        value: u64,
    ) -> Result<(), MemoryFault> {
        let offset = self.offset(address, width, AccessKind::Write)?;
        self.memory[offset..offset + width.bytes()]
            .copy_from_slice(&value.to_le_bytes()[..width.bytes()]);
        Ok(())
    }

    pub fn step(&mut self, address: Address, assignments: &[Assignment]) -> Result<(), Stop> {
        self.instruction = Some(address);
        if self.remaining == 0 {
            return Err(Stop::Limit);
        }
        self.remaining -= 1;
        self.trace.push(address);
        self.assign(assignments)
    }

    pub(crate) fn assign(&mut self, assignments: &[Assignment]) -> Result<(), Stop> {
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
            state: self.snapshot(),
        }
    }

    pub(crate) fn snapshot(self) -> Snapshot {
        Snapshot {
            registers: self.registers,
            trace: self.trace,
            memory: self.memory,
            memory_base: self.memory_base,
            memory_layout: self.memory_layout,
            instruction: self.instruction,
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

    /// Execute exactly one basic block, stopping before its successor. A block
    /// is finite and has no internal control transfer, so no unwind bound is used.
    pub fn run_block_with_memory(
        &self,
        start: Address,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
    ) -> Result<BlockReport, BlockError> {
        let id = self
            .cfg
            .block_at(start)
            .ok_or(BlockError::UnknownBlock(start))?;
        let block = self.cfg.block(id);
        let mut machine = Machine::with_memory(
            self.register_count,
            input,
            memory_base,
            memory,
            block.instructions.len(),
        )
        .map_err(BlockError::Input)?;
        let result = (|| -> Result<BlockExit, Stop> {
            for instruction in &self.instructions[block.instructions.clone()] {
                machine.step(instruction.address, &instruction.assignments)?;
                match &instruction.control {
                    Control::Next => {}
                    Control::Jump(target) => return Ok(BlockExit::Next(*target)),
                    Control::Branch { condition, target } => {
                        return Ok(BlockExit::Next(if condition.evaluate(&machine)? != 0 {
                            *target
                        } else {
                            instruction.address + u64::from(instruction.size)
                        }));
                    }
                    Control::Return(value) => {
                        return Ok(BlockExit::Returned(value.evaluate(&machine)?));
                    }
                }
            }
            Ok(BlockExit::Next(block.end))
        })();
        let exit = match result {
            Ok(exit) => exit,
            Err(Stop::Fault(fault)) => BlockExit::Fault(fault),
            Err(Stop::Limit) => {
                unreachable!("one validated basic block has a finite instruction count")
            }
        };
        Ok(BlockReport {
            exit,
            state: machine.snapshot(),
        })
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
        self.uses_operator(BinaryOp::UMulHigh) || self.uses_operator(BinaryOp::SMulHigh)
    }

    pub fn uses_operator(&self, operator: BinaryOp) -> bool {
        self.instructions.iter().any(|instruction| {
            instruction.assignments.iter().any(|assignment| {
                assignment.value.uses_operator(operator)
                    || match &assignment.destination {
                        Place::Memory { address, .. } => address.uses_operator(operator),
                        _ => false,
                    }
            }) || match &instruction.control {
                Control::Branch { condition, .. } => condition.uses_operator(operator),
                Control::Return(value) => value.uses_operator(operator),
                _ => false,
            }
        })
    }

    pub fn uses_unary_operator(&self, operator: UnaryOp) -> bool {
        self.instructions.iter().any(|instruction| {
            instruction.assignments.iter().any(|assignment| {
                assignment.value.uses_unary_operator(operator)
                    || matches!(&assignment.destination, Place::Memory { address, .. } if address.uses_unary_operator(operator))
            }) || match &instruction.control {
                Control::Branch { condition, .. } => condition.uses_unary_operator(operator),
                Control::Return(value) => value.uses_unary_operator(operator),
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
