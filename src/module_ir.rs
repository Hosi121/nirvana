//! Multiple guest functions with explicit calls, actual return slots and imports.
//! This machine shares scalar IR semantics, while keeping interprocedural control
//! and external effects out of the pure single-function optimization pipeline.

use crate::ir::{AccessKind, Expr, IrInstruction, Snapshot};
use std::fmt;

mod lift;
mod run;
pub use lift::{lift_elf, lift_elf_at};
pub use run::{Environment, ExternalContext, RejectImports};

pub const REGISTER_COUNT: usize = 80;
pub const ROOT_RETURN: u64 = u64::MAX;
pub const MODEL_ID: &str = "module-normal-ram-calls-v2";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Target {
    Value(Expr),
    /// Load the GOT after the calling instruction has pushed its return slot.
    Plt(u64),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Instruction {
    Core(IrInstruction),
    Divide {
        address: u64,
        size: u32,
        source: Expr,
        width: crate::ir::Width,
        signed: bool,
    },
    Transfer {
        address: u64,
        size: u32,
        target: Target,
        link: Option<u64>,
    },
    Return {
        address: u64,
        size: u32,
        extra_pop: u16,
    },
    Vector(crate::x86::VectorInstruction),
}
impl Instruction {
    pub fn address(&self) -> u64 {
        match self {
            Self::Core(i) => i.address,
            Self::Transfer { address, .. }
            | Self::Return { address, .. }
            | Self::Divide { address, .. } => *address,
            Self::Vector(i) => i.address,
        }
    }
    pub fn size(&self) -> u32 {
        match self {
            Self::Core(i) => i.size,
            Self::Transfer { size, .. } | Self::Return { size, .. } | Self::Divide { size, .. } => {
                *size
            }
            Self::Vector(i) => i.size,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Import {
    pub address: u64,
    pub name: String,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub name: String,
    pub address: u64,
    pub size: u64,
}

#[derive(Clone, Debug)]
pub struct Program {
    instructions: Vec<Instruction>,
    imports: Vec<Import>,
    functions: Vec<Function>,
    shape: crate::ir::Program,
    entry: u64,
    errno_address: u64,
}
impl Program {
    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }
    pub fn imports(&self) -> &[Import] {
        &self.imports
    }
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
    /// Validation metadata only: transfer effects are retained in instructions.
    pub(crate) fn shape(&self) -> &crate::ir::Program {
        &self.shape
    }
    pub fn entry(&self) -> u64 {
        self.entry
    }
    pub fn register_count(&self) -> usize {
        REGISTER_COUNT
    }
    pub fn errno_address(&self) -> u64 {
        self.errno_address
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    pub image: crate::loader::LinkedImage,
    pub program: Program,
    /// Symbols whose bodies could not be lifted. Directly reachable rejected
    /// functions prevent module construction; dynamic targets stop explicitly.
    pub rejected_functions: Vec<(String, String)>,
    /// Open initial-image hints used only to discover additional instructions.
    pub jump_tables: Vec<crate::jump_tables::Candidate>,
    pub jump_table_diagnostics: Vec<(u64, String)>,
    /// Branches whose bounded predecessor-context search was truncated.
    pub jump_table_context_limits: Vec<u64>,
}
impl Module {
    pub fn initial_registers(&self) -> Vec<u64> {
        let mut registers = vec![0; REGISTER_COUNT];
        registers[crate::x86::RSP] = self.image.stack_pointer - 16;
        registers
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleError(pub String);
impl fmt::Display for ModuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ModuleError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fault {
    pub address: u64,
    pub width: u64,
    pub access: AccessKind,
}
impl From<crate::ir::MemoryFault> for Fault {
    fn from(value: crate::ir::MemoryFault) -> Self {
        Self {
            address: value.address,
            width: value.width.bytes() as u64,
            access: value.access,
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Limit {
    Instructions,
    Imports,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Status {
    Returned(u64),
    Fault(Fault),
    UnknownTarget(u64),
    UnsupportedImport(String),
    Suspended(Limit),
    Alignment(Fault),
    /// x86 #DE: zero divisor or quotient outside the destination width.
    DivideError,
    Environment(String),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    pub instructions: usize,
    pub imports: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            instructions: 1_000_000,
            imports: 10_000,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Report {
    pub status: Status,
    pub state: Snapshot,
    pub imports: usize,
    pub pc: u64,
}
