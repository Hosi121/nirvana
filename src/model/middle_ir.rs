//! Value-based middle IR for the closed, single-function executable model.
//!
//! Values are immutable within one evaluation region. Loads are explicit;
//! Select owns lazy child regions. A Store evaluates its address region, checks
//! the write range, then evaluates its value region and commits. Guest steps
//! retain PCs and budgets. Storage IDs currently name machine storage locations,
//! independently of value IDs and source-variable/type hypotheses.
//!
//! Lifting is checked by reconstruction against the input and register SSA.
//! Lowering validates value scope, read versions, effect order and CFG layout.
//! The direct runner shares scalar/guest-memory primitives with Low IR, while
//! evaluating this representation without invoking its lowerer.
use crate::dataflow::ssa::{self, SsaFunction};
use crate::model::ir::{self, BinaryOp, Program, Reg, UnaryOp, Width};
use std::fmt;

mod lift;
mod lower;
mod run;
#[cfg(test)]
mod tests;
mod text;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValueId(pub usize);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct StorageId(pub usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operand {
    Address,
    Value,
    Control,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Origin {
    pub site: ssa::Site,
    pub operand: Operand,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Pure {
    Constant(u64),
    Unary(UnaryOp, ValueId),
    Binary(BinaryOp, ValueId, ValueId),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Operation {
    Pure(Pure),
    ReadStorage {
        storage: StorageId,
        /// None denotes a syntactically retained, entry-unreachable site.
        version: Option<ssa::ValueId>,
    },
    Load {
        address: ValueId,
        width: Width,
    },
    Select {
        condition: ValueId,
        taken: Region,
        not_taken: Region,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binding {
    pub id: ValueId,
    pub origin: Origin,
    pub operation: Operation,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Region {
    pub origin: Origin,
    pub bindings: Vec<Binding>,
    pub result: ValueId,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    WriteStorage {
        storage: StorageId,
        version: Option<ssa::ValueId>,
        value: Region,
    },
    Store {
        address: Region,
        width: Width,
        value: Region,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Step {
    pub address: u64,
    pub size: u32,
    pub statements: Vec<Statement>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Terminator {
    Fallthrough(u64),
    Jump(u64),
    Branch {
        condition: Region,
        taken: u64,
        not_taken: u64,
    },
    Return(Region),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub address: u64,
    pub steps: Vec<Step>,
    pub terminator: Terminator,
}
#[derive(Clone, Debug)]
pub struct Function {
    entry: u64,
    storages: Vec<Reg>,
    blocks: Vec<Block>,
    ssa: SsaFunction,
    value_count: usize,
    source_value_count: usize,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Limit(&'static str),
    Invalid(&'static str),
    Ssa(ssa::SsaError),
    Program(ir::ProgramError),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Limit(s) => write!(f, "middle IR resource limit: {s}"),
            Self::Invalid(s) => write!(f, "invalid middle IR: {s}"),
            Self::Ssa(e) => e.fmt(f),
            Self::Program(e) => e.fmt(f),
        }
    }
}
impl std::error::Error for Error {}
impl Function {
    pub fn from_low(source: &Program) -> Result<Self, Error> {
        let function = lift::build(source)?;
        function.validate_source(source)?;
        Ok(function)
    }
    /// Exact source binding of a freshly lifted function. Checked transforms
    /// establish their own relation to this input rather than claiming identity.
    pub fn validate_source(&self, source: &Program) -> Result<(), Error> {
        let restored = self.lower()?;
        if restored.register_count() != source.register_count()
            || restored.cfg().block(restored.cfg().entry()).start
                != source.cfg().block(source.cfg().entry()).start
            || restored.instructions() != source.instructions()
        {
            return Err(Error::Invalid("source reconstruction mismatch"));
        }
        Ok(())
    }
    pub fn lower(&self) -> Result<Program, Error> {
        lower::program(self)
    }
    pub fn entry(&self) -> u64 {
        self.entry
    }
    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }
    pub fn storages(&self) -> &[Reg] {
        &self.storages
    }
    pub fn ssa(&self) -> &SsaFunction {
        &self.ssa
    }
    pub fn value_count(&self) -> usize {
        self.value_count
    }
    /// Expression nodes in the source before region-local pure sharing.
    pub fn source_value_count(&self) -> usize {
        self.source_value_count
    }
}
