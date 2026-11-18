//! Source-bound symbolic references in ELF64 x86-64 relocatable functions.
//!
//! Section identities survive independently of a future link layout. Calls are
//! inspected under the SysV integer-register ABI; their effects remain opaque.
//! This module leaves the executable IR and the original object bytes intact.
use crate::elf::{self, ElfError, ObjectRelocation};
use crate::x86::DecodeError;
use std::fmt;
mod flow;
mod report;
mod resolve;

pub const MAX_FUNCTION_BYTES: usize = 1_048_576;
pub const MAX_INSTRUCTIONS: usize = 16_384;
pub const MAX_REFERENCES: usize = 16_384;
pub const MAX_STRING_BYTES: usize = 4096;
pub const MAX_WORK: usize = 8_000_000;
pub const MAX_REPORT_BYTES: usize = 16_777_216;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Target {
    Section { index: usize, offset: u64 },
    External { name: String, addend: i64 },
    Absolute(u64),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReferenceUse {
    Address,
    Branch,
    Call,
    TailCall,
    GotCall,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reference {
    pub relocation: ObjectRelocation,
    /// Function-relative instruction start, bound to its exact encoded field.
    pub instruction: Option<u64>,
    pub usage: Option<ReferenceUse>,
    pub target: Option<Target>,
    pub literal: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Literal {
    pub section: usize,
    pub section_name: Option<String>,
    pub offset: u64,
    /// Exact file bytes before the verified terminating NUL, at most 4096.
    pub bytes: Vec<u8>,
}
impl Literal {
    /// A byte-preserving C11 spelling, including escapes for trigraph markers.
    pub fn c_literal(&self) -> String {
        let mut result = String::from("\"");
        for &byte in &self.bytes {
            match byte {
                b'\"' => result.push_str("\\\""),
                b'\\' => result.push_str("\\\\"),
                b'?' => result.push_str("\\?"),
                b'\n' => result.push_str("\\n"),
                b'\r' => result.push_str("\\r"),
                b'\t' => result.push_str("\\t"),
                32..=126 => result.push(char::from(byte)),
                _ => {
                    use std::fmt::Write as _;
                    write!(result, "\\{byte:03o}").unwrap();
                }
            }
        }
        result.push('"');
        result
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArgumentRegister {
    pub register: usize,
    pub target: Option<Target>,
    pub literal: Option<usize>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Call {
    pub instruction: u64,
    pub tail: bool,
    pub target: Option<Target>,
    pub symbol: Option<String>,
    /// Candidate argument locations, not an inferred parameter count.
    pub integer_argument_registers: Vec<ArgumentRegister>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectReferences {
    pub function: String,
    pub section: usize,
    pub section_offset: u64,
    pub function_size: usize,
    pub references: Vec<Reference>,
    pub literals: Vec<Literal>,
    /// Syntactic reachable sites after register-reference dataflow converges.
    pub calls: Vec<Call>,
}
impl ObjectReferences {
    pub fn analyze(object: &[u8], symbol: &str) -> Result<Self, ReferenceError> {
        let context = elf::read_function_context(object, symbol)?;
        if context.image.bytes.len() > MAX_FUNCTION_BYTES
            || context.references.len() > MAX_REFERENCES
        {
            return Err(ReferenceError::Limit("function or relocation count"));
        }
        flow::analyze(&context)
    }

    /// A spelling hint for the actual named call and a known file literal.
    /// The report retains addresses and opaque effects alongside this hint.
    pub fn call_hint(&self, call: &Call) -> Option<String> {
        if !matches!(&call.target, Some(Target::External { name, addend: 0 }) if name == "puts") {
            return None;
        }
        let literal = self
            .literals
            .get(call.integer_argument_registers.first()?.literal?)?;
        Some(format!("puts({})", literal.c_literal()))
    }
    pub fn to_json(&self) -> Option<String> {
        report::render(self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReferenceError {
    Elf(ElfError),
    Decode(DecodeError),
    Invalid(&'static str),
    Limit(&'static str),
}
impl From<ElfError> for ReferenceError {
    fn from(error: ElfError) -> Self {
        Self::Elf(error)
    }
}
impl From<DecodeError> for ReferenceError {
    fn from(error: DecodeError) -> Self {
        Self::Decode(error)
    }
}
impl fmt::Display for ReferenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elf(error) => error.fmt(f),
            Self::Decode(error) => error.fmt(f),
            Self::Invalid(reason) => write!(f, "object reference analysis: {reason}"),
            Self::Limit(reason) => write!(f, "object reference analysis limit: {reason}"),
        }
    }
}
impl std::error::Error for ReferenceError {}
