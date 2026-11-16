//! Connect a checked ELF function image to the self-contained machine-code lifter.

use crate::elf::{self, ElfError, FunctionImage, Relocation};
use crate::ir::Program;
use crate::x86::{self, LiftError};
use std::fmt;

#[derive(Clone, Debug)]
pub struct LiftedFunction {
    pub image: FunctionImage,
    pub program: Program,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FrontendError {
    Elf(ElfError),
    Relocations(Vec<Relocation>),
    Lift(LiftError),
}

impl fmt::Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elf(error) => error.fmt(f),
            Self::Lift(error) => error.fmt(f),
            Self::Relocations(relocations) => {
                let Some(first) = relocations.first() else {
                    return f.write_str("unresolved relocations");
                };
                write!(
                    f,
                    "unresolved relocation at function+{:#x}: type {}, symbol {:?} ({} total); linking is not implemented",
                    first.offset,
                    first.kind,
                    first.symbol,
                    relocations.len()
                )
            }
        }
    }
}
impl std::error::Error for FrontendError {}

pub fn lift_elf(object: &[u8], symbol: &str) -> Result<LiftedFunction, FrontendError> {
    let image = elf::read_function(object, symbol).map_err(FrontendError::Elf)?;
    if !image.relocations.is_empty() {
        return Err(FrontendError::Relocations(image.relocations));
    }
    let program =
        x86::lift(&image.bytes, image.address, image.address).map_err(FrontendError::Lift)?;
    Ok(LiftedFunction { image, program })
}
