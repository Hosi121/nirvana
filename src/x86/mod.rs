//! A self-contained x86-64 integer decoder and lifter. No external disassembler.
//! The first target is a single known function, with explicit guest memory and
//! a root return. Default executable decoding uses the integer/memory model;
//! the opt-in effect lifter models puts with a supplied outcome tape.
//! Reference inspection also decodes near calls and indirect branches. ELF
//! placement and relocation resolution live in the separate loader.

mod decode;
mod effects;
mod lift;
mod vector;

pub use decode::{
    Addressing, Alu, DecodeError, DecodedInstruction, Operand, Operation, Register, Rotate, Shift,
    Unary, decode_at, decode_reachable, decode_reference_at,
};
pub(crate) use effects::lift_effects_with_resolver;
pub use effects::{EffectLiftError, lift_effects};
pub(crate) use lift::check_effect_flags;
pub(crate) use lift::lift_instruction;
pub use lift::{LiftError, lift};
pub use vector::{VectorInstruction, VectorMemory, decode_vector_at};

pub const RAX: usize = 0;
pub const RCX: usize = 1;
pub const RDX: usize = 2;
pub const RBX: usize = 3;
pub const RSP: usize = 4;
pub const RBP: usize = 5;
pub const RSI: usize = 6;
pub const RDI: usize = 7;
pub const CF: usize = 16;
pub const ZF: usize = 17;
pub const SF: usize = 18;
pub const OF: usize = 19;
pub const PF: usize = 20;
pub const REGISTER_COUNT: usize = 32;
