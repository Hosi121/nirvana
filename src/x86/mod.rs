//! A self-contained x86-64 integer decoder and lifter. No external disassembler.
//! The first target is a single known function, with explicit guest memory and
//! a root return. Calls, SIMD, privileged instructions and relocation resolution
//! are deliberately rejected.

mod decode;
mod lift;

pub use decode::{
    Addressing, Alu, DecodeError, DecodedInstruction, Operand, Operation, Register, Rotate, Shift,
    Unary, decode_at, decode_reachable,
};
pub use lift::{LiftError, lift};

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
