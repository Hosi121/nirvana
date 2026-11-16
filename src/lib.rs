//! A decompiler built from scratch.
//!
//! A checked ELF function reader and an x86-64 integer decoder/lifter feed an
//! executable IR with guest memory. Basic-block recovery, graph analysis,
//! structuring and C emission use no external disassembler or compiler framework.

pub mod allocation;
pub mod analysis;
pub mod block_verify;
pub mod cfg;
pub mod elf;
pub mod emit;
pub mod frontend;
pub mod hir;
pub mod indexed;
pub mod ir;
mod join;
pub mod loop_shape;
pub mod observe;
pub mod postdom;
pub mod provenance;
pub mod readable;
pub mod reduce;
pub mod sequence;
pub mod simplify;
pub mod stack;
pub mod structure;
pub mod structure_verify;
pub mod value_width;
pub mod verify;
pub mod x86;
