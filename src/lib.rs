//! A decompiler built from scratch.
//!
//! A checked ELF function reader and an x86-64 integer decoder/lifter feed an
//! executable IR with guest memory. Basic-block recovery, graph analysis,
//! structuring and C emission use no external disassembler or compiler framework.

pub mod analysis;
pub mod block_verify;
pub mod cfg;
pub mod elf;
pub mod emit;
pub mod frontend;
pub mod ir;
pub mod observe;
pub mod postdom;
pub mod readable;
pub mod reduce;
pub mod simplify;
pub mod structure;
pub mod structure_verify;
pub mod verify;
pub mod x86;
