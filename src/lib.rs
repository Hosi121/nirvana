//! A decompiler built from scratch.
//!
//! A checked ELF function reader and an x86-64 integer decoder/lifter feed an
//! executable IR with guest memory. Basic-block recovery, graph analysis,
//! structuring and C emission use no external disassembler or compiler framework.

pub mod allocation;
pub mod allocation_verify;
pub mod analysis;
pub mod block_verify;
pub mod branch_tail;
pub mod cfg;
pub mod elf;
pub mod emit;
pub mod for_loop;
pub mod frontend;
pub mod goto_layout;
pub mod guarded_loop;
pub mod hir;
pub mod indexed;
pub mod ir;
mod join;
pub mod local_identity;
pub mod loop_shape;
pub mod observe;
pub mod postdom;
pub mod presentation;
pub mod provenance;
pub mod readable;
pub mod reduce;
pub mod self_update;
pub mod sequence;
pub mod simplify;
pub mod stack;
pub mod stack_role;
pub mod stack_values;
pub mod structure;
pub mod structure_verify;
pub mod value_role;
pub mod value_width;
pub mod verify;
pub mod web;
pub mod web_verify;
pub mod x86;
