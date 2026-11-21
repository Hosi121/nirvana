//! A decompiler built from scratch.
//!
//! A checked ELF function reader and an x86-64 integer decoder/lifter feed an
//! executable IR with guest memory. Basic-block recovery, graph analysis,
//! structuring and C emission are implemented with the Rust standard library.

//! Implementations are grouped by responsibility; root exports preserve the
//! existing Rust API.

pub mod binary;
pub mod codegen;
pub mod control_flow;
pub mod dataflow;
pub mod model;
pub mod transform;
pub mod verification;

pub use binary::{eh_frame, elf, frontend, jump_tables, linked_elf, loader, object_refs, x86};
pub use codegen::{
    address_types, effects_emit, effects_readable, emit, goto_layout, loop_labels, module_emit,
    module_outline, module_readable, module_switch_keys, module_tail_dispatch, presentation,
    readable,
};
pub use control_flow::{
    analysis, branch_tail, cfg, loop_exit, loop_recover, loop_shape, postdom, structure,
    structure_verify,
};
pub use dataflow::{
    address_identity, allocation, allocation_verify, call_footprint, local_identity, memory_ssa,
    module_local_plan, module_values, parallel_copy, provenance, record_shapes, source_locals, ssa,
    ssa_constants, ssa_destroy, ssa_locals, ssa_storage, stack, stack_cells, stack_role,
    stack_values, type_infer, value_graph, value_liveness, value_role, value_width, web,
    web_verify,
};
pub use model::{effects, effects_observe, expression_ir, hir, ir, memory, module_ir, observe};
pub use transform::{
    access_expr, add_division_expr, affine_region, arithmetic_graph, bit_expr, context_remainder,
    display_dce, division_expr, finite_region, for_loop, guarded_loop, indexed, load_mask,
    narrow_division_expr, narrow_rotate, reduce, remainder_expr, remainder_graph, self_update,
    sequence, signed_division_expr, signed_expr, simplify,
};
pub use verification::{block_verify, verify};
