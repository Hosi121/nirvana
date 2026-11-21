//! dataflow integration suite.
#[allow(dead_code)]
mod support;

#[path = "dataflow/allocation.rs"]
mod allocation;
#[path = "dataflow/allocation_hints.rs"]
mod allocation_hints;
#[path = "dataflow/allocation_verify.rs"]
mod allocation_verify;
#[path = "dataflow/call_footprint.rs"]
mod call_footprint;
#[path = "dataflow/copy_allocation.rs"]
mod copy_allocation;
#[path = "dataflow/local_identity.rs"]
mod local_identity;
#[path = "dataflow/memory_ssa.rs"]
mod memory_ssa;
#[path = "dataflow/parallel_copy.rs"]
mod parallel_copy;
#[path = "dataflow/provenance.rs"]
mod provenance;
#[path = "dataflow/record_shapes.rs"]
mod record_shapes;
#[path = "dataflow/source_copy_locals.rs"]
mod source_copy_locals;
#[path = "dataflow/source_locals.rs"]
mod source_locals;
#[path = "dataflow/ssa_build.rs"]
mod ssa_build;
#[path = "dataflow/ssa_constants.rs"]
mod ssa_constants;
#[path = "dataflow/ssa_destroy.rs"]
mod ssa_destroy;
#[path = "dataflow/ssa_locals.rs"]
mod ssa_locals;
#[path = "dataflow/ssa_storage.rs"]
mod ssa_storage;
#[path = "dataflow/ssa_verify.rs"]
mod ssa_verify;
#[path = "dataflow/stack.rs"]
mod stack;
#[path = "dataflow/stack_cells.rs"]
mod stack_cells;
#[path = "dataflow/stack_role.rs"]
mod stack_role;
#[path = "dataflow/stack_values.rs"]
mod stack_values;
#[path = "dataflow/type_infer.rs"]
mod type_infer;
#[path = "dataflow/value_graph.rs"]
mod value_graph;
#[path = "dataflow/value_liveness.rs"]
mod value_liveness;
#[path = "dataflow/value_role.rs"]
mod value_role;
#[path = "dataflow/value_width.rs"]
mod value_width;
#[path = "dataflow/web.rs"]
mod web;
#[path = "dataflow/web_verify.rs"]
mod web_verify;
