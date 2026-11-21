//! module integration suite.
#[allow(dead_code)]
mod support;

#[path = "module/module_bindings.rs"]
mod module_bindings;
#[path = "module/module_divide.rs"]
mod module_divide;
#[path = "module/module_emit.rs"]
mod module_emit;
#[path = "module/module_formatted.rs"]
mod module_formatted;
#[path = "module/module_ir.rs"]
mod module_ir;
#[path = "module/module_local_plan.rs"]
mod module_local_plan;
#[path = "module/module_memory_ssa.rs"]
mod module_memory_ssa;
#[path = "module/module_outline.rs"]
mod module_outline;
#[path = "module/module_posix.rs"]
mod module_posix;
#[path = "module/module_readable.rs"]
mod module_readable;
#[path = "module/module_readable_render.rs"]
mod module_readable_render;
#[path = "module/module_sparse.rs"]
mod module_sparse;
#[path = "module/module_tail_dispatch.rs"]
mod module_tail_dispatch;
#[path = "module/module_values.rs"]
mod module_values;
