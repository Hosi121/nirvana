//! end to end integration suite.
#[allow(dead_code)]
mod support;

#[path = "end_to_end/algorithm_fixtures.rs"]
mod algorithm_fixtures;
#[path = "end_to_end/dispatch_programs.rs"]
mod dispatch_programs;
#[path = "end_to_end/divide_compiler.rs"]
mod divide_compiler;
#[path = "end_to_end/generated_recovery.rs"]
mod generated_recovery;
#[path = "end_to_end/input_breadth.rs"]
mod input_breadth;
#[path = "end_to_end/jump_table_module.rs"]
mod jump_table_module;
#[path = "end_to_end/linked_pipeline.rs"]
mod linked_pipeline;
#[path = "end_to_end/linked_unwind.rs"]
mod linked_unwind;
#[path = "end_to_end/machine_pipeline.rs"]
mod machine_pipeline;
#[path = "end_to_end/module_memory_trace.rs"]
mod module_memory_trace;
#[path = "end_to_end/native_c.rs"]
mod native_c;
#[path = "end_to_end/puts_pipeline.rs"]
mod puts_pipeline;
#[path = "end_to_end/recovery_fixture.rs"]
mod recovery_fixture;
#[path = "end_to_end/stripped_elf.rs"]
mod stripped_elf;
