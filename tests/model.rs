//! model integration suite.
#[path = "support"]
mod support {
    #[allow(dead_code)]
    pub mod checked_c;
    pub mod ir;
    #[allow(dead_code)]
    pub mod native;
    #[path = "../../examples/programs/mod.rs"]
    pub mod programs;
}

#[path = "model/call_preservation.rs"]
mod call_preservation;
#[path = "model/effects.rs"]
mod effects;
#[path = "model/effects_observe.rs"]
mod effects_observe;
#[path = "model/expression_ir.rs"]
mod expression_ir;
#[path = "model/hir.rs"]
mod hir;
#[path = "model/integer_ops.rs"]
mod integer_ops;
#[path = "model/ir_and_structure.rs"]
mod ir_and_structure;
#[path = "model/memory_ir.rs"]
mod memory_ir;
#[path = "model/nonlocal_transfers.rs"]
mod nonlocal_transfers;
#[path = "model/run_reports.rs"]
mod run_reports;
#[path = "model/semantic_ir.rs"]
mod semantic_ir;
#[path = "model/sparse_memory.rs"]
mod sparse_memory;
#[path = "model/unary_ops.rs"]
mod unary_ops;
