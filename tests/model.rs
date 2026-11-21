//! model integration suite.
#[allow(dead_code)]
mod support;

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
#[path = "model/ir_and_structure.rs"]
mod ir_and_structure;
#[path = "model/memory_ir.rs"]
mod memory_ir;
#[path = "model/nonlocal_transfers.rs"]
mod nonlocal_transfers;
#[path = "model/run_reports.rs"]
mod run_reports;
#[path = "model/sparse_memory.rs"]
mod sparse_memory;
