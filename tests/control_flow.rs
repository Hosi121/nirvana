//! control flow integration suite.
#[allow(dead_code)]
mod support;

#[path = "control_flow/analysis.rs"]
mod analysis;
#[path = "control_flow/branch_tail.rs"]
mod branch_tail;
#[path = "control_flow/cfg.rs"]
mod cfg;
#[path = "control_flow/join_recovery.rs"]
mod join_recovery;
#[path = "control_flow/loop_exit.rs"]
mod loop_exit;
#[path = "control_flow/loop_recover.rs"]
mod loop_recover;
#[path = "control_flow/loop_shape.rs"]
mod loop_shape;
#[path = "control_flow/postdom.rs"]
mod postdom;
#[path = "control_flow/structure_splitting.rs"]
mod structure_splitting;
#[path = "control_flow/structure_verification.rs"]
mod structure_verification;
