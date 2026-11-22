//! cli integration suite.
#[path = "support"]
mod support {
    #[allow(dead_code)]
    pub mod native;
}

#[path = "cli/middle_ir_cli.rs"]
mod middle_ir_cli;
#[path = "cli/record_shapes_cli.rs"]
mod record_shapes_cli;
#[path = "cli/reference_cli.rs"]
mod reference_cli;
#[path = "cli/ssa_destroy_cli.rs"]
mod ssa_destroy_cli;
#[path = "cli/type_infer_cli.rs"]
mod type_infer_cli;
