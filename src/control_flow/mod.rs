//! CFG analysis, structural recovery and its independent checks.

pub mod analysis;
pub mod branch_tail;
pub mod cfg;
pub(crate) mod join;
pub mod loop_exit;
pub mod loop_recover;
pub mod loop_shape;
pub mod postdom;
pub mod structure;
pub mod structure_verify;
