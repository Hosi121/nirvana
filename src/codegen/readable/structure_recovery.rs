//! Readable-only alternative loop-follow placement. Public/core recovery
//! retains its established policy and per-block copy bound.

use crate::control_flow::structure::{StructureError, StructuredFunction};
use crate::model::ir::Program;

pub(super) fn recover(program: &Program) -> Result<StructuredFunction, StructureError> {
    StructuredFunction::recover_for_readable(program)
}
