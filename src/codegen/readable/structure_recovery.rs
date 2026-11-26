//! Readable placement is selected independently of expanded core recovery.
//! Every accepted layout retains the original correspondence and copy bounds.

use crate::control_flow::structure::{StructureError, StructuredFunction};
use crate::model::ir::Program;

pub(super) fn recover(program: &Program) -> Result<StructuredFunction, StructureError> {
    StructuredFunction::recover_for_readable(program)
}
