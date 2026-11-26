//! A bijective namespace plus independent paired-tree register correspondence.
use super::*;
pub(super) fn validate(compact: &Compact) -> Result<(), Error> {
    use crate::model::ir::renaming::{self, Unmapped};
    shape::bounded_source(&compact.source, MAX_SOURCE_REGISTERS)?;
    shape::bounded_successors(&compact.program)?;
    if compact.registers.windows(2).any(|p| p[0].0 >= p[1].0)
        || compact
            .registers
            .iter()
            .any(|r| r.0 >= compact.source.register_count())
    {
        return Err(Error::BoundaryMapping);
    }
    let names = compact
        .registers
        .iter()
        .enumerate()
        .map(|(n, r)| (r.0, Reg(n)))
        .collect();
    if !renaming::validate(
        &compact.source,
        &compact.program,
        compact.registers.len(),
        &names,
        Unmapped::Reject,
    ) {
        return Err(Error::BoundaryMapping);
    }
    Ok(())
}
