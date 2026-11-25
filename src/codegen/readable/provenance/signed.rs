//! Retain the signed proof consumed at final display-local selection.

use super::{CapturePolicy, StorageCaptureLimits, source_budget};
use crate::dataflow::signed_width::{Claim, SignedWidths, ValidationError};
use crate::dataflow::ssa::{
    Definition, PhiInput, PointValues, RegisterValue, SsaBlock, SsaFunction, ValueId,
};
use crate::model::ir::Program;
use std::mem::size_of;
use std::sync::Arc;

/// The final prepared display source and the same signed facts used to choose
/// its C locals. This phase is always after accepted presentation/DCE passes;
/// the unsigned snapshot can retain a different, earlier program.
#[derive(Clone, Debug)]
pub struct SignedStorageSnapshot {
    pub source: Arc<Program>,
    pub widths: SignedWidths,
}

#[derive(Clone, Debug, Default)]
pub enum SignedStorageProvenance {
    #[default]
    NotCaptured,
    Unavailable(&'static str),
    /// Preserve a known rejected proposal before optional retention limits.
    /// Signed local selection uses the analysis's U64 fallback.
    Rejected(&'static str),
    Captured(Arc<SignedStorageSnapshot>),
}

pub(in crate::codegen::readable) fn capture(
    policy: CapturePolicy,
    source: &Arc<Program>,
    widths: SignedWidths,
) -> SignedStorageProvenance {
    let status = widths.verification().map(|_| ()).map_err(|error| *error);
    capture_with_status(policy, source, widths, status)
}

fn capture_with_status(
    policy: CapturePolicy,
    source: &Arc<Program>,
    widths: SignedWidths,
    status: Result<(), ValidationError>,
) -> SignedStorageProvenance {
    let CapturePolicy::On(limits) = policy else {
        return SignedStorageProvenance::NotCaptured;
    };
    match status {
        Err(ValidationError::Invalid(reason)) => return SignedStorageProvenance::Rejected(reason),
        Err(ValidationError::Unavailable(reason)) => {
            return SignedStorageProvenance::Unavailable(reason);
        }
        Ok(()) => {}
    }
    if let Err(reason) = preflight(source, &widths, limits) {
        return SignedStorageProvenance::Unavailable(reason);
    }
    SignedStorageProvenance::Captured(Arc::new(SignedStorageSnapshot {
        source: Arc::clone(source),
        widths,
    }))
}

fn preflight(
    source: &Program,
    widths: &SignedWidths,
    limits: StorageCaptureLimits,
) -> Result<(), &'static str> {
    let mut budget = source_budget(source, limits, size_of::<SignedStorageSnapshot>())?;
    let graph = widths
        .ssa()
        .ok_or("signed storage capture missing checked SSA")?;
    budget.bytes(
        1,
        size_of::<SignedWidths>() + size_of::<SsaFunction>() + 256,
    )?;
    // Account for retained vector capacities conservatively, including the
    // exact/width claims in the immutable certificate. No source or graph is
    // cloned while estimating this optional retention cost.
    budget.bytes(
        graph.values.len(),
        2 * (size_of::<Definition>() + size_of::<Claim>()) + 64,
    )?;
    budget.bytes(graph.blocks.len(), 2 * size_of::<SsaBlock>() + 64)?;
    for definition in &graph.values {
        if let Definition::Phi { inputs, .. } = definition {
            budget.bytes(inputs.len(), 2 * size_of::<PhiInput>() + 16)?;
        }
    }
    for block in &graph.blocks {
        budget.bytes(block.phis.len(), 2 * size_of::<ValueId>() + 16)?;
        budget.bytes(block.exit_values.len(), 2 * size_of::<RegisterValue>() + 16)?;
        budget.bytes(block.points.len(), 2 * size_of::<PointValues>() + 32)?;
        for point in &block.points {
            budget.bytes(point.reads.len(), 2 * size_of::<RegisterValue>() + 16)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
