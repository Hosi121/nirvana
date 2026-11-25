//! Select a definition-web candidate only after independent validation.
//!
//! Source structural evidence keeps its original meaning. A renamed display
//! program has its own structural check; neither certificate covers C printing.

use crate::control_flow::structure::{StructureError, StructureStats, StructuredFunction};
use crate::control_flow::structure_verify::StructureEvidence;
use crate::model::ir::Program;

use super::{WebRecovery, structure_recovery};

pub(super) struct SelectedWebs {
    pub program: Option<Program>,
    pub structure: Result<StructuredFunction, StructureError>,
    pub source_evidence: Option<StructureEvidence>,
    pub source_stats: Option<StructureStats>,
    pub recovery: WebRecovery,
}

pub(super) fn select(original: &Program) -> SelectedWebs {
    let mut selected = keep_original(original, WebRecovery::Unchanged);
    let Some(candidate) = crate::dataflow::web::split(original) else {
        selected.recovery = WebRecovery::Unavailable;
        return selected;
    };
    let stats = candidate.stats();
    if stats.fresh_registers == 0 {
        return selected;
    }
    let evidence = match crate::dataflow::web_verify::validate(original, candidate.program()) {
        Ok(evidence) => evidence,
        Err(error) => {
            selected.recovery = if error.is_resource_limit() {
                WebRecovery::Unavailable
            } else {
                WebRecovery::Rejected(error)
            };
            return selected;
        }
    };
    let structure = structure_recovery::recover(candidate.program());
    if selected.structure.is_ok()
        && let Err(reason) = structure
    {
        // An optional value pass must not lose an available structured body.
        selected.recovery = WebRecovery::StructureFallback(reason);
        return selected;
    }
    selected.program = Some(candidate.program().clone());
    selected.structure = structure;
    selected.recovery = WebRecovery::Applied { stats, evidence };
    selected
}

pub(super) fn keep_original(original: &Program, recovery: WebRecovery) -> SelectedWebs {
    let source = structure_recovery::recover(original);
    SelectedWebs {
        program: None,
        source_evidence: source.as_ref().ok().map(StructuredFunction::evidence),
        source_stats: source.as_ref().ok().map(StructuredFunction::stats),
        structure: source,
        recovery,
    }
}
