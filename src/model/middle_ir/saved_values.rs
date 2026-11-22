//! Saved-word identities on native MIR reads. Normal MIR execution/lowering
//! keeps machine storage. Snapshot materialization is an explicit projection.
use super::*;
use crate::dataflow::memory_values::{MemoryValueEvidence, MemoryValuePlan};
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SavedEvidence {
    pub memory: MemoryValueEvidence,
    /// Distinct MIR read bindings; source-tree occurrences may share a binding.
    pub annotated_reads: usize,
    pub phi_values: usize,
    pub merged_snapshots: usize,
}
#[derive(Clone, Debug)]
pub(super) struct Recovery {
    plan: MemoryValuePlan,
    view: SavedValueView,
    evidence: SavedEvidence,
}
#[derive(Clone, Debug)]
pub struct SavedLowering {
    program: Program,
    source_registers: usize,
    evidence: SavedEvidence,
}
impl SavedLowering {
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn source_registers(&self) -> usize {
        self.source_registers
    }
    pub fn evidence(&self) -> SavedEvidence {
        self.evidence
    }
    /// Compare entry executions by discarding only the new internal registers.
    pub fn project_report(&self, mut report: ir::RunReport) -> Result<ir::RunReport, Error> {
        if report.state.registers.len() != self.program.register_count() {
            return Err(Error::Invalid("saved lowering report register count"));
        }
        report.state.registers.truncate(self.source_registers);
        Ok(report)
    }
}
impl Function {
    /// None means the existing bounded analysis produced no checked replacement
    /// plan. This does not prove the absence of saved-value identities.
    pub fn recover_saved_values(&self) -> Result<Option<(Self, SavedEvidence)>, Error> {
        self.lower()?;
        if let Some(saved) = &self.saved {
            return Ok(Some((self.clone(), saved.evidence)));
        }
        let source = lower::program(self, false)?;
        let Some(plan) = MemoryValuePlan::analyze(&source) else {
            return Ok(None);
        };
        let plan = plan
            .canonicalize(&source)
            .ok_or(Error::Invalid("saved root source"))?;
        let view = plan.inspect(&source).map_err(Error::Ssa)?;
        let mut candidate = self.clone();
        let annotated_reads = annotate(&mut candidate, &view);
        let evidence = evidence(
            self,
            &view,
            plan.evidence(),
            annotated_reads,
            plan.merged_snapshots(),
        );
        candidate.saved = Some(Recovery {
            plan,
            view,
            evidence,
        });
        self.validate_saved_recovery(&candidate)?;
        Ok(Some((candidate, evidence)))
    }
    pub fn saved_values(&self) -> Option<&SavedValueView> {
        self.saved.as_ref().map(|s| &s.view)
    }
    pub fn validate_saved_recovery(&self, candidate: &Self) -> Result<SavedEvidence, Error> {
        self.lower()?;
        let mut expected = self.clone();
        let saved = candidate
            .saved
            .as_ref()
            .ok_or(Error::Invalid("missing saved value plan"))?;
        annotate(&mut expected, &saved.view);
        if expected.blocks != candidate.blocks
            || self.storages != candidate.storages
            || self.entry != candidate.entry
            || self.value_count != candidate.value_count
            || self.source_value_count != candidate.source_value_count
        {
            return Err(Error::Invalid("saved recovery changed MIR source"));
        }
        candidate.lower()?;
        Ok(saved.evidence)
    }
    /// Materialize checked captures using the existing saved-value lowerer.
    /// Original machine registers remain the prefix; extra registers are internal.
    pub fn lower_saved_values(&self) -> Result<Option<SavedLowering>, Error> {
        self.lower()?;
        let Some(saved) = &self.saved else {
            return Ok(None);
        };
        let source = lower::program(self, false)?;
        let program = saved
            .plan
            .lower(&source)
            .ok_or(Error::Invalid("saved value materialization"))?;
        Ok(Some(SavedLowering {
            program,
            source_registers: self.storages.len(),
            evidence: saved.evidence,
        }))
    }
}
fn evidence(
    function: &Function,
    view: &SavedValueView,
    memory: MemoryValueEvidence,
    annotated_reads: usize,
    merged_snapshots: usize,
) -> SavedEvidence {
    SavedEvidence {
        memory,
        annotated_reads,
        merged_snapshots,
        phi_values: view
            .values
            .iter()
            .zip(&function.ssa.values)
            .filter(|(fact, definition)| {
                fact.is_some() && matches!(definition, ssa::Definition::Phi { .. })
            })
            .count(),
    }
}
fn annotate(function: &mut Function, view: &SavedValueView) -> usize {
    let mut count = 0;
    walk::visit_mut(function, |binding| {
        if let Operation::ReadStorage { storage, version }
        | Operation::ReadSaved {
            storage, version, ..
        } = binding.operation
        {
            binding.operation = match version.and_then(|id| view.substitutions.get(&id)) {
                Some(&slice) => {
                    count += 1;
                    Operation::ReadSaved {
                        storage,
                        version,
                        slice,
                    }
                }
                None => Operation::ReadStorage { storage, version },
            };
        }
    });
    count
}
pub(super) fn validate(function: &Function) -> Result<(), Error> {
    let Some(saved) = &function.saved else {
        let mut has_saved = false;
        walk::visit(function, |b| {
            has_saved |= matches!(b.operation, Operation::ReadSaved { .. });
            Ok(())
        })?;
        return if has_saved {
            Err(Error::Invalid("saved read without a plan"))
        } else {
            Ok(())
        };
    };
    let source = lower::program(function, false)?;
    let checked = saved.plan.inspect(&source).map_err(Error::Ssa)?;
    if saved.view != checked {
        return Err(Error::Invalid("stale saved value descriptors"));
    }
    let mut expected = function.clone();
    let count = annotate(&mut expected, &checked);
    if expected.blocks != function.blocks
        || saved.evidence
            != evidence(
                function,
                &checked,
                saved.plan.evidence(),
                count,
                saved.plan.merged_snapshots(),
            )
    {
        return Err(Error::Invalid("unproved saved read identity"));
    }
    Ok(())
}
