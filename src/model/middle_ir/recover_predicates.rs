//! Check source-CFG predicates, then rebuild all CFG-dependent value identities.
use super::*;
use crate::dataflow::predicates::{PredicateEvidence, PredicatePlan};

impl Function {
    /// Recover path constants for entry executions of a closed DAG. The result
    /// retains guest steps and effects, with fresh register SSA and MIR values.
    pub fn recover_predicates(&self) -> Result<Option<(Self, PredicateEvidence)>, Error> {
        let source = self.lower()?;
        let Some(plan) = PredicatePlan::analyze(&source) else {
            return Ok(None);
        };
        let (candidate, evidence) = plan
            .lower(&source)
            .ok_or(Error::Invalid("predicate lowering"))?;
        Ok(Some((Self::from_low(&candidate)?, evidence)))
    }
}
