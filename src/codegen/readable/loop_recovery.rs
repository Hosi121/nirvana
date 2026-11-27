//! Opt-in loop recovery with the original render retained as its reference.
//!
//! Region completion, local equivalence, function context and storage naming
//! are checked before rendering. C emission remains a separate M0 boundary.
use super::{ReadableC, ReadableError, ReadableOptions, SignedStorageProvenance};
use crate::model::{ir::Program, middle_ir::Function};
use crate::transform::loop_recovery::{self, EntryAttempt, Recovered};
use crate::verification::verify::Solver;
use std::time::{Duration, Instant};

pub const MODEL_ID: &str = "checked-readable-loop-selection-v1";

#[derive(Clone, Debug)]
pub enum Retention {
    Provenance(&'static str),
    Recovery(loop_recovery::Reason),
    Rendering(ReadableError),
    Parameters,
    Quality,
}
impl Retention {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Provenance(_) => "provenance_unavailable",
            Self::Recovery(loop_recovery::Reason::Unknown(_)) => "unknown",
            Self::Recovery(loop_recovery::Reason::Counterexample(_)) => "counterexample",
            Self::Recovery(loop_recovery::Reason::Incomplete(_)) => "incomplete",
            Self::Recovery(loop_recovery::Reason::NoGroups) => "no_groups",
            Self::Recovery(_) => "recovery_unavailable",
            Self::Rendering(_) => "rendering_unavailable",
            Self::Parameters => "parameters",
            Self::Quality => "quality",
        }
    }
}

/// A rendered candidate always retains the exact source-bound recovery chain.
#[derive(Clone, Debug)]
pub struct Candidate {
    output: ReadableC,
    recovery: Box<Recovered>,
}
impl Candidate {
    pub fn output(&self) -> &ReadableC {
        &self.output
    }
    pub fn recovery(&self) -> &Recovered {
        &self.recovery
    }
}

/// Keeps baseline stage evidence separate from the selected C's evidence.
/// A quality-declined candidate can still be inspected without being adopted.
#[derive(Clone, Debug)]
pub struct Emission {
    baseline: ReadableC,
    candidate: Option<Candidate>,
    retention: Option<Retention>,
    elapsed: Duration,
    entry_attempt: Option<EntryAttempt>,
}
impl Emission {
    pub fn baseline(&self) -> &ReadableC {
        &self.baseline
    }
    pub fn candidate(&self) -> Option<&Candidate> {
        self.candidate.as_ref()
    }
    pub fn retention(&self) -> Option<&Retention> {
        self.retention.as_ref()
    }
    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }
    pub fn entry_attempt(&self) -> Option<&EntryAttempt> {
        self.entry_attempt.as_ref()
    }
    pub fn selected(&self) -> &ReadableC {
        match (&self.candidate, &self.retention) {
            (Some(candidate), None) => candidate.output(),
            _ => &self.baseline,
        }
    }
    pub fn accepted(&self) -> bool {
        self.candidate.is_some() && self.retention.is_none()
    }
    pub fn into_selected(self) -> ReadableC {
        match (self.candidate, self.retention) {
            (Some(candidate), None) => candidate.output,
            _ => self.baseline,
        }
    }
}

/// Prefer a complete structured render, then the ordinary local/text ranking.
/// Existing emission APIs retain their original policy and solver-free path.
fn cost(output: &ReadableC) -> (bool, usize, usize, usize) {
    let (locals, body, all) = super::pipeline::render_cost(output);
    (output.fallback_reason.is_some(), locals, body, all)
}

fn recover(
    baseline: ReadableC,
    options: ReadableOptions,
    solver: &Solver,
    start: Instant,
) -> Emission {
    let mut emission = Emission {
        baseline,
        candidate: None,
        retention: None,
        elapsed: Duration::ZERO,
        entry_attempt: None,
    };
    let retain = |emission: &mut Emission, reason| {
        emission.retention = Some(reason);
        emission.elapsed = start.elapsed();
    };
    let source = match &emission.baseline.signed_storage_provenance {
        SignedStorageProvenance::Captured(snapshot) => snapshot.source.clone(),
        SignedStorageProvenance::NotCaptured => {
            retain(
                &mut emission,
                Retention::Provenance("display source not captured"),
            );
            return emission;
        }
        SignedStorageProvenance::Unavailable(reason)
        | SignedStorageProvenance::Rejected(reason) => {
            let reason = *reason;
            retain(&mut emission, Retention::Provenance(reason));
            return emission;
        }
    };
    let recovery = match loop_recovery::recover_before(
        &source,
        &emission.baseline.parameters,
        solver,
        start + Duration::from_secs(10),
    ) {
        loop_recovery::Outcome::Recovered(recovered) => recovered,
        loop_recovery::Outcome::Retained { reason, .. } => {
            retain(&mut emission, Retention::Recovery(reason));
            return emission;
        }
    };
    emission.entry_attempt = Some(recovery.entry_attempt().clone());
    let output = match super::emit_readable_c_with_storage_provenance(recovery.program(), options) {
        Ok(output) => output,
        Err(error) => {
            retain(&mut emission, Retention::Rendering(error));
            return emission;
        }
    };
    if output.parameters != emission.baseline.parameters {
        retain(&mut emission, Retention::Parameters);
        return emission;
    }
    let improves = cost(&output) < cost(&emission.baseline);
    emission.candidate = Some(Candidate { output, recovery });
    if !improves {
        emission.retention = Some(Retention::Quality);
    }
    emission.elapsed = start.elapsed();
    emission
}

pub fn emit_readable_c(
    source: &Program,
    options: ReadableOptions,
    solver: &Solver,
) -> Result<Emission, ReadableError> {
    let start = Instant::now();
    Ok(recover(
        super::emit_readable_c_with_storage_provenance(source, options)?,
        options,
        solver,
        start,
    ))
}
pub fn emit_middle_c(
    source: &Function,
    options: ReadableOptions,
    solver: &Solver,
) -> Result<Emission, ReadableError> {
    let start = Instant::now();
    Ok(recover(
        super::emit_middle_c_with_storage_provenance(source, options)?,
        options,
        solver,
        start,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{Control, Expr, IrInstruction};

    #[test]
    fn no_lane_group_keeps_the_exact_baseline_without_starting_a_solver() {
        let source = Program::new(
            0,
            1,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(42)),
            }],
        )
        .unwrap();
        let options = ReadableOptions::default();
        let baseline =
            super::super::emit_readable_c_with_storage_provenance(&source, options).unwrap();
        let output = emit_readable_c(&source, options, &Solver::new("/missing/solver")).unwrap();
        assert!(!output.accepted());
        assert!(output.candidate().is_none());
        assert!(matches!(output.retention(), Some(Retention::Recovery(_))));
        assert_eq!(output.selected().code, baseline.code);
        assert_eq!(output.selected().parameters, baseline.parameters);
    }
}
