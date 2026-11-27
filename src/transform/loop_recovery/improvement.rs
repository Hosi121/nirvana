//! Optional source-inductive extension of an already checked recovery.
use super::*;
use crate::transform::loop_entry_facts;
use crate::verification::block_verify::region::{Verdict, invariants};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryStatus {
    NotApplicable,
    SkippedBudget,
    BuildUnavailable,
    FactUnknown,
    FactCounterexample,
    ProvedUnused,
    ProposalUnavailable,
    CandidateUnproved,
    ContextUnavailable,
    UsedInIr,
}
impl EntryStatus {
    pub fn kind(self) -> &'static str {
        match self {
            Self::NotApplicable => "not_applicable",
            Self::SkippedBudget => "skipped_budget",
            Self::BuildUnavailable => "build_unavailable",
            Self::FactUnknown => "fact_unknown",
            Self::FactCounterexample => "fact_counterexample",
            Self::ProvedUnused => "proved_unused",
            Self::ProposalUnavailable => "proposal_unavailable",
            Self::CandidateUnproved => "candidate_unproved",
            Self::ContextUnavailable => "context_unavailable",
            Self::UsedInIr => "used_in_ir",
        }
    }
}
/// Diagnostic metadata, distinct from the retained source-bound certificate.
/// `used_in_ir` describes IR selection; C rendering has its own acceptance gate.
#[derive(Clone, Debug)]
pub struct EntryAttempt {
    pub status: EntryStatus,
    pub phase: Option<invariants::Phase>,
    pub header: Option<u64>,
    pub normalizers: usize,
    pub before_lanes: usize,
    pub after_lanes: usize,
    pub elapsed: Duration,
}
impl EntryAttempt {
    pub(super) fn new(lanes: usize) -> Self {
        Self {
            status: EntryStatus::NotApplicable,
            phase: None,
            header: None,
            normalizers: 0,
            before_lanes: lanes,
            after_lanes: lanes,
            elapsed: Duration::ZERO,
        }
    }
}
impl Recovered {
    pub(super) fn improve(mut self, solver: &Solver, deadline: Instant) -> Self {
        let start = Instant::now();
        let mut attempt = EntryAttempt::new(self.entry_attempt.before_lanes);
        let result = self.try_improve(solver, deadline, &mut attempt);
        if let Some((contextual, expanded, group)) = result {
            let mut candidate = Self {
                prepared: self.prepared.clone(),
                contextual,
                expanded,
                group,
                entry_attempt: attempt.clone(),
            };
            if candidate.validate().is_ok() {
                attempt.status = EntryStatus::UsedInIr;
                attempt.after_lanes = candidate
                    .contextual
                    .verified_region()
                    .proposal()
                    .lane_group()
                    .kernels
                    .len();
                attempt.elapsed = start.elapsed();
                candidate.entry_attempt = attempt;
                return candidate;
            }
            attempt.status = EntryStatus::ContextUnavailable;
        }
        attempt.elapsed = start.elapsed();
        self.entry_attempt = attempt;
        self
    }
    fn try_improve(
        &self,
        solver: &Solver,
        deadline: Instant,
        trace: &mut EntryAttempt,
    ) -> Option<(rolled_loop::ContextualRoll, Expanded, usize)> {
        if Instant::now() >= deadline {
            trace.status = EntryStatus::SkippedBudget;
            return None;
        }
        let base = self.contextual.verified_region().proposal();
        let problem = match loop_entry_facts::propose(base) {
            Ok(Some(problem)) => problem,
            Ok(None) => return None,
            Err(_) => {
                trace.status = EntryStatus::BuildUnavailable;
                return None;
            }
        };
        trace.header = Some(problem.header());
        trace.normalizers = problem.normalizers().len();
        // Share the extension deadline, reserving a small tail for local proofs.
        let remaining = deadline.saturating_duration_since(Instant::now());
        let reserve = (remaining / 3).min(Duration::from_secs(2));
        let budget = remaining
            .saturating_sub(reserve)
            .min(Duration::from_secs(5));
        let certificate: Arc<invariants::Certificate> = match problem.check(solver, budget) {
            invariants::Outcome::Verified(certificate) => certificate.into(),
            invariants::Outcome::Unproved(failure) => {
                trace.phase = Some(failure.phase);
                trace.status = if matches!(failure.verdict, Verdict::Counterexample(_)) {
                    EntryStatus::FactCounterexample
                } else {
                    EntryStatus::FactUnknown
                };
                return None;
            }
        };
        trace.status = EntryStatus::ProvedUnused;
        let source = self.prepared.compact.program();
        let caps: Vec<_> = certificate
            .bit_caps(source, problem.header())
            .ok()?
            .into_iter()
            .enumerate()
            .filter(|(_, bits)| *bits < 64)
            .map(|(n, bits)| (Reg(n), bits))
            .collect();
        let aligned = base
            .discovery()
            .with_advisory_entry_caps(problem.header(), &caps)
            .ok()?;
        let (index, _) = aligned
            .groups()
            .iter()
            .enumerate()
            .filter(|(_, group)| group.kernels.len() > trace.before_lanes)
            .max_by_key(|(_, group)| group.kernels.len())?;
        trace.status = EntryStatus::ProposalUnavailable;
        let proposal =
            rolled_loop::propose_with_invariants(source, &aligned, index, &certificate).ok()?;
        trace.status = EntryStatus::CandidateUnproved;
        let comparison_deadline = deadline.min(Instant::now() + Duration::from_secs(5));
        let rolled_loop::Outcome::Verified(verified) =
            proposal.verify_until(solver, comparison_deadline)
        else {
            return None;
        };
        trace.status = EntryStatus::ContextUnavailable;
        let contextual = verified.in_context().ok()?;
        let expanded = self
            .prepared
            .compact
            .expand_candidate(contextual.program())
            .ok()?;
        Some((contextual, expanded, index))
    }
}
