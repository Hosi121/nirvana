use super::*;
use extraction::{
    live_out::{self, ContinuationOutputs},
    repeat::{self, Complete, Completion, Prefixed},
};
use std::time::Duration;

#[derive(Clone, Debug)]
pub enum Outcome {
    Verified(Box<VerifiedRoll>),
    Counterexample(Box<Counterexample>),
    Incomplete(Box<repeat::Exhaustion>),
    Unknown(UnknownReason),
}
/// Source-bound verification obligations, available before running the solver.
/// The comparison is over a bounded DAG; adoption additionally requires the
/// independent completion query. `check` is the constructor of VerifiedRoll.
#[derive(Clone, Debug)]
pub struct VerificationProblem {
    proposal: Proposal,
    prefixed: Prefixed,
    outputs: ContinuationOutputs,
    query: region::Query,
    completion: region::Query,
}
/// A proposal accepted under the checked region boundary. Its retained problem
/// and completion seal identify the exact sources, interface and bounded DAG.
#[derive(Clone, Debug)]
pub struct VerifiedRoll {
    problem: VerificationProblem,
    complete: Complete,
    checked: usize,
}
impl VerifiedRoll {
    pub fn program(&self) -> &Program {
        self.proposal().program()
    }
    pub fn proposal(&self) -> &Proposal {
        &self.problem.proposal
    }
    pub fn complete(&self) -> &Complete {
        &self.complete
    }
    pub fn outputs(&self) -> &ContinuationOutputs {
        &self.problem.outputs
    }
    pub fn query(&self) -> &region::Query {
        &self.problem.query
    }
    pub fn completion_query(&self) -> &region::Query {
        &self.problem.completion
    }
    pub fn checked_partitions(&self) -> usize {
        self.checked
    }
}
fn query_error(error: region::Error) -> Error {
    if error == region::Error::Limit {
        Error::Limit
    } else {
        Error::Projection
    }
}
impl Proposal {
    pub fn verification_problem(&self) -> Result<VerificationProblem, Error> {
        if !self.before.belongs_to(&self.padded) {
            return Err(Error::Source);
        }
        let mut stops = self.envelope.stops();
        stops.push(self.feedback);
        stops.sort_unstable();
        stops.dedup();
        let prefix = extraction::extract(&self.program, self.envelope.header, &stops, None)?;
        let iteration = extraction::extract(&self.program, self.feedback, &stops, None)?;
        let unfolding = repeat::unfold(&iteration, self.rounds)?;
        let prefixed = Prefixed::new(&prefix, &unfolding)?;
        let completion = prefixed.completion_query()?;
        let outputs = live_out::derive(&self.before)?;
        let shared: Vec<_> = (0..self.padded.register_count()).map(Reg).collect();
        let query = region::query_at_returns(
            self.before.program(),
            prefixed.program(),
            &shared,
            outputs.returns(),
        )
        .map_err(query_error)?;
        Ok(VerificationProblem {
            proposal: self.clone(),
            prefixed,
            outputs,
            query,
            completion,
        })
    }
    pub fn verify(&self, solver: &Solver) -> Outcome {
        match self.verification_problem() {
            Ok(problem) => problem.check(solver),
            Err(Error::Limit) => Outcome::Unknown(UnknownReason::ResourceLimit),
            Err(_) => Outcome::Unknown(UnknownReason::BoundaryMapping),
        }
    }
}
impl VerificationProblem {
    pub fn proposal(&self) -> &Proposal {
        &self.proposal
    }
    pub fn query(&self) -> &region::Query {
        &self.query
    }
    pub fn completion_query(&self) -> &region::Query {
        &self.completion
    }
    pub fn outputs(&self) -> &ContinuationOutputs {
        &self.outputs
    }
    /// Propose local lane relations and source-bound obligations. Incoming
    /// equations are proved at every cut before they can supply a certificate.
    pub fn composition_problem(&self) -> Result<region::composition::Problem, Error> {
        super::composition::problem(&self.proposal, &self.prefixed, &self.query)
    }
    /// The case family covers full64-bit input words and retains all RAM/fault
    /// observations. It is available for replay regardless of solver outcome.
    pub fn input_partitions(&self) -> Result<Option<region::InputPartitions<'_>>, region::Error> {
        let Some(&(reg, bits)) = self.proposal.selectors.first() else {
            return Ok(None);
        };
        let mut cases = self.query.input_partitions(reg, bits)?;
        for &(reg, bits) in &self.proposal.selectors[1..] {
            cases = cases.with_input(reg, bits)?;
        }
        Ok(Some(cases))
    }
    pub fn check(&self, solver: &Solver) -> Outcome {
        let complete = match self
            .prefixed
            .check_complete(&solver.limited_to(Duration::from_secs(5)))
        {
            Completion::Complete(complete) => complete,
            Completion::BoundExceeded(witness) => return Outcome::Incomplete(witness),
            Completion::Unknown(reason) => return Outcome::Unknown(reason),
        };
        let result = match self.input_partitions() {
            Ok(Some(cases)) => cases.check(solver, Duration::from_secs(15)),
            Ok(None) => self
                .query
                .check_partitioned(solver, Duration::from_secs(15)),
            Err(region::Error::Limit) => return Outcome::Unknown(UnknownReason::ResourceLimit),
            Err(_) => return Outcome::Unknown(UnknownReason::BoundaryMapping),
        };
        match result.verdict {
            region::Verdict::EquivalentUnderModel => Outcome::Verified(Box::new(VerifiedRoll {
                problem: self.clone(),
                complete,
                checked: result.checked,
            })),
            region::Verdict::Counterexample(witness) => {
                match super::replay::check(&self.proposal, witness, &self.outputs) {
                    Ok(witness) => Outcome::Counterexample(Box::new(witness)),
                    Err(reason) => Outcome::Unknown(reason),
                }
            }
            region::Verdict::Unknown(reason) => Outcome::Unknown(reason),
        }
    }
}
