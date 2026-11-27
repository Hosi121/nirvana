//! Compose closed DAG regions through explicit, checked cut relations.
//!
//! A relation shares selected registers and requires pure fixed-point equations
//! on either side. Entry normalization covers every related state. Separate
//! postcondition obligations establish those equations at each incoming cut;
//! correspondence obligations establish the next cut and its shared values.
//! Every obligation retains all RAM and first faults. Terminal observations
//! come from the original Query. Local witnesses need not be globally reachable.
use super::*;
use crate::model::ir::Assignment;

mod build;
#[cfg(test)]
mod tests;

pub const MODEL_ID: &str = "checked-dag-cut-composition-v1";
pub const MAX_CUTS: usize = 16;
const MAX_TOTAL_SCRIPT: usize = 16 * 1024 * 1024;

/// The first cut is the original entry and has its exact shared interface and
/// no equations. At later cuts an assignment means `destination == value` in
/// the incoming state. Only register assignments with load-free values qualify.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cut {
    pub before: u64,
    pub after: u64,
    pub shared: Vec<Reg>,
    pub before_invariants: Vec<Assignment>,
    pub after_invariants: Vec<Assignment>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    Region(Error),
    Boundary,
    Invariant,
    DynamicReturn,
    Projection,
    Limit,
}
impl From<Error> for BuildError {
    fn from(error: Error) -> Self {
        Self::Region(error)
    }
}
impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DAG cut composition: {self:?}")
    }
}
impl std::error::Error for BuildError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    Correspondence,
    BeforePostconditions,
    AfterPostconditions,
}

#[derive(Clone, Debug)]
pub struct Obligation {
    cut: usize,
    kind: Kind,
    query: Query,
}
impl Obligation {
    pub fn cut(&self) -> usize {
        self.cut
    }
    pub fn kind(&self) -> Kind {
        self.kind
    }
    pub fn query(&self) -> &Query {
        &self.query
    }
}

#[derive(Clone, Debug)]
pub struct Problem {
    original: Query,
    cuts: Vec<Cut>,
    obligations: Vec<Obligation>,
}
impl Problem {
    pub fn new(original: &Query, cuts: &[Cut]) -> Result<Self, BuildError> {
        build::problem(original, cuts)
    }
    pub fn original(&self) -> &Query {
        &self.original
    }
    pub fn cuts(&self) -> &[Cut] {
        &self.cuts
    }
    pub fn obligations(&self) -> &[Obligation] {
        &self.obligations
    }
    /// All correspondence and postcondition queries share one wall deadline.
    /// Only a complete set of UNSAT results constructs the source-bound seal.
    pub fn check(&self, solver: &Solver, budget: Duration) -> Outcome {
        let deadline = Instant::now() + budget.min(Duration::from_secs(30));
        for (index, obligation) in self.obligations.iter().enumerate() {
            let verdict = if Instant::now() >= deadline {
                Verdict::Unknown(UnknownReason::SolverTimeout)
            } else {
                obligation
                    .query
                    .check_script(solver, obligation.query.smt2(), Some(deadline))
            };
            if verdict != Verdict::EquivalentUnderModel {
                return Outcome::Unproved(Box::new(Failure {
                    cut: obligation.cut,
                    kind: obligation.kind,
                    checked: index + 1,
                    total: self.obligations.len(),
                    verdict,
                }));
            }
        }
        Outcome::Verified(Box::new(Certificate {
            problem: self.clone(),
        }))
    }
}

/// A failed local obligation. Its counterexample may violate an earlier path
/// condition, so it is not a counterexample to the original whole-region Query.
#[derive(Clone, Debug)]
pub struct Failure {
    pub cut: usize,
    pub kind: Kind,
    pub checked: usize,
    pub total: usize,
    pub verdict: Verdict,
}
#[derive(Clone, Debug)]
pub enum Outcome {
    Verified(Box<Certificate>),
    Unproved(Box<Failure>),
}
/// Equivalence of the retained original Query under its unchanged boundary
/// observations, established through all local obligations and cut relations.
#[derive(Clone, Debug)]
pub struct Certificate {
    problem: Problem,
}
impl Certificate {
    pub fn problem(&self) -> &Problem {
        &self.problem
    }
    pub fn checked(&self) -> usize {
        self.problem.obligations.len()
    }
    pub fn matches(&self, query: &Query) -> bool {
        let original = &self.problem.original;
        fn same(a: &Program, b: &Program) -> bool {
            a.register_count() == b.register_count()
                && a.cfg().block(a.cfg().entry()).start == b.cfg().block(b.cfg().entry()).start
                && a.instructions() == b.instructions()
        }
        same(&original.before, &query.before)
            && same(&original.after, &query.after)
            && original.shared == query.shared
            && original.outputs == query.outputs
            && original.script == query.script
    }
}
