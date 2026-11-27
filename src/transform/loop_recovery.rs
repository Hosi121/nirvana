//! Source-bound storage, loop proof, context and ABI namespace recovery.
use super::{allocated_storage, rolled_loop};
use crate::dataflow::{allocation, lane_patterns};
use crate::model::ir::{Program, Reg};
use crate::verification::{
    block_verify::region::{
        self,
        registers::{self, Compact, Expanded},
    },
    verify::{Solver, UnknownReason},
};
use std::collections::BTreeSet;
use std::time::{Duration, Instant};

mod improvement;
pub use improvement::{EntryAttempt, EntryStatus};

pub const MODEL_ID: &str = "checked-loop-recovery-chain-v1";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Input,
    AllocationUnavailable,
    Storage(allocated_storage::Error),
    Projection(region::Error),
    Context(rolled_loop::ContextError),
    Correspondence,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "loop recovery: {self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Debug)]
pub enum Reason {
    Preparation(Error),
    Discovery(lane_patterns::Error),
    NoGroups,
    Proposal(rolled_loop::Error),
    Counterexample(Box<rolled_loop::Counterexample>),
    Incomplete(Box<region::extraction::repeat::Exhaustion>),
    Unknown(UnknownReason),
    Context(rolled_loop::ContextError),
    Projection(region::Error),
    Correspondence,
}
#[derive(Clone, Debug)]
pub enum Outcome {
    Recovered(Box<Recovered>),
    Retained {
        group: Option<usize>,
        reason: Reason,
    },
}

/// Checked allocation followed by an exact compact projection. Parameters keep
/// their input IDs in the original namespace; local bank slots start afterward.
#[derive(Clone, Debug)]
pub struct PreparedStorage {
    storage: allocated_storage::Lowering,
    compact: Compact,
    parameters: Vec<Reg>,
}
fn same(a: &Program, b: &Program) -> bool {
    a.register_count() == b.register_count()
        && a.cfg().block(a.cfg().entry()).start == b.cfg().block(b.cfg().entry()).start
        && a.instructions() == b.instructions()
}
impl PreparedStorage {
    pub fn new(source: &Program, parameters: &[Reg]) -> Result<Self, Error> {
        let dense = registers::compact(source).map_err(Error::Projection)?;
        let mut unique = BTreeSet::new();
        if parameters
            .iter()
            .any(|reg| reg.0 >= source.register_count() || !unique.insert(reg.0))
        {
            return Err(Error::Input);
        }
        let eligible: Vec<_> = dense
            .registers()
            .iter()
            .filter(|r| !parameters.contains(r))
            .copied()
            .collect();
        let allocated =
            allocation::allocate_locals(source, &eligible).ok_or(Error::AllocationUnavailable)?;
        let colors: Vec<_> = eligible
            .iter()
            .map(|&r| allocated.color(r).map(|color| (r, color)))
            .collect::<Option<_>>()
            .ok_or(Error::AllocationUnavailable)?;
        let storage = allocated_storage::lower(source, &colors).map_err(Error::Storage)?;
        let compact = registers::compact(storage.program()).map_err(Error::Projection)?;
        let result = Self {
            storage,
            compact,
            parameters: parameters.to_vec(),
        };
        result.validate()?;
        Ok(result)
    }
    pub fn source(&self) -> &Program {
        self.storage.source()
    }
    pub fn storage(&self) -> &allocated_storage::Lowering {
        &self.storage
    }
    pub fn compact(&self) -> &Compact {
        &self.compact
    }
    pub fn parameters(&self) -> &[Reg] {
        &self.parameters
    }
    pub fn validate(&self) -> Result<(), Error> {
        self.storage.validate().map_err(Error::Storage)?;
        self.compact.validate().map_err(Error::Projection)?;
        if !same(self.storage.program(), self.compact.source()) {
            return Err(Error::Correspondence);
        }
        let mut unique = BTreeSet::new();
        for &parameter in &self.parameters {
            if !unique.insert(parameter.0)
                || self.storage.renamed_register(parameter) != Some(parameter)
            {
                return Err(Error::Input);
            }
        }
        Ok(())
    }
    /// Try one largest lane group. Completion and comparison keep their bounded
    /// proof budgets, and an unsuccessful attempt retains the source function.
    pub fn recover(self, solver: &Solver) -> Outcome {
        self.recover_before(solver, Instant::now() + Duration::from_secs(10))
    }
    pub(crate) fn recover_before(self, solver: &Solver, improvement_deadline: Instant) -> Outcome {
        let discovery = match lane_patterns::discover(self.compact.program()) {
            Ok(found) => found,
            Err(reason) => {
                return Outcome::Retained {
                    group: None,
                    reason: Reason::Discovery(reason),
                };
            }
        };
        let mut selected = None;
        for (index, group) in discovery.groups().iter().enumerate() {
            if selected.is_none_or(|old: usize| {
                group.kernels.len() > discovery.groups()[old].kernels.len()
            }) {
                selected = Some(index);
            }
        }
        let Some(index) = selected else {
            return Outcome::Retained {
                group: None,
                reason: Reason::NoGroups,
            };
        };
        let retained = |reason| Outcome::Retained {
            group: Some(index),
            reason,
        };
        let proposal = match rolled_loop::propose(self.compact.program(), &discovery, index) {
            Ok(value) => value,
            Err(error) => return retained(Reason::Proposal(error)),
        };
        let verified = match proposal.verify(solver) {
            rolled_loop::Outcome::Verified(value) => value,
            rolled_loop::Outcome::Counterexample(w) => return retained(Reason::Counterexample(w)),
            rolled_loop::Outcome::Incomplete(w) => return retained(Reason::Incomplete(w)),
            rolled_loop::Outcome::Unknown(r) => return retained(Reason::Unknown(r)),
        };
        let contextual = match verified.in_context() {
            Ok(value) => value,
            Err(error) => return retained(Reason::Context(error)),
        };
        let expanded = match self.compact.expand_candidate(contextual.program()) {
            Ok(value) => value,
            Err(error) => return retained(Reason::Projection(error)),
        };
        let recovered = Recovered {
            prepared: self,
            contextual,
            expanded,
            group: index,
            entry_attempt: EntryAttempt::new(proposal.lane_group().kernels.len()),
        };
        if recovered.validate().is_err() {
            return retained(Reason::Correspondence);
        }
        Outcome::Recovered(Box::new(recovered.improve(solver, improvement_deadline)))
    }
}

/// The entire checked chain, from the supplied display IR to a whole-function
/// candidate in its original parameter namespace. The execution contract is
/// return, full RAM and first fault; original machine snapshots stay separate.
#[derive(Clone, Debug)]
pub struct Recovered {
    prepared: PreparedStorage,
    contextual: rolled_loop::ContextualRoll,
    expanded: Expanded,
    group: usize,
    entry_attempt: EntryAttempt,
}
impl Recovered {
    pub fn source(&self) -> &Program {
        self.prepared.source()
    }
    pub fn program(&self) -> &Program {
        self.expanded.program()
    }
    pub fn parameters(&self) -> &[Reg] {
        self.prepared.parameters()
    }
    pub fn prepared(&self) -> &PreparedStorage {
        &self.prepared
    }
    pub fn contextual(&self) -> &rolled_loop::ContextualRoll {
        &self.contextual
    }
    pub fn expansion(&self) -> &Expanded {
        &self.expanded
    }
    pub fn group(&self) -> usize {
        self.group
    }
    pub fn entry_attempt(&self) -> &EntryAttempt {
        &self.entry_attempt
    }
    pub fn extend_input(&self, input: &[u64], fresh: u64) -> Result<Vec<u64>, Error> {
        let input = self
            .prepared
            .storage
            .extend_input(input, fresh)
            .map_err(Error::Storage)?;
        self.expanded
            .extend_input(&input, fresh)
            .map_err(Error::Projection)
    }
    pub fn validate(&self) -> Result<(), Error> {
        self.prepared.validate()?;
        self.contextual.validate().map_err(Error::Context)?;
        self.expanded.validate().map_err(Error::Projection)?;
        let compact = &self.prepared.compact;
        let base = compact.registers().len();
        if self.group != self.contextual.verified_region().proposal().group_index()
            || !same(self.contextual.source(), compact.program())
            || !same(self.contextual.program(), self.expanded.source())
            || self.expanded.registers().get(..base) != Some(compact.registers())
            || self.expanded.registers()[base..]
                .iter()
                .enumerate()
                .any(|(n, r)| r.0 != self.prepared.storage.program().register_count() + n)
        {
            return Err(Error::Correspondence);
        }
        Ok(())
    }
}

pub fn recover(source: &Program, parameters: &[Reg], solver: &Solver) -> Outcome {
    recover_before(
        source,
        parameters,
        solver,
        Instant::now() + Duration::from_secs(10),
    )
}
pub(crate) fn recover_before(
    source: &Program,
    parameters: &[Reg],
    solver: &Solver,
    improvement_deadline: Instant,
) -> Outcome {
    match PreparedStorage::new(source, parameters) {
        Ok(prepared) => prepared.recover_before(solver, improvement_deadline),
        Err(error) => Outcome::Retained {
            group: None,
            reason: Reason::Preparation(error),
        },
    }
}
