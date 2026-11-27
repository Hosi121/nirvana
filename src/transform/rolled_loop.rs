//! Propose a rolled control region from source-bound lane expressions.
//!
//! Proposal construction is deliberately separate from semantic acceptance.
//! Acceptance requires completed feedback unfolding and the original source's
//! continuation observations, including all RAM and the first fault.
use crate::control_flow::{
    analysis::ControlFlowAnalysis,
    cfg::{BlockId, Target},
};
use crate::dataflow::{
    lane_patterns::{self, Discovery, LaneGroup, PatternExpr},
    ssa::Site,
    value_width::ValueWidths,
};
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg};
use crate::verification::{
    block_verify::region::{
        self,
        extraction::{self, Region},
    },
    verify::{Solver, UnknownReason},
};
use std::collections::{BTreeMap, BTreeSet};

mod composition;
mod context;
mod controls;
mod emit;
mod envelope;
mod expressions;
mod linear;
mod replay;
mod storage;
mod verify;

pub use context::{CONTEXT_MODEL_ID, ContextError, ContextEvidence, ContextualRoll};
pub use envelope::Envelope;
pub use replay::{Counterexample, Replay, ReplayExit};
pub use verify::{EquivalenceProof, Outcome, VerificationProblem, VerifiedRoll};
pub const MODEL_ID: &str = "source-bound-rolled-loop-proposal-v1";
pub const MAX_LANES: usize = 8;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Limit,
    Source,
    Boundary,
    Pattern,
    Controls,
    Projection,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "rolled loop: {self:?}")
    }
}
impl std::error::Error for Error {}
impl From<extraction::ExtractionError> for Error {
    fn from(error: extraction::ExtractionError) -> Self {
        match error {
            extraction::ExtractionError::Region(region::Error::Limit) => Self::Limit,
            extraction::ExtractionError::Boundary => Self::Boundary,
            extraction::ExtractionError::EntryFacts => Self::Source,
            _ => Self::Projection,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Proposal {
    source: Program,
    discovery: Discovery,
    group: usize,
    padded: Program,
    before: Region,
    program: Program,
    envelope: Envelope,
    counter: Reg,
    feedback: u64,
    rounds: usize,
    selectors: Vec<(Reg, u8)>,
}
impl Proposal {
    pub fn source(&self) -> &Program {
        &self.source
    }
    /// Exact source SSA and lane selection used to build this proposal.
    pub fn discovery(&self) -> &Discovery {
        &self.discovery
    }
    pub fn lane_group(&self) -> &LaneGroup {
        &self.discovery.groups()[self.group]
    }
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn source_region(&self) -> &Region {
        &self.before
    }
    pub fn envelope(&self) -> &Envelope {
        &self.envelope
    }
    pub fn counter(&self) -> Reg {
        self.counter
    }
    pub fn feedback(&self) -> u64 {
        self.feedback
    }
    pub fn rounds(&self) -> usize {
        self.rounds
    }
    pub fn selector(&self) -> Option<(Reg, u8)> {
        self.selectors.first().copied()
    }
    pub fn selectors(&self) -> &[(Reg, u8)] {
        &self.selectors
    }
    pub fn belongs_to(&self, source: &Program) -> bool {
        self.source.register_count() == source.register_count()
            && self.source.cfg().block(self.source.cfg().entry()).start
                == source.cfg().block(source.cfg().entry()).start
            && self.source.instructions() == source.instructions()
    }
}

pub fn propose(
    source: &Program,
    discovery: &Discovery,
    group_index: usize,
) -> Result<Proposal, Error> {
    if source.instructions().len() > region::MAX_INSTRUCTIONS
        || source.register_count() > region::MAX_REGISTERS - 3
    {
        return Err(Error::Limit);
    }
    if !discovery.belongs_to(source) {
        return Err(Error::Source);
    }
    let group = discovery.groups().get(group_index).ok_or(Error::Pattern)?;
    if group.kernels.len() < lane_patterns::MIN_LANES || group.kernels.len() > MAX_LANES {
        return Err(Error::Limit);
    }
    if expressions::has_lane(&group.update_expression)
        || expressions::has_lane(&group.store_address)
    {
        return Err(Error::Pattern);
    }
    let envelope = envelope::locate(source, group)?;
    let counter = Reg(source.register_count());
    let padded = Program::new(
        source.cfg().block(source.cfg().entry()).start,
        source.register_count() + 1,
        source.instructions().to_vec(),
    )
    .map_err(|_| Error::Source)?;
    let widths = ValueWidths::analyze(&padded);
    let stops = envelope.stops();
    let before = extraction::extract(&padded, envelope.header, &stops, Some(&widths))?;
    // The feedback stop adds one candidate tag. Keep actual function Returns
    // outside this cut until their explicit tag correspondence is supported.
    if padded.instructions().iter().any(|i| {
        before.source_to_region().contains_key(&i.address)
            && matches!(i.control, Control::Return(_))
    }) {
        return Err(Error::Boundary);
    }
    let control = controls::analyze(&padded, discovery, group, &envelope, counter)?;
    let mut selectors: Vec<_> = controls::single_register(&control.limit.lhs)
        .map(|reg| (reg, before.input_bit_caps()[reg.0].clamp(1, 4)))
        .into_iter()
        .collect();
    if let Some((reg, bits)) = expressions::address_selector(
        &group.load_address,
        discovery,
        &group
            .kernels
            .iter()
            .map(|kernel| kernel.load)
            .collect::<Vec<_>>(),
    ) {
        if let Some((_, current)) = selectors.iter_mut().find(|(current, _)| *current == reg) {
            *current = (*current).max(bits);
        } else {
            selectors.push((reg, bits));
        }
    }
    let (program, feedback) =
        emit::candidate(&padded, group, &envelope, &before, &control, counter)?;
    Ok(Proposal {
        source: source.clone(),
        discovery: discovery.clone(),
        group: group_index,
        padded,
        before,
        program,
        envelope,
        counter,
        feedback,
        rounds: group.kernels.len(),
        selectors,
    })
}

#[cfg(test)]
mod tests;
