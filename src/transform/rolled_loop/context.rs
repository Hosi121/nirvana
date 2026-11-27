//! Apply a sealed region rewrite inside an unchanged function context.
use super::*;

pub const CONTEXT_MODEL_ID: &str = "checked-rolled-function-context-v1";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContextError {
    Source,
    Boundary,
    Frame,
    Entry,
    Continuation,
}
impl std::fmt::Display for ContextError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "rolled-loop function context: {self:?}")
    }
}
impl std::error::Error for ContextError {}

#[derive(Clone, Debug)]
pub struct ContextEvidence {
    pub original_region_instructions: usize,
    pub candidate_region_instructions: usize,
    pub outside_instructions: usize,
    pub excluded_continuation_reads_checked: usize,
}

/// Whole-function return/RAM/first-fault correspondence. Original machine-step
/// snapshots and instruction budgets keep their separate executable contracts.
#[derive(Clone, Debug)]
pub struct ContextualRoll {
    verified: Box<VerifiedRoll>,
    evidence: ContextEvidence,
}
impl ContextualRoll {
    pub fn program(&self) -> &Program {
        self.verified.program()
    }
    pub fn source(&self) -> &Program {
        self.verified.proposal().source()
    }
    pub fn verified_region(&self) -> &VerifiedRoll {
        &self.verified
    }
    pub fn evidence(&self) -> &ContextEvidence {
        &self.evidence
    }
    pub fn validate(&self) -> Result<(), ContextError> {
        check(&self.verified).map(|_| ())
    }
}
impl VerifiedRoll {
    /// Frame and entry checks connect the sealed region to its original whole
    /// function. The continuation interface covers both programs' future reads.
    pub fn in_context(&self) -> Result<ContextualRoll, ContextError> {
        let evidence = check(self)?;
        Ok(ContextualRoll {
            verified: Box::new(self.clone()),
            evidence,
        })
    }
}

fn successors(source: &Program) -> Result<BTreeMap<u64, Vec<u64>>, ContextError> {
    let known: BTreeSet<_> = source.instructions().iter().map(|i| i.address).collect();
    let mut result = BTreeMap::new();
    for i in source.instructions() {
        let fall = i
            .address
            .checked_add(u64::from(i.size))
            .ok_or(ContextError::Boundary)?;
        let next = match i.control {
            Control::Next => vec![fall],
            Control::Jump(pc) => vec![pc],
            Control::Branch { target, .. } => vec![target, fall],
            Control::Return(_) => vec![],
        };
        if next.iter().any(|pc| !known.contains(pc)) {
            return Err(ContextError::Boundary);
        }
        result.insert(i.address, next);
    }
    Ok(result)
}
fn reachable(edges: &BTreeMap<u64, Vec<u64>>, entry: u64, stops: &BTreeSet<u64>) -> BTreeSet<u64> {
    let mut seen = BTreeSet::new();
    let mut todo = vec![entry];
    while let Some(pc) = todo.pop() {
        if seen.insert(pc) {
            todo.extend(edges[&pc].iter().filter(|pc| !stops.contains(pc)).copied());
        }
    }
    seen
}
fn check(verified: &VerifiedRoll) -> Result<ContextEvidence, ContextError> {
    let proposal = verified.proposal();
    if !verified.outputs().matches(proposal.source_region())
        || !verified
            .complete()
            .source_region()
            .belongs_to(proposal.program())
    {
        return Err(ContextError::Source);
    }
    verified
        .outputs()
        .validate()
        .map_err(|_| ContextError::Continuation)?;
    frame_with_outputs(proposal, verified.outputs())
}

#[cfg(test)]
pub(super) fn frame(proposal: &Proposal) -> Result<ContextEvidence, ContextError> {
    let outputs = extraction::live_out::derive(proposal.source_region())
        .map_err(|_| ContextError::Continuation)?;
    frame_with_outputs(proposal, &outputs)
}

fn frame_with_outputs(
    proposal: &Proposal,
    outputs: &extraction::live_out::ContinuationOutputs,
) -> Result<ContextEvidence, ContextError> {
    let before = proposal.source_region();
    let source = &proposal.padded;
    let candidate = proposal.program();
    if !before.belongs_to(source) || source.register_count() != candidate.register_count() {
        return Err(ContextError::Source);
    }
    before.validate().map_err(|_| ContextError::Source)?;
    let entry = source.cfg().block(source.cfg().entry()).start;
    if entry != candidate.cfg().block(candidate.cfg().entry()).start {
        return Err(ContextError::Boundary);
    }
    let header = before.source_entry();
    let stops: BTreeSet<_> = before.continuations().iter().copied().collect();
    let a = successors(source)?;
    let b = successors(candidate)?;
    let original: BTreeSet<_> = before.source_to_region().keys().copied().collect();
    let replacement = reachable(&b, header, &stops);
    let ra = reachable(&a, entry, &BTreeSet::new());
    let rb = reachable(&b, entry, &BTreeSet::new());
    for (edges, body, all) in [(&a, &original, &ra), (&b, &replacement, &rb)] {
        if body.contains(&entry) && entry != header {
            return Err(ContextError::Entry);
        }
        for pc in all.difference(body) {
            if edges[pc]
                .iter()
                .any(|next| body.contains(next) && *next != header)
            {
                return Err(ContextError::Entry);
            }
        }
    }
    let oa: BTreeSet<_> = ra.difference(&original).copied().collect();
    let ob: BTreeSet<_> = rb.difference(&replacement).copied().collect();
    if oa != ob {
        return Err(ContextError::Frame);
    }
    let source_rows: BTreeMap<_, _> = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let candidate_rows: BTreeMap<_, _> = candidate
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    for pc in &oa {
        if source_rows.get(pc) != candidate_rows.get(pc) {
            return Err(ContextError::Frame);
        }
    }
    if replacement
        .iter()
        .any(|pc| matches!(candidate_rows[pc].control, Control::Return(_)))
    {
        return Err(ContextError::Boundary);
    }
    let excluded = outputs
        .check_candidate_continuations(before, candidate)
        .map_err(|_| ContextError::Continuation)?;
    Ok(ContextEvidence {
        original_region_instructions: original.len(),
        candidate_region_instructions: replacement.len(),
        outside_instructions: oa.len(),
        excluded_continuation_reads_checked: excluded,
    })
}
