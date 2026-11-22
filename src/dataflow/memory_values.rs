//! Recover values saved to memory without removing their checked reloads.
//!
//! Reaching bytes agree on a slice of an SSA value or one pure Store RHS.
//! Captures in single-visit blocks, or checked invariant definitions in loops,
//! replace uses of successful reloads through copies and equal phi inputs. Original
//! registers, memory effects, source PCs and instruction budgets are retained;
//! equivalence projects away the additional internal capture registers.
use crate::dataflow::ssa::{
    self, Budget, Definition, PointValues, Site, SsaError, SsaEvidence, SsaFunction, ValueId,
};
use crate::dataflow::ssa_facts::{LoadInputs, ReachingWriter};
use crate::model::ir::{Assignment, Expr, Program, Reg, UnaryOp, Width};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
mod analyze;
mod projection;
mod rewrite;
mod single_visit;
mod stability;
mod value_facts;
mod verify;
mod view;
pub use view::{SavedLoad, SavedSlice, SavedValueView, Snapshot, SnapshotId};
const MAX_CAPTURES: usize = 256;

#[derive(Clone, Copy)]
enum RecoveryPolicy {
    Source,
    Stored,
    Local,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
/// Source identity of a captured word, scoped to one checked plan.
pub enum SavedValue {
    Register(ValueId),
    Stored(Site),
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Key {
    value: SavedValue,
    start: u8,
    width: Width,
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
/// Source position after a successful assignment, or before a guest step.
pub struct CapturePoint {
    pub instruction: u64,
    /// None is before the instruction's first assignment.
    pub after: Option<usize>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Capture {
    value: SavedValue,
    point: CapturePoint,
    source: Option<Reg>,
}
impl Capture {
    fn expression(self, context: &analyze::Context<'_>) -> Option<Expr> {
        match self.value {
            SavedValue::Register(_) => Some(Expr::Register(self.source?)),
            SavedValue::Stored(site) => {
                let value = &context.assignment(site)?.value;
                (!value.uses_memory()).then(|| value.clone())
            }
        }
    }
}
fn word(key: Key, value: Expr) -> Expr {
    if key.start == 0 && key.width == Width::U64 {
        value
    } else {
        Expr::unary(
            UnaryOp::Extract {
                start: key.start,
                width: key.width,
            },
            value,
        )
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LoadProof {
    site: Site,
    key: Key,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MemoryValueEvidence {
    pub ssa: SsaEvidence,
    pub proved_loads: usize,
    pub snapshot_values: usize,
    pub replaced_reads: usize,
}
#[derive(Clone, Debug)]
pub struct MemoryValuePlan {
    source_registers: usize,
    proofs: Vec<LoadProof>,
    captures: Vec<Capture>,
    /// Equal saved-word slices at each actual SSA definition, including phis.
    facts: Vec<Option<Key>>,
    evidence: MemoryValueEvidence,
}
impl MemoryValuePlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        Self::analyze_mode(source, true)
    }
    pub(crate) fn analyze_once(source: &Program) -> Option<Self> {
        Self::analyze_mode(source, false)
    }
    fn analyze_mode(source: &Program, allow_repeated: bool) -> Option<Self> {
        let mut context = analyze::Context::new(source)?;
        context.allow_repeated = allow_repeated;
        // Keep coverage first, then share a saved word across the most views.
        // Each complete candidate is checked; equal costs retain source words.
        let mut best: Option<Self> = None;
        for policy in [
            RecoveryPolicy::Source,
            RecoveryPolicy::Stored,
            RecoveryPolicy::Local,
        ] {
            let Some(plan) = Self::analyze_context(source, &context, policy, true) else {
                continue;
            };
            let cost = |p: &Self| (usize::MAX - p.evidence.proved_loads, p.captures.len());
            if best.as_ref().is_none_or(|old| cost(&plan) < cost(old)) {
                best = Some(plan);
            }
        }
        best
    }
    /// Retain the register-only alternative for final C cost comparison.
    pub(crate) fn analyze_registers(source: &Program) -> Option<Self> {
        let mut context = analyze::Context::new(source)?;
        context.allow_repeated = false;
        [RecoveryPolicy::Source, RecoveryPolicy::Local]
            .into_iter()
            .find_map(|policy| Self::analyze_context(source, &context, policy, false))
    }
    fn analyze_context(
        source: &Program,
        context: &analyze::Context<'_>,
        policy: RecoveryPolicy,
        allow_stored: bool,
    ) -> Option<Self> {
        let (proofs, captures) = analyze::collect(context, policy, allow_stored)?;
        let facts = value_facts::solve(context, &proofs).ok()?;
        let mut plan = Self {
            source_registers: source.register_count(),
            evidence: MemoryValueEvidence {
                ssa: context.evidence,
                proved_loads: proofs.len(),
                snapshot_values: captures.len(),
                replaced_reads: 0,
            },
            proofs,
            captures,
            facts,
        };
        let (candidate, count) = rewrite::construct(source, &plan, context)?;
        if count == 0 {
            return None;
        }
        plan.evidence.replaced_reads = count;
        verify::check(source, &plan, &candidate, context).ok()?;
        Some(plan)
    }
    pub fn evidence(&self) -> MemoryValueEvidence {
        self.evidence
    }
    /// Entry executions compare by projecting the register file onto the
    /// original prefix. Internal captures remain in the lowered state.
    pub fn lower(&self, source: &Program) -> Option<Program> {
        let context = analyze::Context::new(source)?;
        verify::plan(source, self, &context).ok()?;
        let (candidate, count) = rewrite::construct(source, self, &context)?;
        if count != self.evidence.replaced_reads {
            return None;
        }
        verify::check(source, self, &candidate, &context).ok()?;
        Some(candidate)
    }
}
pub fn validate(
    source: &Program,
    plan: &MemoryValuePlan,
    candidate: &Program,
) -> Result<MemoryValueEvidence, SsaError> {
    let context =
        analyze::Context::new(source).ok_or(SsaError::Unavailable("memory value source"))?;
    verify::check(source, plan, candidate, &context)
}
