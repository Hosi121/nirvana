//! Recover values saved to memory without removing their checked reloads.
//!
//! Exact reaching writers identify the stored word. A value captured once in
//! the acyclic entry prefix can replace uses of its successful reload. Original
//! registers, memory effects, source PCs and instruction budgets are retained;
//! equivalence projects away the additional internal capture registers.
use crate::dataflow::ssa::{
    self, Budget, Definition, PointValues, Site, SsaError, SsaEvidence, SsaFunction, ValueId,
};
use crate::dataflow::ssa_facts::LoadInputs;
use crate::model::ir::{Assignment, Expr, Program, Reg, UnaryOp, Width};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
mod analyze;
mod rewrite;
mod verify;
const MAX_CAPTURES: usize = 256;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Key {
    value: ValueId,
    width: Width,
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CapturePoint {
    instruction: u64,
    /// None is before the instruction's first assignment.
    after: Option<usize>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Capture {
    key: Key,
    point: CapturePoint,
    source: Reg,
}
impl Capture {
    fn expression(self) -> Expr {
        // Preserve the full value so its capture can share storage with the
        // source. A narrow memory word is projected at each replaced read.
        Expr::Register(self.source)
    }
}
fn word(width: Width, value: Expr) -> Expr {
    if width == Width::U64 {
        value
    } else {
        Expr::unary(UnaryOp::Extract { start: 0, width }, value)
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
    evidence: MemoryValueEvidence,
}
impl MemoryValuePlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        let context = analyze::Context::new(source)?;
        let (proofs, captures) = analyze::collect(&context)?;
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
        };
        let (candidate, count) = rewrite::construct(source, &plan, &context)?;
        if count == 0 {
            return None;
        }
        plan.evidence.replaced_reads = count;
        verify::check(source, &plan, &candidate, &context).ok()?;
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
