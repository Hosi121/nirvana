//! Source-bound SSA value identities for the reachable register CFG.
//!
//! Phi inputs name predecessor exits; None is the virtual function-entry edge.
//! Stores, loads and expression order remain at their original source sites.
//! This is register SSA: memory remains an ordered, checked byte store.
use crate::cfg::Target;
use crate::ir::{Control, Expr, Program, Reg};
use std::fmt;
mod build;
mod verify;

pub const MAX_REGISTERS: usize = 4096;
pub const MAX_BLOCKS: usize = 2048;
pub const MAX_INSTRUCTIONS: usize = 16384;
pub const MAX_ASSIGNMENTS: usize = 16384;
pub const MAX_NODES: usize = 65536;
pub const MAX_DEPTH: usize = 128;
pub const MAX_VALUES: usize = 65536;
pub const MAX_PHI_INPUTS: usize = 262144;
pub const MAX_STATE_CELLS: usize = 1_000_000;
pub const MAX_WORK: usize = 8_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct ValueId(pub usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Site {
    pub instruction: u64,
    /// None names the control expression after all sequential assignments.
    pub assignment: Option<usize>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RegisterValue {
    pub register: Reg,
    pub value: ValueId,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PhiInput {
    pub predecessor: Option<u64>,
    pub value: ValueId,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Definition {
    Initial {
        register: Reg,
    },
    Assignment {
        site: Site,
        register: Reg,
    },
    Phi {
        block: u64,
        register: Reg,
        inputs: Vec<PhiInput>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointValues {
    pub site: Site,
    pub definition: Option<ValueId>,
    /// Register-leaf traversal: Store address then RHS; Select condition and
    /// both syntactic arms. Duplicate reads are retained in source order.
    pub reads: Vec<RegisterValue>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SsaBlock {
    pub start: u64,
    pub phis: Vec<ValueId>,
    pub points: Vec<PointValues>,
    /// Values forwarded to successor phi inputs, sorted by raw register.
    pub exit_values: Vec<RegisterValue>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SsaFunction {
    pub entry: u64,
    pub register_count: usize,
    pub values: Vec<Definition>,
    pub blocks: Vec<SsaBlock>,
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SsaEvidence {
    pub blocks: usize,
    pub definitions: usize,
    pub phis: usize,
    pub register_reads: usize,
    pub phi_inputs: usize,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SsaError {
    Unavailable(&'static str),
    Malformed(&'static str),
}
impl fmt::Display for SsaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unavailable(s) => write!(f, "SSA resource/control limit: {s}"),
            Self::Malformed(s) => write!(f, "invalid SSA: {s}"),
        }
    }
}
impl std::error::Error for SsaError {}
impl SsaFunction {
    pub fn build(source: &Program) -> Option<Self> {
        let candidate = build::build(source)?;
        validate(source, &candidate).ok()?;
        Some(candidate)
    }
    pub fn point(&self, site: Site) -> Option<&PointValues> {
        self.blocks
            .iter()
            .flat_map(|b| &b.points)
            .find(|p| p.site == site)
    }
}
pub fn validate(source: &Program, candidate: &SsaFunction) -> Result<SsaEvidence, SsaError> {
    verify::validate(source, candidate)
}

pub(crate) struct Budget(usize);
impl Budget {
    pub(crate) fn new() -> Self {
        Self(MAX_WORK)
    }
    pub(crate) fn spend(&mut self, n: usize) -> Result<(), SsaError> {
        self.0 = self.0.checked_sub(n).ok_or(SsaError::Unavailable("work"))?;
        Ok(())
    }
}
/// Bound the original syntax before cloning or recursive walkers are allowed.
pub(crate) fn preflight(source: &Program, budget: &mut Budget) -> Result<(), SsaError> {
    if source.register_count() > MAX_REGISTERS
        || source.instructions().len() > MAX_INSTRUCTIONS
        || source.cfg().blocks().len() > MAX_BLOCKS
    {
        return Err(SsaError::Unavailable("source size"));
    }
    let mut assignments = 0usize;
    let mut nodes = 0usize;
    for ins in source.instructions() {
        budget.spend(1)?;
        assignments = assignments
            .checked_add(ins.assignments.len())
            .ok_or(SsaError::Unavailable("assignments"))?;
        if assignments > MAX_ASSIGNMENTS {
            return Err(SsaError::Unavailable("assignments"));
        }
        for a in &ins.assignments {
            match &a.destination {
                crate::ir::Place::Register(r) if r.0 >= source.register_count() => {
                    return Err(SsaError::Malformed("destination register"));
                }
                crate::ir::Place::Memory { address, .. } => {
                    scan(address, source.register_count(), &mut nodes, budget)?
                }
                _ => {}
            }
            scan(&a.value, source.register_count(), &mut nodes, budget)?;
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &ins.control {
            scan(condition, source.register_count(), &mut nodes, budget)?;
        }
    }
    for id in source.cfg().reachable_blocks() {
        for edge in &source.cfg().block(id).successors {
            budget.spend(1)?;
            if !matches!(edge.target, Target::Block(_)) {
                return Err(SsaError::Unavailable("unresolved edge"));
            }
        }
    }
    Ok(())
}
fn scan(expr: &Expr, regs: usize, nodes: &mut usize, budget: &mut Budget) -> Result<(), SsaError> {
    let mut pending = vec![(expr, 1usize)];
    while let Some((e, depth)) = pending.pop() {
        budget.spend(1)?;
        *nodes += 1;
        if *nodes > MAX_NODES || depth > MAX_DEPTH {
            return Err(SsaError::Unavailable("expression size"));
        }
        match e {
            Expr::Register(r) if r.0 >= regs => return Err(SsaError::Malformed("read register")),
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, a, b) => pending.extend([(&**b, depth + 1), (&**a, depth + 1)]),
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**not_taken, depth + 1),
                (&**taken, depth + 1),
                (&**condition, depth + 1),
            ]),
        }
    }
    Ok(())
}
