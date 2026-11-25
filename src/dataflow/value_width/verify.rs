//! Check storage observations and inductive block bounds independently of the
//! producer's transfer, worklist, joins, and observed-width aggregation.
//! Unread initial values remain arbitrary u64; only actual syntactic reads and
//! writes must fit storage. CFG layout is immutable Program infrastructure.

use super::{MAX_DEPTH, MAX_POINTS, MAX_STATE_CELLS, MAX_WORK};
use crate::control_flow::cfg::Target;
use crate::dataflow::unsigned_caps;
use crate::model::ir::{Control, Expr, Place, Program, Width};
use std::fmt;

mod edge_bounds;

// One preflight and one interpretation visit each reachable expression node
// (at most the producer's 10m observation budget). Row checks, working states,
// and <=2 successor comparisons per block add <=4m state cells. Source point,
// edge and coverage overhead is bounded by 100k points. 32m therefore retains
// the producer's domain without importing the stricter SSA size/depth limits.
const MAX_VALIDATION_WORK: usize = 32_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationError {
    Invalid(&'static str),
    Unavailable(&'static str),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(reason) => write!(f, "unsigned storage check invalid: {reason}"),
            Self::Unavailable(reason) => write!(f, "unsigned storage check unavailable: {reason}"),
        }
    }
}
impl std::error::Error for ValidationError {}
use ValidationError::{Invalid, Unavailable};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ValidationEvidence {
    pub registers: usize,
    pub narrow_registers: usize,
    pub blocks: usize,
    /// Source CFG successor occurrences, excluding the virtual initial edge.
    pub edges: usize,
    pub assignments: usize,
    pub reads: usize,
    pub expressions: usize,
}

struct Work {
    remaining: usize,
    evidence: ValidationEvidence,
}
impl Work {
    fn take(&mut self, amount: usize) -> Result<(), ValidationError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(Unavailable("work limit"))?;
        Ok(())
    }
}

pub(super) fn validate(
    source: &Program,
    widths: &[Width],
    incoming: &[Option<Vec<u8>>],
) -> Result<ValidationEvidence, ValidationError> {
    validate_bounded(source, widths, incoming, MAX_VALIDATION_WORK)
}

fn validate_bounded(
    source: &Program,
    widths: &[Width],
    incoming: &[Option<Vec<u8>>],
    limit: usize,
) -> Result<ValidationEvidence, ValidationError> {
    let registers = source.register_count();
    let cfg = source.cfg();
    let points = source
        .instructions()
        .iter()
        .try_fold(0usize, |n, instruction| {
            n.checked_add(instruction.assignments.len())?.checked_add(1)
        })
        .ok_or(Unavailable("source points overflow"))?;
    let cells = cfg
        .blocks()
        .len()
        .checked_add(4)
        .and_then(|n| n.checked_mul(registers));
    if points > MAX_POINTS || cells.is_none_or(|n| n > MAX_STATE_CELLS) {
        return Err(Unavailable("source dimensions"));
    }
    if widths.len() != registers || incoming.len() != cfg.blocks().len() {
        return Err(Invalid("candidate dimensions"));
    }
    let mut work = Work {
        remaining: limit,
        evidence: ValidationEvidence::default(),
    };
    work.take(cfg.blocks().len() + registers)?;
    // Source CFG coverage is established independently of candidate presence.
    let mut reachable = vec![false; cfg.blocks().len()];
    for id in cfg.reachable_blocks() {
        work.take(1)?;
        reachable[id.index()] = true;
    }
    for (index, row) in incoming.iter().enumerate() {
        work.take(1)?;
        if row.is_some() != reachable[index] {
            return Err(Invalid("reachable block coverage"));
        }
        if let Some(row) = row {
            if row.len() != registers {
                return Err(Invalid("entry row width"));
            }
            work.take(row.len())?;
            if row.iter().any(|&n| n > 64) {
                return Err(Invalid("entry bit count"));
            }
        }
    }
    work.take(registers)?;
    if incoming[cfg.entry().index()]
        .as_ref()
        .ok_or(Invalid("missing initial edge"))?
        .iter()
        .any(|&n| n != 64)
    {
        return Err(Invalid("arbitrary initial boundary"));
    }

    // Bound only reachable syntax: the original analysis deliberately ignores
    // unreachable writes and expressions. Preflight precedes recursion and
    // u128 state allocation, and preserves its root-depth-zero convention.
    let mut nodes = 0usize;
    for block in cfg.blocks() {
        if !reachable[block.id.index()] {
            continue;
        }
        for instruction in &source.instructions()[block.instructions.clone()] {
            work.take(1)?;
            for assignment in &instruction.assignments {
                work.take(1)?;
                match &assignment.destination {
                    Place::Register(reg) if reg.0 >= registers => {
                        return Err(Invalid("source destination"));
                    }
                    Place::Memory { address, .. } => {
                        scan(address, registers, &mut nodes, &mut work)?
                    }
                    _ => {}
                }
                scan(&assignment.value, registers, &mut nodes, &mut work)?;
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                scan(condition, registers, &mut nodes, &mut work)?;
            }
        }
        for edge in &block.successors {
            work.take(1)?;
            if !matches!(edge.target, Target::Block(_)) {
                return Err(Unavailable("unresolved source edge"));
            }
        }
    }
    work.take(registers)?;
    let storage: Vec<_> = widths.iter().map(|&w| unsigned_caps::load(w)).collect();
    work.evidence.registers = registers;
    work.evidence.narrow_registers = widths.iter().filter(|&&w| w != Width::U64).count();
    let mut guard_budget = edge_bounds::Budget::new(registers);
    for block in cfg.blocks() {
        if !reachable[block.id.index()] {
            continue;
        }
        work.take(registers + 1)?;
        // Optional guards are reconstructed only after all reachable source
        // syntax was checked. Unsupported grammar or structural budget limits
        // preserve unconditional bounds; they cannot hide invalid source.
        let guard = edge_bounds::derive(
            &source.instructions()[block.instructions.clone()],
            registers,
            &mut guard_budget,
        );
        let mut state: Vec<_> = incoming[block.id.index()]
            .as_ref()
            .unwrap()
            .iter()
            .map(|&n| unsigned_caps::from_bits(n).unwrap())
            .collect();
        work.evidence.blocks += 1;
        for instruction in &source.instructions()[block.instructions.clone()] {
            work.take(1)?;
            for assignment in &instruction.assignments {
                work.take(1)?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    upper(address, &state, &storage, &mut work)?;
                }
                let value = upper(&assignment.value, &state, &storage, &mut work)?;
                if let Place::Register(reg) = assignment.destination {
                    if value > storage[reg.0] {
                        return Err(Invalid("storage write bound"));
                    }
                    state[reg.0] = value;
                    work.evidence.assignments += 1;
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                upper(condition, &state, &storage, &mut work)?;
            }
        }
        for edge in &block.successors {
            let Target::Block(target) = edge.target else {
                return Err(Unavailable("unresolved source edge"));
            };
            work.take(registers + 1)?;
            let next = incoming[target.index()]
                .as_ref()
                .ok_or(Invalid("missing successor row"))?;
            if !edge_bounds::covers(guard.as_ref(), edge.kind, &state, next, &mut work)? {
                return Err(Invalid("successor entry bound"));
            }
            work.evidence.edges += 1;
        }
    }
    Ok(work.evidence)
}

fn scan(
    expression: &Expr,
    registers: usize,
    nodes: &mut usize,
    work: &mut Work,
) -> Result<(), ValidationError> {
    let mut pending = vec![(expression, 0usize)];
    while let Some((expression, depth)) = pending.pop() {
        work.take(1)?;
        *nodes += 1;
        if *nodes > MAX_WORK || depth > MAX_DEPTH {
            return Err(Unavailable("source expression limit"));
        }
        match expression {
            Expr::Register(reg) if reg.0 >= registers => {
                return Err(Invalid("source read register"));
            }
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, left, right) => {
                pending.extend([(&**right, depth + 1), (&**left, depth + 1)])
            }
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

fn upper(
    expression: &Expr,
    state: &[u128],
    storage: &[u128],
    work: &mut Work,
) -> Result<u128, ValidationError> {
    work.take(1)?;
    work.evidence.expressions += 1;
    Ok(match expression {
        Expr::Const(value) => u128::from(*value),
        Expr::Register(reg) => {
            work.evidence.reads += 1;
            let value = state[reg.0];
            if value > storage[reg.0] {
                return Err(Invalid("storage read bound"));
            }
            value
        }
        Expr::Load { address, width } => {
            upper(address, state, storage, work)?;
            unsigned_caps::load(*width)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            upper(condition, state, storage, work)?;
            let taken = upper(taken, state, storage, work)?;
            taken.max(upper(not_taken, state, storage, work)?)
        }
        Expr::Unary(op, value) => unsigned_caps::unary(*op, upper(value, state, storage, work)?),
        Expr::Binary(op, left, right) => {
            let a = upper(left, state, storage, work)?;
            let b = upper(right, state, storage, work)?;
            let literal = match right.as_ref() {
                Expr::Const(value) => Some(*value),
                _ => None,
            };
            unsigned_caps::binary(*op, a, b, literal)
        }
    })
}

#[cfg(test)]
mod tests;
