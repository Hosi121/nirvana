//! Conservative unsigned storage widths for registers, without rewriting IR.
//!
//! The entry register file is unknown u64, including fresh registers. A smaller
//! width is possible only when every reachable read and write fits it. These
//! are storage bounds, not signedness, source types, or bounds on intermediate
//! C arithmetic; a consumer must still preserve the IR's u64 arithmetic rules.

use std::collections::VecDeque;
use std::sync::Arc;

use crate::control_flow::cfg::Target;
use crate::model::ir::{BinaryOp, Control, Expr, Place, Program, Reg, Width};

mod edge_bounds;
mod report;
mod verify;
pub use verify::{ValidationError, ValidationEvidence};

const MAX_STATE_CELLS: usize = 1_000_000;
const MAX_POINTS: usize = 100_000;
const MAX_STEPS: usize = 100_000;
const MAX_WORK: usize = 10_000_000;
const MAX_DEPTH: usize = 256;

struct Budget(usize);

impl Budget {
    fn spend(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}

/// Widths which fit every reachable value read from or written to a register.
/// Unused registers, invalid queries, and bounded-analysis failure return U64.
/// Initial values count only if read before being overwritten on some path.
#[derive(Clone, Debug)]
pub struct ValueWidths {
    widths: Vec<Width>,
    incoming: Option<Arc<Incoming>>,
    entry_block: Option<usize>,
    block_starts: Option<Arc<Vec<u64>>>,
    verification: Result<ValidationEvidence, ValidationError>,
}

impl Default for ValueWidths {
    fn default() -> Self {
        Self {
            widths: Vec::new(),
            incoming: None,
            entry_block: None,
            block_starts: None,
            verification: Err(ValidationError::Unavailable("not analyzed")),
        }
    }
}

type Incoming = Vec<Option<Vec<u8>>>;
type Proposal = (Vec<Width>, Incoming);

impl ValueWidths {
    pub fn analyze(program: &Program) -> Self {
        match Self::analyze_bounded(program) {
            Some((widths, incoming)) => Self::checked(program, widths, incoming),
            None => Self {
                widths: Vec::new(),
                incoming: None,
                entry_block: None,
                block_starts: None,
                verification: Err(ValidationError::Unavailable(
                    "inference resource/control limit",
                )),
            },
        }
    }

    pub fn width(&self, reg: Reg) -> Width {
        self.widths.get(reg.0).copied().unwrap_or(Width::U64)
    }

    /// Evidence covers the particular program passed to analyze, before any
    /// width-dependent presentation. An error always accompanies all-U64
    /// fallback storage; failed candidates never escape through width().
    pub fn verification(&self) -> Result<&ValidationEvidence, &ValidationError> {
        self.verification.as_ref()
    }

    /// The complete register storage proposal, available only after checking.
    pub fn widths(&self) -> Option<&[Width]> {
        self.verification.is_ok().then_some(self.widths.as_slice())
    }

    /// Dense source-CFG entry rows; None marks an unreachable block. Successful
    /// clones share the retained certificate without copying its state cells.
    pub fn incoming(&self) -> Option<&[Option<Vec<u8>>]> {
        self.verification.as_ref().ok()?;
        self.incoming.as_deref().map(Vec::as_slice)
    }

    /// Retain the source-entry storage certificate, not source-language types
    /// or a proof of the entire emitted C. Failures expose no partial facts.
    pub fn to_json(&self) -> Result<String, String> {
        report::render(self)
    }

    fn checked(program: &Program, widths: Vec<Width>, incoming: Incoming) -> Self {
        match validate(program, &widths, &incoming) {
            Ok(evidence) => Self {
                widths,
                incoming: Some(Arc::new(incoming)),
                entry_block: Some(program.cfg().entry().index()),
                block_starts: Some(Arc::new(
                    program.cfg().blocks().iter().map(|b| b.start).collect(),
                )),
                verification: Ok(evidence),
            },
            Err(error) => Self {
                widths: Vec::new(),
                incoming: None,
                entry_block: None,
                block_starts: None,
                verification: Err(error),
            },
        }
    }

    fn analyze_bounded(program: &Program) -> Option<Proposal> {
        let cfg = program.cfg();
        let count = program.register_count();
        let points = program.instructions().iter().try_fold(0usize, |n, i| {
            n.checked_add(i.assignments.len())?.checked_add(1)
        })?;
        if points > MAX_POINTS
            || cfg.blocks().len().checked_add(4)?.checked_mul(count)? > MAX_STATE_CELLS
        {
            return None;
        }
        // Guard planning is optional. Unsupported shapes and its separate
        // structural limit preserve the unconditional transfer below.
        let guards = edge_bounds::Plans::build(program, points);

        let mut incoming: Vec<Option<Vec<u8>>> = vec![None; cfg.blocks().len()];
        // Keep the original boundary as an incoming path to entry backedges.
        incoming[cfg.entry().index()] = Some(vec![64; count]);
        let mut pending = VecDeque::from([cfg.entry()]);
        let mut queued = vec![false; cfg.blocks().len()];
        queued[cfg.entry().index()] = true;
        let mut budget = Budget(MAX_WORK);
        let mut steps = MAX_STEPS;
        while let Some(id) = pending.pop_front() {
            steps = steps.checked_sub(1)?;
            queued[id.index()] = false;
            budget.spend(count)?;
            let mut state = incoming[id.index()].as_ref()?.clone();
            for instruction in &program.instructions()[cfg.block(id).instructions.clone()] {
                for assignment in &instruction.assignments {
                    if let Place::Register(reg) = assignment.destination {
                        state[reg.0] = bits(&assignment.value, &state, None, &mut budget, 0)?;
                    }
                }
            }
            for edge in &cfg.block(id).successors {
                let Target::Block(target) = edge.target else {
                    return None;
                };
                let refined = match &guards {
                    Some(guards) => guards.refine(id.index(), edge.kind, &state, &mut budget)?,
                    None => None,
                };
                let outgoing = refined.as_deref().unwrap_or(&state);
                budget.spend(count)?;
                let changed = match &mut incoming[target.index()] {
                    None => {
                        incoming[target.index()] = Some(outgoing.to_vec());
                        true
                    }
                    Some(previous) => {
                        let mut changed = false;
                        for (old, &new) in previous.iter_mut().zip(outgoing) {
                            if new > *old {
                                *old = new;
                                changed = true;
                            }
                        }
                        changed
                    }
                };
                if changed && !queued[target.index()] {
                    queued[target.index()] = true;
                    pending.push_back(target);
                }
            }
        }

        // Do not aggregate transient fixed-point states. In particular the
        // unobserved initial u64 value must not force a narrow local to U64.
        let mut observed = vec![None; count];
        for block in cfg.blocks() {
            let Some(before) = incoming[block.id.index()].as_ref() else {
                continue;
            };
            budget.spend(count)?;
            let mut state = before.clone();
            for instruction in &program.instructions()[block.instructions.clone()] {
                for assignment in &instruction.assignments {
                    if let Place::Memory { address, .. } = &assignment.destination {
                        bits(address, &state, Some(&mut observed), &mut budget, 0)?;
                    }
                    let value = bits(
                        &assignment.value,
                        &state,
                        Some(&mut observed),
                        &mut budget,
                        0,
                    )?;
                    if let Place::Register(reg) = assignment.destination {
                        observe(&mut observed, reg.0, value);
                        state[reg.0] = value;
                    }
                }
                match &instruction.control {
                    Control::Branch { condition, .. } => {
                        bits(condition, &state, Some(&mut observed), &mut budget, 0)?;
                    }
                    Control::Return(value) => {
                        bits(value, &state, Some(&mut observed), &mut budget, 0)?;
                    }
                    _ => {}
                }
            }
        }
        Some((
            observed
                .into_iter()
                .map(|value| match value {
                    Some(0..=8) => Width::U8,
                    Some(9..=16) => Width::U16,
                    Some(17..=32) => Width::U32,
                    _ => Width::U64,
                })
                .collect(),
            incoming,
        ))
    }
}

/// Check a retained storage proposal and its complete source-CFG entry rows.
/// This is independent of inference; no partial evidence is returned on error.
pub fn validate(
    source: &Program,
    widths: &[Width],
    incoming: &[Option<Vec<u8>>],
) -> Result<ValidationEvidence, ValidationError> {
    verify::validate(source, widths, incoming)
}

fn observe(observed: &mut [Option<u8>], register: usize, value: u8) {
    if let Some(previous) = observed.get_mut(register) {
        *previous = Some(previous.unwrap_or(0).max(value));
    }
}

fn bits(
    expression: &Expr,
    state: &[u8],
    mut observed: Option<&mut [Option<u8>]>,
    budget: &mut Budget,
    depth: usize,
) -> Option<u8> {
    if depth > MAX_DEPTH {
        return None;
    }
    budget.spend(1)?;
    Some(match expression {
        Expr::Unary(op, value) => {
            let bits = bits(value, state, observed, budget, depth + 1)?;
            op.result_bits(bits)
        }
        Expr::Const(value) => (64 - value.leading_zeros()) as u8,
        Expr::Register(reg) => {
            let value = state.get(reg.0).copied().unwrap_or(64);
            if let Some(observed) = observed {
                observe(observed, reg.0, value);
            }
            value
        }
        Expr::Load { address, width } => {
            bits(address, state, observed, budget, depth + 1)?;
            width.bits() as u8
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            bits(condition, state, observed.as_deref_mut(), budget, depth + 1)?;
            let taken = bits(taken, state, observed.as_deref_mut(), budget, depth + 1)?;
            let not_taken = bits(not_taken, state, observed, budget, depth + 1)?;
            taken.max(not_taken)
        }
        Expr::Binary(op, left, right) => {
            let left_bits = bits(left, state, observed.as_deref_mut(), budget, depth + 1)?;
            let right_bits = bits(right, state, observed, budget, depth + 1)?;
            match op {
                BinaryOp::Insert { .. } => {
                    let maximum = |bits: u8| {
                        u64::MAX
                            .checked_shr(64 - u32::from(bits.min(64)))
                            .unwrap_or(0)
                    };
                    (64 - op
                        .evaluate(maximum(left_bits), maximum(right_bits))
                        .leading_zeros()) as u8
                }
                BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule => 1,
                BinaryOp::And => left_bits.min(right_bits),
                BinaryOp::Or | BinaryOp::Xor => left_bits.max(right_bits),
                BinaryOp::Add if left_bits == 0 => right_bits,
                BinaryOp::Add if right_bits == 0 => left_bits,
                BinaryOp::Add => (left_bits.max(right_bits) + 1).min(64),
                BinaryOp::Sub if right_bits == 0 => left_bits,
                BinaryOp::Sub => 64,
                BinaryOp::Mul if left_bits == 0 || right_bits == 0 => 0,
                BinaryOp::Mul => (left_bits + right_bits).min(64),
                BinaryOp::UMulHigh => (left_bits + right_bits).saturating_sub(64),
                BinaryOp::SMulHigh => 64,
                BinaryOp::UDiv => quotient_bits(left_bits, constant_divisor(right)),
                BinaryOp::URem | BinaryOp::SRem => left_bits,
                BinaryOp::SDiv => 64,
                BinaryOp::AShr if left_bits == 64 => 64,
                BinaryOp::Shl | BinaryOp::Shr if left_bits == 0 => 0,
                BinaryOp::Shl | BinaryOp::Shr if right_bits == 0 => left_bits,
                BinaryOp::Shl => match right.as_ref() {
                    Expr::Const(shift) => (left_bits + (shift & 63) as u8).min(64),
                    _ => 64,
                },
                BinaryOp::Shr | BinaryOp::AShr => match right.as_ref() {
                    Expr::Const(shift) => left_bits.saturating_sub((shift & 63) as u8),
                    _ => left_bits,
                },
            }
        }
    })
}

pub(crate) fn constant_divisor(e: &Expr) -> Option<u64> {
    if let Expr::Const(n) = e {
        Some(*n)
    } else {
        None
    }
}
/// Monotonic unsigned quotient upper bound. A zero divisor
/// follows the total bit-vector contract; dynamic divisors may also be zero.
pub(crate) fn quotient_bits(input: u8, divisor: Option<u64>) -> u8 {
    let Some(d) = divisor.filter(|n| *n != 0) else {
        return 64;
    };
    let maximum = if input == 0 {
        0
    } else {
        u64::MAX >> (64 - input)
    };
    (64 - (maximum / d).leading_zeros()) as u8
}
