//! Conservative unsigned storage widths for registers, without rewriting IR.
//!
//! The entry register file is unknown u64, including fresh registers. A smaller
//! width is possible only when every reachable read and write fits it. These
//! are storage bounds, not signedness, source types, or bounds on intermediate
//! C arithmetic; a consumer must still preserve the IR's u64 arithmetic rules.

use std::collections::VecDeque;

use crate::control_flow::cfg::Target;
use crate::model::ir::{BinaryOp, Control, Expr, Place, Program, Reg, Width};

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
#[derive(Clone, Debug, Default)]
pub struct ValueWidths {
    widths: Vec<Width>,
}

impl ValueWidths {
    pub fn analyze(program: &Program) -> Self {
        Self::analyze_bounded(program).unwrap_or_default()
    }

    pub fn width(&self, reg: Reg) -> Width {
        self.widths.get(reg.0).copied().unwrap_or(Width::U64)
    }

    fn analyze_bounded(program: &Program) -> Option<Self> {
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
                budget.spend(count)?;
                let changed = match &mut incoming[target.index()] {
                    None => {
                        incoming[target.index()] = Some(state.clone());
                        true
                    }
                    Some(previous) => {
                        let mut changed = false;
                        for (old, &new) in previous.iter_mut().zip(&state) {
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
        Some(Self {
            widths: observed
                .into_iter()
                .map(|value| match value {
                    Some(0..=8) => Width::U8,
                    Some(9..=16) => Width::U16,
                    Some(17..=32) => Width::U32,
                    _ => Width::U64,
                })
                .collect(),
        })
    }
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
                BinaryOp::Shl | BinaryOp::Shr if left_bits == 0 => 0,
                BinaryOp::Shl | BinaryOp::Shr if right_bits == 0 => left_bits,
                BinaryOp::Shl => match right.as_ref() {
                    Expr::Const(shift) => (left_bits + (shift & 63) as u8).min(64),
                    _ => 64,
                },
                BinaryOp::Shr => match right.as_ref() {
                    Expr::Const(shift) => left_bits.saturating_sub((shift & 63) as u8),
                    _ => left_bits,
                },
            }
        }
    })
}
