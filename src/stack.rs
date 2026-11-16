//! Conservative addresses relative to the stack register at function entry.
//!
//! Facts describe values, not stack allocations, bounds, types, or ownership.
//! Offsets wrap modulo 2^64, with the public `i64` using the same bit pattern.
//! Only pure moves, addition/subtraction of constants, and agreeing select arms
//! produce affine facts. Memory is never used as a source of pointer facts.

use std::collections::{BTreeMap, VecDeque};

use crate::cfg::Target;
use crate::ir::{AccessKind, BinaryOp, Control, Expr, Place, Program, Reg, Width};

// Dense point states make ordered assignments explicit. Limit both retained
// state and total work; an exhausted analysis discards all accumulated facts.
const MAX_STATE_CELLS: usize = 1_000_000;
const MAX_POINTS: usize = 100_000;
const MAX_BLOCK_STEPS: usize = 100_000;
const MAX_EXPRESSION_WORK: usize = 2_000_000;
const MAX_EXPRESSION_DEPTH: usize = 256;
const MAX_ACCESSES: usize = 100_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Value {
    Unknown,
    Constant(u64),
    Stack(u64),
}

type State = Vec<Value>;

#[derive(Clone, Copy)]
struct Evaluated {
    value: Value,
    pure: bool,
}

impl Evaluated {
    fn new(value: Value, pure: bool) -> Self {
        Self {
            value: if pure { value } else { Value::Unknown },
            pure,
        }
    }
}

struct Budget(usize);

impl Budget {
    fn spend(&mut self, depth: usize) -> Option<()> {
        if depth > MAX_EXPRESSION_DEPTH {
            return None;
        }
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
}

/// A potential memory access with a proven entry-stack-relative address.
///
/// `assignment` is zero-based; the assignment count denotes the control
/// expression. Lazy select arms are both included, so this is not an execution
/// trace. Widths and overlapping accesses are retained individually.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StackAccess {
    pub instruction: u64,
    pub assignment: usize,
    pub offset: i64,
    pub width: Width,
    pub kind: AccessKind,
}

/// Fixed-point facts for entry-reachable instructions only.
///
/// If the stack register is invalid or a resource bound is exhausted, every
/// query returns `None` and the access list is empty. Partial fixed-point facts
/// are never exposed. All other input registers start unknown, including any
/// fresh registers in a reduced program.
#[derive(Clone, Debug, Default)]
pub struct StackAnalysis {
    points: BTreeMap<u64, Vec<State>>,
    accesses: Vec<StackAccess>,
}

impl StackAnalysis {
    pub fn analyze(program: &Program, stack_register: Reg) -> Self {
        Self::analyze_bounded(program, stack_register).unwrap_or_default()
    }

    /// Query registers immediately before one ordered assignment, or before
    /// control when `assignment == assignments.len()`. Expressions containing
    /// any load return `None`, even if their select arms have equal values: a
    /// caller may replace a proven address without removing memory effects.
    pub fn offset_before(
        &self,
        instruction: u64,
        assignment: usize,
        address: &Expr,
    ) -> Option<i64> {
        let state = self.points.get(&instruction)?.get(assignment)?;
        let value = evaluate(address, state, &mut Budget(MAX_EXPRESSION_WORK), 0)?.value;
        match value {
            Value::Stack(offset) => Some(offset as i64),
            _ => None,
        }
    }

    pub fn accesses(&self) -> &[StackAccess] {
        &self.accesses
    }

    fn analyze_bounded(program: &Program, stack_register: Reg) -> Option<Self> {
        let registers = program.register_count();
        if stack_register.0 >= registers {
            return None;
        }
        let cfg = program.cfg();
        let point_count = program.instructions().iter().try_fold(0usize, |n, i| {
            n.checked_add(i.assignments.len())?.checked_add(1)
        })?;
        if point_count > MAX_POINTS
            || point_count
                .checked_add(cfg.blocks().len())?
                .checked_add(2)?
                .checked_mul(registers)?
                > MAX_STATE_CELLS
        {
            return None;
        }

        let mut boundary = vec![Value::Unknown; registers];
        boundary[stack_register.0] = Value::Stack(0);
        let mut incoming: Vec<Option<State>> = vec![None; cfg.blocks().len()];
        let entry = cfg.entry().index();
        // The initial boundary remains an incoming path even when a backedge
        // targets the entry block. Meeting into this state preserves it.
        incoming[entry] = Some(boundary);
        let mut pending = VecDeque::from([cfg.entry()]);
        let mut queued = vec![false; cfg.blocks().len()];
        queued[entry] = true;
        let mut steps = MAX_BLOCK_STEPS;
        let mut budget = Budget(MAX_EXPRESSION_WORK);

        while let Some(id) = pending.pop_front() {
            steps = steps.checked_sub(1)?;
            queued[id.index()] = false;
            let mut state = incoming[id.index()].as_ref()?.clone();
            for instruction in &program.instructions()[cfg.block(id).instructions.clone()] {
                for assignment in &instruction.assignments {
                    if let Place::Register(reg) = assignment.destination {
                        state[reg.0] = evaluate(&assignment.value, &state, &mut budget, 0)?.value;
                    }
                }
            }
            for edge in &cfg.block(id).successors {
                let Target::Block(target) = edge.target else {
                    // Program validates complete reachable control flow.
                    return None;
                };
                let changed = match &mut incoming[target.index()] {
                    None => {
                        incoming[target.index()] = Some(state.clone());
                        true
                    }
                    Some(previous) => meet(previous, &state),
                };
                if changed && !queued[target.index()] {
                    queued[target.index()] = true;
                    pending.push_back(target);
                }
            }
        }

        // Materialize points and accesses only after every input has converged.
        let mut result = Self::default();
        for block in cfg.blocks() {
            let Some(mut state) = incoming[block.id.index()].clone() else {
                continue;
            };
            for instruction in &program.instructions()[block.instructions.clone()] {
                let mut points = Vec::with_capacity(instruction.assignments.len() + 1);
                for (index, assignment) in instruction.assignments.iter().enumerate() {
                    points.push(state.clone());
                    let mut collector = Collector {
                        instruction: instruction.address,
                        assignment: index,
                        state: &state,
                        budget: &mut budget,
                        accesses: &mut result.accesses,
                    };
                    if let Place::Memory { address, width } = &assignment.destination {
                        collector.expression(address, 0)?;
                        collector.access(address, *width, AccessKind::Write)?;
                    }
                    collector.expression(&assignment.value, 0)?;
                    if let Place::Register(reg) = assignment.destination {
                        state[reg.0] = evaluate(&assignment.value, &state, &mut budget, 0)?.value;
                    }
                }
                points.push(state.clone());
                let mut collector = Collector {
                    instruction: instruction.address,
                    assignment: instruction.assignments.len(),
                    state: &state,
                    budget: &mut budget,
                    accesses: &mut result.accesses,
                };
                match &instruction.control {
                    Control::Branch { condition, .. } => collector.expression(condition, 0)?,
                    Control::Return(value) => collector.expression(value, 0)?,
                    _ => {}
                }
                result.points.insert(instruction.address, points);
            }
        }
        Some(result)
    }
}

fn meet(previous: &mut State, incoming: &[Value]) -> bool {
    let mut changed = false;
    for (old, &new) in previous.iter_mut().zip(incoming) {
        if *old != new && *old != Value::Unknown {
            *old = Value::Unknown;
            changed = true;
        }
    }
    changed
}

fn evaluate(
    expression: &Expr,
    state: &[Value],
    budget: &mut Budget,
    depth: usize,
) -> Option<Evaluated> {
    budget.spend(depth)?;
    let evaluated = match expression {
        Expr::Const(value) => Evaluated::new(Value::Constant(*value), true),
        Expr::Register(reg) => {
            Evaluated::new(state.get(reg.0).copied().unwrap_or(Value::Unknown), true)
        }
        Expr::Load { .. } => Evaluated::new(Value::Unknown, false),
        Expr::Binary(op, left, right) => {
            let left = evaluate(left, state, budget, depth + 1)?;
            let right = evaluate(right, state, budget, depth + 1)?;
            use Value::{Constant, Stack, Unknown};
            let value = match (op, left.value, right.value) {
                (BinaryOp::Add, Constant(a), Constant(b)) => Constant(a.wrapping_add(b)),
                (BinaryOp::Sub, Constant(a), Constant(b)) => Constant(a.wrapping_sub(b)),
                (BinaryOp::Add, Stack(a), Constant(b)) | (BinaryOp::Add, Constant(b), Stack(a)) => {
                    Stack(a.wrapping_add(b))
                }
                (BinaryOp::Sub, Stack(a), Constant(b)) => Stack(a.wrapping_sub(b)),
                _ => Unknown,
            };
            Evaluated::new(value, left.pure && right.pure)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let condition = evaluate(condition, state, budget, depth + 1)?;
            let taken = evaluate(taken, state, budget, depth + 1)?;
            let not_taken = evaluate(not_taken, state, budget, depth + 1)?;
            let value = if taken.value == not_taken.value {
                taken.value
            } else {
                Value::Unknown
            };
            Evaluated::new(value, condition.pure && taken.pure && not_taken.pure)
        }
    };
    Some(evaluated)
}

struct Collector<'a> {
    instruction: u64,
    assignment: usize,
    state: &'a [Value],
    budget: &'a mut Budget,
    accesses: &'a mut Vec<StackAccess>,
}

impl Collector<'_> {
    fn access(&mut self, address: &Expr, width: Width, kind: AccessKind) -> Option<()> {
        if let Value::Stack(offset) = evaluate(address, self.state, self.budget, 0)?.value {
            if self.accesses.len() >= MAX_ACCESSES {
                return None;
            }
            self.accesses.push(StackAccess {
                instruction: self.instruction,
                assignment: self.assignment,
                offset: offset as i64,
                width,
                kind,
            });
        }
        Some(())
    }

    fn expression(&mut self, expression: &Expr, depth: usize) -> Option<()> {
        self.budget.spend(depth)?;
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, left, right) => {
                self.expression(left, depth + 1)?;
                self.expression(right, depth + 1)?;
            }
            Expr::Load { address, width } => {
                self.expression(address, depth + 1)?;
                self.access(address, *width, AccessKind::Read)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.expression(condition, depth + 1)?;
                self.expression(taken, depth + 1)?;
                self.expression(not_taken, depth + 1)?;
            }
        }
        Some(())
    }
}
