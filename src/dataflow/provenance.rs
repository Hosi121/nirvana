//! Conservative input-register origins, including exact 64-bit spill reloads.
//!
//! Origins describe modular values after successful evaluation. They do not
//! establish allocation, source type, bounds, or separation between inputs.
//! Loads and stores remain real guest-memory operations; address queries reject
//! every expression containing a load so callers cannot erase its effects.

use std::collections::{BTreeMap, VecDeque};

use crate::control_flow::cfg::Target;
use crate::model::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, Place, Program, Reg, Width,
};

const MAX_STATE_CELLS: usize = 1_000_000;
const MAX_POINTS: usize = 100_000;
const MAX_STEPS: usize = 100_000;
const MAX_WORK: usize = 10_000_000;
const MAX_DEPTH: usize = 256;
const MAX_MEMORY_FACTS: usize = 256;
const MAX_RETAINED_FACTS: usize = 100_000;
const MAX_ACCESSES: usize = 100_000;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Value {
    Constant(u64),
    Input { register: usize, offset: u64 },
}

type Fact = Option<Value>;
type Memory = BTreeMap<Value, Value>;

#[derive(Clone, Debug)]
struct State {
    registers: Vec<Fact>,
    memory: Memory,
}

#[derive(Clone, Copy)]
struct Evaluated {
    value: Fact,
    pure: bool,
}

struct Budget(usize);

impl Budget {
    fn spend(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}

/// Entry-register value plus a wrapping offset, represented as signed bits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AddressOrigin {
    pub register: Reg,
    pub offset: i64,
}

/// A potential access, including both arms of lazy select expressions.
/// `assignment == assignments.len()` denotes the control expression. Accesses
/// describe addresses after successful address evaluation, not execution traces.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AddressAccess {
    pub instruction: u64,
    pub assignment: usize,
    pub origin: AddressOrigin,
    pub width: Width,
    pub kind: AccessKind,
}

/// Forward fixed-point facts for reachable instructions and sequential writes.
/// Non-input registers and initial memory are unknown. Invalid inputs or any
/// exhausted bound discard every result, including already collected accesses.
#[derive(Clone, Debug, Default)]
pub struct AddressAnalysis {
    points: BTreeMap<u64, Vec<Vec<Fact>>>,
    accesses: Vec<AddressAccess>,
}

impl AddressAnalysis {
    pub fn analyze(program: &Program, inputs: &[Reg]) -> Self {
        Self::analyze_bounded(program, inputs).unwrap_or_default()
    }

    /// Registers immediately before an assignment; its count denotes control.
    /// Any load anywhere in `address`, including a lazy arm or condition, makes
    /// the query return `None`. No memory operation is replaced by a fact.
    pub fn origin_before(
        &self,
        instruction: u64,
        assignment: usize,
        address: &Expr,
    ) -> Option<AddressOrigin> {
        let registers = self.points.get(&instruction)?.get(assignment)?;
        let evaluated = evaluate(address, registers, &Memory::new(), &mut Budget(MAX_WORK), 0)?;
        evaluated.pure.then_some(())?;
        origin(evaluated.value)
    }

    pub fn accesses(&self) -> &[AddressAccess] {
        &self.accesses
    }

    fn analyze_bounded(program: &Program, inputs: &[Reg]) -> Option<Self> {
        let count = program.register_count();
        if inputs.len() > MAX_POINTS || inputs.iter().any(|reg| reg.0 >= count) {
            return None;
        }
        let cfg = program.cfg();
        let points = program.instructions().iter().try_fold(0usize, |n, i| {
            n.checked_add(i.assignments.len())?.checked_add(1)
        })?;
        if points > MAX_POINTS
            || points
                .checked_add(cfg.blocks().len())?
                .checked_add(2)?
                .checked_mul(count)?
                > MAX_STATE_CELLS
        {
            return None;
        }
        let mut boundary = State {
            registers: vec![None; count],
            memory: Memory::new(),
        };
        for reg in inputs {
            boundary.registers[reg.0] = Some(Value::Input {
                register: reg.0,
                offset: 0,
            });
        }
        let mut incoming: Vec<Option<State>> = vec![None; cfg.blocks().len()];
        incoming[cfg.entry().index()] = Some(boundary);
        // Meeting backedges into this boundary also preserves unknown initial
        // registers and memory when the entry is itself a loop header.
        let mut pending = VecDeque::from([cfg.entry()]);
        let mut queued = vec![false; cfg.blocks().len()];
        queued[cfg.entry().index()] = true;
        let mut budget = Budget(MAX_WORK);
        let mut steps = MAX_STEPS;
        let mut retained_facts = 0usize;
        while let Some(id) = pending.pop_front() {
            steps = steps.checked_sub(1)?;
            queued[id.index()] = false;
            let before = incoming[id.index()].as_ref()?;
            budget.spend(before.registers.len() + before.memory.len())?;
            let mut state = before.clone();
            for i in &program.instructions()[cfg.block(id).instructions.clone()] {
                for assignment in &i.assignments {
                    transfer(assignment, &mut state, &mut budget)?;
                }
            }
            for edge in &cfg.block(id).successors {
                let Target::Block(target) = edge.target else {
                    return None;
                };
                budget.spend(state.registers.len() + state.memory.len())?;
                let changed = match &mut incoming[target.index()] {
                    None => {
                        retained_facts = retained_facts.checked_add(state.memory.len())?;
                        if retained_facts > MAX_RETAINED_FACTS {
                            return None;
                        }
                        incoming[target.index()] = Some(state.clone());
                        true
                    }
                    Some(previous) => {
                        budget.spend(previous.memory.len())?;
                        let old_len = previous.memory.len();
                        let changed = meet(previous, &state);
                        retained_facts -= old_len - previous.memory.len();
                        changed
                    }
                };
                if changed && !queued[target.index()] {
                    queued[target.index()] = true;
                    pending.push_back(target);
                }
            }
        }

        let mut result = Self::default();
        for block in cfg.blocks() {
            let Some(before) = incoming[block.id.index()].as_ref() else {
                continue;
            };
            budget.spend(before.registers.len() + before.memory.len())?;
            let mut state = before.clone();
            for i in &program.instructions()[block.instructions.clone()] {
                let mut points = Vec::with_capacity(i.assignments.len() + 1);
                for (index, assignment) in i.assignments.iter().enumerate() {
                    budget.spend(state.registers.len())?;
                    points.push(state.registers.clone());
                    let mut collector = Collector {
                        instruction: i.address,
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
                    transfer(assignment, &mut state, &mut budget)?;
                }
                budget.spend(state.registers.len())?;
                points.push(state.registers.clone());
                let mut collector = Collector {
                    instruction: i.address,
                    assignment: i.assignments.len(),
                    state: &state,
                    budget: &mut budget,
                    accesses: &mut result.accesses,
                };
                match &i.control {
                    Control::Branch { condition, .. } => collector.expression(condition, 0)?,
                    Control::Return(value) => collector.expression(value, 0)?,
                    _ => {}
                }
                result.points.insert(i.address, points);
            }
        }
        Some(result)
    }
}

fn origin(value: Fact) -> Option<AddressOrigin> {
    match value? {
        Value::Input { register, offset } => Some(AddressOrigin {
            register: Reg(register),
            offset: offset as i64,
        }),
        Value::Constant(_) => None,
    }
}

fn meet(previous: &mut State, incoming: &State) -> bool {
    let mut changed = false;
    for (old, &new) in previous.registers.iter_mut().zip(&incoming.registers) {
        if old.is_some() && *old != new {
            *old = None;
            changed = true;
        }
    }
    let old_len = previous.memory.len();
    previous
        .memory
        .retain(|address, value| incoming.memory.get(address) == Some(value));
    changed || old_len != previous.memory.len()
}

fn transfer(assignment: &Assignment, state: &mut State, budget: &mut Budget) -> Option<()> {
    // Both expressions use the state before this assignment. In particular a
    // store's RHS may reload a slot which this same store will overwrite.
    let address = match &assignment.destination {
        Place::Register(_) => None,
        Place::Memory { address, .. } => {
            evaluate(address, &state.registers, &state.memory, budget, 0)?.value
        }
    };
    let value = evaluate(
        &assignment.value,
        &state.registers,
        &state.memory,
        budget,
        0,
    )?
    .value;
    match &assignment.destination {
        Place::Register(reg) => state.registers[reg.0] = value,
        Place::Memory { width, .. } => {
            budget.spend(state.memory.len())?;
            let Some(address) = address else {
                state.memory.clear();
                return Some(());
            };
            state
                .memory
                .retain(|&old, _| disjoint(old, 8, address, width.bytes() as u64));
            if *width == Width::U64
                && let Some(value) = value
            {
                state.memory.insert(address, value);
                if state.memory.len() > MAX_MEMORY_FACTS {
                    return None;
                }
            }
        }
    }
    Some(())
}

fn disjoint(left: Value, left_width: u64, right: Value, right_width: u64) -> bool {
    let offsets = match (left, right) {
        (Value::Constant(a), Value::Constant(b)) => Some((a, b)),
        (
            Value::Input {
                register: a,
                offset: left,
            },
            Value::Input {
                register: b,
                offset: right,
            },
        ) if a == b => Some((left, right)),
        // Different input bases, and symbolic vs absolute addresses, may alias.
        _ => None,
    };
    offsets
        .is_some_and(|(a, b)| a.wrapping_sub(b) >= right_width && b.wrapping_sub(a) >= left_width)
}

fn evaluate(
    expression: &Expr,
    registers: &[Fact],
    memory: &Memory,
    budget: &mut Budget,
    depth: usize,
) -> Option<Evaluated> {
    if depth > MAX_DEPTH {
        return None;
    }
    budget.spend(1)?;
    let evaluated = match expression {
        Expr::Const(value) => Evaluated {
            value: Some(Value::Constant(*value)),
            pure: true,
        },
        Expr::Register(reg) => Evaluated {
            value: registers.get(reg.0).copied().flatten(),
            pure: true,
        },
        Expr::Load { address, width } => {
            let address = evaluate(address, registers, memory, budget, depth + 1)?;
            Evaluated {
                value: if *width == Width::U64 {
                    address
                        .value
                        .and_then(|address| memory.get(&address).copied())
                } else {
                    None
                },
                pure: false,
            }
        }
        Expr::Binary(op, left, right) => {
            let left = evaluate(left, registers, memory, budget, depth + 1)?;
            let right = evaluate(right, registers, memory, budget, depth + 1)?;
            use Value::{Constant, Input};
            let value = match (op, left.value, right.value) {
                (BinaryOp::Add, Some(Constant(a)), Some(Constant(b))) => {
                    Some(Constant(a.wrapping_add(b)))
                }
                (BinaryOp::Sub, Some(Constant(a)), Some(Constant(b))) => {
                    Some(Constant(a.wrapping_sub(b)))
                }
                (BinaryOp::Add, Some(Input { register, offset }), Some(Constant(c)))
                | (BinaryOp::Add, Some(Constant(c)), Some(Input { register, offset })) => {
                    Some(Input {
                        register,
                        offset: offset.wrapping_add(c),
                    })
                }
                (BinaryOp::Sub, Some(Input { register, offset }), Some(Constant(c))) => {
                    Some(Input {
                        register,
                        offset: offset.wrapping_sub(c),
                    })
                }
                _ => None,
            };
            Evaluated {
                value,
                pure: left.pure && right.pure,
            }
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let condition = evaluate(condition, registers, memory, budget, depth + 1)?;
            let taken = evaluate(taken, registers, memory, budget, depth + 1)?;
            let not_taken = evaluate(not_taken, registers, memory, budget, depth + 1)?;
            Evaluated {
                value: if taken.value == not_taken.value {
                    taken.value
                } else {
                    None
                },
                pure: condition.pure && taken.pure && not_taken.pure,
            }
        }
    };
    Some(evaluated)
}

struct Collector<'a> {
    instruction: u64,
    assignment: usize,
    state: &'a State,
    budget: &'a mut Budget,
    accesses: &'a mut Vec<AddressAccess>,
}

impl Collector<'_> {
    fn access(&mut self, address: &Expr, width: Width, kind: AccessKind) -> Option<()> {
        let evaluated = evaluate(
            address,
            &self.state.registers,
            &self.state.memory,
            self.budget,
            0,
        )?;
        if let Some(origin) = origin(evaluated.value) {
            if self.accesses.len() >= MAX_ACCESSES {
                return None;
            }
            self.accesses.push(AddressAccess {
                instruction: self.instruction,
                assignment: self.assignment,
                origin,
                width,
                kind,
            });
        }
        Some(())
    }

    fn expression(&mut self, expression: &Expr, depth: usize) -> Option<()> {
        if depth > MAX_DEPTH {
            return None;
        }
        self.budget.spend(1)?;
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
