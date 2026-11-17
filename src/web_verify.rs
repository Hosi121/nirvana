//! Independent finite validation of register-only IR renaming.
//!
//! Paired expressions keep exact syntax apart from register leaves. A MUST
//! relation proves each paired register read equal before its assignment, with
//! arbitrary values in fresh initial registers. This certifies return, memory,
//! first fault, and instruction trace, not the final original register file.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use crate::cfg::Target;
use crate::ir::{Control, Expr, Place, Program, Reg};

pub const MAX_ACTIVE_REGISTERS: usize = 4_096;
pub const MAX_BLOCKS: usize = 4_096;
pub const MAX_POINTS: usize = 100_000;
pub const MAX_ITEMS: usize = 200_000;
pub const MAX_DEPTH: usize = 128;
pub const MAX_PAIRS: usize = 8_192;
pub const MAX_STATE_CELLS: usize = 1_000_000;
pub const MAX_WORK: usize = 10_000_000;
pub const MAX_ITERATIONS: usize = 100_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WebEvidence {
    /// All instruction layouts checked, including unreachable instructions.
    pub instructions: usize,
    /// All assignment shapes checked, including unreachable instructions.
    pub assignments: usize,
    /// Reachable syntactic register-read obligations, including lazy arms.
    pub register_reads: usize,
    pub relation_pairs: usize,
    /// Reachable blocks included in the inductive fixed point.
    pub blocks: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WebError {
    Shape {
        instruction: Option<u64>,
        detail: &'static str,
    },
    UnreachableChanged {
        instruction: u64,
    },
    Correspondence {
        instruction: u64,
        assignment: Option<usize>,
        original: Reg,
        renamed: Reg,
    },
    Unavailable {
        resource: &'static str,
    },
}

impl fmt::Display for WebError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Shape {
                instruction: Some(pc),
                detail,
            } => write!(f, "renamed instruction at {pc:#x} changed {detail}"),
            Self::Shape {
                instruction: None,
                detail,
            } => write!(f, "renamed program changed {detail}"),
            Self::UnreachableChanged { instruction } => write!(
                f,
                "unreachable instruction at {instruction:#x} must stay exact"
            ),
            Self::Correspondence {
                instruction,
                assignment,
                original,
                renamed,
            } => write!(
                f,
                "unproved r{} -> r{} read at {instruction:#x}, assignment {assignment:?}",
                original.0, renamed.0
            ),
            Self::Unavailable { resource } => write!(
                f,
                "register-renaming validation unavailable: {resource} limit"
            ),
        }
    }
}
impl std::error::Error for WebError {}
impl WebError {
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, Self::Unavailable { .. })
    }
}

type Pair = (usize, usize);
type Facts = BTreeSet<usize>;
type Result<T> = std::result::Result<T, WebError>;

struct Budget(usize);
impl Budget {
    fn spend(&mut self, amount: usize) -> Result<()> {
        self.0 = self
            .0
            .checked_sub(amount)
            .ok_or_else(|| unavailable("work"))?;
        Ok(())
    }
}
fn unavailable(resource: &'static str) -> WebError {
    WebError::Unavailable { resource }
}
fn shape(instruction: Option<u64>, detail: &'static str) -> WebError {
    WebError::Shape {
        instruction,
        detail,
    }
}

struct Operation {
    instruction: u64,
    assignment: Option<usize>,
    reads: Vec<Pair>,
    write: Option<Pair>,
}

/// Check syntax and inductive read correspondence without depending on any
/// particular renaming builder or on concrete initial/fresh register values.
pub fn validate(original: &Program, renamed: &Program) -> Result<WebEvidence> {
    // Include unreachable expressions before any recursive derived equality.
    let assignments = bounds(original)?;
    bounds(renamed)?;
    if renamed.register_count() < original.register_count() {
        return Err(shape(None, "register count below original"));
    }
    let cfg = original.cfg();
    let other_cfg = renamed.cfg();
    if cfg.block(cfg.entry()).start != other_cfg.block(other_cfg.entry()).start {
        return Err(shape(None, "entry"));
    }
    if original.instructions().len() != renamed.instructions().len() {
        return Err(shape(None, "instruction count"));
    }
    let reachable = cfg.reachable_blocks();
    let mut reachable_instruction = vec![false; original.instructions().len()];
    for &id in &reachable {
        for index in cfg.block(id).instructions.clone() {
            reachable_instruction[index] = true;
        }
    }
    let mut operations = Vec::new();
    let mut offsets = Vec::with_capacity(original.instructions().len() + 1);
    let mut domain = BTreeSet::new();
    let mut reads = 0usize;
    for (index, (old, new)) in original
        .instructions()
        .iter()
        .zip(renamed.instructions())
        .enumerate()
    {
        offsets.push(operations.len());
        if old.address != new.address || old.size != new.size {
            return Err(shape(Some(old.address), "layout"));
        }
        if !reachable_instruction[index] {
            if old != new {
                return Err(WebError::UnreachableChanged {
                    instruction: old.address,
                });
            }
            continue;
        }
        if old.assignments.len() != new.assignments.len() {
            return Err(shape(Some(old.address), "assignment count"));
        }
        for (assignment, (left, right)) in old.assignments.iter().zip(&new.assignments).enumerate()
        {
            let mut operation = Operation {
                instruction: old.address,
                assignment: Some(assignment),
                reads: Vec::new(),
                write: None,
            };
            match (&left.destination, &right.destination) {
                (Place::Register(old), Place::Register(new)) => {
                    operation.write = Some((old.0, new.0));
                }
                (
                    Place::Memory {
                        address: a,
                        width: x,
                    },
                    Place::Memory {
                        address: b,
                        width: y,
                    },
                ) if x == y => paired(a, b, &mut operation.reads, Some(old.address))?,
                _ => return Err(shape(Some(old.address), "assignment destination/width")),
            }
            paired(
                &left.value,
                &right.value,
                &mut operation.reads,
                Some(old.address),
            )?;
            record(&operation, &mut domain, &mut reads)?;
            operations.push(operation);
        }
        let mut operation = Operation {
            instruction: old.address,
            assignment: None,
            reads: Vec::new(),
            write: None,
        };
        match (&old.control, &new.control) {
            (Control::Next, Control::Next) => {}
            (Control::Jump(a), Control::Jump(b)) if a == b => {}
            (
                Control::Branch {
                    condition: a,
                    target: x,
                },
                Control::Branch {
                    condition: b,
                    target: y,
                },
            ) if x == y => paired(a, b, &mut operation.reads, Some(old.address))?,
            (Control::Return(a), Control::Return(b)) => {
                paired(a, b, &mut operation.reads, Some(old.address))?
            }
            _ => return Err(shape(Some(old.address), "control kind/target")),
        }
        record(&operation, &mut domain, &mut reads)?;
        operations.push(operation);
    }
    offsets.push(operations.len());
    // Exact paired control/layout implies identical block boundaries and edges.
    if cfg.blocks() != other_cfg.blocks() {
        return Err(shape(None, "CFG"));
    }
    let pairs: Vec<_> = domain.into_iter().collect();
    let indices: BTreeMap<_, _> = pairs
        .iter()
        .enumerate()
        .map(|(index, &pair)| (pair, index))
        .collect();
    if pairs
        .len()
        .checked_mul(reachable.len())
        .and_then(|n| n.checked_mul(2))
        .is_none_or(|n| n > MAX_STATE_CELLS)
    {
        return Err(unavailable("relation state cells"));
    }
    let top: Facts = (0..pairs.len()).collect();
    let seed: Facts = pairs
        .iter()
        .enumerate()
        .filter_map(|(i, &(a, b))| (a == b).then_some(i))
        .collect();
    let mut incoming = vec![Facts::new(); cfg.blocks().len()];
    let mut outgoing = incoming.clone();
    for &id in &reachable {
        incoming[id.index()] = top.clone();
        outgoing[id.index()] = top.clone();
    }
    let mut pending: VecDeque<_> = reachable.iter().copied().collect();
    let mut queued = vec![false; cfg.blocks().len()];
    for &id in &reachable {
        queued[id.index()] = true;
    }
    let mut work = Budget(MAX_WORK);
    let mut iterations = MAX_ITERATIONS;
    while let Some(id) = pending.pop_front() {
        iterations = iterations
            .checked_sub(1)
            .ok_or_else(|| unavailable("iterations"))?;
        queued[id.index()] = false;
        let block = cfg.block(id);
        let mut before = if id == cfg.entry() {
            seed.clone()
        } else {
            top.clone()
        };
        work.spend(before.len())?;
        let mut predecessors = 0;
        for pred in block.predecessors.iter().filter(|p| reachable.contains(p)) {
            predecessors += 1;
            work.spend(before.len() + outgoing[pred.index()].len())?;
            before.retain(|pair| outgoing[pred.index()].contains(pair));
        }
        if id != cfg.entry() && predecessors == 0 {
            return Err(shape(None, "reachable predecessor"));
        }
        incoming[id.index()] = before.clone();
        let mut after = before;
        for operation in
            &operations[offsets[block.instructions.start]..offsets[block.instructions.end]]
        {
            write(&mut after, operation.write, &pairs, &indices, &mut work)?;
        }
        if outgoing[id.index()] != after {
            outgoing[id.index()] = after;
            for edge in &block.successors {
                let Target::Block(next) = edge.target else {
                    return Err(shape(None, "resolved CFG"));
                };
                if !queued[next.index()] {
                    pending.push_back(next);
                    queued[next.index()] = true;
                }
            }
        }
    }
    // Intermediate fixed-point states are not proof obligations. Only these
    // converged facts can justify reads before each sequential write.
    for &id in &reachable {
        let block = cfg.block(id);
        let mut facts = incoming[id.index()].clone();
        for operation in
            &operations[offsets[block.instructions.start]..offsets[block.instructions.end]]
        {
            for &(old, new) in &operation.reads {
                work.spend(1)?;
                if !facts.contains(&indices[&(old, new)]) {
                    return Err(WebError::Correspondence {
                        instruction: operation.instruction,
                        assignment: operation.assignment,
                        original: Reg(old),
                        renamed: Reg(new),
                    });
                }
            }
            write(&mut facts, operation.write, &pairs, &indices, &mut work)?;
        }
    }
    Ok(WebEvidence {
        instructions: original.instructions().len(),
        assignments,
        register_reads: reads,
        relation_pairs: pairs.len(),
        blocks: reachable.len(),
    })
}

fn write(
    facts: &mut Facts,
    pair: Option<Pair>,
    domain: &[Pair],
    indices: &BTreeMap<Pair, usize>,
    work: &mut Budget,
) -> Result<()> {
    work.spend(1)?;
    if let Some((old, new)) = pair {
        work.spend(facts.len())?;
        facts.retain(|&id| domain[id].0 != old && domain[id].1 != new);
        facts.insert(indices[&(old, new)]);
    }
    Ok(())
}

fn record(operation: &Operation, domain: &mut BTreeSet<Pair>, reads: &mut usize) -> Result<()> {
    *reads += operation.reads.len();
    for pair in operation.reads.iter().copied().chain(operation.write) {
        domain.insert(pair);
        if domain.len() > MAX_PAIRS {
            return Err(unavailable("pairs"));
        }
    }
    Ok(())
}

fn paired(old: &Expr, new: &Expr, reads: &mut Vec<Pair>, pc: Option<u64>) -> Result<()> {
    let mut pending = vec![(old, new)];
    while let Some((old, new)) = pending.pop() {
        match (old, new) {
            (Expr::Const(a), Expr::Const(b)) if a == b => {}
            (Expr::Register(a), Expr::Register(b)) => reads.push((a.0, b.0)),
            (Expr::Binary(a, x, y), Expr::Binary(b, u, v)) if a == b => {
                pending.extend([(&**y, &**v), (&**x, &**u)]);
            }
            (
                Expr::Load {
                    address: a,
                    width: x,
                },
                Expr::Load {
                    address: b,
                    width: y,
                },
            ) if x == y => pending.push((a, b)),
            (
                Expr::Select {
                    condition: a,
                    taken: b,
                    not_taken: c,
                },
                Expr::Select {
                    condition: x,
                    taken: y,
                    not_taken: z,
                },
            ) => pending.extend([(&**c, &**z), (&**b, &**y), (&**a, &**x)]),
            _ => return Err(shape(pc, "expression syntax/width")),
        }
    }
    Ok(())
}

// Upfront validation includes every destination and lazy/unreachable expression.
// Sparse sets bound actual referenced registers, never register_count-sized data.
fn bounds(program: &Program) -> Result<usize> {
    if program.cfg().blocks().len() > MAX_BLOCKS {
        return Err(unavailable("blocks"));
    }
    let mut assignments = 0usize;
    let mut items = program.instructions().len();
    let mut registers = BTreeSet::new();
    for instruction in program.instructions() {
        assignments = assignments
            .checked_add(instruction.assignments.len())
            .ok_or_else(|| unavailable("points"))?;
        if assignments
            .checked_add(program.instructions().len())
            .is_none_or(|n| n > MAX_POINTS)
        {
            return Err(unavailable("points"));
        }
        for assignment in &instruction.assignments {
            items += 1;
            match &assignment.destination {
                Place::Register(reg) => {
                    registers.insert(reg.0);
                }
                Place::Memory { address, .. } => {
                    expression_bounds(address, &mut items, &mut registers)?
                }
            }
            expression_bounds(&assignment.value, &mut items, &mut registers)?;
        }
        match &instruction.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                expression_bounds(condition, &mut items, &mut registers)?
            }
            _ => {}
        }
    }
    if items > MAX_ITEMS {
        return Err(unavailable("items"));
    }
    Ok(assignments)
}

fn expression_bounds(
    expression: &Expr,
    items: &mut usize,
    registers: &mut BTreeSet<usize>,
) -> Result<()> {
    let mut pending = vec![(expression, 1)];
    while let Some((expression, depth)) = pending.pop() {
        *items += 1;
        if *items > MAX_ITEMS || depth > MAX_DEPTH {
            return Err(unavailable("expression items/depth"));
        }
        match expression {
            Expr::Const(_) => {}
            Expr::Register(reg) => {
                registers.insert(reg.0);
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Binary(_, left, right) => {
                pending.extend([(&**right, depth + 1), (&**left, depth + 1)])
            }
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
        if registers.len() > MAX_ACTIVE_REGISTERS {
            return Err(unavailable("active registers"));
        }
    }
    Ok(())
}
