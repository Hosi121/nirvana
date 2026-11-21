//! Bounded, block-local value numbering for the sequential IR.
//!
//! Register writes append immutable definitions. Copies share value IDs; pure
//! syntax is interned by operator and children. Each syntactic load occurrence
//! gets its own opaque captured value, even in a lazy select arm. Nothing here
//! substitutes, duplicates, or evaluates a memory operation. Values from
//! different blocks must never be compared.
use crate::model::ir::{BinaryOp, Control, Expr, Place, Program, Reg, UnaryOp};
use std::collections::BTreeMap;

pub const MAX_REGISTERS: usize = 4096;
pub const MAX_INSTRUCTIONS: usize = 16384;
pub const MAX_ASSIGNMENTS: usize = 16384;
pub const MAX_NODES: usize = 65536;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 2_000_000;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValueId(usize);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Point {
    pub instruction: u64,
    /// assignments.len() denotes the control expression in control-aware graphs.
    pub assignment: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueNode {
    Initial(Reg),
    Constant(u64),
    Unary(UnaryOp, ValueId),
    Binary(BinaryOp, ValueId, ValueId),
    Select(ValueId, ValueId, ValueId),
    /// Unique syntax occurrence, not an address or an expression to replay.
    CapturedLoad(usize),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Definition {
    pub point: Point,
    pub value: ValueId,
    /// Assignment order within this block; the RHS precedes this write.
    pub order: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Rhs {
    pub point: Point,
    pub value: ValueId,
}
#[derive(Clone, Debug)]
pub struct BlockValues {
    start: u64,
    nodes: Vec<ValueNode>,
    rhs: Vec<Rhs>,
    definitions: Vec<Vec<Definition>>,
    initial: Vec<ValueId>,
    control: Option<Rhs>,
    origins: Vec<Option<Point>>,
    intern: BTreeMap<Key, ValueId>,
}
#[derive(Clone, Debug)]
pub struct ValueGraph {
    blocks: Vec<BlockValues>,
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Key {
    Constant(u64),
    Unary(UnaryOp, ValueId),
    Binary(u8, ValueId, ValueId),
    Select(ValueId, ValueId, ValueId),
}
pub(crate) struct Work(usize);
impl Work {
    pub(crate) fn new() -> Self {
        Self(MAX_WORK)
    }
    pub(crate) fn spend(&mut self, n: usize) -> Option<()> {
        self.0 = self.0.checked_sub(n)?;
        Some(())
    }
}

impl ValueGraph {
    /// An exhausted bound declines the entire graph, never a partial result.
    pub fn build(program: &Program) -> Option<Self> {
        Self::build_mode(program, false)
    }

    /// Include the final branch/return expression without changing the legacy
    /// assignment-only points or their value numbering and resource budgets.
    pub fn build_with_control(program: &Program) -> Option<Self> {
        Self::build_mode(program, true)
    }

    fn build_mode(program: &Program, control: bool) -> Option<Self> {
        let mut work = Work::new();
        preflight(program, &mut work)?;
        let mut remaining_nodes = MAX_NODES;
        let mut blocks = Vec::new();
        for id in program.cfg().reachable_blocks() {
            work.spend(1)?;
            let block = program.cfg().block(id);
            let mut out = BlockValues {
                start: block.start,
                nodes: Vec::new(),
                rhs: Vec::new(),
                definitions: vec![Vec::new(); program.register_count()],
                initial: Vec::new(),
                control: None,
                origins: Vec::new(),
                intern: BTreeMap::new(),
            };
            let mut current = Vec::new();
            for index in 0..program.register_count() {
                let id = out.push(ValueNode::Initial(Reg(index)), None, &mut remaining_nodes)?;
                current.push(id);
                out.initial.push(id);
            }
            let mut intern = BTreeMap::new();
            for ins in &program.instructions()[block.instructions.clone()] {
                for (assignment, source) in ins.assignments.iter().enumerate() {
                    work.spend(1)?;
                    let point = Point {
                        instruction: ins.address,
                        assignment,
                    };
                    let value = out.expression(
                        &source.value,
                        &current,
                        &mut intern,
                        &mut remaining_nodes,
                        &mut work,
                        point,
                    )?;
                    let order = out.rhs.len();
                    out.rhs.push(Rhs { point, value });
                    if let Place::Register(reg) = source.destination {
                        out.definitions.get_mut(reg.0)?.push(Definition {
                            point,
                            value,
                            order,
                        });
                        *current.get_mut(reg.0)? = value;
                    }
                }
                if control
                    && let Control::Branch {
                        condition: value, ..
                    }
                    | Control::Return(value) = &ins.control
                {
                    let point = Point {
                        instruction: ins.address,
                        assignment: ins.assignments.len(),
                    };
                    let value = out.expression(
                        value,
                        &current,
                        &mut intern,
                        &mut remaining_nodes,
                        &mut work,
                        point,
                    )?;
                    if out.control.replace(Rhs { point, value }).is_some() {
                        return None;
                    }
                }
            }
            out.intern = intern;
            blocks.push(out);
        }
        blocks.sort_by_key(|b| b.start);
        Some(Self { blocks })
    }
    pub fn blocks(&self) -> &[BlockValues] {
        &self.blocks
    }
    pub fn block(&self, start: u64) -> Option<&BlockValues> {
        Some(&self.blocks[self.blocks.binary_search_by_key(&start, |b| b.start).ok()?])
    }
}
impl BlockValues {
    pub fn start(&self) -> u64 {
        self.start
    }
    pub fn points(&self) -> &[Rhs] {
        &self.rhs
    }
    pub fn all_points(&self) -> impl Iterator<Item = &Rhs> {
        self.rhs.iter().chain(self.control.iter())
    }
    pub fn control(&self) -> Option<Rhs> {
        self.control
    }
    pub fn nodes(&self) -> impl Iterator<Item = (ValueId, ValueNode)> + '_ {
        self.nodes
            .iter()
            .copied()
            .enumerate()
            .map(|(i, node)| (ValueId(i), node))
    }
    pub fn origin(&self, id: ValueId) -> Option<Point> {
        self.origins.get(id.0).copied().flatten()
    }
    pub fn node(&self, id: ValueId) -> Option<ValueNode> {
        self.nodes.get(id.0).copied()
    }
    pub fn order(&self, point: Point) -> Option<usize> {
        if self.control.is_some_and(|c| c.point == point) {
            return Some(self.rhs.len());
        }
        self.rhs.binary_search_by_key(&point, |p| p.point).ok()
    }
    pub fn rhs(&self, point: Point) -> Option<ValueId> {
        if let Some(c) = self.control
            && c.point == point
        {
            return Some(c.value);
        }
        Some(self.rhs[self.order(point)?].value)
    }
    pub fn definition_before(&self, reg: Reg, point: Point) -> Option<Definition> {
        let order = self.order(point)?;
        let defs = self.definitions.get(reg.0)?;
        let index = defs.partition_point(|d| d.order < order);
        index.checked_sub(1).map(|i| defs[i])
    }
    pub fn value_before(&self, reg: Reg, point: Point) -> Option<ValueId> {
        self.order(point)?;
        self.definitions.get(reg.0)?;
        Some(
            self.definition_before(reg, point)
                .map_or(*self.initial.get(reg.0)?, |d| d.value),
        )
    }
    fn push(
        &mut self,
        node: ValueNode,
        origin: Option<Point>,
        remaining: &mut usize,
    ) -> Option<ValueId> {
        *remaining = remaining.checked_sub(1)?;
        let id = ValueId(self.nodes.len());
        self.nodes.push(node);
        self.origins.push(origin);
        Some(id)
    }
    fn expression(
        &mut self,
        e: &Expr,
        current: &[ValueId],
        intern: &mut BTreeMap<Key, ValueId>,
        remaining: &mut usize,
        work: &mut Work,
        point: Point,
    ) -> Option<ValueId> {
        work.spend(1)?;
        // The iterative preflight has already bounded all recursive depths.
        let (key, node) = match e {
            Expr::Unary(op, value) => {
                let value = self.expression(value, current, intern, remaining, work, point)?;
                (Key::Unary(*op, value), ValueNode::Unary(*op, value))
            }
            Expr::Register(reg) => return current.get(reg.0).copied(),
            Expr::Const(n) => (Key::Constant(*n), ValueNode::Constant(*n)),
            Expr::Load { .. } => {
                // Do not inspect/reconstruct the address here. Preflight bounds
                // it, and this unique value denotes the original checked read.
                return self.push(
                    ValueNode::CapturedLoad(self.nodes.len()),
                    Some(point),
                    remaining,
                );
            }
            Expr::Binary(op, left, right) => {
                let left = self.expression(left, current, intern, remaining, work, point)?;
                let right = self.expression(right, current, intern, remaining, work, point)?;
                (
                    Key::Binary(*op as u8, left, right),
                    ValueNode::Binary(*op, left, right),
                )
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let c = self.expression(condition, current, intern, remaining, work, point)?;
                let t = self.expression(taken, current, intern, remaining, work, point)?;
                let n = self.expression(not_taken, current, intern, remaining, work, point)?;
                (Key::Select(c, t, n), ValueNode::Select(c, t, n))
            }
        };
        if let Some(value) = intern.get(&key) {
            return Some(*value);
        }
        let value = self.push(node, Some(point), remaining)?;
        intern.insert(key, value);
        Some(value)
    }

    /// Resolve only pure source syntax under the register versions at a point.
    /// Loads stay opaque occurrences; their addresses are never reconstructed.
    pub(crate) fn value_of(
        &self,
        e: &Expr,
        point: Point,
        work: &mut Work,
    ) -> Option<Option<ValueId>> {
        work.spend(1)?;
        let key = match e {
            Expr::Unary(op, value) => Key::Unary(
                *op,
                match self.value_of(value, point, work)? {
                    Some(v) => v,
                    None => return Some(None),
                },
            ),
            Expr::Register(reg) => return Some(self.value_before(*reg, point)),
            Expr::Const(value) => Key::Constant(*value),
            Expr::Binary(op, a, b) => Key::Binary(
                *op as u8,
                match self.value_of(a, point, work)? {
                    Some(v) => v,
                    None => return Some(None),
                },
                match self.value_of(b, point, work)? {
                    Some(v) => v,
                    None => return Some(None),
                },
            ),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Key::Select(
                match self.value_of(condition, point, work)? {
                    Some(v) => v,
                    None => return Some(None),
                },
                match self.value_of(taken, point, work)? {
                    Some(v) => v,
                    None => return Some(None),
                },
                match self.value_of(not_taken, point, work)? {
                    Some(v) => v,
                    None => return Some(None),
                },
            ),
            Expr::Load { .. } => return Some(None),
        };
        Some(self.intern.get(&key).copied())
    }
}

/// Iterative preflight before any clone, recursive walk or register allocation.
pub(crate) fn preflight(p: &Program, work: &mut Work) -> Option<()> {
    if p.register_count() > MAX_REGISTERS || p.instructions().len() > MAX_INSTRUCTIONS {
        return None;
    }
    let mut nodes = 0;
    let mut assignments: usize = 0;
    for ins in p.instructions() {
        work.spend(1)?;
        assignments = assignments.checked_add(ins.assignments.len())?;
        if assignments > MAX_ASSIGNMENTS {
            return None;
        }
        for a in &ins.assignments {
            match &a.destination {
                Place::Register(r) if r.0 >= p.register_count() => return None,
                Place::Memory { address, .. } => {
                    bounded(address, p.register_count(), &mut nodes, work)?;
                }
                _ => {}
            }
            bounded(&a.value, p.register_count(), &mut nodes, work)?;
        }
        if let Control::Branch { condition: e, .. } | Control::Return(e) = &ins.control {
            bounded(e, p.register_count(), &mut nodes, work)?;
        }
    }
    Some(())
}
fn bounded(e: &Expr, regs: usize, nodes: &mut usize, work: &mut Work) -> Option<()> {
    let mut pending = vec![(e, 1usize)];
    while let Some((e, depth)) = pending.pop() {
        work.spend(1)?;
        *nodes = nodes.checked_add(1)?;
        if *nodes > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        match e {
            Expr::Register(r) if r.0 >= regs => return None,
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**condition, depth + 1),
                (&**taken, depth + 1),
                (&**not_taken, depth + 1),
            ]),
        }
    }
    Some(())
}
/// Reject syntactic loads, including dead lazy arms, before cloning a source.
pub(crate) fn pure(e: &Expr, work: &mut Work) -> Option<bool> {
    let mut count = 0;
    let mut pending = vec![(e, 1usize)];
    while let Some((e, depth)) = pending.pop() {
        work.spend(1)?;
        count += 1;
        if count > crate::transform::division_expr::MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        match e {
            Expr::Load { .. } => return Some(false),
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**condition, depth + 1),
                (&**taken, depth + 1),
                (&**not_taken, depth + 1),
            ]),
            _ => {}
        }
    }
    Some(true)
}
