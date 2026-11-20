//! Independent AST-to-flow lowering and exact control-flow correspondence.
//!
//! No dominators, loop discovery, post-dominators or structuring helpers are
//! used here. Original expressions/assignments must match syntactically. Loop
//! routing may add silent jumps, but it may not change the next original step.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::{self, Write};

use crate::ir::{Assignment, Control, Expr, Program};
use crate::structure::Node;

pub const MODEL_ID: &str = "structured-flow-v1";
const NODE_LIMIT: usize = 100_000;
const DEPTH_LIMIT: usize = 256;
const EXPRESSION_LIMIT: usize = 100_000;
const WORK_LIMIT: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FlowId(usize);

impl FlowId {
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlowNode {
    Step {
        address: u64,
        assignments: Vec<Assignment>,
        next: FlowId,
    },
    Evaluate {
        expression: Expr,
        next: FlowId,
    },
    Branch {
        condition: Expr,
        taken: FlowId,
        not_taken: FlowId,
    },
    Return(Expr),
    Jump(FlowId),
    End,
}

#[derive(Clone, Debug)]
pub struct FlowGraph {
    nodes: Vec<FlowNode>,
    entry: FlowId,
    ast_nodes: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValidationError {
    ResourceLimit,
    InvalidTransfer {
        levels: usize,
        loop_depth: usize,
    },
    SilentCycle {
        node: FlowId,
    },
    ExpectedStep {
        expected_address: u64,
        node: FlowId,
    },
    Address {
        expected: u64,
        actual: u64,
        node: FlowId,
    },
    Assignments {
        address: u64,
        node: FlowId,
    },
    Control {
        address: u64,
        node: FlowId,
    },
    MissingInstruction(u64),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit => f.write_str("structured-flow validation resource limit"),
            Self::InvalidTransfer { levels, loop_depth } => write!(
                f,
                "transfer of {levels} outer levels at loop depth {loop_depth}"
            ),
            Self::SilentCycle { node } => write!(
                f,
                "routing cycle without an original instruction at flow node {}",
                node.0
            ),
            Self::ExpectedStep {
                expected_address,
                node,
            } => write!(
                f,
                "expected original step {expected_address:#x} at flow node {}",
                node.0
            ),
            Self::Address {
                expected,
                actual,
                node,
            } => write!(
                f,
                "expected step {expected:#x}, got {actual:#x} at flow node {}",
                node.0
            ),
            Self::Assignments { address, node } => write!(
                f,
                "assignments changed at {address:#x}, flow node {}",
                node.0
            ),
            Self::Control { address, node } => write!(
                f,
                "control evaluation changed after {address:#x}, flow node {}",
                node.0
            ),
            Self::MissingInstruction(address) => {
                write!(f, "missing original instruction at {address:#x}")
            }
        }
    }
}
impl std::error::Error for ValidationError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructureEvidence {
    pub original_steps: usize,
    pub compared_copies: usize,
    pub flow_nodes: usize,
}

#[derive(Clone, Copy)]
struct LoopTargets {
    again: FlowId,
    after: FlowId,
}

impl FlowGraph {
    /// Lower syntax by lexical scope and continuations only. End is a sentinel
    /// for falling out of the function; no successful validation may reach it.
    pub fn from_nodes(body: &[Node]) -> Result<Self, ValidationError> {
        let mut graph = Self {
            nodes: vec![FlowNode::End],
            entry: FlowId(0),
            ast_nodes: 0,
        };
        graph.entry = graph.lower(body, FlowId(0), &[], 0)?;
        Ok(graph)
    }
    pub fn entry(&self) -> FlowId {
        self.entry
    }
    pub fn nodes(&self) -> &[FlowNode] {
        &self.nodes
    }
    fn push(&mut self, node: FlowNode) -> Result<FlowId, ValidationError> {
        if self.nodes.len() >= NODE_LIMIT {
            return Err(ValidationError::ResourceLimit);
        }
        let id = FlowId(self.nodes.len());
        self.nodes.push(node);
        Ok(id)
    }
    fn lower(
        &mut self,
        body: &[Node],
        mut next: FlowId,
        loops: &[LoopTargets],
        depth: usize,
    ) -> Result<FlowId, ValidationError> {
        if depth > DEPTH_LIMIT {
            return Err(ValidationError::ResourceLimit);
        }
        for node in body.iter().rev() {
            self.ast_nodes += 1;
            if self.ast_nodes >= NODE_LIMIT {
                return Err(ValidationError::ResourceLimit);
            }
            next = match node {
                Node::Step {
                    address,
                    assignments,
                } => self.push(FlowNode::Step {
                    address: *address,
                    assignments: assignments.clone(),
                    next,
                })?,
                Node::Evaluate(expression) => self.push(FlowNode::Evaluate {
                    expression: expression.clone(),
                    next,
                })?,
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let taken = self.lower(taken, next, loops, depth + 1)?;
                    let not_taken = self.lower(not_taken, next, loops, depth + 1)?;
                    self.push(FlowNode::Branch {
                        condition: condition.clone(),
                        taken,
                        not_taken,
                    })?
                }
                Node::Return(value) => self.push(FlowNode::Return(value.clone()))?,
                Node::Loop(body) => {
                    let anchor = self.push(FlowNode::End)?;
                    let mut nested = loops.to_vec();
                    nested.push(LoopTargets {
                        again: anchor,
                        after: next,
                    });
                    let first = self.lower(body, anchor, &nested, depth + 1)?;
                    self.nodes[anchor.0] = FlowNode::Jump(first);
                    anchor
                }
                Node::Break
                | Node::Continue
                | Node::BreakOuter { .. }
                | Node::ContinueOuter { .. } => {
                    let levels = match node {
                        Node::BreakOuter { levels } | Node::ContinueOuter { levels } => *levels,
                        _ => 0,
                    };
                    let scope = loops
                        .len()
                        .checked_sub(1)
                        .and_then(|innermost| innermost.checked_sub(levels))
                        .ok_or(ValidationError::InvalidTransfer {
                            levels,
                            loop_depth: loops.len(),
                        })?;
                    if matches!(node, Node::Continue | Node::ContinueOuter { .. }) {
                        loops[scope].again
                    } else {
                        loops[scope].after
                    }
                }
            };
        }
        Ok(next)
    }
    fn resolve_with_work(
        &self,
        mut id: FlowId,
        work: &mut Work,
    ) -> Result<FlowId, ValidationError> {
        for _ in 0..self.nodes.len() {
            work.spend()?;
            match &self.nodes[id.0] {
                FlowNode::Jump(target) => id = *target,
                _ => return Ok(id),
            }
        }
        Err(ValidationError::SilentCycle { node: id })
    }
    pub fn to_dot(&self) -> String {
        let mut dot = format!(
            "digraph structured_flow {{\n  entry [shape=point];\n  entry -> n{};\n",
            self.entry.0
        );
        for (index, node) in self.nodes.iter().enumerate() {
            let (label, edges) = match node {
                FlowNode::Step {
                    address,
                    assignments,
                    next,
                } => (
                    format!("step {address:#x}, {} assignments", assignments.len()),
                    vec![("", *next)],
                ),
                FlowNode::Evaluate { next, .. } => ("evaluate".into(), vec![("", *next)]),
                FlowNode::Branch {
                    taken, not_taken, ..
                } => (
                    "if".into(),
                    vec![("taken", *taken), ("not taken", *not_taken)],
                ),
                FlowNode::Return(_) => ("return".into(), vec![]),
                FlowNode::Jump(next) => ("route".into(), vec![("", *next)]),
                FlowNode::End => ("fallthrough".into(), vec![]),
            };
            writeln!(dot, "  n{index} [label=\"{label}\"];").unwrap();
            for (label, target) in edges {
                writeln!(dot, "  n{index} -> n{} [label=\"{label}\"];", target.0).unwrap();
            }
        }
        dot.push_str("}\n");
        dot
    }
}

/// Check a finite correspondence of original instruction steps and AST copies.
/// Both branch arms are checked regardless of feasibility, without evaluating
/// conditions or unrolling loops. The checker is conservative about expression
/// changes: even an equivalent rewritten expression is rejected by this model.
pub fn validate(program: &Program, body: &[Node]) -> Result<StructureEvidence, ValidationError> {
    let graph = FlowGraph::from_nodes(body)?;
    validate_graph(program, &graph, false)
}

/// Prove that every syntactic Step is a valid independent resumption point.
///
/// This also checks copies hidden after returns or in unreachable AST tails,
/// and requires every source instruction (including unreachable ones) to have
/// a checked copy. No source expression, condition, or assignment is executed.
/// Exhausted syntax, expression, routing, or correspondence budgets fail closed.
pub fn validate_reentries(
    program: &Program,
    body: &[Node],
) -> Result<StructureEvidence, ValidationError> {
    bounded_reentry_syntax(program, body)?;
    let graph = FlowGraph::from_nodes(body)?;
    validate_graph(program, &graph, true)
}

struct Work(Option<usize>);
impl Work {
    fn spend(&mut self) -> Result<(), ValidationError> {
        if let Some(remaining) = &mut self.0 {
            *remaining = remaining
                .checked_sub(1)
                .ok_or(ValidationError::ResourceLimit)?;
        }
        Ok(())
    }
}

fn bounded_reentry_syntax(program: &Program, body: &[Node]) -> Result<(), ValidationError> {
    if body.len() >= NODE_LIMIT || program.instructions().len() >= NODE_LIMIT {
        return Err(ValidationError::ResourceLimit);
    }
    let mut work = Work(Some(WORK_LIMIT));
    let mut remaining_nodes = NODE_LIMIT - 1 - body.len();
    let mut remaining_expressions = EXPRESSION_LIMIT;
    let mut pending: Vec<_> = body.iter().map(|node| (node, 1usize)).collect();
    while let Some((node, depth)) = pending.pop() {
        work.spend()?;
        if depth > DEPTH_LIMIT {
            return Err(ValidationError::ResourceLimit);
        }
        let mut push = |children: &[Node]| -> Result<(), ValidationError> {
            remaining_nodes = remaining_nodes
                .checked_sub(children.len())
                .ok_or(ValidationError::ResourceLimit)?;
            Ok(())
        };
        match node {
            Node::Step { assignments, .. } => {
                bounded_assignments(assignments, &mut remaining_expressions, &mut work)?;
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                bounded_expression(condition, &mut remaining_expressions, &mut work)?;
                push(taken)?;
                push(not_taken)?;
                pending.extend(taken.iter().chain(not_taken).map(|node| (node, depth + 1)));
            }
            Node::Loop(body) => {
                push(body)?;
                pending.extend(body.iter().map(|node| (node, depth + 1)));
            }
            Node::Evaluate(value) | Node::Return(value) => {
                bounded_expression(value, &mut remaining_expressions, &mut work)?;
            }
            _ => {}
        }
    }
    for instruction in program.instructions() {
        work.spend()?;
        bounded_assignments(
            &instruction.assignments,
            &mut remaining_expressions,
            &mut work,
        )?;
        if let Control::Branch { condition, .. } | Control::Return(condition) = &instruction.control
        {
            bounded_expression(condition, &mut remaining_expressions, &mut work)?;
        }
    }
    Ok(())
}

fn bounded_assignments(
    assignments: &[Assignment],
    remaining: &mut usize,
    work: &mut Work,
) -> Result<(), ValidationError> {
    use crate::ir::Place;
    for assignment in assignments {
        work.spend()?;
        if let Place::Memory { address, .. } = &assignment.destination {
            bounded_expression(address, remaining, work)?;
        }
        bounded_expression(&assignment.value, remaining, work)?;
    }
    Ok(())
}

fn bounded_expression(
    expression: &Expr,
    remaining: &mut usize,
    work: &mut Work,
) -> Result<(), ValidationError> {
    let mut pending = vec![(expression, 1usize)];
    while let Some((expression, depth)) = pending.pop() {
        work.spend()?;
        *remaining = remaining
            .checked_sub(1)
            .ok_or(ValidationError::ResourceLimit)?;
        if depth > DEPTH_LIMIT {
            return Err(ValidationError::ResourceLimit);
        }
        match expression {
            Expr::Binary(_, left, right) => {
                pending.extend([(left.as_ref(), depth + 1), (right.as_ref(), depth + 1)]);
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.extend([
                    (condition.as_ref(), depth + 1),
                    (taken.as_ref(), depth + 1),
                    (not_taken.as_ref(), depth + 1),
                ]);
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_graph(
    program: &Program,
    graph: &FlowGraph,
    all_reentries: bool,
) -> Result<StructureEvidence, ValidationError> {
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let entry = program.cfg().block(program.cfg().entry()).start;
    let mut pending = VecDeque::from([(entry, graph.entry)]);
    if all_reentries {
        for (index, node) in graph.nodes.iter().enumerate() {
            if let FlowNode::Step { address, .. } = node {
                pending.push_back((*address, FlowId(index)));
            }
        }
    }
    let mut work = Work(all_reentries.then_some(WORK_LIMIT));
    let mut checked = BTreeSet::new();
    let mut covered = BTreeSet::new();
    while let Some((address, id)) = pending.pop_front() {
        work.spend()?;
        let id = graph.resolve_with_work(id, &mut work)?;
        if !checked.insert((address, id)) {
            continue;
        }
        if checked.len() > NODE_LIMIT {
            return Err(ValidationError::ResourceLimit);
        }
        let instruction = instructions
            .get(&address)
            .ok_or(ValidationError::MissingInstruction(address))?;
        let FlowNode::Step {
            address: actual,
            assignments,
            next,
        } = &graph.nodes[id.0]
        else {
            return Err(ValidationError::ExpectedStep {
                expected_address: address,
                node: id,
            });
        };
        if *actual != address {
            return Err(ValidationError::Address {
                expected: address,
                actual: *actual,
                node: id,
            });
        }
        if *assignments != instruction.assignments {
            return Err(ValidationError::Assignments { address, node: id });
        }
        covered.insert(address);
        let next = graph.resolve_with_work(*next, &mut work)?;
        let fallthrough = instruction.address + u64::from(instruction.size);
        match (&instruction.control, &graph.nodes[next.0]) {
            (Control::Next, _) => pending.push_back((fallthrough, next)),
            (Control::Jump(target), _) => pending.push_back((*target, next)),
            (Control::Return(value), FlowNode::Return(actual)) if value == actual => {}
            (
                Control::Branch { condition, target },
                FlowNode::Branch {
                    condition: actual,
                    taken,
                    not_taken,
                },
            ) if condition == actual => {
                pending.push_back((*target, *taken));
                pending.push_back((fallthrough, *not_taken));
            }
            (Control::Branch { condition, target }, FlowNode::Evaluate { expression, next })
                if *target == fallthrough && condition == expression =>
            {
                pending.push_back((fallthrough, *next));
            }
            _ => {
                return Err(ValidationError::Control {
                    address,
                    node: next,
                });
            }
        }
    }
    if all_reentries {
        for instruction in program.instructions() {
            if !covered.contains(&instruction.address) {
                return Err(ValidationError::MissingInstruction(instruction.address));
            }
        }
    }
    // Check coverage independently of the structurer's visited/copy counters.
    for id in program.cfg().reachable_blocks() {
        for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()] {
            if !covered.contains(&instruction.address) {
                return Err(ValidationError::MissingInstruction(instruction.address));
            }
        }
    }
    Ok(StructureEvidence {
        original_steps: covered.len(),
        compared_copies: checked.len(),
        flow_nodes: graph.nodes.len(),
    })
}
