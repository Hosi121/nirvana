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
    fn resolve(&self, mut id: FlowId) -> Result<FlowId, ValidationError> {
        for _ in 0..self.nodes.len() {
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
    validate_graph(program, &graph)
}

fn validate_graph(
    program: &Program,
    graph: &FlowGraph,
) -> Result<StructureEvidence, ValidationError> {
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let entry = program.cfg().block(program.cfg().entry()).start;
    let mut pending = VecDeque::from([(entry, graph.entry)]);
    let mut checked = BTreeSet::new();
    let mut covered = BTreeSet::new();
    while let Some((address, id)) = pending.pop_front() {
        let id = graph.resolve(id)?;
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
        let next = graph.resolve(*next)?;
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
