//! CFG-to-structured-tree recovery with bounded static code duplication.
//! Multi-exit loop tails are placed before breaks to a common follow block.
//! Transfers across nested loops retain their lexical target in the tree.

use std::collections::BTreeSet;
use std::fmt;

use crate::analysis::ControlFlowAnalysis;
use crate::cfg::{Address, BlockId, Target};
use crate::ir::{
    Assignment, Control, Execution, ExecutionError, Expr, Machine, Program, RunReport, Stop,
};
use crate::postdom::{PostDomNode, PostDominators};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Node {
    Evaluate(Expr),
    Step {
        address: Address,
        assignments: Vec<Assignment>,
    },
    If {
        condition: Expr,
        taken: Vec<Node>,
        not_taken: Vec<Node>,
    },
    Loop(Vec<Node>),
    Break,
    Continue,
    /// Break the loop `levels` enclosing loops beyond the innermost loop.
    /// Recovered trees only use positive levels here.
    BreakOuter {
        levels: usize,
    },
    /// Continue the loop `levels` enclosing loops beyond the innermost loop.
    ContinueOuter {
        levels: usize,
    },
    Return(Expr),
}

#[derive(Clone, Debug)]
pub struct StructuredFunction {
    register_count: usize,
    body: Vec<Node>,
    stats: StructureStats,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructureStats {
    pub unique_blocks: usize,
    pub emitted_block_copies: usize,
    pub extra_block_copies: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StructureError {
    Irreducible,
    CopyLimit { block: BlockId, limit: usize },
    MissingLoopFollow(BlockId),
    NonlocalLoopTransfer(BlockId),
    MissingJoin(BlockId),
    UncoveredBlocks,
}

impl fmt::Display for StructureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Irreducible => f.write_str("irreducible control flow"),
            Self::CopyLimit { block, limit } => {
                write!(f, "{block} exceeds the static copy limit of {limit}")
            }
            Self::MissingLoopFollow(id) => write!(f, "no supported common follow for loop at {id}"),
            Self::NonlocalLoopTransfer(id) => write!(f, "nonlocal loop transfer to {id}"),
            Self::MissingJoin(id) => write!(f, "no supported post-dominance join for {id}"),
            Self::UncoveredBlocks => {
                f.write_str("structured tree does not cover every reachable block")
            }
        }
    }
}

impl std::error::Error for StructureError {}

#[derive(Clone)]
struct LoopContext {
    header: BlockId,
    body: BTreeSet<BlockId>,
    exits: BTreeSet<BlockId>,
    follow: Option<BlockId>,
}

struct Builder<'a> {
    program: &'a Program,
    analysis: ControlFlowAnalysis,
    postdom: Option<PostDominators>,
    visited: BTreeSet<BlockId>,
    copies: Vec<usize>,
    copy_limit: usize,
}

impl StructuredFunction {
    pub fn recover(program: &Program) -> Result<Self, StructureError> {
        Self::recover_with_copy_limit(program, 2)
    }

    /// Bound static growth independently of the number of dynamic executions.
    /// A limit of one disables duplication; zero refuses every block.
    pub fn recover_with_copy_limit(
        program: &Program,
        copy_limit: usize,
    ) -> Result<Self, StructureError> {
        let analysis = ControlFlowAnalysis::compute(program.cfg()).expect("validated program CFG");
        if !analysis.is_reducible() {
            return Err(StructureError::Irreducible);
        }
        let mut builder = Builder {
            program,
            analysis,
            // Lack of real exits must not invent joins. Simple infinite loops
            // can still be reconstructed without using post-dominance.
            postdom: PostDominators::compute(program.cfg()).ok(),
            visited: BTreeSet::new(),
            copies: vec![0; program.cfg().blocks().len()],
            copy_limit,
        };
        let body = builder.region(program.cfg().entry(), None, &[], None)?;
        if &builder.visited != builder.analysis.reachable() {
            return Err(StructureError::UncoveredBlocks);
        }
        let emitted_block_copies = builder.copies.iter().sum();
        let stats = StructureStats {
            unique_blocks: builder.visited.len(),
            emitted_block_copies,
            extra_block_copies: emitted_block_copies - builder.visited.len(),
        };
        Ok(Self {
            register_count: program.register_count(),
            body,
            stats,
        })
    }

    pub fn body(&self) -> &[Node] {
        &self.body
    }

    pub fn stats(&self) -> StructureStats {
        self.stats
    }

    pub fn execute(&self, input: &[u64], step_limit: usize) -> Result<Execution, ExecutionError> {
        self.execute_with_memory(input, 0, &[], step_limit)
    }

    pub fn execute_with_memory(
        &self,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        step_limit: usize,
    ) -> Result<Execution, ExecutionError> {
        self.run_with_memory(input, memory_base, memory, step_limit)?
            .into_execution()
    }

    pub fn run_with_memory(
        &self,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        step_limit: usize,
    ) -> Result<RunReport, ExecutionError> {
        let mut machine =
            Machine::with_memory(self.register_count, input, memory_base, memory, step_limit)?;
        let result = match execute_nodes(&self.body, &mut machine) {
            Ok(Signal::Return(value)) => Ok(value),
            Err(stop) => Err(stop),
            _ => unreachable!("recovered function must return or exhaust its step limit"),
        };
        Ok(machine.finish(result))
    }
}

impl Builder<'_> {
    fn block_at(&self, address: Address) -> BlockId {
        self.program
            .cfg()
            .block_at(address)
            .expect("validated branch destination")
    }

    fn boundary(target: BlockId, contexts: &[LoopContext]) -> Option<Node> {
        for (levels, context) in contexts.iter().rev().enumerate() {
            if target == context.header {
                return Some(if levels == 0 {
                    Node::Continue
                } else {
                    Node::ContinueOuter { levels }
                });
            }
            if Some(target) == context.follow {
                return Some(if levels == 0 {
                    Node::Break
                } else {
                    Node::BreakOuter { levels }
                });
            }
        }
        None
    }

    fn region(
        &mut self,
        mut current: BlockId,
        stop: Option<BlockId>,
        contexts: &[LoopContext],
        entering: Option<BlockId>,
    ) -> Result<Vec<Node>, StructureError> {
        let mut nodes = Vec::new();
        let mut entering = entering;
        loop {
            if Some(current) == stop {
                return Ok(nodes);
            }
            if entering != Some(current) {
                if let Some(transfer) = Self::boundary(current, contexts) {
                    nodes.push(transfer);
                    return Ok(nodes);
                }
                if let Some(context) = contexts.last()
                    && !context.body.contains(&current)
                {
                    if !context.exits.contains(&current) {
                        return Err(StructureError::NonlocalLoopTransfer(current));
                    }
                    // Recover the selected exit in its original CFG scope,
                    // then account for moving it inside the current tree loop.
                    // Transfers local to loops in the tail keep their target;
                    // transfers to an enclosing loop cross one extra loop.
                    let mut tail = self.region(
                        current,
                        context.follow,
                        &contexts[..contexts.len() - 1],
                        None,
                    )?;
                    enclose_tail(&mut tail, 0);
                    if !always_transfers(&tail) {
                        tail.push(Node::Break);
                    }
                    nodes.extend(tail);
                    return Ok(nodes);
                }
            }

            if let Some(natural_loop) = self
                .analysis
                .natural_loops()
                .iter()
                .find(|natural_loop| natural_loop.header == current)
                .cloned()
                && entering != Some(current)
            {
                let mut exits = BTreeSet::new();
                for &member in &natural_loop.body {
                    for edge in &self.program.cfg().block(member).successors {
                        let Target::Block(target) = edge.target else {
                            unreachable!()
                        };
                        if !natural_loop.body.contains(&target) {
                            exits.insert(target);
                        }
                    }
                }
                let follow = match exits.len() {
                    0 => None,
                    1 => exits.first().copied(),
                    _ => {
                        let destinations: Vec<_> = exits.iter().copied().collect();
                        match self.postdom.as_ref().and_then(|postdom| {
                            postdom.nearest_common_post_dominator(&destinations)
                        }) {
                            Some(PostDomNode::Block(follow))
                                if !natural_loop.body.contains(&follow) =>
                            {
                                Some(follow)
                            }
                            Some(PostDomNode::Exit) => None,
                            _ => return Err(StructureError::MissingLoopFollow(current)),
                        }
                    }
                };
                let mut nested = contexts.to_vec();
                nested.push(LoopContext {
                    header: current,
                    body: natural_loop.body,
                    exits,
                    follow,
                });
                let body = self.region(current, None, &nested, Some(current))?;
                nodes.push(Node::Loop(body));
                if let Some(follow) = follow {
                    current = follow;
                    continue;
                }
                return Ok(nodes);
            }
            entering = None;
            if self.copies[current.index()] >= self.copy_limit {
                return Err(StructureError::CopyLimit {
                    block: current,
                    limit: self.copy_limit,
                });
            }
            self.copies[current.index()] += 1;
            self.visited.insert(current);
            let block = self.program.cfg().block(current);
            for instruction in &self.program.instructions()[block.instructions.clone()] {
                nodes.push(Node::Step {
                    address: instruction.address,
                    assignments: instruction.assignments.clone(),
                });
            }
            let last = &self.program.instructions()[block.instructions.end - 1];
            match &last.control {
                Control::Return(value) => {
                    nodes.push(Node::Return(value.clone()));
                    return Ok(nodes);
                }
                Control::Next => current = self.block_at(last.address + u64::from(last.size)),
                Control::Jump(target) => current = self.block_at(*target),
                Control::Branch { condition, target } => {
                    let taken = self.block_at(*target);
                    let not_taken = self.block_at(last.address + u64::from(last.size));
                    if taken == not_taken {
                        nodes.push(Node::Evaluate(condition.clone()));
                        current = taken;
                        continue;
                    }
                    let taken_transfer = Self::boundary(taken, contexts);
                    let not_transfer = Self::boundary(not_taken, contexts);
                    if taken_transfer.is_some() || not_transfer.is_some() {
                        let taken_ends = taken_transfer.is_some();
                        let not_ends = not_transfer.is_some();
                        nodes.push(Node::If {
                            condition: condition.clone(),
                            taken: taken_transfer.into_iter().collect(),
                            not_taken: not_transfer.into_iter().collect(),
                        });
                        if taken_ends && not_ends {
                            return Ok(nodes);
                        }
                        current = if taken_ends { not_taken } else { taken };
                        continue;
                    }
                    let join = match self
                        .postdom
                        .as_ref()
                        .and_then(|postdom| postdom.immediate_post_dominator(current))
                    {
                        Some(PostDomNode::Block(join)) => Some(join),
                        Some(PostDomNode::Exit) => None,
                        None => return Err(StructureError::MissingJoin(current)),
                    };
                    let taken_body = self.region(taken, join, contexts, None)?;
                    let not_body = self.region(not_taken, join, contexts, None)?;
                    let both_transfer =
                        always_transfers(&taken_body) && always_transfers(&not_body);
                    nodes.push(Node::If {
                        condition: condition.clone(),
                        taken: taken_body,
                        not_taken: not_body,
                    });
                    if both_transfer {
                        return Ok(nodes);
                    }
                    if let Some(join) = join {
                        current = join;
                    } else {
                        return Ok(nodes);
                    }
                }
            }
        }
    }
}

fn always_transfers(nodes: &[Node]) -> bool {
    match nodes.last() {
        Some(
            Node::Break
            | Node::Continue
            | Node::BreakOuter { .. }
            | Node::ContinueOuter { .. }
            | Node::Return(_),
        ) => true,
        Some(Node::If {
            taken, not_taken, ..
        }) => always_transfers(taken) && always_transfers(not_taken),
        _ => false,
    }
}

fn enclose_tail(nodes: &mut [Node], nested_loops: usize) {
    for node in nodes {
        match node {
            Node::Break if nested_loops == 0 => *node = Node::BreakOuter { levels: 1 },
            Node::Continue if nested_loops == 0 => *node = Node::ContinueOuter { levels: 1 },
            Node::BreakOuter { levels } | Node::ContinueOuter { levels }
                if *levels >= nested_loops =>
            {
                *levels += 1;
            }
            Node::If {
                taken, not_taken, ..
            } => {
                enclose_tail(taken, nested_loops);
                enclose_tail(not_taken, nested_loops);
            }
            Node::Loop(body) => enclose_tail(body, nested_loops + 1),
            _ => {}
        }
    }
}

enum Signal {
    Normal,
    Break(usize),
    Continue(usize),
    Return(u64),
}

fn execute_nodes(nodes: &[Node], machine: &mut Machine) -> Result<Signal, Stop> {
    for node in nodes {
        let signal = match node {
            Node::Evaluate(value) => {
                value.evaluate(machine)?;
                Signal::Normal
            }
            Node::Step {
                address,
                assignments,
            } => {
                machine.step(*address, assignments)?;
                Signal::Normal
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                let branch = if condition.evaluate(machine)? != 0 {
                    taken
                } else {
                    not_taken
                };
                execute_nodes(branch, machine)?
            }
            Node::Loop(body) => loop {
                match execute_nodes(body, machine)? {
                    Signal::Break(0) => break Signal::Normal,
                    Signal::Normal | Signal::Continue(0) => {}
                    Signal::Break(levels) => break Signal::Break(levels - 1),
                    Signal::Continue(levels) => break Signal::Continue(levels - 1),
                    Signal::Return(value) => break Signal::Return(value),
                }
            },
            Node::Break => Signal::Break(0),
            Node::Continue => Signal::Continue(0),
            Node::BreakOuter { levels } => Signal::Break(*levels),
            Node::ContinueOuter { levels } => Signal::Continue(*levels),
            Node::Return(value) => Signal::Return(value.evaluate(machine)?),
        };
        if !matches!(signal, Signal::Normal) {
            return Ok(signal);
        }
    }
    Ok(Signal::Normal)
}
