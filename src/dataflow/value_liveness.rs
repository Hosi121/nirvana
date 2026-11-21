//! Checked def-use chains and path-aware liveness of register SSA identities.
//!
//! A point's `before` set precedes its reads and `after` follows its definition.
//! Block `live_in` is after simultaneous phi definitions. An incoming edge is
//! before those definitions: it removes all destination phis and adds only that
//! predecessor's operands. Every syntactic phi operand is a use, even when its
//! result is unused. No execution, expression evaluation, or dead-code removal
//! is performed here.
use crate::control_flow::cfg::Target;
use crate::dataflow::ssa::{self, Definition, PointValues, Site, SsaError, SsaFunction, ValueId};
use crate::model::ir::Program;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Includes working sets and returned live-set/live-block memberships. Sparse
/// sets are bounded before insertion or copying; no value-pair matrix is built.
pub const MAX_LIVE_MEMBERS: usize = 1_000_000;
pub const MAX_WORK: usize = 8_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Liveness {
    pub blocks: Vec<BlockLiveness>,
    pub edges: Vec<EdgeLiveness>,
    /// Indexed by the corresponding `SsaFunction::values` identity.
    pub values: Vec<ValueLifetime>,
    /// Largest point, block, or individual edge live set. A block's live-out
    /// joins mutually exclusive successor paths, so this is a static bound.
    pub peak_live: usize,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockLiveness {
    pub start: u64,
    pub live_in: Vec<ValueId>,
    pub live_out: Vec<ValueId>,
    pub points: Vec<PointLiveness>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointLiveness {
    pub site: Site,
    pub before: Vec<ValueId>,
    pub after: Vec<ValueId>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EdgeLiveness {
    pub from: Option<u64>,
    pub to: u64,
    pub live: Vec<ValueId>,
}
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ValueLifetime {
    /// Point uses retain duplicate read indices in source order, followed by
    /// phi uses in result-value order and predecessor order.
    pub uses: Vec<Use>,
    /// Blocks containing the value in a block or point live set. A value used
    /// only on the virtual entry edge has no live block.
    pub live_blocks: Vec<u64>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Use {
    Point {
        site: Site,
        read: usize,
    },
    Phi {
        value: ValueId,
        predecessor: Option<u64>,
    },
}

struct Budget {
    work: usize,
    members: usize,
}
impl Budget {
    fn new() -> Self {
        Self {
            work: MAX_WORK,
            members: 0,
        }
    }
    fn spend(&mut self, amount: usize) -> Result<(), SsaError> {
        self.work = self
            .work
            .checked_sub(amount)
            .ok_or(SsaError::Unavailable("liveness work"))?;
        Ok(())
    }
    fn reserve(&mut self, amount: usize) -> Result<(), SsaError> {
        let next = self
            .members
            .checked_add(amount)
            .filter(|&next| next <= MAX_LIVE_MEMBERS)
            .ok_or(SsaError::Unavailable("liveness memberships"))?;
        self.members = next;
        Ok(())
    }
    fn release(&mut self, amount: usize) {
        self.members -= amount;
    }
    fn insert(&mut self, set: &mut BTreeSet<ValueId>, value: ValueId) -> Result<(), SsaError> {
        self.spend(1)?;
        if !set.contains(&value) {
            self.reserve(1)?;
            set.insert(value);
        }
        Ok(())
    }
    fn remove(&mut self, set: &mut BTreeSet<ValueId>, value: ValueId) -> Result<(), SsaError> {
        self.spend(1)?;
        if set.remove(&value) {
            self.release(1);
        }
        Ok(())
    }
    fn copy_set(&mut self, set: &BTreeSet<ValueId>) -> Result<BTreeSet<ValueId>, SsaError> {
        self.spend(set.len())?;
        self.reserve(set.len())?;
        Ok(set.clone())
    }
    fn vector(&mut self, set: &BTreeSet<ValueId>) -> Result<Vec<ValueId>, SsaError> {
        self.spend(set.len())?;
        self.reserve(set.len())?;
        Ok(set.iter().copied().collect())
    }
}

#[derive(Default)]
struct State {
    input: BTreeSet<ValueId>,
    output: BTreeSet<ValueId>,
}
struct Edge {
    from: Option<usize>,
    to: usize,
    operands: BTreeSet<ValueId>,
}

fn transfer(
    point: &PointValues,
    live: &mut BTreeSet<ValueId>,
    budget: &mut Budget,
) -> Result<(), SsaError> {
    budget.spend(1)?;
    if let Some(value) = point.definition {
        budget.remove(live, value)?;
    }
    for read in &point.reads {
        budget.insert(live, read.value)?;
    }
    Ok(())
}

fn edge_set(
    edge: &Edge,
    states: &[State],
    phis: &[BTreeSet<ValueId>],
    budget: &mut Budget,
) -> Result<BTreeSet<ValueId>, SsaError> {
    budget.spend(1)?;
    let mut live = BTreeSet::new();
    for &value in &states[edge.to].input {
        budget.spend(1)?;
        if !phis[edge.to].contains(&value) {
            budget.insert(&mut live, value)?;
        }
    }
    for &value in &edge.operands {
        budget.insert(&mut live, value)?;
    }
    Ok(live)
}

/// Validate source correspondence before following any candidate reference.
/// Resource exhaustion returns an error and never a partial analysis.
pub fn analyze(source: &Program, graph: &SsaFunction) -> Result<Liveness, SsaError> {
    ssa::validate(source, graph)?;
    let mut budget = Budget::new();
    // Structural allocations are bounded by SSA validation, independently of
    // live-set membership limits. Candidate block/phi order need not be sorted.
    let mut blocks: Vec<_> = graph.blocks.iter().collect();
    budget.spend(blocks.len() * (blocks.len().ilog2() as usize + 1))?;
    blocks.sort_unstable_by_key(|b| b.start);
    let indices: BTreeMap<_, _> = blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let entry = indices[&graph.entry];
    let mut phis = Vec::with_capacity(blocks.len());
    for block in &blocks {
        let mut set = BTreeSet::new();
        for &value in &block.phis {
            budget.insert(&mut set, value)?;
        }
        phis.push(set);
    }
    let mut edge_indices = BTreeMap::new();
    edge_indices.insert((None, entry), 0usize);
    for (index, block) in blocks.iter().enumerate() {
        let id = source.cfg().block_at(block.start).expect("validated block");
        for edge in &source.cfg().block(id).successors {
            budget.spend(1)?;
            let Target::Block(target) = edge.target else {
                unreachable!("validated edge")
            };
            edge_indices.insert((Some(index), indices[&source.cfg().block(target).start]), 0);
        }
    }
    let mut edges = Vec::with_capacity(edge_indices.len());
    for ((from, to), index) in &mut edge_indices {
        *index = edges.len();
        edges.push(Edge {
            from: *from,
            to: *to,
            operands: BTreeSet::new(),
        });
    }
    let mut outgoing = vec![Vec::new(); blocks.len()];
    let mut predecessors = vec![Vec::new(); blocks.len()];
    for (index, edge) in edges.iter().enumerate() {
        budget.spend(1)?;
        if let Some(from) = edge.from {
            outgoing[from].push(index);
            predecessors[edge.to].push(from);
        }
    }
    let mut values = vec![ValueLifetime::default(); graph.values.len()];
    for block in &blocks {
        for point in &block.points {
            for (read, operand) in point.reads.iter().enumerate() {
                budget.spend(1)?;
                // Total uses are bounded by validated read/phi-input caps.
                values[operand.value.0].uses.push(Use::Point {
                    site: point.site,
                    read,
                });
            }
        }
    }
    for (index, definition) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        if let Definition::Phi { block, inputs, .. } = definition {
            let mut inputs: Vec<_> = inputs.iter().collect();
            budget
                .spend(inputs.len() * (inputs.len().checked_ilog2().unwrap_or(0) as usize + 1))?;
            inputs.sort_unstable_by_key(|input| input.predecessor);
            for input in inputs {
                budget.spend(1)?;
                values[input.value.0].uses.push(Use::Phi {
                    value: ValueId(index),
                    predecessor: input.predecessor,
                });
                let from = input.predecessor.map(|start| indices[&start]);
                let edge = edge_indices[&(from, indices[block])];
                budget.insert(&mut edges[edge].operands, input.value)?;
            }
        }
    }
    let mut states: Vec<_> = (0..blocks.len()).map(|_| State::default()).collect();
    let mut pending: VecDeque<_> = (0..blocks.len()).rev().collect();
    let mut queued = vec![true; blocks.len()];
    while let Some(index) = pending.pop_front() {
        budget.spend(1)?;
        queued[index] = false;
        let mut output = BTreeSet::new();
        for &edge in &outgoing[index] {
            let live = edge_set(&edges[edge], &states, &phis, &mut budget)?;
            for &value in &live {
                budget.insert(&mut output, value)?;
            }
            budget.release(live.len());
        }
        let mut input = budget.copy_set(&output)?;
        for point in blocks[index].points.iter().rev() {
            transfer(point, &mut input, &mut budget)?;
        }
        // Set comparisons are also bounded work, including unchanged iterations.
        budget.spend(input.len() + states[index].input.len())?;
        let changed = input != states[index].input;
        budget.release(states[index].input.len() + states[index].output.len());
        states[index] = State { input, output };
        if changed {
            for &predecessor in &predecessors[index] {
                budget.spend(1)?;
                if !queued[predecessor] {
                    queued[predecessor] = true;
                    pending.push_back(predecessor);
                }
            }
        }
    }
    let mut result = Liveness {
        blocks: Vec::with_capacity(blocks.len()),
        edges: Vec::with_capacity(edges.len()),
        values,
        peak_live: 0,
    };
    for (index, block) in blocks.iter().enumerate() {
        let mut live = budget.copy_set(&states[index].output)?;
        let mut points = Vec::with_capacity(block.points.len());
        for point in block.points.iter().rev() {
            let after = budget.vector(&live)?;
            transfer(point, &mut live, &mut budget)?;
            let before = budget.vector(&live)?;
            points.push(PointLiveness {
                site: point.site,
                before,
                after,
            });
        }
        budget.spend(points.len())?;
        points.reverse();
        budget.release(live.len());
        drop(live);
        let input = budget.vector(&states[index].input)?;
        let output = budget.vector(&states[index].output)?;
        for set in std::iter::once(&input)
            .chain(std::iter::once(&output))
            .chain(points.iter().flat_map(|p| [&p.before, &p.after]))
        {
            result.peak_live = result.peak_live.max(set.len());
            for &value in set {
                budget.spend(1)?;
                let live_blocks = &mut result.values[value.0].live_blocks;
                if live_blocks.last() != Some(&block.start) {
                    budget.reserve(1)?;
                    live_blocks.push(block.start);
                }
            }
        }
        result.blocks.push(BlockLiveness {
            start: block.start,
            live_in: input,
            live_out: output,
            points,
        });
    }
    for edge in &edges {
        let live = edge_set(edge, &states, &phis, &mut budget)?;
        result.peak_live = result.peak_live.max(live.len());
        let members = budget.vector(&live)?;
        budget.release(live.len());
        result.edges.push(EdgeLiveness {
            from: edge.from.map(|index| blocks[index].start),
            to: blocks[edge.to].start,
            live: members,
        });
    }
    Ok(result)
}
