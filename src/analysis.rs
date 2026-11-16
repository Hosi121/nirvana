//! Analyses of the entry-reachable portion of a recovered CFG.
//!
//! Reachable unresolved edges prevent analysis: they could hide paths that
//! invalidate dominance or loop results. Unreachable blocks are retained in
//! the CFG but have no dominator sets in this analysis.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use crate::cfg::{BlockId, Cfg, Edge, Target};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NaturalLoop {
    pub header: BlockId,
    /// Sources of back edges to the header; multiple latches are merged.
    pub latches: BTreeSet<BlockId>,
    pub body: BTreeSet<BlockId>,
}

#[derive(Clone, Debug)]
pub struct ControlFlowAnalysis {
    reachable: BTreeSet<BlockId>,
    dominators: Vec<BTreeSet<BlockId>>,
    immediate: Vec<Option<BlockId>>,
    natural_loops: Vec<NaturalLoop>,
    reducible: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnresolvedControlFlow {
    pub block: BlockId,
    pub edge: Edge,
}

impl fmt::Display for UnresolvedControlFlow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "cannot analyze: {} has unresolved {} edge to {:?}",
            self.block, self.edge.kind, self.edge.target
        )
    }
}

impl std::error::Error for UnresolvedControlFlow {}

impl ControlFlowAnalysis {
    pub fn compute(cfg: &Cfg) -> Result<Self, UnresolvedControlFlow> {
        let reachable = cfg.reachable_blocks();
        for &id in &reachable {
            for &edge in &cfg.block(id).successors {
                if !matches!(edge.target, Target::Block(_)) {
                    return Err(UnresolvedControlFlow { block: id, edge });
                }
            }
        }

        // A simple fixed-point algorithm first. Keep the semantics explicit;
        // optimize the representation only if measurements justify it.
        let mut dominators = vec![BTreeSet::new(); cfg.blocks().len()];
        for &id in &reachable {
            dominators[id.index()] = if id == cfg.entry() {
                BTreeSet::from([id])
            } else {
                reachable.clone()
            };
        }
        loop {
            let mut changed = false;
            for &id in &reachable {
                if id == cfg.entry() {
                    continue;
                }
                let mut predecessors = cfg
                    .block(id)
                    .predecessors
                    .iter()
                    .copied()
                    .filter(|pred| reachable.contains(pred));
                let first = predecessors
                    .next()
                    .expect("reachable non-entry has a predecessor");
                let mut next = dominators[first.index()].clone();
                for pred in predecessors {
                    next.retain(|dom| dominators[pred.index()].contains(dom));
                }
                next.insert(id);
                if dominators[id.index()] != next {
                    dominators[id.index()] = next;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let mut immediate = vec![None; cfg.blocks().len()];
        for &id in &reachable {
            // Strict dominators form a chain. The deepest one is the idom.
            immediate[id.index()] = dominators[id.index()]
                .iter()
                .copied()
                .filter(|&dom| dom != id)
                .max_by_key(|dom| dominators[dom.index()].len());
        }

        let mut loops: BTreeMap<BlockId, NaturalLoop> = BTreeMap::new();
        for &source in &reachable {
            for edge in &cfg.block(source).successors {
                let Target::Block(header) = edge.target else {
                    unreachable!()
                };
                if !dominators[source.index()].contains(&header) {
                    continue;
                }
                let natural_loop = loops.entry(header).or_insert_with(|| NaturalLoop {
                    header,
                    latches: BTreeSet::new(),
                    body: BTreeSet::from([header]),
                });
                natural_loop.latches.insert(source);
                let mut pending = vec![source];
                while let Some(id) = pending.pop() {
                    // Do not traverse the header's incoming edges, including
                    // when a block jumps to itself.
                    if natural_loop.body.insert(id) {
                        pending.extend(
                            cfg.block(id)
                                .predecessors
                                .iter()
                                .copied()
                                .filter(|pred| reachable.contains(pred)),
                        );
                    }
                }
            }
        }

        // A flow graph is reducible iff removing every edge whose target
        // dominates its source leaves an acyclic graph. A topological sort
        // detects irreducible cycles even inside a single-entry outer loop.
        let mut indegree = vec![0usize; cfg.blocks().len()];
        for &source in &reachable {
            for edge in &cfg.block(source).successors {
                let Target::Block(target) = edge.target else {
                    unreachable!()
                };
                if !dominators[source.index()].contains(&target) {
                    indegree[target.index()] += 1;
                }
            }
        }
        let mut pending: VecDeque<_> = reachable
            .iter()
            .copied()
            .filter(|id| indegree[id.index()] == 0)
            .collect();
        let mut visited = 0;
        while let Some(source) = pending.pop_front() {
            visited += 1;
            for edge in &cfg.block(source).successors {
                let Target::Block(target) = edge.target else {
                    unreachable!()
                };
                if !dominators[source.index()].contains(&target) {
                    indegree[target.index()] -= 1;
                    if indegree[target.index()] == 0 {
                        pending.push_back(target);
                    }
                }
            }
        }

        let reducible = visited == reachable.len();
        Ok(Self {
            reachable,
            dominators,
            immediate,
            natural_loops: loops.into_values().collect(),
            reducible,
        })
    }

    pub fn reachable(&self) -> &BTreeSet<BlockId> {
        &self.reachable
    }

    pub fn dominators(&self, block: BlockId) -> Option<&BTreeSet<BlockId>> {
        self.reachable
            .contains(&block)
            .then(|| &self.dominators[block.index()])
    }

    /// False when `block` is unreachable.
    pub fn dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        self.dominators(block)
            .is_some_and(|set| set.contains(&dominator))
    }

    /// None for the entry block and unreachable blocks.
    pub fn immediate_dominator(&self, block: BlockId) -> Option<BlockId> {
        self.immediate.get(block.index()).copied().flatten()
    }

    /// Natural loops only; irreducible cycles need not appear here.
    pub fn natural_loops(&self) -> &[NaturalLoop] {
        &self.natural_loops
    }

    pub fn is_reducible(&self) -> bool {
        self.reducible
    }
}
