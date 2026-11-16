//! Post-dominance on finite paths to an explicit virtual exit.
//!
//! This is not a termination proof. Every reachable block must have a path to
//! a real terminal block; no synthetic exit edges are added to infinite SCCs.

use std::collections::BTreeSet;
use std::fmt;

use crate::analysis::{ControlFlowAnalysis, UnresolvedControlFlow};
use crate::cfg::{BlockId, Cfg, Target};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PostDomNode {
    Block(BlockId),
    Exit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PostDomError {
    Unresolved(UnresolvedControlFlow),
    NoExitPath(BTreeSet<BlockId>),
}

impl fmt::Display for PostDomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unresolved(error) => error.fmt(f),
            Self::NoExitPath(blocks) => write!(f, "no path to a terminal block from {blocks:?}"),
        }
    }
}

impl std::error::Error for PostDomError {}

#[derive(Clone, Debug)]
pub struct PostDominators {
    reachable: BTreeSet<BlockId>,
    sets: Vec<BTreeSet<PostDomNode>>,
    immediate: Vec<Option<PostDomNode>>,
}

impl PostDominators {
    pub fn compute(cfg: &Cfg) -> Result<Self, PostDomError> {
        let analysis = ControlFlowAnalysis::compute(cfg).map_err(PostDomError::Unresolved)?;
        let reachable = analysis.reachable().clone();
        let mut can_exit = BTreeSet::new();
        let mut pending: Vec<_> = reachable
            .iter()
            .copied()
            .filter(|&id| cfg.block(id).successors.is_empty())
            .collect();
        while let Some(id) = pending.pop() {
            if can_exit.insert(id) {
                pending.extend(
                    cfg.block(id)
                        .predecessors
                        .iter()
                        .copied()
                        .filter(|pred| reachable.contains(pred)),
                );
            }
        }
        let missing: BTreeSet<_> = reachable.difference(&can_exit).copied().collect();
        if !missing.is_empty() {
            return Err(PostDomError::NoExitPath(missing));
        }

        let mut universe: BTreeSet<_> = reachable.iter().copied().map(PostDomNode::Block).collect();
        universe.insert(PostDomNode::Exit);
        let mut sets = vec![BTreeSet::new(); cfg.blocks().len()];
        for &id in &reachable {
            sets[id.index()] = universe.clone();
        }
        loop {
            let mut changed = false;
            for &id in reachable.iter().rev() {
                let block = cfg.block(id);
                let mut next = if block.successors.is_empty() {
                    BTreeSet::from([PostDomNode::Exit])
                } else {
                    let mut next = universe.clone();
                    for edge in &block.successors {
                        let Target::Block(target) = edge.target else {
                            unreachable!()
                        };
                        next.retain(|node| sets[target.index()].contains(node));
                    }
                    next
                };
                next.insert(PostDomNode::Block(id));
                if sets[id.index()] != next {
                    sets[id.index()] = next;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut immediate = vec![None; cfg.blocks().len()];
        for &id in &reachable {
            immediate[id.index()] = sets[id.index()]
                .iter()
                .copied()
                .filter(|&node| node != PostDomNode::Block(id))
                .max_by_key(|node| match node {
                    PostDomNode::Exit => 1,
                    PostDomNode::Block(block) => sets[block.index()].len(),
                });
        }
        Ok(Self {
            reachable,
            sets,
            immediate,
        })
    }

    pub fn post_dominators(&self, block: BlockId) -> Option<&BTreeSet<PostDomNode>> {
        self.reachable
            .contains(&block)
            .then(|| &self.sets[block.index()])
    }

    pub fn post_dominates(&self, candidate: PostDomNode, block: BlockId) -> bool {
        self.post_dominators(block)
            .is_some_and(|set| set.contains(&candidate))
    }

    /// Exit denotes distinct return paths with no common real join block.
    pub fn immediate_post_dominator(&self, block: BlockId) -> Option<PostDomNode> {
        self.immediate.get(block.index()).copied().flatten()
    }

    /// Closest common node on the finite exit paths of all supplied blocks.
    /// None for an empty list or a block outside this analysis.
    pub fn nearest_common_post_dominator(&self, blocks: &[BlockId]) -> Option<PostDomNode> {
        let (&first, rest) = blocks.split_first()?;
        let mut common = self.post_dominators(first)?.clone();
        for &block in rest {
            let set = self.post_dominators(block)?;
            common.retain(|node| set.contains(node));
        }
        common.into_iter().max_by_key(|node| match node {
            PostDomNode::Exit => 1,
            PostDomNode::Block(block) => self.sets[block.index()].len(),
        })
    }
}
