//! A fallthrough-oriented C layout of the original reachable basic blocks.
//!
//! Only literally assignment-free unconditional routing blocks can disappear
//! from this view. Conditions, assignments, and the executable Program remain
//! untouched. Routing removal deliberately does not preserve instruction traces
//! or instruction-budget cutoffs. An empty routing cycle keeps one self-looping
//! representative so a nonterminating path cannot turn into a return.

pub mod loops;

use crate::control_flow::cfg::{BlockId, Target};
use crate::model::ir::{Control, Program};

pub const MAX_LAYOUT_BLOCKS: usize = 16_384;
pub const MAX_LAYOUT_INSTRUCTIONS: usize = 262_144;

#[derive(Clone, Debug)]
pub struct GotoLayout {
    blocks: Vec<BlockId>,
    entry: BlockId,
    resolved: Vec<BlockId>,
}

impl GotoLayout {
    /// Plan the reachable blocks, preferring the not-taken successor at branches.
    /// No partial plan is returned on invalid edges or exhausted size bounds.
    /// Unresolved edges are rejected even in unreachable blocks.
    pub fn compute(program: &Program) -> Option<Self> {
        let cfg = program.cfg();
        let count = cfg.blocks().len();
        if count == 0
            || count > MAX_LAYOUT_BLOCKS
            || program.instructions().len() > MAX_LAYOUT_INSTRUCTIONS
            || cfg.entry().index() >= count
        {
            return None;
        }
        let ids: Vec<_> = cfg.blocks().iter().map(|block| block.id).collect();
        let mut successors = vec![Vec::new(); count];
        let mut routing = vec![None; count];
        for (index, block) in cfg.blocks().iter().enumerate() {
            if block.id.index() != index
                || block.instructions.is_empty()
                || block.instructions.end > program.instructions().len()
            {
                return None;
            }
            for edge in &block.successors {
                let Target::Block(target) = edge.target else {
                    return None;
                };
                if target.index() >= count {
                    return None;
                }
            }
            let instructions = &program.instructions()[block.instructions.clone()];
            let last = instructions.last()?;
            let target = |address| cfg.block_at(address);
            let fallthrough = || target(last.address.checked_add(u64::from(last.size))?);
            successors[index] = match &last.control {
                Control::Next => vec![fallthrough()?],
                Control::Jump(address) => vec![target(*address)?],
                Control::Branch { target: taken, .. } => {
                    vec![fallthrough()?, target(*taken)?]
                }
                Control::Return(_) => vec![],
            };
            if instructions.iter().all(|i| i.assignments.is_empty())
                && matches!(last.control, Control::Next | Control::Jump(_))
            {
                routing[index] = successors[index].first().copied();
            }
        }

        // A routing block has exactly one successor. Resolve its functional
        // graph once, marking each active path to find cycles in linear work.
        let mut resolved = vec![None; count];
        let mut active_position = vec![None; count];
        for start in 0..count {
            if resolved[start].is_some() {
                continue;
            }
            let mut path = Vec::new();
            let mut cursor = start;
            let destination = loop {
                if let Some(destination) = resolved[cursor] {
                    break destination;
                }
                if let Some(position) = active_position[cursor] {
                    let representative = path[position..].iter().copied().min()?;
                    let destination = ids[representative];
                    for &member in &path[position..] {
                        resolved[member] = Some(destination);
                    }
                    break destination;
                }
                let Some(next) = routing[cursor] else {
                    resolved[cursor] = Some(ids[cursor]);
                    break ids[cursor];
                };
                active_position[cursor] = Some(path.len());
                path.push(cursor);
                cursor = next.index();
            };
            for member in path.into_iter().rev() {
                resolved[member] = Some(destination);
                active_position[member] = None;
            }
        }
        let resolved = resolved.into_iter().collect::<Option<Vec<_>>>()?;
        let entry = resolved[cfg.entry().index()];

        // Preorder DFS follows preferred fallthroughs first. A routing cycle
        // representative resolves its original successor back to itself.
        let mut visited = vec![false; count];
        let mut pending = vec![entry];
        let mut blocks = Vec::new();
        while let Some(block) = pending.pop() {
            if visited[block.index()] {
                continue;
            }
            visited[block.index()] = true;
            blocks.push(block);
            for successor in successors[block.index()].iter().rev() {
                let successor = resolved[successor.index()];
                if !visited[successor.index()] {
                    pending.push(successor);
                }
            }
        }
        Some(Self {
            blocks,
            entry,
            resolved,
        })
    }

    pub fn blocks(&self) -> &[BlockId] {
        &self.blocks
    }

    pub fn entry(&self) -> BlockId {
        self.entry
    }

    /// Resolve an original block before emitting a jump or comparing adjacency.
    /// Valid original IDs include unreachable blocks, although `blocks()` only
    /// emits reachable ones. An out-of-range foreign ID is returned unchanged.
    pub fn resolve(&self, block: BlockId) -> BlockId {
        self.resolved.get(block.index()).copied().unwrap_or(block)
    }
}
