//! Partial natural-loop layout over the checked assignment-preserving goto view.
//! Blocks stay unique; edges retain explicit local transfers where needed.
//! The underlying routing projection observes return, memory and first fault.
//! Original instruction traces and budget cutoffs use the executable structurer.
use super::GotoLayout;
use crate::control_flow::analysis::ControlFlowAnalysis;
use crate::control_flow::cfg::BlockId;
use crate::model::ir::{Control, Program};
use std::collections::{BTreeMap, BTreeSet};

mod check;
#[cfg(test)]
mod tests;

const MAX_BLOCKS: usize = 128;
const MAX_INSTRUCTIONS: usize = 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Event {
    Open(BlockId),
    Block(BlockId),
    Close(BlockId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Transfer {
    Fallthrough,
    Continue,
    Break,
    Goto(BlockId),
}

#[derive(Clone, Debug)]
pub struct LoopLayout {
    events: Vec<Event>,
    edges: BTreeMap<(BlockId, BlockId), Transfer>,
    entry: BlockId,
}

struct Region {
    header: BlockId,
    members: BTreeSet<BlockId>,
}

impl LoopLayout {
    /// Add genuine single-entry loop scopes, retaining residual local edges.
    /// A separate checker parses the scopes and verifies every transfer target.
    /// Bound optional work to 128 blocks/1024 instructions; keep the flat layout
    /// available on source mismatch, non-laminar regions or any rejected plan.
    pub fn compute(program: &Program, flat: &GotoLayout) -> Option<Self> {
        if program.cfg().blocks().len() > MAX_BLOCKS
            || program.instructions().len() > MAX_INSTRUCTIONS
        {
            return None;
        }
        let analysis = ControlFlowAnalysis::compute(program.cfg()).ok()?;
        let kept: BTreeSet<_> = flat.blocks().iter().copied().collect();
        let mut regions: Vec<Region> = Vec::new();
        for natural in analysis.natural_loops() {
            let header = flat.resolve(natural.header);
            let members: BTreeSet<_> = natural.body.iter().map(|&id| flat.resolve(id)).collect();
            if !kept.contains(&header) {
                continue;
            }
            if regions.iter().any(|r| r.header == header) {
                // Collapsing assignment-free routes can identify two headers.
                // Keep the larger region, with one actual loop at that header.
                let r = regions.iter_mut().find(|r| r.header == header)?;
                if r.members.len() < members.len() {
                    r.members = members;
                }
            } else {
                regions.push(Region { header, members });
            }
        }
        if regions.is_empty() {
            return None;
        }
        regions.sort_by_key(|r| (std::cmp::Reverse(r.members.len()), r.header));
        for (index, a) in regions.iter().enumerate() {
            for b in &regions[index + 1..] {
                if !a.members.is_disjoint(&b.members) && !b.members.is_subset(&a.members) {
                    return None;
                }
                if a.members == b.members {
                    return None;
                }
            }
        }
        let mut events = Vec::new();
        schedule(flat.blocks(), &kept, None, &regions, &mut events);
        let mut closing = BTreeMap::new();
        for (index, event) in events.iter().enumerate() {
            if let Event::Close(header) = event {
                closing.insert(*header, index);
            }
        }
        let flow = |start: usize| {
            events[start..].iter().find_map(|event| match event {
                Event::Open(_) => None,
                Event::Block(id) | Event::Close(id) => Some(*id),
            })
        };
        let mut stack = Vec::new();
        let mut edges = BTreeMap::new();
        for (index, event) in events.iter().enumerate() {
            match event {
                Event::Open(header) => stack.push(*header),
                Event::Close(_) => {
                    stack.pop()?;
                }
                Event::Block(id) => {
                    let next = flow(index + 1);
                    let header = stack.last().copied();
                    let exit = header.and_then(|h| flow(closing[&h] + 1));
                    for target in successors(program, flat, *id)? {
                        let transfer = if Some(target) == next {
                            Transfer::Fallthrough
                        } else if Some(target) == header {
                            Transfer::Continue
                        } else if Some(target) == exit {
                            Transfer::Break
                        } else {
                            Transfer::Goto(target)
                        };
                        edges.insert((*id, target), transfer);
                    }
                }
            }
        }
        let result = Self {
            events,
            edges,
            entry: flat.entry(),
        };
        check::validate(program, flat, &result).then_some(result)
    }

    pub fn events(&self) -> &[Event] {
        &self.events
    }
    pub fn entry(&self) -> BlockId {
        self.entry
    }
    pub fn transfer(&self, from: BlockId, target: BlockId) -> Option<Transfer> {
        self.edges.get(&(from, target)).copied()
    }
    pub fn loop_count(&self) -> usize {
        self.events
            .iter()
            .filter(|e| matches!(e, Event::Open(_)))
            .count()
    }
    pub fn goto_count(&self) -> usize {
        self.edges
            .values()
            .filter(|e| matches!(e, Transfer::Goto(_)))
            .count()
    }
}

fn schedule(
    order: &[BlockId],
    members: &BTreeSet<BlockId>,
    header: Option<BlockId>,
    regions: &[Region],
    events: &mut Vec<Event>,
) {
    let children: Vec<_> = regions
        .iter()
        .filter(|r| {
            Some(r.header) != header
                && r.members.is_subset(members)
                && !regions.iter().any(|parent| {
                    Some(parent.header) != header
                        && parent.members != r.members
                        && parent.members.is_subset(members)
                        && r.members.is_subset(&parent.members)
                })
        })
        .collect();
    let mut emitted = BTreeSet::new();
    for id in header
        .into_iter()
        .chain(order.iter().copied().filter(|id| Some(*id) != header))
    {
        if !members.contains(&id) {
            continue;
        }
        if let Some(child) = children.iter().find(|r| r.members.contains(&id)) {
            if emitted.insert(child.header) {
                events.push(Event::Open(child.header));
                schedule(order, &child.members, Some(child.header), regions, events);
                events.push(Event::Close(child.header));
            }
        } else {
            events.push(Event::Block(id));
        }
    }
}

fn successors(program: &Program, flat: &GotoLayout, id: BlockId) -> Option<Vec<BlockId>> {
    let cfg = program.cfg();
    let i = &program.instructions()[cfg.block(id).instructions.end - 1];
    let at = |address| cfg.block_at(address).map(|id| flat.resolve(id));
    Some(match &i.control {
        Control::Next => vec![at(i.address.checked_add(u64::from(i.size))?)?],
        Control::Jump(target) => vec![at(*target)?],
        Control::Branch { target, .. } => {
            vec![at(*target)?, at(i.address.checked_add(u64::from(i.size))?)?]
        }
        Control::Return(_) => vec![],
    })
}
