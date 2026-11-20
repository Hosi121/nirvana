//! Bounded predecessor paths keep alternative table bases separate at joins.

use super::{Candidate, DecodedInstruction, Operation, discover_path};
use std::collections::BTreeMap;
use std::ops::Range;

pub const MAX_CONTEXT_INSTRUCTIONS: usize = 64;
pub const MAX_CONTEXT_PATHS: usize = 64;
pub const MAX_CONTEXT_WORK: usize = 32_768;
const MAX_GRAPH: usize = 16_384;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ContextSearch {
    pub candidates: Vec<Candidate>,
    /// A cycle, depth, path or work cap left additional contexts unexplored.
    pub reached_limit: bool,
    pub paths: usize,
    pub work: usize,
}

/// Follow decoded direct CFG edges backwards from one indirect jump. Each
/// context starts with unknown registers, then interprets its actual branch
/// edges. Alternatives supply open instruction-discovery hints, never a
/// proof that all dynamic targets or paths have been enumerated.
pub fn discover_cfg(
    instructions: &[DecodedInstruction],
    branch: u64,
    memory_base: u64,
    memory: &[u8],
    function: Range<u64>,
) -> ContextSearch {
    let mut result = ContextSearch::default();
    if instructions.len() > MAX_GRAPH {
        result.reached_limit = true;
        return result;
    }
    let mut graph = BTreeMap::new();
    for &i in instructions {
        if i.size == 0
            || i.size > 15
            || !function.contains(&i.address)
            || i.address
                .checked_add(u64::from(i.size))
                .is_none_or(|next| next > function.end)
            || graph.insert(i.address, i).is_some()
        {
            return result;
        }
    }
    if !graph
        .get(&branch)
        .is_some_and(|i| matches!(i.operation, Operation::IndirectJump(_)))
    {
        return result;
    }
    let mut predecessors: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for i in graph.values() {
        let next = i.address + u64::from(i.size);
        let targets = match i.operation {
            Operation::Jump(target) => [Some(target), None],
            Operation::Branch { target, .. } => [Some(next), (target != next).then_some(target)],
            Operation::Return { .. } | Operation::IndirectJump(_) => [None, None],
            _ => [Some(next), None],
        };
        for target in targets.into_iter().flatten() {
            if graph.contains_key(&target) {
                predecessors.entry(target).or_default().push(i.address);
            }
        }
    }
    let mut pending = vec![vec![branch]];
    while let Some(path) = pending.pop() {
        if result.paths == MAX_CONTEXT_PATHS || result.work == MAX_CONTEXT_WORK {
            result.reached_limit = true;
            break;
        }
        result.work += 1;
        let previous = predecessors.get(path.last().unwrap());
        let mut extended = false;
        if path.len() < MAX_CONTEXT_INSTRUCTIONS {
            for &pc in previous.into_iter().flatten() {
                if result.work == MAX_CONTEXT_WORK {
                    result.reached_limit = true;
                    break;
                }
                result.work += 1;
                if path.contains(&pc) {
                    result.reached_limit = true;
                    continue;
                }
                if pending.len() == MAX_CONTEXT_PATHS {
                    result.reached_limit = true;
                    continue;
                }
                let mut context = path.clone();
                context.push(pc);
                pending.push(context);
                extended = true;
            }
        } else if previous.is_some() {
            result.reached_limit = true;
        }
        if !extended {
            result.paths += 1;
            let context: Vec<_> = path.iter().rev().map(|pc| graph[pc]).collect();
            if let Some(candidate) = discover_path(&context, memory_base, memory, function.clone())
            {
                merge(&mut result.candidates, candidate);
            }
        }
    }
    result
        .candidates
        .sort_by_key(|t| (t.branch, t.table, t.width.bits(), t.signed, t.bias));
    result
}

pub(crate) fn merge(tables: &mut Vec<Candidate>, mut candidate: Candidate) {
    if let Some(old) = tables.iter_mut().find(|t| {
        (t.branch, t.table, t.width, t.signed, t.bias)
            == (
                candidate.branch,
                candidate.table,
                candidate.width,
                candidate.signed,
                candidate.bias,
            )
    }) {
        old.entry_limit_hint = match (old.entry_limit_hint, candidate.entry_limit_hint) {
            (Some(a), Some(b)) => Some(a.max(b)),
            _ => None,
        };
        old.reached_entry_limit |= candidate.reached_entry_limit;
        old.entries.append(&mut candidate.entries);
        old.entries.sort_by_key(|e| e.address);
        old.entries.dedup();
        for read in candidate.read_sites {
            if old.read_sites.len() < super::MAX_READ_SITES && !old.read_sites.contains(&read) {
                old.read_sites.push(read);
            }
        }
    } else {
        tables.push(candidate);
    }
}
