//! Bounded node splitting for multiple-entry cycles. Synthetic PCs exist only
//! while proposing a reducible graph. Routing steps are removed and original
//! PCs restored before the independent source/AST checker accepts anything.

use super::*;
use crate::model::ir::{Expr, IrInstruction, Place};
use std::collections::BTreeMap;

const MAX_BLOCKS: usize = 128;
const MAX_STEPS: usize = 1024;
const MAX_EXPRESSIONS: usize = 65_536;
const MAX_ATTEMPTS: usize = 16;
const MAX_COPIED_STEPS: usize = 8;
const MAX_AST_STEPS: usize = 8192;

pub(super) fn recover(
    source: &Program,
    analysis: &ControlFlowAnalysis,
    copy_limit: usize,
    step_limit: usize,
) -> Option<StructuredFunction> {
    if copy_limit < 2 || !bounded(source) || source.instructions().len() > step_limit {
        return None;
    }
    for (attempt, (from, to)) in candidates(source, analysis).into_iter().enumerate() {
        if attempt >= MAX_ATTEMPTS {
            break;
        }
        let Some((candidate, origins)) = proposal(source, from, to) else {
            continue;
        };
        let candidate_analysis = ControlFlowAnalysis::compute(candidate.cfg()).ok()?;
        if !candidate_analysis.is_reducible() {
            continue;
        }
        let Ok(mut recovered) = StructuredFunction::recover_with_step_limit(
            &candidate,
            copy_limit.min(4),
            step_limit.saturating_mul(2).min(MAX_AST_STEPS),
        ) else {
            continue;
        };
        let mut counts = BTreeMap::new();
        if restore(&mut recovered.body, &origins, &mut counts, 0).is_none() {
            continue;
        }
        let Some(total) = counts
            .values()
            .try_fold(0usize, |sum, &n| sum.checked_add(n))
        else {
            continue;
        };
        if total > step_limit {
            continue;
        }
        let mut copies = 0;
        let mut valid = true;
        for &id in analysis.reachable() {
            let block = source.cfg().block(id);
            // A structured branch can copy a suffix of a block. Charge the
            // maximum multiplicity of any original instruction in that block.
            let n = source.instructions()[block.instructions.clone()]
                .iter()
                .map(|i| counts.get(&i.address).copied().unwrap_or(0))
                .max()
                .unwrap_or(0);
            valid &= n > 0 && n <= copy_limit;
            copies += n;
        }
        if !valid {
            continue;
        }
        let Ok(evidence) = structure_verify::validate(source, &recovered.body) else {
            continue;
        };
        recovered.register_count = source.register_count();
        recovered.evidence = evidence;
        recovered.stats = StructureStats {
            unique_blocks: analysis.reachable().len(),
            emitted_block_copies: copies,
            extra_block_copies: copies - analysis.reachable().len(),
        };
        let from = source.cfg().block(from);
        let to = source.cfg().block(to);
        recovered.split_evidence = Some(SplitEvidence {
            redirected_from: source.instructions()[from.instructions.end - 1].address,
            copied_entry: to.start,
            copied_steps: to.instructions.len(),
            attempted_candidates: attempt + 1,
        });
        return Some(recovered);
    }
    None
}

fn bounded(source: &Program) -> bool {
    if source.cfg().blocks().len() > MAX_BLOCKS
        || source.instructions().len() > MAX_STEPS
        || source.register_count() > 4096
    {
        return false;
    }
    let mut remaining = MAX_EXPRESSIONS;
    let mut pending = Vec::new();
    for i in source.instructions() {
        if i.assignments.len() > remaining {
            return false;
        }
        for a in &i.assignments {
            if let Place::Memory { address, .. } = &a.destination {
                pending.push((address, 0));
            }
            pending.push((&a.value, 0));
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &i.control {
            pending.push((condition, 0));
        }
        if pending.len() > remaining {
            return false;
        }
    }
    while let Some((e, depth)) = pending.pop() {
        if remaining == 0 || depth > 128 {
            return false;
        }
        remaining -= 1;
        match e {
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
            _ => {}
        }
    }
    true
}

// SCCs after removing natural backedges also expose irreducible cycles nested
// inside a single-entry outer loop. Whole-CFG SCCs would hide those cases.
fn candidates(source: &Program, analysis: &ControlFlowAnalysis) -> Vec<(BlockId, BlockId)> {
    let cfg = source.cfg();
    let n = cfg.blocks().len();
    let mut edges = vec![Vec::new(); n];
    let mut reverse = vec![Vec::new(); n];
    for &from in analysis.reachable() {
        for edge in &cfg.block(from).successors {
            if let Target::Block(to) = edge.target
                && !analysis.dominates(to, from)
            {
                edges[from.index()].push(to);
                reverse[to.index()].push(from);
            }
        }
    }
    let mut seen = vec![false; n];
    let mut finished = Vec::new();
    for &root in analysis.reachable() {
        let mut pending = vec![(root, false)];
        while let Some((id, finish)) = pending.pop() {
            if finish {
                finished.push(id);
            } else if !std::mem::replace(&mut seen[id.index()], true) {
                pending.push((id, true));
                pending.extend(edges[id.index()].iter().rev().map(|&id| (id, false)));
            }
        }
    }
    let mut component = vec![usize::MAX; n];
    let mut sizes = Vec::new();
    for root in finished.into_iter().rev() {
        if component[root.index()] != usize::MAX {
            continue;
        }
        let group = sizes.len();
        let mut size = 0;
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            if component[id.index()] != usize::MAX {
                continue;
            }
            component[id.index()] = group;
            size += 1;
            pending.extend_from_slice(&reverse[id.index()]);
        }
        sizes.push(size);
    }
    let mut found = Vec::new();
    for &from in analysis.reachable() {
        for &to in &edges[from.index()] {
            if component[from.index()] != component[to.index()]
                && sizes[component[to.index()]] > 1
                && cfg.block(to).instructions.len() <= MAX_COPIED_STEPS
            {
                found.push((from, to));
            }
        }
    }
    found.sort_by_key(|&(from, to)| {
        (
            cfg.block(to).instructions.len(),
            cfg.block(to).start,
            cfg.block(from).start,
        )
    });
    found.dedup();
    found
}

type Origins = BTreeMap<u64, Option<u64>>;

fn proposal(source: &Program, from: BlockId, to: BlockId) -> Option<(Program, Origins)> {
    let instructions = source.instructions();
    let from = &instructions[source.cfg().block(from).instructions.end - 1];
    let copied = source.cfg().block(to).instructions.clone();
    let copied_entry = source.cfg().block(to).start;
    let normal: BTreeMap<_, _> = instructions
        .iter()
        .enumerate()
        .map(|(i, instruction)| (instruction.address, (i * 2) as u64))
        .collect();
    let duplicates: BTreeMap<_, _> = instructions[copied.clone()]
        .iter()
        .enumerate()
        .map(|(i, instruction)| (instruction.address, ((instructions.len() + i) * 2) as u64))
        .collect();
    let entry = normal[&source.cfg().block(source.cfg().entry()).start];
    let mut output = Vec::new();
    let mut origins = BTreeMap::new();
    for (original, duplicate) in instructions
        .iter()
        .map(|i| (i, false))
        .chain(instructions[copied.clone()].iter().map(|i| (i, true)))
    {
        let address = if duplicate {
            duplicates[&original.address]
        } else {
            normal[&original.address]
        };
        let fallthrough = original.address.checked_add(u64::from(original.size))?;
        let resolve = |target: u64| -> Option<u64> {
            if !duplicate && original.address == from.address && target == copied_entry {
                return duplicates.get(&target).copied();
            }
            // Copies keep their internal sequential steps together; outgoing
            // edges (including a self-loop) return to the original graph.
            if duplicate
                && target == fallthrough
                && original.address != instructions[copied.end - 1].address
            {
                return duplicates.get(&target).copied();
            }
            normal.get(&target).copied()
        };
        let control = match &original.control {
            Control::Next => Control::Jump(resolve(fallthrough)?),
            Control::Jump(target) => Control::Jump(resolve(*target)?),
            Control::Branch { condition, target } => {
                origins.insert(address + 1, None);
                output.push(IrInstruction {
                    address: address + 1,
                    size: 1,
                    assignments: vec![],
                    control: Control::Jump(resolve(fallthrough)?),
                });
                Control::Branch {
                    condition: condition.clone(),
                    target: resolve(*target)?,
                }
            }
            Control::Return(value) => Control::Return(value.clone()),
        };
        origins.insert(address, Some(original.address));
        output.push(IrInstruction {
            address,
            size: 1,
            assignments: original.assignments.clone(),
            control,
        });
    }
    Some((
        Program::new(entry, source.register_count(), output).ok()?,
        origins,
    ))
}

fn restore(
    nodes: &mut Vec<Node>,
    origins: &Origins,
    counts: &mut BTreeMap<u64, usize>,
    depth: usize,
) -> Option<()> {
    if depth > 256 {
        return None;
    }
    let mut output = Vec::new();
    for mut node in nodes.drain(..) {
        match &mut node {
            Node::Step {
                address,
                assignments,
            } => match origins.get(address)? {
                Some(original) => {
                    *address = *original;
                    *counts.entry(*original).or_default() += 1;
                }
                None => {
                    if !assignments.is_empty() {
                        return None;
                    }
                    continue;
                }
            },
            Node::If {
                taken, not_taken, ..
            } => {
                restore(taken, origins, counts, depth + 1)?;
                restore(not_taken, origins, counts, depth + 1)?;
            }
            Node::Loop(body) => restore(body, origins, counts, depth + 1)?,
            _ => {}
        }
        output.push(node);
    }
    *nodes = output;
    Some(())
}
