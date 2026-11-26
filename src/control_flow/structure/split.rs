//! Bounded entry-region splitting for multiple-entry cycles. Synthetic PCs exist only
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
    for (attempt, plan) in plans(source, analysis).into_iter().enumerate() {
        let Some((candidate, origins)) = proposal(source, &plan) else {
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
        let from = source.cfg().block(plan.from);
        let to = source.cfg().block(plan.blocks[0]);
        recovered.split_evidence = Some(SplitEvidence {
            redirected_from: source.instructions()[from.instructions.end - 1].address,
            copied_entry: to.start,
            copied_steps: plan.steps,
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
struct EntryCandidates {
    edges: Vec<(BlockId, BlockId)>,
    component: Vec<usize>,
}

fn candidates(source: &Program, analysis: &ControlFlowAnalysis) -> EntryCandidates {
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
    EntryCandidates {
        edges: found,
        component,
    }
}

type Origins = BTreeMap<u64, Option<u64>>;

#[derive(Clone, Copy, Eq, PartialEq)]
enum CopyEdges {
    PeelPath,
    CloneRegion,
}

#[derive(Clone)]
struct SplitPlan {
    from: BlockId,
    blocks: Vec<BlockId>,
    steps: usize,
    edges: CopyEdges,
}

fn plans(source: &Program, analysis: &ControlFlowAnalysis) -> Vec<SplitPlan> {
    let mut plans = peeled_plans(source, analysis);
    let original_count = plans.len();
    // Preserve the previous candidates and their order. Spend only remaining
    // attempt slots on regions whose terminal edge closes an internal cycle.
    for index in 0..original_count {
        if plans.len() == MAX_ATTEMPTS {
            break;
        }
        let plan = &plans[index];
        let terminal = source
            .cfg()
            .block(*plan.blocks.last().expect("entry region"));
        if terminal.successors.iter().any(
            |edge| matches!(edge.target, Target::Block(target) if plan.blocks.contains(&target)),
        ) {
            let mut region = plan.clone();
            region.edges = CopyEdges::CloneRegion;
            plans.push(region);
        }
    }
    plans
}

fn peeled_plans(source: &Program, analysis: &ControlFlowAnalysis) -> Vec<SplitPlan> {
    let cfg = source.cfg();
    let EntryCandidates {
        edges: entries,
        component,
    } = candidates(source, analysis);
    // Preserve every old single-block attempt and its order before spending
    // any of the remaining attempt budget on a longer forward entry path.
    let mut plans: Vec<_> = entries
        .iter()
        .take(MAX_ATTEMPTS)
        .map(|&(from, to)| SplitPlan {
            from,
            blocks: vec![to],
            steps: cfg.block(to).instructions.len(),
            edges: CopyEdges::PeelPath,
        })
        .collect();
    for &entry in &entries {
        append_paths(source, analysis, entry, None, None, &mut plans);
        if plans.len() == MAX_ATTEMPTS {
            return plans;
        }
    }
    // A second entry is a candidate header, not a fact about the source CFG.
    // Side exits can keep targeting it while the copied forward path grows.
    // Only an actually reducible proposal and the final source/AST checker
    // can accept this placement; the same attempt budget covers every phase.
    let headers: BTreeSet<_> = entries.iter().map(|&(_, to)| to).collect();
    for restrict_to_component in [false, true] {
        for &entry in &entries {
            let group = component[entry.1.index()];
            for &header in &headers {
                if header != entry.0
                    && header != entry.1
                    && (!restrict_to_component || component[header.index()] == group)
                {
                    append_paths(
                        source,
                        analysis,
                        entry,
                        Some(header),
                        restrict_to_component.then_some((component.as_slice(), group)),
                        &mut plans,
                    );
                    if plans.len() == MAX_ATTEMPTS {
                        return plans;
                    }
                }
            }
        }
    }
    plans
}

fn append_paths(
    source: &Program,
    analysis: &ControlFlowAnalysis,
    (from, to): (BlockId, BlockId),
    header: Option<BlockId>,
    component: Option<(&[usize], usize)>,
    plans: &mut Vec<SplitPlan>,
) {
    let cfg = source.cfg();
    let mut blocks = vec![to];
    let mut steps = cfg.block(to).instructions.len();
    while plans.len() < MAX_ATTEMPTS {
        let current = *blocks.last().expect("entry path");
        // Exclude only proven backedges and the nominated boundary for path
        // discovery. The last phase also treats exits from the original
        // cyclic component as boundaries. All real edges are retained by
        // proposal(), including internal loops and exits to other regions.
        let mut successors = cfg.block(current).successors.iter().filter(|edge| {
            !matches!(edge.target, Target::Block(target)
                if analysis.dominates(target, current)
                    || Some(target) == header
                    || component.is_some_and(|(groups, group)| groups[target.index()] != group))
        });
        let Some(first) = successors.next() else {
            break;
        };
        let Target::Block(next) = first.target else {
            break;
        };
        if successors.any(|edge| edge.target != first.target)
            || next == from
            || blocks.contains(&next)
        {
            break;
        }
        steps += cfg.block(next).instructions.len();
        if steps > MAX_COPIED_STEPS {
            break;
        }
        blocks.push(next);
        if !plans
            .iter()
            .any(|plan| plan.from == from && plan.blocks == blocks)
        {
            plans.push(SplitPlan {
                from,
                blocks: blocks.clone(),
                steps,
                edges: CopyEdges::PeelPath,
            });
        }
    }
}

fn proposal(source: &Program, plan: &SplitPlan) -> Option<(Program, Origins)> {
    let instructions = source.instructions();
    let from = &instructions[source.cfg().block(plan.from).instructions.end - 1];
    let copied: Vec<_> = plan
        .blocks
        .iter()
        .flat_map(|&id| instructions[source.cfg().block(id).instructions.clone()].iter())
        .collect();
    let copied_entry = copied.first()?.address;
    let copied_last = copied.last()?.address;
    let normal: BTreeMap<_, _> = instructions
        .iter()
        .enumerate()
        .map(|(i, instruction)| (instruction.address, (i * 2) as u64))
        .collect();
    let duplicates: BTreeMap<_, _> = copied
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
        .chain(copied.iter().map(|&i| (i, true)))
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
            // A peeled path returns its final edges to the original graph.
            // A cloned region retains every internal edge, including that
            // last backedge. Both keep side exits in the original graph.
            if duplicate
                && (plan.edges == CopyEdges::CloneRegion || original.address != copied_last)
            {
                return duplicates
                    .get(&target)
                    .copied()
                    .or_else(|| normal.get(&target).copied());
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
