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
    let origins = source
        .instructions()
        .iter()
        .map(|i| {
            (
                i.address,
                Origin {
                    step: Some(i.address),
                    owner: i.address,
                },
            )
        })
        .collect();
    let mut search = Search {
        source,
        analysis,
        copy_limit,
        step_limit,
        attempts: 0,
        pending: std::collections::VecDeque::new(),
        deferred: Vec::new(),
    };
    if let Some(function) = search.expand(
        source,
        analysis,
        &origins,
        &Lineage::default(),
        candidates(source, analysis),
    ) {
        return Some(function);
    }
    while search.attempts < MAX_ATTEMPTS {
        let Some(work) = search.pending.pop_front() else {
            break;
        };
        if let Some(function) = search.expand(
            &work.program,
            &work.analysis,
            &work.origins,
            &work.lineage,
            work.entries,
        ) {
            return Some(function);
        }
    }
    // A new placement can make an earlier split constructible while duplicating
    // a return that a later traditional split shares. Keep established successful
    // trees first; source-checked alternatives complete only otherwise-refused
    // proposals and consume no additional program-split attempts.
    for work in std::mem::take(&mut search.deferred) {
        let postdom = PostDominators::compute(work.program.cfg()).ok();
        if let Some(function) = StructuredFunction::recover_with_placement_candidates(
            &work.program,
            copy_limit.min(4),
            work.step_limit,
            &work.analysis,
            postdom.as_ref(),
            |candidate| search.finish(candidate, &work.origins, &work.lineage),
        ) {
            return Some(function);
        }
    }
    None
}

#[derive(Clone, Default)]
struct Lineage {
    sites: Vec<SplitSite>,
    redirects: Vec<SplitRedirect>,
    copied_steps: usize,
}

struct Work {
    program: Program,
    analysis: ControlFlowAnalysis,
    origins: Origins,
    lineage: Lineage,
    entries: EntryCandidates,
}

struct Completion {
    program: Program,
    analysis: ControlFlowAnalysis,
    origins: Origins,
    lineage: Lineage,
    step_limit: usize,
}

struct Search<'a> {
    source: &'a Program,
    analysis: &'a ControlFlowAnalysis,
    copy_limit: usize,
    step_limit: usize,
    attempts: usize,
    pending: std::collections::VecDeque<Work>,
    deferred: Vec<Completion>,
}

impl Search<'_> {
    fn expand(
        &mut self,
        program: &Program,
        analysis: &ControlFlowAnalysis,
        origins: &Origins,
        lineage: &Lineage,
        entries: EntryCandidates,
    ) -> Option<StructuredFunction> {
        let groups = entries.cyclic_groups();
        for plan in plans(program, analysis, &entries) {
            if self.attempts == MAX_ATTEMPTS {
                break;
            }
            self.attempts += 1;
            let copied_steps = plan
                .blocks
                .iter()
                .flat_map(|&id| {
                    program.instructions()[program.cfg().block(id).instructions.clone()].iter()
                })
                .filter(|i| origins[&i.address].step.is_some())
                .count();
            let total = lineage.copied_steps.checked_add(copied_steps)?;
            if total > MAX_COPIED_STEPS {
                continue;
            }
            let redirects: Vec<_> = plan
                .redirects
                .iter()
                .map(|&(from, to)| {
                    let from = program.cfg().block(from);
                    SplitRedirect {
                        stage: lineage.sites.len(),
                        redirected_from: origins
                            [&program.instructions()[from.instructions.end - 1].address]
                            .owner,
                        copied_entry: origins[&program.cfg().block(to).start].owner,
                    }
                })
                .collect();
            let first = redirects.first()?;
            let site = SplitSite {
                redirected_from: first.redirected_from,
                copied_entry: first.copied_entry,
                copied_steps,
            };
            let Some((candidate, local)) = proposal(program, &plan) else {
                continue;
            };
            let Some(composed) = compose(&local, origins) else {
                continue;
            };
            let Ok(candidate_analysis) = ControlFlowAnalysis::compute(candidate.cfg()) else {
                continue;
            };
            let mut path = lineage.clone();
            path.sites.push(site);
            path.redirects.extend(redirects);
            path.copied_steps = total;
            if candidate_analysis.is_reducible() {
                let routes = composed
                    .values()
                    .filter(|origin| origin.step.is_none())
                    .count();
                // Original instruction budgets exclude transport-only routing.
                // Preserve the original single-stage policy; later stages add
                // a bounded allowance for synthetic routes, removed at finish.
                let candidate_limit = if lineage.sites.is_empty() {
                    self.step_limit.saturating_mul(2)
                } else {
                    self.step_limit
                        .saturating_add(routes.saturating_mul(self.copy_limit.min(4)))
                }
                .min(MAX_AST_STEPS);
                let postdom = PostDominators::compute(candidate.cfg()).ok();
                if let Ok(recovered) = StructuredFunction::recover_reducible(
                    &candidate,
                    self.copy_limit.min(4),
                    candidate_limit,
                    &candidate_analysis,
                    postdom.as_ref(),
                ) && let Some(function) = self.finish(recovered, &composed, &path)
                {
                    return Some(function);
                }
                self.deferred.push(Completion {
                    program: candidate,
                    analysis: candidate_analysis,
                    origins: composed,
                    lineage: path,
                    step_limit: candidate_limit,
                });
            } else if bounded(&candidate) {
                let next = candidates(&candidate, &candidate_analysis);
                if next.cyclic_groups() < groups {
                    // Independent cyclic components are resolved in sequence.
                    // A strict reduction gets priority; all attempts and copied
                    // original steps still share the same global limits.
                    if let Some(function) =
                        self.expand(&candidate, &candidate_analysis, &composed, &path, next)
                    {
                        return Some(function);
                    }
                } else {
                    self.pending.push_back(Work {
                        program: candidate,
                        analysis: candidate_analysis,
                        origins: composed,
                        lineage: path,
                        entries: next,
                    });
                }
            }
        }
        None
    }

    fn finish(
        &self,
        mut recovered: StructuredFunction,
        origins: &Origins,
        lineage: &Lineage,
    ) -> Option<StructuredFunction> {
        let mut counts = BTreeMap::new();
        restore(&mut recovered.body, origins, &mut counts, 0)?;
        let total = counts
            .values()
            .try_fold(0usize, |sum, &n| sum.checked_add(n))?;
        if total > self.step_limit {
            return None;
        }
        let mut copies = 0;
        for &id in self.analysis.reachable() {
            let block = self.source.cfg().block(id);
            let n = self.source.instructions()[block.instructions.clone()]
                .iter()
                .map(|i| counts.get(&i.address).copied().unwrap_or(0))
                .max()
                .unwrap_or(0);
            if n == 0 || n > self.copy_limit {
                return None;
            }
            copies += n;
        }
        recovered.register_count = self.source.register_count();
        recovered.evidence = structure_verify::validate(self.source, &recovered.body).ok()?;
        recovered.stats = StructureStats {
            unique_blocks: self.analysis.reachable().len(),
            emitted_block_copies: copies,
            extra_block_copies: copies - self.analysis.reachable().len(),
        };
        let first = lineage.sites.first()?;
        recovered.split_evidence = Some(SplitEvidence {
            redirected_from: first.redirected_from,
            copied_entry: first.copied_entry,
            copied_steps: lineage.copied_steps,
            attempted_candidates: self.attempts,
        });
        recovered.split_sites = lineage.sites.clone();
        recovered.split_redirects = lineage.redirects.clone();
        Some(recovered)
    }
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

impl EntryCandidates {
    fn cyclic_groups(&self) -> usize {
        let mut sizes = BTreeMap::new();
        for &group in &self.component {
            if group != usize::MAX {
                *sizes.entry(group).or_insert(0usize) += 1;
            }
        }
        sizes.values().filter(|&&size| size > 1).count()
    }
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

#[derive(Clone, Copy)]
struct Origin {
    step: Option<u64>,
    owner: u64,
}

type Origins = BTreeMap<u64, Origin>;

fn compose(local: &Origins, parent: &Origins) -> Option<Origins> {
    local
        .iter()
        .map(|(&pc, origin)| {
            let step = match origin.step {
                Some(previous) => parent.get(&previous)?.step,
                None => None,
            };
            Some((
                pc,
                Origin {
                    step,
                    owner: parent.get(&origin.owner)?.owner,
                },
            ))
        })
        .collect()
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CopyEdges {
    PeelPath,
    CloneRegion,
}

#[derive(Clone)]
struct SplitPlan {
    redirects: Vec<(BlockId, BlockId)>,
    blocks: Vec<BlockId>,
    edges: CopyEdges,
}

fn plans(
    source: &Program,
    analysis: &ControlFlowAnalysis,
    entries: &EntryCandidates,
) -> Vec<SplitPlan> {
    let mut plans = peeled_plans(source, analysis, entries);
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
        if plan.edges == CopyEdges::PeelPath && terminal.successors.iter().any(
            |edge| matches!(edge.target, Target::Block(target) if plan.blocks.contains(&target)),
        ) {
            let mut region = plan.clone();
            region.edges = CopyEdges::CloneRegion;
            plans.push(region);
        }
    }
    // A component with two external entries can be split into two complete
    // single-entry regions. This also preserves a common return outside the
    // component, instead of distributing it among several peeled side exits.
    for &(from, to) in &entries.edges {
        if plans.len() == MAX_ATTEMPTS {
            break;
        }
        let group = entries.component[to.index()];
        let mut blocks = vec![to];
        blocks.extend(
            source
                .cfg()
                .blocks()
                .iter()
                .map(|block| block.id)
                .filter(|&id| id != to && entries.component[id.index()] == group),
        );
        let steps: usize = blocks
            .iter()
            .map(|&id| source.cfg().block(id).instructions.len())
            .sum();
        if steps <= MAX_COPIED_STEPS
            && !plans.iter().any(|plan| {
                plan.redirects == [(from, to)]
                    && plan.blocks == blocks
                    && plan.edges == CopyEdges::CloneRegion
            })
        {
            plans.push(SplitPlan {
                redirects: vec![(from, to)],
                blocks,
                edges: CopyEdges::CloneRegion,
            });
        }
    }
    plans
}

fn peeled_plans(
    source: &Program,
    analysis: &ControlFlowAnalysis,
    entries: &EntryCandidates,
) -> Vec<SplitPlan> {
    let EntryCandidates {
        edges: entry_edges,
        component,
    } = entries;
    // Preserve every old single-block attempt and its order before spending
    // any of the remaining attempt budget on a longer forward entry path.
    let mut plans: Vec<_> = entry_edges
        .iter()
        .take(MAX_ATTEMPTS)
        .map(|&(from, to)| SplitPlan {
            redirects: vec![(from, to)],
            blocks: vec![to],
            edges: CopyEdges::PeelPath,
        })
        .collect();
    for plan in shared_entry_plans(source, entries) {
        if plans.len() == MAX_ATTEMPTS {
            return plans;
        }
        plans.push(plan);
    }
    for &entry in entry_edges {
        append_paths(source, analysis, entry, None, None, &mut plans);
        if plans.len() == MAX_ATTEMPTS {
            return plans;
        }
    }
    // A second entry is a candidate header, not a fact about the source CFG.
    // Side exits can keep targeting it while the copied forward path grows.
    // Only an actually reducible proposal and the final source/AST checker
    // can accept this placement; the same attempt budget covers every phase.
    let headers: BTreeSet<_> = entry_edges.iter().map(|&(_, to)| to).collect();
    for restrict_to_component in [false, true] {
        for &entry in entry_edges {
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

// Keep one header in the original cyclic component. External entries into
// the remaining blocks share one copied region instead of duplicating that
// region separately for each entry. Both the copied region's inner loops and
// all original-header backedges remain subject to the usual reducibility check.
fn shared_entry_plans(source: &Program, entries: &EntryCandidates) -> Vec<SplitPlan> {
    let groups: BTreeSet<_> = entries
        .edges
        .iter()
        .map(|&(_, to)| entries.component[to.index()])
        .collect();
    let mut plans = Vec::new();
    for group in groups {
        let members: Vec<_> = source
            .cfg()
            .blocks()
            .iter()
            .map(|block| block.id)
            .filter(|id| entries.component[id.index()] == group)
            .collect();
        for &header in &members {
            let redirects: Vec<_> = entries
                .edges
                .iter()
                .copied()
                .filter(|&(_, to)| entries.component[to.index()] == group && to != header)
                .collect();
            if redirects.len() < 2 {
                continue;
            }
            let first = redirects[0].1;
            let mut blocks = vec![first];
            blocks.extend(
                members
                    .iter()
                    .copied()
                    .filter(|&id| id != header && id != first),
            );
            let steps: usize = blocks
                .iter()
                .map(|&id| source.cfg().block(id).instructions.len())
                .sum();
            if steps <= MAX_COPIED_STEPS {
                plans.push(SplitPlan {
                    redirects,
                    blocks,
                    edges: CopyEdges::CloneRegion,
                });
                if plans.len() == MAX_ATTEMPTS {
                    return plans;
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
            .any(|plan| plan.redirects == [(from, to)] && plan.blocks == blocks)
        {
            plans.push(SplitPlan {
                redirects: vec![(from, to)],
                blocks: blocks.clone(),
                edges: CopyEdges::PeelPath,
            });
        }
    }
}

fn proposal(source: &Program, plan: &SplitPlan) -> Option<(Program, Origins)> {
    let instructions = source.instructions();
    let redirects: BTreeSet<_> = plan
        .redirects
        .iter()
        .map(|&(from, to)| {
            (
                instructions[source.cfg().block(from).instructions.end - 1].address,
                source.cfg().block(to).start,
            )
        })
        .collect();
    let copied: Vec<_> = plan
        .blocks
        .iter()
        .flat_map(|&id| instructions[source.cfg().block(id).instructions.clone()].iter())
        .collect();
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
            if !duplicate && redirects.contains(&(original.address, target)) {
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
                origins.insert(
                    address + 1,
                    Origin {
                        step: None,
                        owner: original.address,
                    },
                );
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
        origins.insert(
            address,
            Origin {
                step: Some(original.address),
                owner: original.address,
            },
        );
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
            } => match origins.get(address)?.step {
                Some(original) => {
                    *address = original;
                    *counts.entry(original).or_default() += 1;
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
