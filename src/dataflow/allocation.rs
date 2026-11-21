//! Reuse storage with CFG liveness and preferences between equal copy values.
//!
//! This is only a storage assignment; no instruction or expression is removed.
//! Return values, checked memory effects, faults, and traces may be preserved
//! by relabeling according to the allocation. The complete final register file
//! is deliberately not an observation of such a relabeling.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::control_flow::cfg::Target;
use crate::model::ir::{Control, Expr, Place, Program, Reg};

const MAX_ELIGIBLE: usize = 4096;
const MAX_POINTS: usize = 100_000;
const MAX_STATE_CELLS: usize = 1_000_000;
const MAX_STEPS: usize = 100_000;
const MAX_WORK: usize = 10_000_000;
const MAX_EDGES: usize = 100_000;
const MAX_DEPTH: usize = 256;
const MAX_HINTS: usize = 8192;
const MAX_HINT_WORK: usize = 2_000_000;

type Live = BTreeSet<usize>;

struct Budget(usize);
impl Budget {
    fn spend(&mut self, work: usize) -> Option<()> {
        self.0 = self.0.checked_sub(work)?;
        Some(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct LocalAllocation {
    by_register: BTreeMap<usize, usize>,
    color_count: usize,
}

impl LocalAllocation {
    pub fn color(&self, reg: Reg) -> Option<usize> {
        self.by_register.get(&reg.0).copied()
    }

    pub fn colors(&self) -> usize {
        self.color_count
    }
}

#[derive(Clone, Default)]
struct BlockFacts {
    uses: Live,
    definitions: Live,
}

/// Deterministic storage coloring for exactly the supplied registers. A strict
/// greedy baseline competes with a copy-aware candidate; fewer storage slots
/// wins, then fewer remaining copies. A failed candidate keeps the baseline.
///
/// Inputs/parameters should be excluded. Any eligible register live at entry
/// causes rejection, as do duplicates, invalid register indices, and exhausted
/// resource bounds. A caller can use identity storage on `None`. No partial
/// allocation is returned. Equal widths are not required: consumers must choose
/// a storage width that fits every register assigned to a color.
pub fn allocate_locals(program: &Program, eligible: &[Reg]) -> Option<LocalAllocation> {
    allocate_locals_with_hints(program, eligible, &[])
}

/// Add preferences between compatible local values without weakening any
/// interference edge. Empty hints retain the ordinary allocation exactly.
/// Hints are undirected, deduplicated pairs; self-pairs have no effect. All
/// endpoints must belong to `eligible`. Invalid, excessive or exhausted hints
/// discard the entire hinted candidate and retain the ordinary allocation.
///
/// The candidate competes by storage count, then cut hint pairs, then remaining
/// copy weight. It can never increase the ordinary allocation's storage count.
/// Width compatibility is the caller's responsibility, as with allocate_locals.
pub fn allocate_locals_with_hints(
    program: &Program,
    eligible: &[Reg],
    hints: &[(Reg, Reg)],
) -> Option<LocalAllocation> {
    if eligible.len() > MAX_ELIGIBLE {
        return None;
    }
    let mut indices = BTreeMap::new();
    for reg in eligible {
        if reg.0 >= program.register_count() || indices.insert(reg.0, 0).is_some() {
            return None;
        }
    }
    if indices.is_empty() {
        return Some(LocalAllocation::default());
    }
    for (index, value) in indices.values_mut().enumerate() {
        *value = index;
    }
    let cfg = program.cfg();
    let points = program.instructions().iter().try_fold(0usize, |n, i| {
        n.checked_add(i.assignments.len())?.checked_add(1)
    })?;
    if points > MAX_POINTS
        || cfg
            .blocks()
            .len()
            .checked_mul(indices.len())?
            .checked_mul(4)?
            > MAX_STATE_CELLS
    {
        return None;
    }
    let reachable = cfg.reachable_blocks();
    let mut budget = Budget(MAX_WORK);
    let mut facts = vec![BlockFacts::default(); cfg.blocks().len()];
    for &id in &reachable {
        let block = &mut facts[id.index()];
        for instruction in &program.instructions()[cfg.block(id).instructions.clone()] {
            for assignment in &instruction.assignments {
                let mut uses = Live::new();
                reads(&assignment.value, &indices, &mut uses, &mut budget, 0)?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    reads(address, &indices, &mut uses, &mut budget, 0)?;
                }
                budget.spend(uses.len())?;
                block.uses.extend(uses.difference(&block.definitions));
                if let Place::Register(reg) = assignment.destination
                    && let Some(&index) = indices.get(&reg.0)
                {
                    block.definitions.insert(index);
                }
            }
            let mut uses = Live::new();
            control_reads(&instruction.control, &indices, &mut uses, &mut budget)?;
            budget.spend(uses.len())?;
            block.uses.extend(uses.difference(&block.definitions));
        }
    }

    let mut incoming = vec![Live::new(); cfg.blocks().len()];
    let mut outgoing = incoming.clone();
    let mut pending: VecDeque<_> = reachable.iter().rev().copied().collect();
    let mut queued = vec![false; cfg.blocks().len()];
    for &id in &reachable {
        queued[id.index()] = true;
    }
    let mut steps = MAX_STEPS;
    while let Some(id) = pending.pop_front() {
        steps = steps.checked_sub(1)?;
        queued[id.index()] = false;
        let mut after = Live::new();
        for edge in &cfg.block(id).successors {
            let Target::Block(target) = edge.target else {
                return None;
            };
            budget.spend(incoming[target.index()].len())?;
            after.extend(&incoming[target.index()]);
        }
        let facts = &facts[id.index()];
        budget.spend(facts.uses.len() + after.len())?;
        let mut before = facts.uses.clone();
        before.extend(after.difference(&facts.definitions));
        outgoing[id.index()] = after;
        if incoming[id.index()] != before {
            incoming[id.index()] = before;
            for &predecessor in &cfg.block(id).predecessors {
                if reachable.contains(&predecessor) && !queued[predecessor.index()] {
                    queued[predecessor.index()] = true;
                    pending.push_back(predecessor);
                }
            }
        }
    }
    if !incoming[cfg.entry().index()].is_empty() {
        return None;
    }

    // Always retain the old strict coloring as a valid candidate. The optional
    // copy-aware pass has its own budget and cannot turn a successful baseline
    // allocation into a resource failure or increase its storage count.
    let (strict, _) = interference(program, &indices, &reachable, &outgoing, false, &mut budget)?;
    let baseline = color_graph(&strict, None, &mut budget)?;
    let mut chosen = baseline.clone();
    let candidate = (|| {
        let mut copy_budget = Budget(MAX_WORK);
        let (graph, affinity) = interference(
            program,
            &indices,
            &reachable,
            &outgoing,
            true,
            &mut copy_budget,
        )?;
        let candidate = color_graph(&graph, Some(&affinity), &mut copy_budget)?;
        copy_budget.spend(affinity.iter().map(BTreeMap::len).sum::<usize>() * 2)?;
        let score = |coloring: &Coloring| {
            affinity
                .iter()
                .enumerate()
                .map(|(a, neighbors)| {
                    neighbors
                        .iter()
                        .filter(|(b, _)| a < **b && coloring.colors[a] != coloring.colors[**b])
                        .map(|(_, weight)| *weight)
                        .sum::<usize>()
                })
                .sum::<usize>()
        };
        if (candidate.count, score(&candidate)) < (baseline.count, score(&baseline)) {
            Some(candidate)
        } else {
            None
        }
    })();
    if let Some(candidate) = candidate {
        chosen = candidate;
    }
    // Hint processing is deliberately isolated: neither bad preferences nor
    // an exhausted optional pass can invalidate the existing allocation.
    if !hints.is_empty() {
        let hinted = (|| {
            let mut hint_budget = Budget(MAX_HINT_WORK);
            let hints = hint_affinities(hints, &indices, &mut hint_budget)?;
            let (graph, copies) = interference(
                program,
                &indices,
                &reachable,
                &outgoing,
                true,
                &mut hint_budget,
            )?;
            let candidate =
                color_graph_with_hints(&graph, Some(&copies), Some(&hints), &mut hint_budget)?;
            let score = |coloring: &Coloring, budget: &mut Budget| {
                Some((
                    coloring.count,
                    cut_weight(&hints, coloring, budget)?,
                    cut_weight(&copies, coloring, budget)?,
                ))
            };
            (score(&candidate, &mut hint_budget)? < score(&chosen, &mut hint_budget)?)
                .then_some(candidate)
        })();
        if let Some(candidate) = hinted {
            chosen = candidate;
        }
    }
    Some(LocalAllocation {
        by_register: indices
            .into_iter()
            .map(|(register, index)| (register, chosen.colors[index]))
            .collect(),
        color_count: chosen.count,
    })
}

type Affinities = Vec<BTreeMap<usize, usize>>;

fn hint_affinities(
    pairs: &[(Reg, Reg)],
    indices: &BTreeMap<usize, usize>,
    budget: &mut Budget,
) -> Option<Affinities> {
    if pairs.len() > MAX_HINTS {
        return None;
    }
    let mut hints = vec![BTreeMap::new(); indices.len()];
    for &(a, b) in pairs {
        budget.spend(1)?;
        let (&a, &b) = (indices.get(&a.0)?, indices.get(&b.0)?);
        if a != b {
            hints[a].insert(b, 1);
            hints[b].insert(a, 1);
        }
    }
    Some(hints)
}

fn cut_weight(affinity: &Affinities, coloring: &Coloring, budget: &mut Budget) -> Option<usize> {
    let mut cost = 0usize;
    for (a, neighbors) in affinity.iter().enumerate() {
        budget.spend(neighbors.len() + 1)?;
        for (&b, &weight) in neighbors {
            if a < b && coloring.colors[a] != coloring.colors[b] {
                cost = cost.checked_add(weight)?;
            }
        }
    }
    Some(cost)
}

fn interference(
    program: &Program,
    indices: &BTreeMap<usize, usize>,
    reachable: &BTreeSet<crate::control_flow::cfg::BlockId>,
    outgoing: &[Live],
    copies: bool,
    budget: &mut Budget,
) -> Option<(Graph, Affinities)> {
    let cfg = program.cfg();
    let mut graph = Graph {
        adjacent: vec![Live::new(); indices.len()],
        edges: 0,
    };
    let mut affinity = vec![BTreeMap::new(); indices.len()];
    for &id in reachable {
        budget.spend(outgoing[id.index()].len())?;
        let mut live = outgoing[id.index()].clone();
        for instruction in program.instructions()[cfg.block(id).instructions.clone()]
            .iter()
            .rev()
        {
            let mut uses = Live::new();
            control_reads(&instruction.control, indices, &mut uses, budget)?;
            // Simultaneous operands stay distinct. This also avoids exposing
            // x==x in C merely because two virtual operands share storage.
            graph.clique(&uses, budget)?;
            live.extend(uses);
            for assignment in instruction.assignments.iter().rev() {
                if let Place::Register(reg) = assignment.destination
                    && let Some(&definition) = indices.get(&reg.0)
                {
                    let source = if copies && let Expr::Register(source) = assignment.value {
                        indices.get(&source.0).copied()
                    } else {
                        None
                    };
                    if let Some(source) = source
                        && source != definition
                    {
                        budget.spend(2)?;
                        *affinity[definition].entry(source).or_default() += 1;
                        *affinity[source].entry(definition).or_default() += 1;
                    }
                    for &other in &live {
                        // At d=s both slots hold s after this assignment. This
                        // exception applies only at this exact copy; every
                        // other definition still adds its ordinary conflicts.
                        if Some(other) != source {
                            graph.edge(definition, other, budget)?;
                        }
                    }
                    live.remove(&definition);
                }
                let mut uses = Live::new();
                reads(&assignment.value, indices, &mut uses, budget, 0)?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    reads(address, indices, &mut uses, budget, 0)?;
                }
                graph.clique(&uses, budget)?;
                budget.spend(uses.len())?;
                live.extend(uses);
            }
        }
    }
    Some((graph, affinity))
}

#[derive(Clone)]
struct Coloring {
    colors: Vec<usize>,
    count: usize,
}

fn color_graph(
    graph: &Graph,
    affinity: Option<&Affinities>,
    budget: &mut Budget,
) -> Option<Coloring> {
    color_graph_with_hints(graph, affinity, None, budget)
}

fn color_graph_with_hints(
    graph: &Graph,
    affinity: Option<&Affinities>,
    hints: Option<&Affinities>,
    budget: &mut Budget,
) -> Option<Coloring> {
    let mut order: Vec<_> = (0..graph.adjacent.len()).collect();
    order.sort_by_key(|&index| (std::cmp::Reverse(graph.adjacent[index].len()), index));
    let mut colors: Vec<Option<usize>> = vec![None; graph.adjacent.len()];
    let mut count = 0;
    for vertex in order {
        let moves = affinity.map(|a| &a[vertex]);
        budget.spend(count + graph.adjacent[vertex].len() + moves.map_or(0, |a| a.len()) + 1)?;
        let mut used = vec![false; count];
        for &neighbor in &graph.adjacent[vertex] {
            if let Some(color) = colors[neighbor] {
                used[color] = true;
            }
        }
        let mut preference = vec![0usize; count];
        if let Some(moves) = moves {
            for (&neighbor, &weight) in moves {
                if let Some(color) = colors[neighbor]
                    && !used[color]
                {
                    preference[color] += weight;
                }
            }
        }
        let mut hint_preference = vec![0usize; count];
        if let Some(hints) = hints {
            budget.spend(count + hints[vertex].len())?;
            for (&neighbor, &weight) in &hints[vertex] {
                if let Some(color) = colors[neighbor]
                    && !used[color]
                {
                    hint_preference[color] += weight;
                }
            }
        }
        let preferred = (0..count)
            .filter(|&c| !used[c])
            .max_by_key(|&c| (hint_preference[c], preference[c], std::cmp::Reverse(c)));
        let color = preferred.unwrap_or(count);
        count = count.max(color + 1);
        colors[vertex] = Some(color);
    }
    Some(Coloring {
        colors: colors.into_iter().collect::<Option<_>>()?,
        count,
    })
}

struct Graph {
    adjacent: Vec<Live>,
    edges: usize,
}
impl Graph {
    fn edge(&mut self, left: usize, right: usize, budget: &mut Budget) -> Option<()> {
        budget.spend(1)?;
        if left != right && !self.adjacent[left].contains(&right) {
            if self.edges >= MAX_EDGES {
                return None;
            }
            self.adjacent[left].insert(right);
            self.adjacent[right].insert(left);
            self.edges += 1;
        }
        Some(())
    }

    fn clique(&mut self, uses: &Live, budget: &mut Budget) -> Option<()> {
        for &left in uses {
            for &right in uses.range((std::ops::Bound::Excluded(left), std::ops::Bound::Unbounded))
            {
                self.edge(left, right, budget)?;
            }
        }
        Some(())
    }
}

fn control_reads(
    control: &Control,
    indices: &BTreeMap<usize, usize>,
    uses: &mut Live,
    budget: &mut Budget,
) -> Option<()> {
    match control {
        Control::Branch { condition, .. } => reads(condition, indices, uses, budget, 0),
        Control::Return(value) => reads(value, indices, uses, budget, 0),
        _ => Some(()),
    }
}

fn reads(
    expression: &Expr,
    indices: &BTreeMap<usize, usize>,
    uses: &mut Live,
    budget: &mut Budget,
    depth: usize,
) -> Option<()> {
    if depth > MAX_DEPTH {
        return None;
    }
    budget.spend(1)?;
    match expression {
        Expr::Const(_) => {}
        Expr::Unary(_, value) => reads(value, indices, uses, budget, depth + 1)?,
        Expr::Register(reg) => {
            if let Some(&index) = indices.get(&reg.0) {
                uses.insert(index);
            }
        }
        Expr::Binary(_, left, right) => {
            reads(left, indices, uses, budget, depth + 1)?;
            reads(right, indices, uses, budget, depth + 1)?;
        }
        Expr::Load { address, .. } => reads(address, indices, uses, budget, depth + 1)?,
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            reads(condition, indices, uses, budget, depth + 1)?;
            reads(taken, indices, uses, budget, depth + 1)?;
            reads(not_taken, indices, uses, budget, depth + 1)?;
        }
    }
    Some(())
}
