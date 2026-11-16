//! Reuse storage for eligible local registers using ordinary CFG liveness.
//!
//! This is only a storage assignment; no instruction or expression is removed.
//! Return values, checked memory effects, faults, and traces may be preserved
//! by relabeling according to the allocation. The complete final register file
//! is deliberately not an observation of such a relabeling.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::cfg::Target;
use crate::ir::{Control, Expr, Place, Program, Reg};

const MAX_ELIGIBLE: usize = 4096;
const MAX_POINTS: usize = 100_000;
const MAX_STATE_CELLS: usize = 1_000_000;
const MAX_STEPS: usize = 100_000;
const MAX_WORK: usize = 10_000_000;
const MAX_EDGES: usize = 100_000;
const MAX_DEPTH: usize = 256;

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

/// Deterministic greedy storage coloring for exactly the supplied registers.
///
/// Inputs/parameters should be excluded. Any eligible register live at entry
/// causes rejection, as do duplicates, invalid register indices, and exhausted
/// resource bounds. A caller can use identity storage on `None`. No partial
/// allocation is returned. Equal widths are not required: consumers must choose
/// a storage width that fits every register assigned to a color.
pub fn allocate_locals(program: &Program, eligible: &[Reg]) -> Option<LocalAllocation> {
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

    let mut graph = Graph {
        adjacent: vec![Live::new(); indices.len()],
        edges: 0,
    };
    for &id in &reachable {
        budget.spend(outgoing[id.index()].len())?;
        let mut live = outgoing[id.index()].clone();
        for instruction in program.instructions()[cfg.block(id).instructions.clone()]
            .iter()
            .rev()
        {
            let mut uses = Live::new();
            control_reads(&instruction.control, &indices, &mut uses, &mut budget)?;
            graph.clique(&uses, &mut budget)?;
            live.extend(uses);
            for assignment in instruction.assignments.iter().rev() {
                if let Place::Register(reg) = assignment.destination
                    && let Some(&definition) = indices.get(&reg.0)
                {
                    // Even an unused write must not clobber another live value.
                    for &other in &live {
                        graph.edge(definition, other, &mut budget)?;
                    }
                    live.remove(&definition);
                }
                let mut uses = Live::new();
                reads(&assignment.value, &indices, &mut uses, &mut budget, 0)?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    reads(address, &indices, &mut uses, &mut budget, 0)?;
                }
                graph.clique(&uses, &mut budget)?;
                budget.spend(uses.len())?;
                live.extend(uses);
            }
        }
    }

    let mut order: Vec<_> = (0..indices.len()).collect();
    order.sort_by_key(|&index| (std::cmp::Reverse(graph.adjacent[index].len()), index));
    let mut colors = vec![None; indices.len()];
    let mut color_count = 0;
    for vertex in order {
        budget.spend(color_count + graph.adjacent[vertex].len() + 1)?;
        let mut used = vec![false; color_count];
        for &neighbor in &graph.adjacent[vertex] {
            if let Some(color) = colors[neighbor] {
                used[color] = true;
            }
        }
        let color = used.iter().position(|&used| !used).unwrap_or(color_count);
        color_count = color_count.max(color + 1);
        colors[vertex] = Some(color);
    }
    Some(LocalAllocation {
        by_register: indices
            .into_iter()
            .map(|(register, index)| Some((register, colors[index]?)))
            .collect::<Option<_>>()?,
        color_count,
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
