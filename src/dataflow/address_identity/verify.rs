//! Check supplied alias classes without replaying the union-find producer.
//!
//! A class is grounded at the representative's source-copy endpoint. Every
//! other member is a real copy, or a phi whose *entire* incoming equation is
//! in the class. Reaching the anchor rules out self-supporting cycles. The
//! anchor need not be constant: a varying phi is a valid fresh class anchor.
use crate::control_flow::cfg::{BlockId, Target};
use crate::dataflow::ssa::{self, Definition, Site, SsaFunction, ValueId};
use crate::model::ir::{Expr, Program};
use std::collections::{BTreeMap, BTreeSet};

struct Budget(usize);
impl Budget {
    fn spend(&mut self, n: usize) -> Option<()> {
        self.0 = self.0.checked_sub(n)?;
        Some(())
    }
}

#[derive(Clone, Copy)]
enum Origin {
    Initial,
    Phi(BlockId),
    Assignment(BlockId, usize),
}

struct Availability<'a> {
    source: &'a Program,
    origins: Vec<Origin>,
    // For each queried definition block, nodes reachable while avoiding it.
    // A bounded source-CFG search gives dominance without producer helpers.
    avoiding: BTreeMap<BlockId, Vec<bool>>,
}
impl Availability<'_> {
    fn at(
        &mut self,
        value: ValueId,
        location: Option<(BlockId, usize)>,
        budget: &mut Budget,
    ) -> Option<bool> {
        budget.spend(1)?;
        let origin = self.origins[value.0];
        let (owner, order) = match origin {
            Origin::Initial => return Some(true),
            Origin::Phi(owner) => (owner, None),
            Origin::Assignment(owner, order) => (owner, Some(order)),
        };
        let Some((block, point)) = location else {
            // The virtual initial edge precedes every source definition.
            return Some(false);
        };
        if owner == block {
            return Some(order.is_none_or(|order| order < point));
        }
        if !self.avoiding.contains_key(&owner) {
            let cfg = self.source.cfg();
            budget.spend(cfg.blocks().len())?;
            let mut visited = vec![false; cfg.blocks().len()];
            let mut pending = vec![cfg.entry()];
            while let Some(id) = pending.pop() {
                budget.spend(1)?;
                if id == owner || std::mem::replace(&mut visited[id.index()], true) {
                    continue;
                }
                for edge in &cfg.block(id).successors {
                    budget.spend(1)?;
                    let Target::Block(next) = edge.target else {
                        return None;
                    };
                    pending.push(next);
                }
            }
            self.avoiding.insert(owner, visited);
        }
        Some(!self.avoiding[&owner][block.index()])
    }
}

pub(super) fn validate(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
) -> Option<()> {
    // This independent boundary also protects direct supplied-vector callers.
    ssa::validate(source, graph).ok()?;
    validate_checked(source, graph, aliases, opaque, &mut Budget(ssa::MAX_WORK))
}

fn validate_checked(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
    budget: &mut Budget,
) -> Option<()> {
    let count = graph.values.len();
    if aliases.len() != count {
        return None;
    }
    budget.spend(count)?;
    for &root in aliases {
        if root.0 >= count || aliases[root.0] != root {
            return None;
        }
    }
    let mut classes = vec![Vec::new(); count];
    for (id, root) in aliases.iter().enumerate() {
        classes[root.0].push(ValueId(id));
    }
    // Identity classes assert nothing, including for copies whose input was
    // intentionally left unmerged. Do not require maximal alias precision.
    if classes.iter().all(|members| members.len() <= 1) {
        return Some(());
    }

    budget.spend(count)?;
    let mut origins = vec![Origin::Initial; count];
    let mut copies = vec![None; count];
    let mut sites = BTreeMap::new();
    let mut exits = BTreeMap::new();
    for block in &graph.blocks {
        budget.spend(1)?;
        let block_id = source.cfg().block_at(block.start)?;
        for &phi in &block.phis {
            budget.spend(1)?;
            origins[phi.0] = Origin::Phi(block_id);
        }
        for (order, point) in block.points.iter().enumerate() {
            budget.spend(1)?;
            sites.insert(point.site, (block_id, order));
            if let Some(id) = point.definition {
                origins[id.0] = Origin::Assignment(block_id, order);
                if !opaque.contains(&point.site) {
                    let instruction = source
                        .instructions()
                        .binary_search_by_key(&point.site.instruction, |i| i.address)
                        .ok()?;
                    let rhs = &source.instructions()[instruction]
                        .assignments
                        .get(point.site.assignment?)?
                        .value;
                    if matches!(rhs, Expr::Register(_)) {
                        copies[id.0] = Some(point.reads.first()?.value);
                    }
                }
            }
        }
        exits.insert(block.start, (block_id, block.points.len()));
    }
    let mut availability = Availability {
        source,
        origins,
        avoiding: BTreeMap::new(),
    };
    let mut reverse = vec![Vec::new(); count];
    let mut grounded = vec![false; count];
    for (root, members) in classes.iter().enumerate().filter(|(_, c)| c.len() > 1) {
        budget.spend(members.len())?;
        let root = ValueId(root);
        let mut anchor = root;
        let mut steps = 0;
        while let Some(input) = copies[anchor.0] {
            budget.spend(1)?;
            steps += 1;
            if aliases[input.0] != root || steps > members.len() {
                return None;
            }
            anchor = input;
        }
        // Initials, noncopy/opaque assignments, and arbitrary phis are fresh
        // atoms. Only this one endpoint may enter the class without an equation.
        for &member in members {
            budget.spend(1)?;
            if member == anchor {
                continue;
            }
            if let Some(input) = copies[member.0] {
                let Definition::Assignment { site, .. } = graph.values[member.0] else {
                    return None;
                };
                if aliases[input.0] != root
                    || !availability.at(anchor, Some(sites[&site]), budget)?
                {
                    return None;
                }
                reverse[input.0].push(member);
            } else if let Definition::Phi { inputs, .. } = &graph.values[member.0] {
                for input in inputs {
                    budget.spend(1)?;
                    let location = input.predecessor.map(|start| exits[&start]);
                    if aliases[input.value.0] != root
                        || !availability.at(anchor, location, budget)?
                    {
                        return None;
                    }
                    reverse[input.value.0].push(member);
                }
            } else {
                return None;
            }
        }
        let mut pending = vec![anchor];
        while let Some(value) = pending.pop() {
            budget.spend(1)?;
            if std::mem::replace(&mut grounded[value.0], true) {
                continue;
            }
            budget.spend(reverse[value.0].len())?;
            pending.extend(reverse[value.0].iter().copied());
        }
        if members.iter().any(|value| !grounded[value.0]) {
            return None;
        }
    }
    // Class equations establish equality with the anchor. The actual chosen
    // representative must also be available wherever substitution occurs.
    for block in &graph.blocks {
        for point in &block.points {
            budget.spend(1)?;
            for read in &point.reads {
                budget.spend(1)?;
                let root = aliases[read.value.0];
                if root != read.value && !availability.at(root, Some(sites[&point.site]), budget)? {
                    return None;
                }
            }
        }
    }
    for definition in &graph.values {
        budget.spend(1)?;
        if let Definition::Phi { inputs, .. } = definition {
            for input in inputs {
                budget.spend(1)?;
                let root = aliases[input.value.0];
                let location = input.predecessor.map(|start| exits[&start]);
                if root != input.value && !availability.at(root, location, budget)? {
                    return None;
                }
            }
        }
    }
    Some(())
}

#[cfg(test)]
mod tests;
