//! Plan function-scope declarations at initial root assignments without changing
//! the AST, register grouping, expression evaluation, or control transfers.

use std::collections::{BTreeMap, BTreeSet};

use crate::control_flow::structure::Node;
use crate::model::ir::{Assignment, Expr, Place};

pub const MAX_ITEMS: usize = 65_536;
pub const MAX_NODE_DEPTH: usize = 64;
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_NAMES: usize = 4_096;
pub const MAX_NAME_BYTES: usize = 256;
pub const MAX_METADATA_BYTES: usize = 262_144;
pub const MAX_WORK: usize = 262_144;

type Point = (u64, usize);

#[derive(Debug, Default)]
pub struct DeclarationPlan {
    sites: BTreeMap<String, Point>,
}

impl DeclarationPlan {
    /// `names` is the final C storage-name mapping; aliases share a name.
    /// `eligible` contains local names only, excluding every parameter name.
    /// A declaration must be safe in both layouts when `alternate` is present.
    /// Any resource failure discards the whole plan. No AST clone or equality
    /// comparison occurs, and input register IDs never index an allocation.
    pub fn build(
        nodes: Option<&[Node]>,
        alternate: Option<&[Node]>,
        names: &BTreeMap<usize, String>,
        read: &BTreeSet<usize>,
        eligible: &BTreeSet<String>,
    ) -> Self {
        let Some(nodes) = nodes else {
            return Self::default();
        };
        let mut budget = Budget::default();
        let result = (|| {
            metadata(names, read, eligible, &mut budget)?;
            let mut sites = candidates(nodes, names, read, eligible, &mut budget)?;
            if let Some(alternate) = alternate {
                let other = candidates(alternate, names, read, eligible, &mut budget)?;
                sites.retain(|name, point| other.get(name) == Some(point));
            }
            Some(
                sites
                    .into_iter()
                    .map(|(name, point)| (name.to_owned(), point))
                    .collect(),
            )
        })();
        Self {
            sites: result.unwrap_or_default(),
        }
    }

    /// Whether the prolog declaration for this local may be omitted.
    pub fn inline(&self, name: &str) -> bool {
        self.sites.contains_key(name)
    }

    /// Whether this exact assignment is the declaration/initialization site.
    pub fn at(&self, point: Point, name: &str) -> bool {
        self.sites.get(name) == Some(&point)
    }
}

#[derive(Default)]
struct Budget {
    items: usize,
    work: usize,
}
impl Budget {
    fn work(&mut self) -> Option<()> {
        self.work = self.work.checked_add(1)?;
        (self.work <= MAX_WORK).then_some(())
    }
    fn item(&mut self) -> Option<()> {
        self.items = self.items.checked_add(1)?;
        if self.items > MAX_ITEMS {
            return None;
        }
        self.work()
    }
}

fn metadata(
    names: &BTreeMap<usize, String>,
    read: &BTreeSet<usize>,
    eligible: &BTreeSet<String>,
    budget: &mut Budget,
) -> Option<()> {
    if names.len() > MAX_NAMES || read.len() > MAX_NAMES || eligible.len() > MAX_NAMES {
        return None;
    }
    let mut bytes = 0usize;
    for name in names.values().chain(eligible) {
        budget.work()?;
        if name.len() > MAX_NAME_BYTES {
            return None;
        }
        bytes = bytes.checked_add(name.len())?;
        if bytes > MAX_METADATA_BYTES {
            return None;
        }
    }
    Some(())
}

enum Item<'a> {
    Node(&'a Node, usize),
    Assignment(&'a Assignment, Point),
    Expression(&'a Expr, usize),
}

fn push<'a>(pending: &mut Vec<Item<'a>>, budget: &mut Budget, item: Item<'a>) -> Option<()> {
    // Charge at enqueue time so wide sibling lists cannot bypass the bound.
    budget.item()?;
    pending.push(item);
    Some(())
}

fn unique_sites(nodes: &[Node], budget: &mut Budget) -> Option<BTreeMap<Point, bool>> {
    let mut pending = Vec::new();
    for node in nodes {
        push(&mut pending, budget, Item::Node(node, 1))?;
    }
    let mut unique = BTreeMap::new();
    while let Some(item) = pending.pop() {
        match item {
            Item::Node(node, depth) => {
                if depth > MAX_NODE_DEPTH {
                    return None;
                }
                match node {
                    Node::Step {
                        address,
                        assignments,
                    } => {
                        for (index, assignment) in assignments.iter().enumerate() {
                            push(
                                &mut pending,
                                budget,
                                Item::Assignment(assignment, (*address, index)),
                            )?;
                        }
                    }
                    Node::Evaluate(value) | Node::Return(value) => {
                        push(&mut pending, budget, Item::Expression(value, 1))?
                    }
                    Node::If {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        push(&mut pending, budget, Item::Expression(condition, 1))?;
                        for node in taken.iter().chain(not_taken) {
                            push(&mut pending, budget, Item::Node(node, depth + 1))?;
                        }
                    }
                    Node::Loop(body) => {
                        for node in body {
                            push(&mut pending, budget, Item::Node(node, depth + 1))?;
                        }
                    }
                    Node::Break
                    | Node::Continue
                    | Node::BreakOuter { .. }
                    | Node::ContinueOuter { .. } => {}
                }
            }
            Item::Assignment(assignment, point) => {
                unique
                    .entry(point)
                    .and_modify(|value| *value = false)
                    .or_insert(true);
                if let Place::Memory { address, .. } = &assignment.destination {
                    push(&mut pending, budget, Item::Expression(address, 1))?;
                }
                push(&mut pending, budget, Item::Expression(&assignment.value, 1))?;
            }
            Item::Expression(expression, depth) => {
                if depth > MAX_EXPRESSION_DEPTH {
                    return None;
                }
                match expression {
                    Expr::Const(_) | Expr::Register(_) => {}
                    Expr::Unary(_, value) => {
                        push(&mut pending, budget, Item::Expression(value, depth + 1))?
                    }
                    Expr::Load { address, .. } => {
                        push(&mut pending, budget, Item::Expression(address, depth + 1))?
                    }
                    Expr::Binary(_, left, right) => {
                        push(&mut pending, budget, Item::Expression(left, depth + 1))?;
                        push(&mut pending, budget, Item::Expression(right, depth + 1))?;
                    }
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        for expression in [&**condition, &**taken, &**not_taken] {
                            push(
                                &mut pending,
                                budget,
                                Item::Expression(expression, depth + 1),
                            )?;
                        }
                    }
                }
            }
        }
    }
    Some(unique)
}

fn reads<'a>(
    expression: &Expr,
    names: &'a BTreeMap<usize, String>,
    seen: &mut BTreeSet<&'a str>,
    budget: &mut Budget,
) -> Option<usize> {
    let mut pending = vec![expression];
    let mut loads = 0usize;
    while let Some(expression) = pending.pop() {
        budget.work()?;
        match expression {
            Expr::Const(_) => {}
            Expr::Unary(_, value) => pending.push(value),
            Expr::Register(reg) => {
                if let Some(name) = names.get(&reg.0) {
                    seen.insert(name.as_str());
                }
            }
            Expr::Load { address, .. } => {
                loads = loads.checked_add(1)?;
                pending.push(address);
            }
            Expr::Binary(_, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(condition);
                pending.push(taken);
                pending.push(not_taken);
            }
        }
    }
    Some(loads)
}

fn candidates<'a>(
    nodes: &[Node],
    names: &'a BTreeMap<usize, String>,
    read: &BTreeSet<usize>,
    eligible: &BTreeSet<String>,
    budget: &mut Budget,
) -> Option<BTreeMap<&'a str, Point>> {
    let unique = unique_sites(nodes, budget)?;
    let mut seen_reads = BTreeSet::new();
    let mut seen_writes = BTreeSet::new();
    let mut sites = BTreeMap::new();
    for node in nodes {
        let Node::Step {
            address,
            assignments,
        } = node
        else {
            break;
        };
        for (index, assignment) in assignments.iter().enumerate() {
            budget.work()?;
            if let Place::Memory { address, .. } = &assignment.destination {
                reads(address, names, &mut seen_reads, budget)?;
            }
            let loads = reads(&assignment.value, names, &mut seen_reads, budget)?;
            if let Place::Register(reg) = assignment.destination
                && let Some(name) = names.get(&reg.0).map(String::as_str)
                && seen_writes.insert(name)
                && read.contains(&reg.0)
                && eligible.contains(name)
                && !seen_reads.contains(name)
                && loads <= 1
                && unique.get(&(*address, index)) == Some(&true)
            {
                sites.insert(name, (*address, index));
            }
        }
    }
    Some(sites)
}

#[cfg(test)]
mod tests;
