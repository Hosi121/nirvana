//! Bounded candidates for undoing pure, finite compiler loop expansion.
//!
//! Roles only choose a proposal. Independent exhaustive finite-region validation
//! is the acceptance gate; unknown domains, memory, nontermination or exhausted
//! verification never authorize a rewrite. This is not a structure certificate
//! for the original CFG, nor a claim about arbitrary unbounded input values.

use std::collections::{BTreeMap, BTreeSet};

use crate::finite_region::{self, FiniteEvidence};
use crate::ir::{Assignment, BinaryOp, Expr, Place, Reg, Width};
use crate::structure::Node;
use crate::value_role::ValueRole;

const MAX_NODES: usize = 8192;
const MAX_DEPTH: usize = 64;
const MAX_METADATA: usize = 4096;
const MAX_WINDOW: usize = 16;
const MAX_ATTEMPTS: usize = 16;

pub struct LoopRecovery {
    nodes: Vec<Node>,
    evidence: FiniteEvidence,
    region: std::ops::Range<usize>,
    replacement_len: usize,
}

impl LoopRecovery {
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    pub fn evidence(&self) -> &FiniteEvidence {
        &self.evidence
    }

    /// Original root sibling indices covered by the finite-region evidence.
    pub fn region(&self) -> std::ops::Range<usize> {
        self.region.clone()
    }

    /// Candidate nodes only. Consumers analyzing a canonical register view can
    /// splice these into their original tree, preserving untouched memory points.
    pub fn replacement(&self) -> &[Node] {
        &self.nodes[self.region.start..self.region.start + self.replacement_len]
    }
}

/// Replace at most one root-level pure region with a smaller ordinary summing
/// loop. Prefix and suffix nodes are preserved exactly. In particular this
/// search never treats a first iteration's facts as an enclosing loop invariant.
/// Every role register needs an explicit storage width; all recorded original
/// and candidate maxima must fit it, without implicit C narrowing assumptions.
pub fn recover(
    nodes: &[Node],
    roles: &[(Reg, ValueRole)],
    widths: &[(Reg, Width)],
) -> Option<LoopRecovery> {
    let registers = Roles::new(roles, widths)?;
    // Inspect the entire input, including untouched memory expressions and dead
    // suffixes, before any recursive cloning or candidate validation.
    let mut budget = Budget(MAX_NODES);
    let summaries = inspect_nodes(nodes, 0, false, &registers, &mut budget)?;
    let inputs = [registers.counter, registers.accumulator, registers.limit];
    let observed = [registers.counter, registers.accumulator];
    let mut attempts = 0;
    for start in 0..nodes.len() {
        let summary = summaries[start];
        if !summary.safe
            || !matches!(nodes[start], Node::Loop(_) | Node::If { .. })
            || summary.loops == 0
        {
            continue;
        }
        let mut cost = 0;
        let mut loops = 0;
        let mut first_point = None;
        for end in start..nodes.len().min(start + MAX_WINDOW) {
            let info = summaries[end];
            if !info.safe {
                break;
            }
            cost += info.cost;
            loops += info.loops;
            first_point = first_point.or(info.first_point);
            if loops < 2 {
                continue;
            }
            let candidate = registers.ordinary_loop(first_point.unwrap_or(0));
            let candidate_cost =
                inspect_nodes(&candidate, 0, false, &registers, &mut Budget(MAX_NODES))?
                    .iter()
                    .map(|info| info.cost)
                    .sum::<usize>();
            if cost <= candidate_cost {
                continue;
            }
            if attempts == MAX_ATTEMPTS {
                return None;
            }
            attempts += 1;
            let Ok(evidence) = finite_region::validate(
                &nodes[..start],
                &nodes[start..=end],
                &candidate,
                &inputs,
                &observed,
            ) else {
                continue;
            };
            if !registers.fits(&evidence) {
                continue;
            }
            let mut result = Vec::with_capacity(nodes.len() - (end - start + 1) + 1);
            result.extend_from_slice(&nodes[..start]);
            let replacement_len = candidate.len();
            result.extend(candidate);
            result.extend_from_slice(&nodes[end + 1..]);
            return Some(LoopRecovery {
                nodes: result,
                evidence,
                region: start..end + 1,
                replacement_len,
            });
        }
    }
    None
}

struct Roles {
    counter: Reg,
    accumulator: Reg,
    limit: Reg,
    widths: [Width; 3],
}
impl Roles {
    fn new(roles: &[(Reg, ValueRole)], widths: &[(Reg, Width)]) -> Option<Self> {
        if roles.len() > MAX_METADATA || widths.len() > MAX_METADATA {
            return None;
        }
        let (mut counter, mut accumulator, mut limit) = (None, None, None);
        let mut seen = BTreeSet::new();
        for &(reg, role) in roles {
            if !seen.insert(reg.0) {
                return None;
            }
            let target = match role {
                ValueRole::Counter => &mut counter,
                ValueRole::Accumulator => &mut accumulator,
                ValueRole::Limit => &mut limit,
                ValueRole::Address => continue,
            };
            if target.replace(reg).is_some() {
                return None;
            }
        }
        let (counter, accumulator, limit) = (counter?, accumulator?, limit?);
        let mut known_widths = BTreeMap::new();
        for &(reg, width) in widths {
            if known_widths.insert(reg.0, width).is_some() {
                return None;
            }
        }
        Some(Self {
            counter,
            accumulator,
            limit,
            widths: [
                *known_widths.get(&counter.0)?,
                *known_widths.get(&accumulator.0)?,
                *known_widths.get(&limit.0)?,
            ],
        })
    }
    fn fits(&self, evidence: &FiniteEvidence) -> bool {
        let mut seen = BTreeSet::new();
        let registers = [self.counter, self.accumulator, self.limit];
        evidence.cases > 0
            && evidence.maxima.iter().all(|&(reg, maximum)| {
                let Some(index) = registers.iter().position(|candidate| *candidate == reg) else {
                    return false;
                };
                seen.insert(reg.0) && maximum <= self.widths[index].mask()
            })
            && seen.len() == registers.len()
    }
    fn ordinary_loop(&self, address: u64) -> Vec<Node> {
        let r = Expr::Register;
        vec![Node::Loop(vec![
            Node::If {
                condition: Expr::binary(BinaryOp::Ult, r(self.counter), r(self.limit)),
                taken: vec![],
                not_taken: vec![Node::Break],
            },
            Node::Step {
                address,
                assignments: vec![
                    Assignment {
                        destination: self.accumulator.into(),
                        value: Expr::binary(BinaryOp::Add, r(self.accumulator), r(self.counter)),
                    },
                    Assignment {
                        destination: self.counter.into(),
                        value: Expr::binary(BinaryOp::Add, r(self.counter), Expr::Const(1)),
                    },
                ],
            },
        ])]
    }
}

#[derive(Clone, Copy)]
struct Summary {
    cost: usize,
    loops: usize,
    first_point: Option<u64>,
    safe: bool,
}
impl Summary {
    fn new() -> Self {
        Self {
            cost: 1,
            loops: 0,
            first_point: None,
            safe: true,
        }
    }
    fn children(&mut self, children: Vec<Self>) {
        for child in children {
            self.cost += child.cost;
            self.loops += child.loops;
            self.first_point = self.first_point.or(child.first_point);
            self.safe &= child.safe;
        }
    }
    fn expression(&mut self, value: &Expr, depth: usize, budget: &mut Budget) -> Option<()> {
        let (cost, pure) = inspect_expression(value, depth, budget)?;
        self.cost += cost;
        self.safe &= pure;
        Some(())
    }
}
fn inspect_nodes(
    nodes: &[Node],
    depth: usize,
    inside_loop: bool,
    roles: &Roles,
    budget: &mut Budget,
) -> Option<Vec<Summary>> {
    if depth > MAX_DEPTH {
        return None;
    }
    let mut result = Vec::new();
    for node in nodes {
        budget.spend()?;
        let mut summary = Summary::new();
        match node {
            Node::Step {
                address,
                assignments,
            } => {
                summary.first_point = Some(*address);
                for assignment in assignments {
                    budget.spend()?;
                    summary.cost += 1;
                    match &assignment.destination {
                        Place::Register(reg) => {
                            budget.spend()?;
                            summary.cost += 1;
                            summary.safe &= *reg == roles.counter || *reg == roles.accumulator;
                        }
                        Place::Memory { address, .. } => {
                            summary.expression(address, depth + 1, budget)?;
                            summary.safe = false;
                        }
                    }
                    summary.expression(&assignment.value, depth + 1, budget)?;
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                summary.expression(condition, depth + 1, budget)?;
                summary.children(inspect_nodes(taken, depth + 1, inside_loop, roles, budget)?);
                summary.children(inspect_nodes(
                    not_taken,
                    depth + 1,
                    inside_loop,
                    roles,
                    budget,
                )?);
            }
            Node::Loop(body) => {
                summary.loops = 1;
                summary.children(inspect_nodes(body, depth + 1, true, roles, budget)?);
            }
            Node::Evaluate(value) => summary.expression(value, depth + 1, budget)?,
            Node::Return(value) => {
                summary.expression(value, depth + 1, budget)?;
                summary.safe = false;
            }
            Node::Break | Node::Continue => summary.safe = inside_loop,
            Node::BreakOuter { .. } | Node::ContinueOuter { .. } => summary.safe = false,
        }
        result.push(summary);
    }
    Some(result)
}
fn inspect_expression(value: &Expr, depth: usize, budget: &mut Budget) -> Option<(usize, bool)> {
    if depth > MAX_DEPTH {
        return None;
    }
    budget.spend()?;
    let mut cost = 1;
    let mut pure = true;
    let mut child = |value, depth| {
        let (nodes, safe) = inspect_expression(value, depth, budget)?;
        cost += nodes;
        pure &= safe;
        Some(())
    };
    match value {
        Expr::Binary(_, a, b) => {
            child(a, depth + 1)?;
            child(b, depth + 1)?;
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            child(condition, depth + 1)?;
            child(taken, depth + 1)?;
            child(not_taken, depth + 1)?;
        }
        Expr::Load { address, .. } => {
            child(address, depth + 1)?;
            pure = false;
        }
        Expr::Const(_) | Expr::Register(_) => {}
    }
    Some((cost, pure))
}
struct Budget(usize);
impl Budget {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
}
