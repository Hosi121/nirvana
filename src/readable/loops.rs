//! Project actual C storage for pure-region validation, replacing only the
//! accepted region in the original tree. Memory view points stay untouched.
use std::collections::BTreeMap;

use crate::finite_region::FiniteEvidence;
use crate::ir::{Assignment, Expr, Place, Reg};
use crate::structure::Node;

use super::{LocalValue, Printer};

pub(super) struct BodyRecovery {
    pub nodes: Vec<Node>,
    pub evidence: RegionEvidence,
}

pub(super) enum RegionEvidence {
    Finite(FiniteEvidence),
    Affine(crate::affine_region::AffineEvidence),
}

pub(super) fn recover(
    printer: &Printer,
    nodes: &[Node],
    locals: &[LocalValue],
) -> Option<BodyRecovery> {
    if printer.names.len() > 4096 || locals.len() > 4096 {
        return None;
    }
    let mut names = BTreeMap::new();
    let mut aliases = BTreeMap::new();
    for (&reg, name) in &printer.names {
        let representative = *names.entry(name).or_insert(Reg(reg));
        aliases.insert(reg, representative);
    }
    let roles: Vec<_> = locals
        .iter()
        .filter_map(|local| Some((*aliases.get(&local.register.0)?, local.role?)))
        .collect();
    let widths: Vec<_> = locals
        .iter()
        .map(|local| Some((*aliases.get(&local.register.0)?, local.width)))
        .collect::<Option<_>>()?;
    let canonical = Project {
        aliases,
        printer,
        budget: 32_768,
    }
    .nodes(nodes, 0)?;
    if let Some(recovered) = crate::loop_recover::recover(&canonical, &roles, &widths) {
        let (nodes, evidence) = restore(nodes, &recovered);
        return Some(BodyRecovery {
            nodes,
            evidence: RegionEvidence::Finite(evidence),
        });
    }
    let recovered = crate::loop_recover::recover_affine(&canonical, &roles, &widths)?;
    let (nodes, evidence) = restore(nodes, &recovered);
    Some(BodyRecovery {
        nodes,
        evidence: RegionEvidence::Affine(evidence),
    })
}

fn restore<E: Clone>(
    nodes: &[Node],
    recovered: &crate::loop_recover::Recovery<E>,
) -> (Vec<Node>, E) {
    let region = recovered.region();
    let mut result = Vec::with_capacity(nodes.len() + recovered.replacement().len());
    // Projection inspected every original node/expression before these clones.
    // Only the replacement is canonicalized; original view operands/points are
    // retained throughout the prefix and suffix.
    result.extend_from_slice(&nodes[..region.start]);
    result.extend_from_slice(recovered.replacement());
    result.extend_from_slice(&nodes[region.end..]);
    (result, recovered.evidence().clone())
}

struct Project<'a> {
    aliases: BTreeMap<usize, Reg>,
    printer: &'a Printer,
    budget: usize,
}

impl Project<'_> {
    fn spend(&mut self, depth: usize) -> Option<()> {
        if depth > 64 {
            return None;
        }
        self.budget = self.budget.checked_sub(1)?;
        Some(())
    }

    fn reg(&self, reg: Reg) -> Reg {
        self.aliases.get(&reg.0).copied().unwrap_or(reg)
    }

    fn expression(&mut self, expr: &Expr, depth: usize) -> Option<(Expr, bool)> {
        self.spend(depth)?;
        Some(match expr {
            Expr::Const(value) => (Expr::Const(*value), false),
            Expr::Register(reg) => (Expr::Register(self.reg(*reg)), false),
            Expr::Binary(op, a, b) => {
                let (a, a_load) = self.expression(a, depth + 1)?;
                let (b, b_load) = self.expression(b, depth + 1)?;
                (Expr::binary(*op, a, b), a_load || b_load)
            }
            Expr::Load { address, width } => {
                let (address, _) = self.expression(address, depth + 1)?;
                (Expr::load(address, *width), true)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let (condition, c_load) = self.expression(condition, depth + 1)?;
                let (taken, t_load) = self.expression(taken, depth + 1)?;
                let (not_taken, n_load) = self.expression(not_taken, depth + 1)?;
                (
                    Expr::select(condition, taken, not_taken),
                    c_load || t_load || n_load,
                )
            }
        })
    }

    fn nodes(&mut self, nodes: &[Node], depth: usize) -> Option<Vec<Node>> {
        let mut result = Vec::new();
        for node in nodes {
            self.spend(depth)?;
            result.push(match node {
                Node::Step {
                    address,
                    assignments,
                } => {
                    let mut kept = Vec::new();
                    for assignment in assignments {
                        self.spend(depth)?;
                        let (value, loads) = self.expression(&assignment.value, depth + 1)?;
                        let destination = match &assignment.destination {
                            Place::Register(reg) => {
                                if !self.printer.read.contains(&reg.0) && !loads {
                                    continue;
                                }
                                Place::Register(self.reg(*reg))
                            }
                            Place::Memory { address, width } => Place::Memory {
                                address: self.expression(address, depth + 1)?.0,
                                width: *width,
                            },
                        };
                        kept.push(Assignment { destination, value });
                    }
                    Node::Step {
                        address: *address,
                        assignments: kept,
                    }
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => Node::If {
                    condition: self.expression(condition, depth + 1)?.0,
                    taken: self.nodes(taken, depth + 1)?,
                    not_taken: self.nodes(not_taken, depth + 1)?,
                },
                Node::Loop(body) => Node::Loop(self.nodes(body, depth + 1)?),
                Node::Evaluate(expr) => Node::Evaluate(self.expression(expr, depth + 1)?.0),
                Node::Return(expr) => Node::Return(self.expression(expr, depth + 1)?.0),
                Node::Break | Node::Continue => node.clone(),
                Node::BreakOuter { levels } => Node::BreakOuter { levels: *levels },
                Node::ContinueOuter { levels } => Node::ContinueOuter { levels: *levels },
            });
        }
        Some(result)
    }
}
