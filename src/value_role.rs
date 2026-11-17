//! Bounded syntax evidence for naming final C storage slots.
//!
//! Roles describe uses, not original names, source types, monotonicity, or a
//! proof of loop termination. This module never changes or evaluates the AST.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BinaryOp, Expr, Place, Reg};
use crate::structure::Node;

const MAX_DEPTH: usize = 128;
const MAX_NODES: usize = 32_768;
const MAX_SLOTS: usize = 4096;
const MAX_WORK: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueRole {
    Counter,
    Accumulator,
    Limit,
    Address,
}

impl ValueRole {
    pub const fn stem(self) -> &'static str {
        match self {
            Self::Counter => "counter",
            Self::Accumulator => "accumulator",
            Self::Limit => "limit",
            Self::Address => "address",
        }
    }
}

/// Infer roles for the supplied final storage groups. `None` excludes a
/// register; aliases sharing a slot are treated as the same storage location.
/// Contradictory evidence is permanently suppressed. Any resource failure
/// discards all results, rather than returning a partially named function.
pub fn infer(nodes: &[Node], slot: impl Fn(Reg) -> Option<usize>) -> BTreeMap<usize, ValueRole> {
    let mut remaining = MAX_NODES;
    if validate_nodes(nodes, 0, &mut remaining).is_none() {
        return BTreeMap::new();
    }
    let mut analysis = Analysis {
        slot: &slot,
        roles: BTreeMap::new(),
        work: MAX_WORK,
    };
    if analysis.visit(nodes).is_none() {
        return BTreeMap::new();
    }
    analysis
        .roles
        .into_iter()
        .filter_map(|(slot, role)| Some((slot, role?)))
        .collect()
}

fn spend(remaining: &mut usize, amount: usize) -> Option<()> {
    *remaining = remaining.checked_sub(amount)?;
    Some(())
}

fn validate_expr(expr: &Expr, depth: usize, remaining: &mut usize) -> Option<()> {
    if depth > MAX_DEPTH {
        return None;
    }
    spend(remaining, 1)?;
    match expr {
        Expr::Const(_) | Expr::Register(_) => {}
        Expr::Binary(_, a, b) => {
            validate_expr(a, depth + 1, remaining)?;
            validate_expr(b, depth + 1, remaining)?;
        }
        Expr::Load { address, .. } => validate_expr(address, depth + 1, remaining)?,
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            validate_expr(condition, depth + 1, remaining)?;
            validate_expr(taken, depth + 1, remaining)?;
            validate_expr(not_taken, depth + 1, remaining)?;
        }
    }
    Some(())
}

fn validate_nodes(nodes: &[Node], depth: usize, remaining: &mut usize) -> Option<()> {
    if depth > MAX_DEPTH {
        return None;
    }
    for node in nodes {
        spend(remaining, 1)?;
        match node {
            Node::Step { assignments, .. } => {
                for assignment in assignments {
                    spend(remaining, 1)?;
                    if let Place::Memory { address, .. } = &assignment.destination {
                        validate_expr(address, depth + 1, remaining)?;
                    }
                    validate_expr(&assignment.value, depth + 1, remaining)?;
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                validate_expr(condition, depth + 1, remaining)?;
                validate_nodes(taken, depth + 1, remaining)?;
                validate_nodes(not_taken, depth + 1, remaining)?;
            }
            Node::Loop(body) => validate_nodes(body, depth + 1, remaining)?,
            Node::Evaluate(expr) | Node::Return(expr) => validate_expr(expr, depth + 1, remaining)?,
            _ => {}
        }
    }
    Some(())
}

#[derive(Clone, Copy)]
struct Writes {
    affine: bool,
    rooted: bool,
    nested: bool,
}

struct Analysis<'a, F> {
    slot: &'a F,
    roles: BTreeMap<usize, Option<ValueRole>>,
    work: usize,
}

impl<F: Fn(Reg) -> Option<usize>> Analysis<'_, F> {
    fn bare(&self, expr: &Expr) -> Option<usize> {
        let Expr::Register(reg) = expr else {
            return None;
        };
        (self.slot)(*reg)
    }

    fn mark(&mut self, slot: usize, role: ValueRole) -> Option<()> {
        spend(&mut self.work, 1)?;
        self.roles
            .entry(slot)
            .and_modify(|old| {
                if *old != Some(role) {
                    *old = None;
                }
            })
            .or_insert(Some(role));
        (self.roles.len() <= MAX_SLOTS).then_some(())
    }

    fn expression(&mut self, expr: &Expr) -> Option<()> {
        spend(&mut self.work, 1)?;
        match expr {
            Expr::Load { address, .. } => {
                if let Some(slot) = self.bare(address) {
                    self.mark(slot, ValueRole::Address)?;
                }
                self.expression(address)?;
            }
            Expr::Binary(_, a, b) => {
                self.expression(a)?;
                self.expression(b)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.expression(condition)?;
                self.expression(taken)?;
                self.expression(not_taken)?;
            }
            _ => {}
        }
        Some(())
    }

    fn visit(&mut self, nodes: &[Node]) -> Option<()> {
        for node in nodes {
            spend(&mut self.work, 1)?;
            match node {
                Node::Step { assignments, .. } => {
                    for assignment in assignments {
                        if let Place::Memory { address, .. } = &assignment.destination {
                            if let Some(slot) = self.bare(address) {
                                self.mark(slot, ValueRole::Address)?;
                            }
                            self.expression(address)?;
                        }
                        self.expression(&assignment.value)?;
                    }
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    self.expression(condition)?;
                    self.visit(taken)?;
                    self.visit(not_taken)?;
                }
                Node::Loop(body) => {
                    self.loop_roles(body)?;
                    self.visit(body)?;
                }
                Node::Evaluate(expr) | Node::Return(expr) => self.expression(expr)?,
                _ => {}
            }
        }
        Some(())
    }

    // Only additive/subtractive constant chains around one self slot count as
    // affine. All arithmetic is modular; zero net updates are not evidence.
    fn delta(&self, expr: &Expr, destination: usize) -> Option<u64> {
        if self.bare(expr) == Some(destination) {
            return Some(0);
        }
        match expr {
            Expr::Binary(BinaryOp::Add, a, b) => match (&**a, &**b) {
                (Expr::Const(n), other) | (other, Expr::Const(n)) => {
                    Some(self.delta(other, destination)?.wrapping_add(*n))
                }
                _ => None,
            },
            Expr::Binary(BinaryOp::Sub, a, b) => {
                let Expr::Const(n) = &**b else {
                    return None;
                };
                Some(self.delta(a, destination)?.wrapping_sub(*n))
            }
            _ => None,
        }
    }

    fn rooted(&self, expr: &Expr, destination: usize) -> bool {
        if self.bare(expr) == Some(destination) {
            return true;
        }
        match expr {
            Expr::Binary(
                BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor,
                a,
                b,
            ) => self.rooted(a, destination) || self.rooted(b, destination),
            Expr::Binary(BinaryOp::Sub | BinaryOp::Shl | BinaryOp::Shr, a, _) => {
                self.rooted(a, destination)
            }
            // Reading the slot as an address or only in a Select does not
            // establish a self-rooted arithmetic update.
            _ => false,
        }
    }

    fn writes(
        &mut self,
        nodes: &[Node],
        nested: bool,
        result: &mut BTreeMap<usize, Writes>,
    ) -> Option<()> {
        for node in nodes {
            spend(&mut self.work, 1)?;
            match node {
                Node::Step { assignments, .. } => {
                    for assignment in assignments {
                        spend(&mut self.work, 1)?;
                        let Place::Register(reg) = assignment.destination else {
                            continue;
                        };
                        let Some(slot) = (self.slot)(reg) else {
                            continue;
                        };
                        let delta = self.delta(&assignment.value, slot);
                        if delta == Some(0) {
                            continue;
                        }
                        let affine = delta.is_some();
                        let rooted = self.rooted(&assignment.value, slot);
                        result
                            .entry(slot)
                            .and_modify(|old| {
                                old.affine &= affine;
                                old.rooted &= rooted;
                                old.nested |= nested;
                            })
                            .or_insert(Writes {
                                affine,
                                rooted,
                                nested,
                            });
                        if result.len() > MAX_SLOTS {
                            return None;
                        }
                    }
                }
                Node::If {
                    taken, not_taken, ..
                } => {
                    self.writes(taken, nested, result)?;
                    self.writes(not_taken, nested, result)?;
                }
                Node::Loop(body) => self.writes(body, true, result)?,
                _ => {}
            }
        }
        Some(())
    }

    fn loop_roles(&mut self, body: &[Node]) -> Option<()> {
        let mut writes = BTreeMap::new();
        self.writes(body, false, &mut writes)?;
        let mut counters = BTreeSet::new();
        self.guards(body, &writes, &mut BTreeMap::new(), &mut counters)?;
        for (&slot, write) in &writes {
            if counters.contains(&slot) {
                self.mark(slot, ValueRole::Counter)?;
            } else if write.rooted && !write.nested {
                self.mark(slot, ValueRole::Accumulator)?;
            }
        }
        Some(())
    }

    fn guards<'a>(
        &mut self,
        nodes: &'a [Node],
        writes: &BTreeMap<usize, Writes>,
        definitions: &mut BTreeMap<usize, &'a Expr>,
        counters: &mut BTreeSet<usize>,
    ) -> Option<()> {
        for node in nodes {
            spend(&mut self.work, 1)?;
            match node {
                Node::Step { assignments, .. } => {
                    for assignment in assignments {
                        if let Place::Register(reg) = assignment.destination
                            && let Some(slot) = (self.slot)(reg)
                        {
                            definitions.insert(slot, &assignment.value);
                            if definitions.len() > MAX_SLOTS {
                                return None;
                            }
                        }
                    }
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    if exits(taken) != exits(not_taken) {
                        self.predicate(
                            condition,
                            writes,
                            definitions,
                            counters,
                            &mut BTreeSet::new(),
                            0,
                        )?;
                    }
                    spend(&mut self.work, definitions.len().checked_mul(2)?)?;
                    self.guards(taken, writes, &mut definitions.clone(), counters)?;
                    self.guards(not_taken, writes, &mut definitions.clone(), counters)?;
                    // No path-sensitive definition merge is claimed.
                    definitions.clear();
                }
                Node::Loop(_) => definitions.clear(),
                _ => {}
            }
        }
        Some(())
    }

    fn predicate(
        &mut self,
        expr: &Expr,
        writes: &BTreeMap<usize, Writes>,
        definitions: &BTreeMap<usize, &Expr>,
        counters: &mut BTreeSet<usize>,
        visited: &mut BTreeSet<usize>,
        depth: usize,
    ) -> Option<()> {
        if depth > MAX_DEPTH {
            return None;
        }
        spend(&mut self.work, 1)?;
        let candidate = |slot| writes.get(&slot).is_some_and(|w| w.affine && !w.nested);
        if let Some(slot) = self.bare(expr) {
            if candidate(slot) {
                counters.insert(slot);
            } else if visited.insert(slot)
                && let Some(value) = definitions.get(&slot)
            {
                self.predicate(value, writes, definitions, counters, visited, depth + 1)?;
            }
            return Some(());
        }
        if let Expr::Binary(
            op @ (BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule),
            left,
            right,
        ) = expr
        {
            let a = self.bare(left);
            let b = self.bare(right);
            if a.is_some() && a == b {
                return Some(());
            }
            for (counter, partner) in [(a, b), (b, a)] {
                if let Some(counter) = counter
                    && candidate(counter)
                {
                    counters.insert(counter);
                    if let Some(limit) = partner
                        && !writes.contains_key(&limit)
                    {
                        self.mark(limit, ValueRole::Limit)?;
                    }
                }
            }
            // Follow a comparison/flag through truth tests, not memory or
            // arbitrary arithmetic used to compute an address or data value.
            if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                if matches!(&**right, Expr::Const(0 | 1)) {
                    self.predicate(left, writes, definitions, counters, visited, depth + 1)?;
                }
                if matches!(&**left, Expr::Const(0 | 1)) {
                    self.predicate(right, writes, definitions, counters, visited, depth + 1)?;
                }
            }
        }
        Some(())
    }
}

fn exits(nodes: &[Node]) -> bool {
    matches!(nodes.last(), Some(Node::Break | Node::Return(_)))
}
