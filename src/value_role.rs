//! Bounded syntax evidence for naming final C storage slots.
//!
//! Roles describe uses, not original names, source types, monotonicity, or a
//! proof of loop termination. This module never changes or evaluates the AST.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BinaryOp, Expr, Place, Reg};
use crate::structure::Node;

mod arithmetic;

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
    Quotient,
}

impl ValueRole {
    pub const fn stem(self) -> &'static str {
        match self {
            Self::Counter => "counter",
            Self::Accumulator => "accumulator",
            Self::Limit => "limit",
            Self::Address => "address",
            Self::Quotient => "quotient",
        }
    }
}

/// Infer roles for the supplied final storage groups. `None` excludes a
/// register; aliases sharing a slot are treated as the same storage location.
/// Contradictory evidence is permanently suppressed. Any resource failure
/// discards all results, rather than returning a partially named function.
pub fn infer(nodes: &[Node], slot: impl Fn(Reg) -> Option<usize>) -> BTreeMap<usize, ValueRole> {
    infer_base(nodes, &slot)
        .map(|base| base.roles)
        .unwrap_or_default()
}

/// Add certified arithmetic hints for C names and copy-compatibility filters.
/// The callback includes named local storage and excludes input parameters.
/// `infer` supplies canonical identity/loop and projected stack-web roles.
/// Storage sharing uses independent allocation validation; these hints constrain
/// copy proposals. Existing roles and their contradictions take priority.
/// Exhausting the optional arithmetic pass leaves all original roles intact.
pub fn infer_with_arithmetic(
    nodes: &[Node],
    slot: impl Fn(Reg) -> Option<usize>,
) -> BTreeMap<usize, ValueRole> {
    let Some(mut base) = infer_base(nodes, &slot) else {
        return BTreeMap::new();
    };
    if let Some(quotients) = arithmetic::quotients(nodes, &slot, &base.blocked) {
        for slot in quotients {
            base.roles.entry(slot).or_insert(ValueRole::Quotient);
        }
    }
    base.roles
}

struct BaseRoles {
    roles: BTreeMap<usize, ValueRole>,
    blocked: BTreeSet<usize>,
}

fn infer_base(nodes: &[Node], slot: &impl Fn(Reg) -> Option<usize>) -> Option<BaseRoles> {
    let mut remaining = MAX_NODES;
    validate_nodes(nodes, 0, &mut remaining)?;
    let mut analysis = Analysis {
        slot,
        roles: BTreeMap::new(),
        work: MAX_WORK,
    };
    analysis.visit(nodes)?;
    let blocked = analysis.roles.keys().copied().collect();
    // A storage group can be reused for an unrelated scalar lifetime. Address
    // dereference evidence alone must not name that entire group "address".
    if analysis
        .roles
        .values()
        .any(|role| *role == Some(ValueRole::Address))
    {
        let mut data = BTreeSet::new();
        analysis.data_uses(nodes, &mut data)?;
        analysis
            .roles
            .retain(|slot, role| *role != Some(ValueRole::Address) || !data.contains(slot));
    }
    Some(BaseRoles {
        roles: analysis
            .roles
            .into_iter()
            .filter_map(|(slot, role)| Some((slot, role?)))
            .collect(),
        blocked,
    })
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

// Normal completion outcomes relative to the loop currently being analyzed.
// Faulting expressions are untouched; Step/Evaluate fall through if successful.
#[derive(Clone, Copy, Eq, PartialEq)]
struct Flow(u8);
impl Flow {
    const FALL: Self = Self(1);
    const CONTINUE: Self = Self(2);
    const EXIT: Self = Self(4);
    const OTHER: Self = Self(8);

    fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    fn falls_through(self) -> bool {
        self.0 & Self::FALL.0 != 0
    }
    fn then(self, after: Self) -> Self {
        Self((self.0 & !Self::FALL.0) | if self.falls_through() { after.0 } else { 0 })
    }
    fn controls(self, other: Self) -> bool {
        // An explicit exit remains a controlling guard even if another later
        // guard can also exit. Unknown/outer flow cannot establish this fact.
        // Continue versus a mixed Continue/Exit path is still insufficient.
        let can_continue = |flow: Self| {
            flow.0 & Self::CONTINUE.0 != 0 && flow.0 & !(Self::CONTINUE.0 | Self::EXIT.0) == 0
        };
        (self == Self::EXIT && can_continue(other)) || (other == Self::EXIT && can_continue(self))
    }
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

    // A single base wrapped in byte constants remains address evidence. Do
    // not extract either operand from base+index, scales, Select, or c-base:
    // address syntax alone cannot distinguish a base from an integer index.
    fn address_use(&mut self, mut address: &Expr) -> Option<()> {
        loop {
            spend(&mut self.work, 1)?;
            match address {
                Expr::Register(reg) => {
                    if let Some(slot) = (self.slot)(*reg) {
                        self.mark(slot, ValueRole::Address)?;
                    }
                    return Some(());
                }
                Expr::Binary(BinaryOp::Add, a, b) => match (&**a, &**b) {
                    (Expr::Const(_), base) | (base, Expr::Const(_)) => address = base,
                    _ => return Some(()),
                },
                Expr::Binary(BinaryOp::Sub, base, offset)
                    if matches!(&**offset, Expr::Const(_)) =>
                {
                    address = base;
                }
                _ => return Some(()),
            }
        }
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

    // Registers beneath a load address are address uses, even for nested or
    // lazy loads. The load's resulting value is not the address register.
    fn data_expression(&mut self, expr: &Expr, data: &mut BTreeSet<usize>) -> Option<()> {
        spend(&mut self.work, 1)?;
        match expr {
            Expr::Register(reg) => {
                if let Some(slot) = (self.slot)(*reg)
                    && self.roles.get(&slot) == Some(&Some(ValueRole::Address))
                {
                    data.insert(slot);
                }
            }
            Expr::Binary(_, a, b) => {
                self.data_expression(a, data)?;
                self.data_expression(b, data)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.data_expression(condition, data)?;
                self.data_expression(taken, data)?;
                self.data_expression(not_taken, data)?;
            }
            Expr::Const(_) | Expr::Load { .. } => {}
        }
        Some(())
    }

    fn data_uses(&mut self, nodes: &[Node], data: &mut BTreeSet<usize>) -> Option<()> {
        for node in nodes {
            spend(&mut self.work, 1)?;
            match node {
                Node::Step { assignments, .. } => {
                    for assignment in assignments {
                        // Only same-slot copies and constant affine pointer
                        // updates are exempt from the conservative data-use test.
                        if let Place::Register(reg) = assignment.destination
                            && let Some(slot) = (self.slot)(reg)
                            && self.delta(&assignment.value, slot).is_some()
                        {
                            continue;
                        }
                        self.data_expression(&assignment.value, data)?;
                        // A store destination is entirely an address context.
                    }
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    self.data_expression(condition, data)?;
                    self.data_uses(taken, data)?;
                    self.data_uses(not_taken, data)?;
                }
                Node::Loop(body) => self.data_uses(body, data)?,
                Node::Evaluate(expr) | Node::Return(expr) => self.data_expression(expr, data)?,
                _ => {}
            }
        }
        Some(())
    }

    fn expression(&mut self, expr: &Expr) -> Option<()> {
        spend(&mut self.work, 1)?;
        match expr {
            Expr::Load { address, .. } => {
                self.address_use(address)?;
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
                            self.address_use(address)?;
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

    // Only direct, flat producer/copyback pairs are extra naming evidence.
    // Every write of a promoted slot must still be an affine self update or
    // such a pair. Branch/inner-loop writes permanently exclude that slot.
    fn copyback_counters(
        &mut self,
        nodes: &[Node],
        writes: &mut BTreeMap<usize, Writes>,
    ) -> Option<()> {
        let mut producers = BTreeMap::<usize, (usize, u64)>::new();
        let mut candidates = BTreeSet::new();
        let mut excluded = BTreeSet::new();
        let mut reachable = true;
        for node in nodes {
            spend(&mut self.work, 1)?;
            if let Node::Step { assignments, .. } = node {
                for assignment in assignments {
                    spend(&mut self.work, 1)?;
                    let Place::Register(reg) = assignment.destination else {
                        continue;
                    };
                    let Some(slot) = (self.slot)(reg) else {
                        continue;
                    };
                    let direct = self.delta(&assignment.value, slot);
                    let copyback = self
                        .bare(&assignment.value)
                        .and_then(|source| producers.get(&source))
                        .is_some_and(|&(base, delta)| base == slot && delta != 0);
                    if !reachable || direct.is_none() && !copyback {
                        excluded.insert(slot);
                    }
                    if reachable && copyback {
                        candidates.insert(slot);
                    }
                    if candidates.len() > MAX_SLOTS || excluded.len() > MAX_SLOTS {
                        return None;
                    }
                    let origin = self.affine_origin(&assignment.value)?;
                    spend(&mut self.work, producers.len())?;
                    producers
                        .retain(|&destination, (base, _)| destination != slot && *base != slot);
                    if reachable
                        && let Some((base, delta)) = origin
                        && base != slot
                        && delta != 0
                    {
                        producers.insert(slot, (base, delta));
                        if producers.len() > MAX_SLOTS {
                            return None;
                        }
                    }
                }
            } else {
                if matches!(node, Node::If { .. } | Node::Loop(_)) {
                    let mut touched = BTreeMap::new();
                    self.writes(std::slice::from_ref(node), false, &mut touched)?;
                    spend(&mut self.work, touched.len())?;
                    excluded.extend(touched.into_keys());
                    producers.clear();
                }
                if !self.flow_node(node)?.falls_through() {
                    reachable = false;
                    producers.clear();
                }
            }
        }
        for slot in candidates.difference(&excluded) {
            spend(&mut self.work, 1)?;
            if let Some(write) = writes.get_mut(slot)
                && !write.nested
            {
                write.affine = true;
                write.rooted = true;
            }
        }
        Some(())
    }

    fn affine_origin(&mut self, value: &Expr) -> Option<Option<(usize, u64)>> {
        spend(&mut self.work, 1)?;
        if let Some(base) = self.bare(value) {
            return Some(Some((base, 0)));
        }
        let (base, offset, subtract) = match value {
            Expr::Binary(BinaryOp::Add, a, b) => match (&**a, &**b) {
                (Expr::Const(offset), base) | (base, Expr::Const(offset)) => (base, *offset, false),
                _ => return Some(None),
            },
            Expr::Binary(BinaryOp::Sub, base, offset) => {
                let Expr::Const(offset) = &**offset else {
                    return Some(None);
                };
                (&**base, *offset, true)
            }
            _ => return Some(None),
        };
        Some(self.affine_origin(base)?.map(|(base, delta)| {
            (
                base,
                if subtract {
                    delta.wrapping_sub(offset)
                } else {
                    delta.wrapping_add(offset)
                },
            )
        }))
    }

    fn loop_roles(&mut self, body: &[Node]) -> Option<()> {
        let mut writes = BTreeMap::new();
        self.writes(body, false, &mut writes)?;
        self.copyback_counters(body, &mut writes)?;
        let mut counters = BTreeSet::new();
        self.guards(
            body,
            &writes,
            &mut BTreeMap::new(),
            &mut counters,
            Flow::CONTINUE,
        )?;
        for (&slot, write) in &writes {
            if counters.contains(&slot) {
                self.mark(slot, ValueRole::Counter)?;
            } else if write.rooted && !write.nested {
                self.mark(slot, ValueRole::Accumulator)?;
            }
        }
        Some(())
    }

    fn invalidate_read_definitions(
        &mut self,
        definitions: &mut BTreeMap<usize, &Expr>,
        overwritten: usize,
    ) -> Option<()> {
        let mut stale = Vec::new();
        for (&destination, &value) in definitions.iter() {
            spend(&mut self.work, 1)?;
            // RHS syntax refers to the values at its original assignment,
            // not a snapshot we can reinterpret after a source slot changes.
            // Whole-AST validation already bounded size/depth; visit every
            // kind of raw register dependency, including lazy/load addresses.
            let mut pending = vec![value];
            while let Some(value) = pending.pop() {
                spend(&mut self.work, 1)?;
                match value {
                    Expr::Register(reg) if (self.slot)(*reg) == Some(overwritten) => {
                        stale.push(destination);
                        break;
                    }
                    Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
                    Expr::Load { address, .. } => pending.push(address),
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => pending.extend([&**condition, &**taken, &**not_taken]),
                    _ => {}
                }
            }
        }
        // Complete all fallible discovery/charging before changing the map.
        // A failure propagates to infer(), which discards every role result.
        spend(&mut self.work, stale.len())?;
        for destination in stale {
            definitions.remove(&destination);
        }
        Some(())
    }

    fn guards<'a>(
        &mut self,
        nodes: &'a [Node],
        writes: &BTreeMap<usize, Writes>,
        definitions: &mut BTreeMap<usize, &'a Expr>,
        counters: &mut BTreeSet<usize>,
        continuation: Flow,
    ) -> Option<()> {
        let flows = nodes
            .iter()
            .map(|node| self.flow_node(node))
            .collect::<Option<Vec<_>>>()?;
        let mut suffix = vec![continuation; nodes.len() + 1];
        for index in (0..nodes.len()).rev() {
            suffix[index] = flows[index].then(suffix[index + 1]);
        }
        for (index, node) in nodes.iter().enumerate() {
            spend(&mut self.work, 1)?;
            match node {
                Node::Step { assignments, .. } => {
                    for assignment in assignments {
                        if let Place::Register(reg) = assignment.destination
                            && let Some(slot) = (self.slot)(reg)
                        {
                            self.invalidate_read_definitions(definitions, slot)?;
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
                    let taken_flow = self.flow_nodes(taken)?.then(suffix[index + 1]);
                    let not_taken_flow = self.flow_nodes(not_taken)?.then(suffix[index + 1]);
                    if taken_flow.controls(not_taken_flow) {
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
                    self.guards(
                        taken,
                        writes,
                        &mut definitions.clone(),
                        counters,
                        suffix[index + 1],
                    )?;
                    self.guards(
                        not_taken,
                        writes,
                        &mut definitions.clone(),
                        counters,
                        suffix[index + 1],
                    )?;
                    // No path-sensitive definition merge is claimed.
                    definitions.clear();
                }
                Node::Loop(_) => definitions.clear(),
                _ => {}
            }
            // A transfer prevents later syntactic nodes from being evidence.
            if !flows[index].falls_through() {
                break;
            }
        }
        Some(())
    }

    fn flow_nodes(&mut self, nodes: &[Node]) -> Option<Flow> {
        let mut result = Flow::FALL;
        for node in nodes.iter().rev() {
            result = self.flow_node(node)?.then(result);
        }
        Some(result)
    }

    fn flow_node(&mut self, node: &Node) -> Option<Flow> {
        spend(&mut self.work, 1)?;
        Some(match node {
            Node::Step { .. } | Node::Evaluate(_) => Flow::FALL,
            Node::Continue => Flow::CONTINUE,
            Node::Break | Node::Return(_) => Flow::EXIT,
            Node::If {
                taken, not_taken, ..
            } => self.flow_nodes(taken)?.union(self.flow_nodes(not_taken)?),
            // Inner-loop transfers must not be mistaken for this loop's
            // transfers. Its completion is deliberately not proved here.
            Node::Loop(_) => Flow::OTHER.union(Flow::FALL),
            Node::BreakOuter { .. } | Node::ContinueOuter { .. } => Flow::OTHER,
        })
    }

    fn guard_counter(
        &mut self,
        slot: usize,
        writes: &BTreeMap<usize, Writes>,
        definitions: &BTreeMap<usize, &Expr>,
    ) -> Option<Option<usize>> {
        let candidate = |slot| writes.get(&slot).is_some_and(|w| w.affine && !w.nested);
        if candidate(slot) {
            return Some(Some(slot));
        }
        let mut found = None;
        for (&destination, value) in definitions {
            spend(&mut self.work, 1)?;
            if candidate(destination) && self.bare(value) == Some(slot) {
                if found.is_some() {
                    return Some(None);
                }
                found = Some(destination);
            }
        }
        Some(found)
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
        if let Some(slot) = self.bare(expr) {
            if let Some(counter) = self.guard_counter(slot, writes, definitions)? {
                counters.insert(counter);
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
            let resolved_a = if let Some(a) = a {
                self.guard_counter(a, writes, definitions)?
            } else {
                None
            };
            let resolved_b = if let Some(b) = b {
                self.guard_counter(b, writes, definitions)?
            } else {
                None
            };
            if resolved_a.is_some() && resolved_a == resolved_b {
                return Some(());
            }
            for (counter, partner) in [(resolved_a, b), (resolved_b, a)] {
                if let Some(counter) = counter {
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
