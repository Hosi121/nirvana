//! Independently check source access coverage and all-64 modular identities.
//!
//! The producer's affine maps are not replayed here. Supported source syntax
//! builds a scalar affine DAG; its zero and unit-vector evaluations uniquely
//! determine a polynomial over Z/(2^64). Source-discovered atoms, including
//! cancelled ones absent from the proposed form, supply the basis vectors.
use super::{AddressShape, MemoryAddresses, ModularAddress, Operand, PathEdge};
use crate::dataflow::ssa::{self, Definition, PointValues, Site, SsaFunction, ValueId};
use crate::model::ir::{AccessKind, BinaryOp, Control, Expr, Place, Program, UnaryOp, Width};
use std::collections::{BTreeMap, BTreeSet};

const MAX_ACCESSES: usize = 16384;
const MAX_TERMS: usize = 16;
const MAX_MEMBERS: usize = 1_000_000;
const MAX_DAG_NODES: usize = ssa::MAX_NODES * 4;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValidationEvidence {
    pub accesses: usize,
    pub modular_forms: usize,
    /// Distinct source SSA values required by phi incoming edges.
    pub phi_inputs: usize,
    /// True when every required incoming-phi identity was checked as well.
    pub phi_checked: bool,
    /// Distinct fresh source atoms encountered while checking identities.
    pub source_atoms: usize,
    pub basis_evaluations: usize,
}

fn invalid(reason: &str) -> String {
    format!("invalid modular address facts: {reason}")
}
fn unavailable(reason: &str) -> String {
    format!("unavailable: modular address {reason}")
}

struct Budget {
    work: usize,
    members: usize,
}
impl Budget {
    fn new() -> Self {
        Self {
            work: ssa::MAX_WORK,
            members: 0,
        }
    }
    fn spend(&mut self, amount: usize) -> Result<(), String> {
        self.work = self
            .work
            .checked_sub(amount)
            .ok_or_else(|| unavailable("work budget"))?;
        Ok(())
    }
    fn retain(&mut self, amount: usize) -> Result<(), String> {
        self.members = self
            .members
            .checked_add(amount)
            .ok_or_else(|| unavailable("storage budget"))?;
        if self.members > MAX_MEMBERS {
            return Err(unavailable("storage budget"));
        }
        self.spend(amount)
    }
}

type NodeId = usize;
#[derive(Clone, Copy)]
enum Node {
    Constant(u64),
    Atom(ValueId),
    Add(NodeId, NodeId),
    Subtract(NodeId, NodeId),
    Scale(NodeId, u64),
}

struct Checker<'a> {
    source: &'a Program,
    graph: &'a SsaFunction,
    aliases: &'a [ValueId],
    opaque: &'a BTreeSet<Site>,
    candidate: &'a MemoryAddresses,
    points: BTreeMap<Site, &'a PointValues>,
    memo: Vec<Option<NodeId>>,
    visiting: Vec<bool>,
    nodes: Vec<Node>,
    scratch: Vec<u64>,
    atoms: BTreeSet<ValueId>,
    next_access: usize,
    evidence: ValidationEvidence,
    budget: Budget,
}

impl Checker<'_> {
    fn depth(&mut self, depth: usize) -> Result<(), String> {
        self.budget.spend(1)?;
        if depth > ssa::MAX_DEPTH {
            return Err(unavailable("depth budget"));
        }
        Ok(())
    }
    fn node(&mut self, node: Node) -> Result<NodeId, String> {
        if self.nodes.len() >= MAX_DAG_NODES {
            return Err(unavailable("DAG size"));
        }
        self.budget.retain(2)?;
        if let Node::Atom(id) = node {
            self.budget.spend(1)?;
            if self.atoms.insert(id) {
                self.budget.retain(1)?;
            }
        }
        let id = self.nodes.len();
        self.nodes.push(node);
        self.scratch.push(0);
        Ok(id)
    }

    // Decide the raw source grammar before expanding assignments. In
    // particular an unsupported RHS remains its own atom even when a more
    // permissive constant folder could discover a constant result.
    fn pure(&mut self, expr: &Expr, depth: usize) -> Result<bool, String> {
        self.depth(depth)?;
        Ok(match expr {
            Expr::Const(_) | Expr::Register(_) => true,
            Expr::Unary(_, value) => self.pure(value, depth + 1)?,
            Expr::Binary(BinaryOp::Add | BinaryOp::Sub, a, b) => {
                self.pure(a, depth + 1)? && self.pure(b, depth + 1)?
            }
            Expr::Binary(BinaryOp::Mul | BinaryOp::And, a, b) => {
                if matches!(&**a, Expr::Const(_)) {
                    self.pure(b, depth + 1)?
                } else if matches!(&**b, Expr::Const(_)) {
                    self.pure(a, depth + 1)?
                } else {
                    false
                }
            }
            Expr::Binary(BinaryOp::Shl, a, b) if matches!(&**b, Expr::Const(_)) => {
                self.pure(a, depth + 1)?
            }
            _ => false,
        })
    }

    fn value(&mut self, value: ValueId, depth: usize) -> Result<NodeId, String> {
        self.depth(depth)?;
        let id = *self
            .aliases
            .get(value.0)
            .ok_or_else(|| invalid("alias value"))?;
        if let Some(node) = self.memo[id.0] {
            return Ok(node);
        }
        if self.visiting[id.0] {
            return self.node(Node::Atom(id));
        }
        self.visiting[id.0] = true;
        let graph = self.graph;
        let result = match &graph.values[id.0] {
            Definition::Assignment { site, .. } if !self.opaque.contains(site) => {
                let source = self.source;
                let instruction = source
                    .instructions()
                    .binary_search_by_key(&site.instruction, |i| i.address)
                    .map_err(|_| invalid("assignment instruction"))?;
                let expr = &source.instructions()[instruction]
                    .assignments
                    .get(site.assignment.ok_or_else(|| invalid("assignment site"))?)
                    .ok_or_else(|| invalid("assignment index"))?
                    .value;
                if self.pure(expr, 1)? {
                    let point = *self
                        .points
                        .get(site)
                        .ok_or_else(|| invalid("assignment point"))?;
                    let mut cursor = 0;
                    let node = self.expression(expr, point, &mut cursor, depth + 1)?;
                    if cursor != point.reads.len() {
                        return Err(invalid("assignment reads"));
                    }
                    node
                } else {
                    None
                }
            }
            _ => None,
        };
        let node = match result {
            Some(node) => node,
            None => self.node(Node::Atom(id))?,
        };
        self.visiting[id.0] = false;
        self.memo[id.0] = Some(node);
        Ok(node)
    }

    fn expression(
        &mut self,
        expr: &Expr,
        point: &PointValues,
        cursor: &mut usize,
        depth: usize,
    ) -> Result<Option<NodeId>, String> {
        self.depth(depth)?;
        Ok(match expr {
            Expr::Const(value) => Some(self.node(Node::Constant(*value))?),
            Expr::Register(register) => {
                let read = point
                    .reads
                    .get(*cursor)
                    .ok_or_else(|| invalid("source read"))?;
                if read.register != *register {
                    return Err(invalid("source register"));
                }
                *cursor += 1;
                Some(self.value(read.value, depth + 1)?)
            }
            Expr::Unary(op, child) => {
                let value = self.expression(child, point, cursor, depth + 1)?;
                match (*op, value) {
                    (
                        UnaryOp::SignExtend(Width::U64)
                        | UnaryOp::Extract {
                            start: 0,
                            width: Width::U64,
                        },
                        node,
                    ) => node,
                    (op, Some(node)) => match self.constant(node)? {
                        Some(value) => {
                            let value = match op {
                                UnaryOp::Extract { start, width } => {
                                    value.checked_shr(u32::from(start)).unwrap_or(0) & width.mask()
                                }
                                UnaryOp::SignExtend(width) => {
                                    let low = value & width.mask();
                                    if low & (1u64 << (width.bits() - 1)) == 0 {
                                        low
                                    } else {
                                        low | !width.mask()
                                    }
                                }
                            };
                            Some(self.node(Node::Constant(value))?)
                        }
                        None => None,
                    },
                    _ => None,
                }
            }
            Expr::Binary(op, left, right) => {
                let a = self.expression(left, point, cursor, depth + 1)?;
                let b = self.expression(right, point, cursor, depth + 1)?;
                match (op, a, b) {
                    (BinaryOp::Add, Some(a), Some(b)) => Some(self.node(Node::Add(a, b))?),
                    (BinaryOp::Sub, Some(a), Some(b)) => Some(self.node(Node::Subtract(a, b))?),
                    (BinaryOp::Mul, Some(a), Some(b)) => match (&**left, &**right) {
                        (Expr::Const(n), _) => Some(self.node(Node::Scale(b, *n))?),
                        (_, Expr::Const(n)) => Some(self.node(Node::Scale(a, *n))?),
                        _ => None,
                    },
                    (BinaryOp::Shl, Some(a), _) => match &**right {
                        Expr::Const(n) => Some(self.node(Node::Scale(a, 1u64 << (n & 63)))?),
                        _ => None,
                    },
                    // Every atom's hull is the entire u64 word here. The
                    // producer only elides a literal all-ones mask; it does
                    // not fold other masks, even on constant expressions.
                    (BinaryOp::And, Some(a), Some(b)) => match (&**left, &**right) {
                        // The producer chooses the left literal first when
                        // both operands are literals. Preserve that grammar:
                        // c(7) & c(MAX) is unsupported, rather than a new
                        // constant-folding rule that changes RHS atomization.
                        (Expr::Const(mask), _) => (*mask == u64::MAX).then_some(b),
                        (_, Expr::Const(mask)) => (*mask == u64::MAX).then_some(a),
                        _ => None,
                    },
                    _ => None,
                }
            }
            Expr::Load { address, .. } => {
                self.expression(address, point, cursor, depth + 1)?;
                None
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.expression(condition, point, cursor, depth + 1)?;
                self.expression(taken, point, cursor, depth + 1)?;
                self.expression(not_taken, point, cursor, depth + 1)?;
                None
            }
        })
    }

    fn basis(&mut self, root: NodeId) -> Result<(Vec<NodeId>, BTreeSet<ValueId>), String> {
        let mut visited = BTreeSet::new();
        let mut atoms = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            self.budget.spend(1)?;
            if !visited.insert(id) {
                continue;
            }
            // Temporary storage also counts against the work/storage bound;
            // the total retained counter is deliberately conservative.
            self.budget.retain(1)?;
            match self.nodes[id] {
                Node::Constant(_) => {}
                Node::Atom(atom) => {
                    self.budget.spend(1)?;
                    if atoms.insert(atom) {
                        self.budget.retain(1)?;
                    }
                }
                Node::Add(a, b) | Node::Subtract(a, b) => pending.extend([a, b]),
                Node::Scale(a, _) => pending.push(a),
            }
        }
        Ok((visited.into_iter().collect(), atoms))
    }
    fn evaluate(
        &mut self,
        nodes: &[NodeId],
        root: NodeId,
        unit: Option<ValueId>,
    ) -> Result<u64, String> {
        self.budget.spend(nodes.len() + 1)?;
        self.evidence.basis_evaluations += 1;
        // Child IDs precede parents, so sorted reachable nodes give a scalar
        // topological evaluation without recursion or coefficient algebra.
        for &id in nodes {
            self.scratch[id] = match self.nodes[id] {
                Node::Constant(value) => value,
                Node::Atom(atom) => u64::from(unit == Some(atom)),
                Node::Add(a, b) => self.scratch[a].wrapping_add(self.scratch[b]),
                Node::Subtract(a, b) => self.scratch[a].wrapping_sub(self.scratch[b]),
                Node::Scale(a, scale) => self.scratch[a].wrapping_mul(scale),
            };
        }
        Ok(self.scratch[root])
    }
    fn constant(&mut self, root: NodeId) -> Result<Option<u64>, String> {
        let (nodes, atoms) = self.basis(root)?;
        let zero = self.evaluate(&nodes, root, None)?;
        for atom in atoms {
            if self.evaluate(&nodes, root, Some(atom))? != zero {
                return Ok(None);
            }
        }
        Ok(Some(zero))
    }
    fn form(&mut self, root: NodeId, proposed: &ModularAddress) -> Result<(), String> {
        let (nodes, atoms) = self.basis(root)?;
        if self.evaluate(&nodes, root, None)? != proposed.offset {
            return Err(invalid("modular offset"));
        }
        for &(atom, _) in &proposed.terms {
            self.budget.spend(1)?;
            if !atoms.contains(&atom) {
                return Err(invalid("extra modular atom"));
            }
        }
        for atom in atoms {
            let coefficient = proposed
                .terms
                .binary_search_by_key(&atom, |&(id, _)| id)
                .map_or(0, |i| proposed.terms[i].1);
            if self.evaluate(&nodes, root, Some(atom))? != proposed.offset.wrapping_add(coefficient)
            {
                return Err(invalid("modular coefficient"));
            }
        }
        self.evidence.modular_forms += 1;
        Ok(())
    }

    fn shape(&mut self, shape: AddressShape, form: Option<&ModularAddress>) -> Result<(), String> {
        self.budget.spend(1)?;
        let Some(form) = form else {
            return if shape == AddressShape::Unknown {
                Ok(())
            } else {
                Err(invalid("shape without identity"))
            };
        };
        match shape {
            AddressShape::Unknown => Ok(()),
            AddressShape::Absolute(offset) if form.offset == offset && form.terms.is_empty() => {
                Ok(())
            }
            AddressShape::Base {
                base,
                offset,
                index,
            } if offset == form.offset => {
                let mut terms = vec![(base, 1u64)];
                if let Some(index) = index {
                    if index.stride == 0 || index.value == base {
                        return Err(invalid("shape index"));
                    }
                    terms.push((index.value, index.stride));
                }
                terms.sort_unstable();
                if terms == form.terms {
                    Ok(())
                } else {
                    Err(invalid("shape terms"))
                }
            }
            _ => Err(invalid("shape identity")),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn access(
        &mut self,
        point: &PointValues,
        operand: Operand,
        path: &[PathEdge],
        kind: AccessKind,
        width: Width,
        result: Option<ValueId>,
        address: &Expr,
        first_read: usize,
    ) -> Result<(), String> {
        self.budget.spend(path.len() + 1)?;
        let candidate = self.candidate;
        let index = self.next_access;
        let access = candidate
            .accesses
            .get(index)
            .ok_or_else(|| invalid("missing source access"))?;
        if access.site != point.site
            || access.operand != operand
            || access.path != path
            || access.kind != kind
            || access.width != width
            || access.result != result
        {
            return Err(invalid("ordered source access"));
        }
        let form = candidate.forms[index].as_ref();
        if let Some(form) = form {
            let mut cursor = first_read;
            let root = self
                .expression(address, point, &mut cursor, 1)?
                .ok_or_else(|| invalid("unsupported source identity"))?;
            self.form(root, form)?;
        }
        self.shape(access.address, form)?;
        self.next_access += 1;
        self.evidence.accesses += 1;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn child(
        &mut self,
        expr: &Expr,
        edge: PathEdge,
        point: &PointValues,
        operand: Operand,
        path: &mut Vec<PathEdge>,
        cursor: &mut usize,
        depth: usize,
    ) -> Result<(), String> {
        path.push(edge);
        let result = self.walk(expr, point, operand, path, None, cursor, depth + 1);
        path.pop();
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn walk(
        &mut self,
        expr: &Expr,
        point: &PointValues,
        operand: Operand,
        path: &mut Vec<PathEdge>,
        result: Option<ValueId>,
        cursor: &mut usize,
        depth: usize,
    ) -> Result<(), String> {
        self.depth(depth)?;
        match expr {
            Expr::Const(_) => {}
            Expr::Register(register) => {
                let read = point
                    .reads
                    .get(*cursor)
                    .ok_or_else(|| invalid("access read"))?;
                if read.register != *register {
                    return Err(invalid("access register"));
                }
                *cursor += 1;
            }
            Expr::Unary(_, value) => {
                self.child(value, PathEdge::Unary, point, operand, path, cursor, depth)?
            }
            Expr::Binary(_, a, b) => {
                self.child(a, PathEdge::Left, point, operand, path, cursor, depth)?;
                self.child(b, PathEdge::Right, point, operand, path, cursor, depth)?;
            }
            Expr::Load { address, width } => {
                let first_read = *cursor;
                self.child(
                    address,
                    PathEdge::Address,
                    point,
                    operand,
                    path,
                    cursor,
                    depth,
                )?;
                self.access(
                    point,
                    operand,
                    path,
                    AccessKind::Read,
                    *width,
                    result,
                    address,
                    first_read,
                )?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.child(
                    condition,
                    PathEdge::Condition,
                    point,
                    operand,
                    path,
                    cursor,
                    depth,
                )?;
                self.child(taken, PathEdge::Taken, point, operand, path, cursor, depth)?;
                self.child(
                    not_taken,
                    PathEdge::NotTaken,
                    point,
                    operand,
                    path,
                    cursor,
                    depth,
                )?;
            }
        }
        Ok(())
    }
}

fn canonical(form: &ModularAddress, values: usize) -> Result<(), String> {
    if form.terms.len() > MAX_TERMS
        || form
            .terms
            .iter()
            .any(|&(id, scale)| id.0 >= values || scale == 0)
        || form.terms.windows(2).any(|p| p[0].0 >= p[1].0)
    {
        return Err(invalid("canonical modular form"));
    }
    Ok(())
}

/// Check only the all-u64-hull memory analysis. Unavailable obligations return
/// no partial evidence, separately from malformed or false candidate facts.
pub(super) fn validate(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
    candidate: &MemoryAddresses,
) -> Result<ValidationEvidence, String> {
    validate_mode(source, graph, aliases, opaque, candidate, true)
}

/// Independently check graph access facts while retaining an unavailable phi
/// analysis. No incoming-phi identity is consumed or certified in this mode.
pub(super) fn validate_accesses(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
    candidate: &MemoryAddresses,
) -> Result<ValidationEvidence, String> {
    validate_mode(source, graph, aliases, opaque, candidate, false)
}

fn validate_mode(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
    candidate: &MemoryAddresses,
    include_phi: bool,
) -> Result<ValidationEvidence, String> {
    ssa::validate(source, graph).map_err(|error| match error {
        ssa::SsaError::Unavailable(_) => unavailable("source SSA"),
        ssa::SsaError::Malformed(_) => invalid("source SSA"),
    })?;
    super::verify::validate(source, graph, aliases, opaque)
        .ok_or_else(|| unavailable("source aliases"))?;
    check(
        source,
        graph,
        aliases,
        opaque,
        candidate,
        Budget::new(),
        include_phi,
    )
}

fn check(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
    candidate: &MemoryAddresses,
    mut budget: Budget,
    include_phi: bool,
) -> Result<ValidationEvidence, String> {
    if candidate.accesses.len() > MAX_ACCESSES || opaque.len() > ssa::MAX_ASSIGNMENTS {
        return Err(unavailable("candidate size"));
    }
    if candidate.forms.len() != candidate.accesses.len() {
        return Err(invalid("candidate form coverage"));
    }
    budget.retain(candidate.accesses.len() + candidate.forms.len() + graph.values.len() * 2)?;
    for (access, form) in candidate.accesses.iter().zip(&candidate.forms) {
        if access.path.len() > ssa::MAX_DEPTH {
            return Err(invalid("access path depth"));
        }
        budget.retain(access.path.len() + 1)?;
        if let Some(form) = form {
            canonical(form, graph.values.len())?;
            budget.retain(form.terms.len() + 1)?;
        }
    }
    let mut points = BTreeMap::new();
    for block in &graph.blocks {
        for point in &block.points {
            budget.retain(1)?;
            points.insert(point.site, point);
        }
    }
    for site in opaque {
        budget.spend(1)?;
        // Declarations cover the original source, including unreachable
        // instructions. Reachable SSA points alone cannot validate this set.
        let source_index = source
            .instructions()
            .binary_search_by_key(&site.instruction, |instruction| instruction.address)
            .map_err(|_| invalid("opaque source instruction"))?;
        if !site
            .assignment
            .and_then(|index| source.instructions()[source_index].assignments.get(index))
            .is_some_and(|assignment| matches!(assignment.destination, Place::Register(_)))
        {
            return Err(invalid("opaque definition"));
        }
    }
    let mut checker = Checker {
        source,
        graph,
        aliases,
        opaque,
        candidate,
        points,
        memo: vec![None; graph.values.len()],
        visiting: vec![false; graph.values.len()],
        nodes: Vec::new(),
        scratch: Vec::new(),
        atoms: BTreeSet::new(),
        next_access: 0,
        evidence: ValidationEvidence {
            accesses: 0,
            modular_forms: 0,
            phi_inputs: 0,
            phi_checked: include_phi,
            source_atoms: 0,
            basis_evaluations: 0,
        },
        budget,
    };
    // Source syntax supplies the events. The independently checked SSA only
    // supplies read bindings and the chosen order of otherwise distinct blocks.
    for block in &graph.blocks {
        checker.budget.spend(1)?;
        let source_block = source
            .cfg()
            .block_at(block.start)
            .ok_or_else(|| invalid("source block"))?;
        for instruction in
            &source.instructions()[source.cfg().block(source_block).instructions.clone()]
        {
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                let site = Site {
                    instruction: instruction.address,
                    assignment: Some(index),
                };
                let point = *checker
                    .points
                    .get(&site)
                    .ok_or_else(|| invalid("source assignment point"))?;
                let mut cursor = 0;
                let mut path = Vec::new();
                if let Place::Memory { address, .. } = &assignment.destination {
                    path.push(PathEdge::Address);
                    checker.walk(
                        address,
                        point,
                        Operand::Destination,
                        &mut path,
                        None,
                        &mut cursor,
                        1,
                    )?;
                    path.pop();
                }
                let result = if matches!(assignment.destination, Place::Register(_))
                    && matches!(assignment.value, Expr::Load { .. })
                {
                    point.definition
                } else {
                    None
                };
                checker.walk(
                    &assignment.value,
                    point,
                    Operand::Value,
                    &mut path,
                    result,
                    &mut cursor,
                    1,
                )?;
                if let Place::Memory { address, width } = &assignment.destination {
                    checker.access(
                        point,
                        Operand::Destination,
                        &[],
                        AccessKind::Write,
                        *width,
                        None,
                        address,
                        0,
                    )?;
                }
                if cursor != point.reads.len() {
                    return Err(invalid("source point reads"));
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                let site = Site {
                    instruction: instruction.address,
                    assignment: None,
                };
                let point = *checker
                    .points
                    .get(&site)
                    .ok_or_else(|| invalid("source control point"))?;
                let mut cursor = 0;
                checker.walk(
                    condition,
                    point,
                    Operand::Control,
                    &mut Vec::new(),
                    None,
                    &mut cursor,
                    1,
                )?;
                if cursor != point.reads.len() {
                    return Err(invalid("source control reads"));
                }
            }
        }
    }
    if checker.next_access != candidate.accesses.len() {
        return Err(invalid("extra source access"));
    }
    if !include_phi {
        checker.evidence.source_atoms = checker.atoms.len();
        return Ok(checker.evidence);
    }
    let phi_values = candidate
        .phi_values
        .as_ref()
        .map_err(|_| unavailable("phi address identities"))?;
    if phi_values.len() > graph.values.len() {
        return Err(invalid("phi value coverage"));
    }
    checker.budget.retain(phi_values.len())?;
    for form in phi_values.values() {
        canonical(form, graph.values.len())?;
        checker.budget.retain(form.terms.len() + 1)?;
    }
    let mut required = BTreeSet::new();
    for definition in &graph.values {
        checker.budget.spend(1)?;
        if let Definition::Phi { inputs, .. } = definition {
            for input in inputs {
                checker.budget.spend(1)?;
                if required.insert(input.value) {
                    checker.budget.retain(1)?;
                }
            }
        }
    }
    if required.len() != phi_values.len() || required.iter().any(|id| !phi_values.contains_key(id))
    {
        return Err(invalid("phi input coverage"));
    }
    for id in required {
        let node = checker.value(id, 1)?;
        checker.form(node, &phi_values[&id])?;
        checker.evidence.phi_inputs += 1;
    }
    checker.evidence.source_atoms = checker.atoms.len();
    Ok(checker.evidence)
}

#[cfg(test)]
mod tests;
