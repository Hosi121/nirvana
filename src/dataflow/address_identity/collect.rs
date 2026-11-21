//! Exact modular address identities and tentative, evidence-only layouts.
use super::*;
use crate::dataflow::ssa::{self, Definition, PointValues};
use crate::model::ir::{BinaryOp, Control, Expr, Place};
use std::collections::BTreeMap;

const MAX_ACCESSES: usize = 16384;
const MAX_TERMS: usize = 16;
const MAX_WORK: usize = ssa::MAX_WORK;

struct Budget(usize);
impl Budget {
    fn spend(&mut self, n: usize) -> Result<(), ()> {
        self.0 = self.0.checked_sub(n).ok_or(())?;
        Ok(())
    }
}
#[derive(Clone, Copy)]
struct Term {
    coefficient: u64,
    scaled: bool,
}
#[derive(Clone, Default)]
struct Affine {
    offset: u64,
    terms: BTreeMap<ValueId, Term>,
}
impl Affine {
    fn modular(&self) -> ModularAddress {
        ModularAddress {
            offset: self.offset,
            terms: self
                .terms
                .iter()
                .map(|(id, term)| (*id, term.coefficient))
                .collect(),
        }
    }
    fn constant(offset: u64) -> Self {
        Self {
            offset,
            ..Self::default()
        }
    }
    fn atom(value: ValueId) -> Self {
        Self {
            offset: 0,
            terms: BTreeMap::from([(
                value,
                Term {
                    coefficient: 1,
                    scaled: false,
                },
            )]),
        }
    }
    fn add(mut self, other: Self, subtract: bool, budget: &mut Budget) -> Result<Self, ()> {
        budget.spend(other.terms.len() + 1)?;
        self.offset = if subtract {
            self.offset.wrapping_sub(other.offset)
        } else {
            self.offset.wrapping_add(other.offset)
        };
        for (id, term) in other.terms {
            let coefficient = if subtract {
                term.coefficient.wrapping_neg()
            } else {
                term.coefficient
            };
            let old = self.terms.get(&id).copied().unwrap_or(Term {
                coefficient: 0,
                scaled: false,
            });
            let sum = old.coefficient.wrapping_add(coefficient);
            if sum == 0 {
                self.terms.remove(&id);
            } else {
                if !self.terms.contains_key(&id) && self.terms.len() >= MAX_TERMS {
                    return Err(());
                }
                self.terms.insert(
                    id,
                    Term {
                        coefficient: sum,
                        scaled: old.scaled || term.scaled,
                    },
                );
            }
        }
        Ok(self)
    }
    fn scale(mut self, factor: u64, budget: &mut Budget) -> Result<Self, ()> {
        budget.spend(self.terms.len() + 1)?;
        self.offset = self.offset.wrapping_mul(factor);
        self.terms.retain(|_, term| {
            term.coefficient = term.coefficient.wrapping_mul(factor);
            term.scaled = true;
            term.coefficient != 0
        });
        Ok(self)
    }
    fn masked(self, mask: u64, bits: &[u8]) -> Option<Self> {
        if mask == u64::MAX {
            return Some(self);
        }
        if self.offset != 0 || self.terms.len() != 1 {
            return None;
        }
        let (&value, term) = self.terms.first_key_value()?;
        if term.coefficient != 1 {
            return None;
        }
        // A bit-count hull means every low bit can be set. Comparing numeric
        // maxima alone would incorrectly accept masks with missing low bits.
        let hull = match *bits.get(value.0)? {
            0 => 0,
            64 => u64::MAX,
            n @ 1..=63 => u64::MAX >> (64 - n),
            _ => return None,
        };
        (hull & !mask == 0).then_some(self)
    }
    fn shape(&self) -> AddressShape {
        if self.terms.is_empty() {
            return AddressShape::Absolute(self.offset);
        }
        if self.terms.len() == 1 {
            let (&base, term) = self.terms.first_key_value().unwrap();
            return if term.coefficient == 1 {
                AddressShape::Base {
                    base,
                    offset: self.offset,
                    index: None,
                }
            } else {
                AddressShape::Unknown
            };
        }
        if self.terms.len() != 2 {
            return AddressShape::Unknown;
        }
        let candidates: Vec<_> = self
            .terms
            .iter()
            .filter(|(_, term)| term.coefficient == 1)
            .collect();
        // Identity scaling cannot distinguish a pointer base from an index.
        let base = (candidates.len() == 1).then(|| *candidates[0].0);
        let Some(base) = base else {
            return AddressShape::Unknown;
        };
        let (&value, term) = self.terms.iter().find(|(id, _)| **id != base).unwrap();
        if !term.scaled {
            return AddressShape::Unknown;
        }
        AddressShape::Base {
            base,
            offset: self.offset,
            index: Some(ScaledIndex {
                value,
                stride: term.coefficient,
            }),
        }
    }
}

// Reject memory and unsupported syntax before following a definition. In
// particular, a pointer loaded twice keeps two independent SSA atoms.
fn pure(expr: &Expr, depth: usize, budget: &mut Budget) -> Result<bool, ()> {
    budget.spend(1)?;
    if depth > ssa::MAX_DEPTH {
        return Err(());
    }
    Ok(match expr {
        Expr::Const(_) | Expr::Register(_) => true,
        Expr::Unary(_, value) => pure(value, depth + 1, budget)?,
        Expr::Binary(BinaryOp::Add | BinaryOp::Sub, a, b) => {
            pure(a, depth + 1, budget)? && pure(b, depth + 1, budget)?
        }
        Expr::Binary(BinaryOp::Mul | BinaryOp::And, a, b) => match (&**a, &**b) {
            (Expr::Const(_), _) => pure(b, depth + 1, budget)?,
            (_, Expr::Const(_)) => pure(a, depth + 1, budget)?,
            _ => false,
        },
        Expr::Binary(BinaryOp::Shl, a, b) if matches!(&**b, Expr::Const(_)) => {
            pure(a, depth + 1, budget)?
        }
        _ => false,
    })
}

struct Collector<'a> {
    graph: &'a SsaFunction,
    aliases: &'a [ValueId],
    bits: &'a [u8],
    opaque: &'a std::collections::BTreeSet<Site>,
    assignments: BTreeMap<Site, (&'a Expr, &'a PointValues)>,
    memo: Vec<Option<Affine>>,
    visiting: Vec<bool>,
    accesses: Vec<MemoryAccess>,
    memory_forms: Option<Vec<Option<ModularAddress>>>,
    budget: Budget,
}
impl Collector<'_> {
    fn value(&mut self, id: ValueId, depth: usize) -> Result<Affine, ()> {
        self.budget.spend(1)?;
        if depth > ssa::MAX_DEPTH {
            return Err(());
        }
        let id = *self.aliases.get(id.0).ok_or(())?;
        if let Some(form) = &self.memo[id.0] {
            self.budget.spend(form.terms.len() + 1)?;
            return Ok(form.clone());
        }
        if self.visiting[id.0] {
            return Ok(Affine::atom(id));
        }
        self.visiting[id.0] = true;
        let form = match self.graph.values.get(id.0).ok_or(())? {
            Definition::Assignment { site, .. } if self.opaque.contains(site) => Affine::atom(id),
            Definition::Assignment { site, .. } => {
                let (expr, point) = *self.assignments.get(site).ok_or(())?;
                if pure(expr, 1, &mut self.budget)? {
                    let mut cursor = 0;
                    let form = self.expr(
                        expr,
                        point,
                        &mut cursor,
                        &mut Vec::new(),
                        Operand::Value,
                        None,
                        false,
                        depth + 1,
                    )?;
                    if cursor != point.reads.len() {
                        return Err(());
                    }
                    form.unwrap_or_else(|| Affine::atom(id))
                } else {
                    Affine::atom(id)
                }
            }
            _ => Affine::atom(id),
        };
        self.visiting[id.0] = false;
        self.budget.spend(form.terms.len() + 1)?;
        self.memo[id.0] = Some(form.clone());
        Ok(form)
    }
    #[allow(clippy::too_many_arguments)]
    fn record(
        &mut self,
        point: &PointValues,
        operand: Operand,
        path: &[PathEdge],
        kind: AccessKind,
        width: Width,
        form: Option<&Affine>,
        result: Option<ValueId>,
    ) -> Result<(), ()> {
        if self.accesses.len() >= MAX_ACCESSES {
            return Err(());
        }
        self.budget.spend(
            path.len()
                + 1
                + if self.memory_forms.is_some() {
                    form.map_or(0, |f| f.terms.len())
                } else {
                    0
                },
        )?;
        if let Some(forms) = &mut self.memory_forms {
            forms.push(form.map(Affine::modular));
        }
        self.accesses.push(MemoryAccess {
            site: point.site,
            operand,
            path: path.to_vec(),
            kind,
            width,
            address: form.map_or(AddressShape::Unknown, Affine::shape),
            result,
        });
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    fn child(
        &mut self,
        expr: &Expr,
        edge: PathEdge,
        point: &PointValues,
        cursor: &mut usize,
        path: &mut Vec<PathEdge>,
        operand: Operand,
        emit: bool,
        depth: usize,
    ) -> Result<Option<Affine>, ()> {
        path.push(edge);
        let result = self.expr(expr, point, cursor, path, operand, None, emit, depth + 1);
        path.pop();
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn expr(
        &mut self,
        expr: &Expr,
        point: &PointValues,
        cursor: &mut usize,
        path: &mut Vec<PathEdge>,
        operand: Operand,
        result: Option<ValueId>,
        emit: bool,
        depth: usize,
    ) -> Result<Option<Affine>, ()> {
        self.budget.spend(1)?;
        if depth > ssa::MAX_DEPTH {
            return Err(());
        }
        Ok(match expr {
            Expr::Unary(op, value) => {
                let value = self.child(
                    value,
                    PathEdge::Unary,
                    point,
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                match (*op, value) {
                    (
                        crate::model::ir::UnaryOp::SignExtend(crate::model::ir::Width::U64),
                        value,
                    ) => value,
                    (op, Some(Affine { offset, terms })) if terms.is_empty() => {
                        Some(Affine::constant(op.evaluate(offset)))
                    }
                    _ => None,
                }
            }
            Expr::Const(n) => Some(Affine::constant(*n)),
            Expr::Register(register) => {
                let read = point.reads.get(*cursor).ok_or(())?;
                if read.register != *register {
                    return Err(());
                }
                *cursor += 1;
                Some(self.value(read.value, depth + 1)?)
            }
            Expr::Binary(op, left, right) => {
                let lhs = self.child(
                    left,
                    PathEdge::Left,
                    point,
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                let rhs = self.child(
                    right,
                    PathEdge::Right,
                    point,
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                match (op, lhs, rhs) {
                    (BinaryOp::Add, Some(a), Some(b)) => Some(a.add(b, false, &mut self.budget)?),
                    (BinaryOp::Sub, Some(a), Some(b)) => Some(a.add(b, true, &mut self.budget)?),
                    (BinaryOp::Mul, Some(a), Some(b)) => match (&**left, &**right) {
                        (Expr::Const(n), _) => Some(b.scale(*n, &mut self.budget)?),
                        (_, Expr::Const(n)) => Some(a.scale(*n, &mut self.budget)?),
                        _ => None,
                    },
                    (BinaryOp::And, Some(a), Some(b)) => match (&**left, &**right) {
                        (Expr::Const(mask), _) => b.masked(*mask, self.bits),
                        (_, Expr::Const(mask)) => a.masked(*mask, self.bits),
                        _ => None,
                    },
                    (BinaryOp::Shl, Some(a), _) => match &**right {
                        Expr::Const(n) => Some(a.scale(1u64 << (n & 63), &mut self.budget)?),
                        _ => None,
                    },
                    _ => None,
                }
            }
            Expr::Load { address, width } => {
                let form = self.child(
                    address,
                    PathEdge::Address,
                    point,
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                if emit {
                    self.record(
                        point,
                        operand,
                        path,
                        AccessKind::Read,
                        *width,
                        form.as_ref(),
                        result,
                    )?;
                }
                None
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
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                self.child(
                    taken,
                    PathEdge::Taken,
                    point,
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                self.child(
                    not_taken,
                    PathEdge::NotTaken,
                    point,
                    cursor,
                    path,
                    operand,
                    emit,
                    depth,
                )?;
                None
            }
        })
    }
}

#[cfg(test)]
pub(super) fn collect(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
) -> Option<Vec<MemoryAccess>> {
    // Even the test convenience entry point bounds storage before allocating.
    if graph.values.len() > ssa::MAX_VALUES {
        return None;
    }
    collect_with_bounds(source, graph, aliases, &vec![64; graph.values.len()])
}

/// The caller supplies independently checked maximum-bit hulls. This private
/// function checks representation bounds, then uses only canonical atom IDs.
pub(crate) fn collect_with_bounds(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    bits: &[u8],
) -> Option<Vec<MemoryAccess>> {
    collect_with_opaque(
        source,
        graph,
        aliases,
        bits,
        &std::collections::BTreeSet::new(),
    )
}

pub(super) fn collect_with_opaque(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    bits: &[u8],
    opaque: &std::collections::BTreeSet<Site>,
) -> Option<Vec<MemoryAccess>> {
    Some(collect_impl(source, graph, aliases, bits, opaque, false)?.accesses)
}

pub(super) fn collect_memory(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    bits: &[u8],
    opaque: &std::collections::BTreeSet<Site>,
) -> Option<MemoryAddresses> {
    let mut collector = collect_impl(source, graph, aliases, bits, opaque, true)?;
    let phi_values = (|| {
        let mut values = BTreeMap::new();
        for definition in &graph.values {
            if let Definition::Phi { inputs, .. } = definition {
                for input in inputs {
                    collector.budget.spend(1).ok()?;
                    if let std::collections::btree_map::Entry::Vacant(slot) =
                        values.entry(input.value)
                    {
                        slot.insert(collector.value(input.value, 1).ok()?.modular());
                    }
                }
            }
        }
        Some(values)
    })()
    .ok_or_else(|| "memory SSA phi address resource limit".into());
    Some(MemoryAddresses {
        accesses: collector.accesses,
        forms: collector.memory_forms?,
        phi_values,
    })
}

fn collect_impl<'a>(
    source: &'a Program,
    graph: &'a SsaFunction,
    aliases: &'a [ValueId],
    bits: &'a [u8],
    opaque: &'a std::collections::BTreeSet<Site>,
    memory: bool,
) -> Option<Collector<'a>> {
    ssa::validate(source, graph).ok()?;
    if bits.len() != graph.values.len() || bits.iter().any(|&n| n > 64) {
        return None;
    }
    if aliases.len() != graph.values.len() || aliases.iter().any(|id| id.0 >= graph.values.len()) {
        return None;
    }
    let mut assignments = BTreeMap::new();
    let mut collector = Collector {
        graph,
        aliases,
        bits,
        opaque,
        assignments: BTreeMap::new(),
        memo: vec![None; graph.values.len()],
        visiting: vec![false; graph.values.len()],
        accesses: Vec::new(),
        memory_forms: memory.then(Vec::new),
        budget: Budget(MAX_WORK),
    };
    for block in &graph.blocks {
        for point in &block.points {
            collector.budget.spend(1).ok()?;
            if let Some(index) = point.site.assignment {
                let instruction = source
                    .instructions()
                    .binary_search_by_key(&point.site.instruction, |i| i.address)
                    .ok()?;
                let assignment = source.instructions()[instruction].assignments.get(index)?;
                if matches!(assignment.destination, Place::Register(_)) {
                    assignments.insert(point.site, (&assignment.value, point));
                }
            }
        }
    }
    collector.assignments = assignments;
    for block in &graph.blocks {
        for point in &block.points {
            let instruction = source
                .instructions()
                .binary_search_by_key(&point.site.instruction, |i| i.address)
                .ok()?;
            let instruction = &source.instructions()[instruction];
            let mut cursor = 0;
            let mut path = Vec::new();
            if let Some(index) = point.site.assignment {
                let assignment = instruction.assignments.get(index)?;
                let store = if let Place::Memory { address, width } = &assignment.destination {
                    path.push(PathEdge::Address);
                    let form = collector
                        .expr(
                            address,
                            point,
                            &mut cursor,
                            &mut path,
                            Operand::Destination,
                            None,
                            true,
                            1,
                        )
                        .ok()?;
                    path.pop();
                    Some((*width, form))
                } else {
                    None
                };
                let result = if matches!(assignment.destination, Place::Register(_))
                    && matches!(assignment.value, Expr::Load { .. })
                {
                    point.definition
                } else {
                    None
                };
                collector
                    .expr(
                        &assignment.value,
                        point,
                        &mut cursor,
                        &mut path,
                        Operand::Value,
                        result,
                        true,
                        1,
                    )
                    .ok()?;
                if let Some((width, form)) = store {
                    collector
                        .record(
                            point,
                            Operand::Destination,
                            &[],
                            AccessKind::Write,
                            width,
                            form.as_ref(),
                            None,
                        )
                        .ok()?;
                }
            } else {
                let expr = match &instruction.control {
                    Control::Branch { condition, .. } | Control::Return(condition) => condition,
                    _ => return None,
                };
                collector
                    .expr(
                        expr,
                        point,
                        &mut cursor,
                        &mut path,
                        Operand::Control,
                        None,
                        true,
                        1,
                    )
                    .ok()?;
            }
            if cursor != point.reads.len() {
                return None;
            }
        }
    }
    Some(collector)
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
