//! Exact modular address identities and tentative, evidence-only layouts.
use super::*;
use crate::ir::{BinaryOp, Control, Expr, Place};
use crate::ssa::{self, Definition, PointValues};
use std::collections::BTreeMap;

const MAX_ACCESSES: usize = 16384;
const MAX_TERMS: usize = 16;
const MAX_OVERLAP_PAIRS: usize = 65536;
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
        self.budget.spend(path.len() + 1)?;
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
pub(super) fn collect_with_bounds(
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
    Some(collector.accesses)
}

pub(super) fn layouts(accesses: &[MemoryAccess]) -> Option<Vec<LayoutCandidate>> {
    if accesses.len() > MAX_ACCESSES {
        return None;
    }
    let mut budget = Budget(MAX_WORK);
    let mut groups = BTreeMap::<ValueId, LayoutCandidate>::new();
    for access in accesses {
        budget.spend(1).ok()?;
        let AddressShape::Base {
            base,
            offset,
            index,
        } = access.address
        else {
            continue;
        };
        let group = groups.entry(base).or_insert_with(|| LayoutCandidate {
            base,
            fields: Vec::new(),
            arrays: Vec::new(),
            overlaps: Vec::new(),
            ambiguous_intervals: false,
        });
        group.ambiguous_intervals |= (offset as i64)
            .checked_add(access.width.bytes() as i64)
            .is_none();
        let (reads, writes) = match access.kind {
            AccessKind::Read => (true, false),
            AccessKind::Write => (false, true),
        };
        if let Some(index) = index {
            budget.spend(group.arrays.len()).ok()?;
            let slot = group.arrays.iter().position(|f| {
                f.offset == offset && f.stride == index.stride && f.width == access.width
            });
            let slot = slot.unwrap_or_else(|| {
                group.arrays.push(ArrayCandidate {
                    offset,
                    stride: index.stride,
                    width: access.width,
                    indices: Vec::new(),
                    loaded_values: Vec::new(),
                    reads: false,
                    writes: false,
                });
                group.arrays.len() - 1
            });
            let field = &mut group.arrays[slot];
            budget
                .spend(field.indices.len() + field.loaded_values.len())
                .ok()?;
            if !field.indices.contains(&index.value) {
                field.indices.push(index.value);
            }
            if let Some(value) = access.result
                && !field.loaded_values.contains(&value)
            {
                field.loaded_values.push(value);
            }
            field.reads |= reads;
            field.writes |= writes;
        } else {
            budget.spend(group.fields.len()).ok()?;
            let slot = group
                .fields
                .iter()
                .position(|f| f.offset == offset && f.width == access.width);
            let slot = slot.unwrap_or_else(|| {
                group.fields.push(FieldCandidate {
                    offset,
                    width: access.width,
                    loaded_values: Vec::new(),
                    reads: false,
                    writes: false,
                });
                group.fields.len() - 1
            });
            let field = &mut group.fields[slot];
            budget.spend(field.loaded_values.len()).ok()?;
            if let Some(value) = access.result
                && !field.loaded_values.contains(&value)
            {
                field.loaded_values.push(value);
            }
            field.reads |= reads;
            field.writes |= writes;
        }
    }
    let mut pairs = 0usize;
    for group in groups.values_mut() {
        let mut intervals = Vec::with_capacity(group.fields.len());
        for field in &group.fields {
            budget.spend(1).ok()?;
            let start = field.offset as i64;
            let end = start.checked_add(field.width.bytes() as i64);
            group.ambiguous_intervals |= end.is_none();
            intervals.push(end.map(|end| (start, end)));
        }
        for (a, left) in intervals.iter().enumerate() {
            for (b, right) in intervals.iter().enumerate().skip(a + 1) {
                budget.spend(1).ok()?;
                if let (Some((l0, l1)), Some((r0, r1))) = (left, right)
                    && l0 < r1
                    && r0 < l1
                {
                    pairs = pairs.checked_add(1)?;
                    if pairs > MAX_OVERLAP_PAIRS {
                        return None;
                    }
                    group.overlaps.push((a, b));
                }
            }
        }
    }
    Some(groups.into_values().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Assignment, IrInstruction, Reg};

    fn r(n: usize) -> Expr {
        Expr::Register(Reg(n))
    }
    fn c(n: u64) -> Expr {
        Expr::Const(n)
    }
    fn add(a: Expr, b: Expr) -> Expr {
        Expr::binary(BinaryOp::Add, a, b)
    }
    fn mul(a: Expr, n: u64) -> Expr {
        Expr::binary(BinaryOp::Mul, a, c(n))
    }
    fn shl(a: Expr, n: u64) -> Expr {
        Expr::binary(BinaryOp::Shl, a, c(n))
    }
    fn load(address: Expr, width: Width) -> Expr {
        Expr::load(address, width)
    }
    fn set(n: usize, value: Expr) -> Assignment {
        Assignment {
            destination: Place::Register(Reg(n)),
            value,
        }
    }
    fn store(address: Expr, width: Width, value: Expr) -> Assignment {
        Assignment {
            destination: Place::Memory { address, width },
            value,
        }
    }
    fn program(assignments: Vec<Assignment>, control: Expr) -> Program {
        Program::new(
            0,
            8,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(control),
            }],
        )
        .unwrap()
    }
    fn graph(source: &Program) -> (SsaFunction, Vec<ValueId>) {
        let graph = SsaFunction::build(source).unwrap();
        let ids = (0..graph.values.len()).map(ValueId).collect();
        (graph, ids)
    }
    fn accesses(source: &Program) -> (SsaFunction, Vec<MemoryAccess>) {
        let (graph, ids) = graph(source);
        let result = collect(source, &graph, &ids).unwrap();
        (graph, result)
    }
    fn definition(graph: &SsaFunction, assignment: usize) -> ValueId {
        graph
            .point(Site {
                instruction: 0,
                assignment: Some(assignment),
            })
            .unwrap()
            .definition
            .unwrap()
    }
    fn base(address: AddressShape) -> ValueId {
        let AddressShape::Base { base, .. } = address else {
            panic!("not a base: {address:?}")
        };
        base
    }

    #[test]
    fn scalar_fields_preserve_widths_results_and_overlap() {
        let source = program(
            vec![
                set(2, load(r(0), Width::U32)),
                set(3, load(add(r(0), c(8)), Width::U64)),
                store(r(0), Width::U64, c(1)),
                set(4, load(r(0), Width::U32)),
            ],
            c(0),
        );
        let (graph, found) = accesses(&source);
        assert_eq!(found.len(), 4);
        assert_eq!(found[0].result, Some(definition(&graph, 0)));
        assert_eq!(found[1].result, Some(definition(&graph, 1)));
        assert_eq!(found[2].result, None);
        let grouped = layouts(&found).unwrap();
        assert_eq!(grouped.len(), 1);
        let group = &grouped[0];
        assert_eq!(group.fields.len(), 3);
        assert_eq!(group.fields[0].offset, 0);
        assert_eq!(group.fields[1].offset, 8);
        assert_eq!(
            group.fields[0].loaded_values,
            vec![definition(&graph, 0), definition(&graph, 3)]
        );
        assert!(group.fields[0].reads && !group.fields[0].writes);
        assert!(group.fields[2].writes && !group.fields[2].reads);
        assert_eq!(group.overlaps, vec![(0, 2)]);
        assert!(!group.ambiguous_intervals);
    }
    #[test]
    fn loaded_pointer_is_an_atom_and_explicit_scaled_indices_group() {
        let source = program(
            vec![
                set(2, load(r(0), Width::U64)),
                set(3, load(add(r(2), mul(r(1), 4)), Width::U32)),
                store(add(r(2), shl(r(4), 2)), Width::U32, c(9)),
            ],
            c(0),
        );
        let (graph, found) = accesses(&source);
        let pointer = definition(&graph, 0);
        assert_eq!(base(found[1].address), pointer);
        let grouped = layouts(&found).unwrap();
        let arrays = &grouped.iter().find(|g| g.base == pointer).unwrap().arrays;
        assert_eq!(arrays.len(), 1);
        assert_eq!(arrays[0].stride, 4);
        assert_eq!(arrays[0].indices.len(), 2);
        assert_eq!(arrays[0].loaded_values, vec![definition(&graph, 1)]);
        assert!(arrays[0].reads && arrays[0].writes);
    }
    #[test]
    fn wrapping_offsets_negative_factors_and_shift_mask_are_exact() {
        let source = program(
            vec![
                set(2, load(Expr::binary(BinaryOp::Sub, r(0), c(8)), Width::U8)),
                set(
                    2,
                    load(
                        add(r(0), Expr::binary(BinaryOp::Sub, c(0), mul(r(1), 4))),
                        Width::U8,
                    ),
                ),
                set(2, load(add(r(0), shl(r(1), 65)), Width::U8)),
                set(2, load(add(c(u64::MAX), c(4)), Width::U8)),
                set(2, load(add(r(0), mul(r(1), 0)), Width::U8)),
            ],
            c(0),
        );
        let (_, found) = accesses(&source);
        assert!(
            matches!(found[0].address, AddressShape::Base { offset, index: None, .. } if offset == u64::MAX - 7)
        );
        assert!(
            matches!(found[1].address, AddressShape::Base { index: Some(ScaledIndex { stride, .. }), .. } if stride == 0u64.wrapping_sub(4))
        );
        assert!(matches!(
            found[2].address,
            AddressShape::Base {
                index: Some(ScaledIndex { stride: 2, .. }),
                ..
            }
        ));
        assert_eq!(found[3].address, AddressShape::Absolute(3));
        assert!(matches!(
            found[4].address,
            AddressShape::Base { index: None, .. }
        ));
    }
    #[test]
    fn coefficient_one_sum_is_ambiguous_even_after_identity_scaling() {
        let source = program(
            vec![
                set(2, load(add(r(0), r(1)), Width::U8)),
                set(2, load(add(r(0), mul(r(1), 1)), Width::U8)),
                set(2, load(add(r(0), shl(r(1), 64)), Width::U8)),
                set(2, load(mul(r(1), 4), Width::U8)),
            ],
            c(0),
        );
        let (_, found) = accesses(&source);
        assert!(found.iter().all(|a| a.address == AddressShape::Unknown));
        assert!(layouts(&found).unwrap().is_empty());
    }
    #[test]
    fn pure_lea_temporaries_expand_but_changed_source_versions_do_not_merge() {
        let source = program(
            vec![
                set(2, add(r(0), c(8))),
                set(3, add(r(2), mul(r(1), 4))),
                set(4, load(r(3), Width::U32)),
                set(0, load(c(4096), Width::U64)),
                set(4, load(add(r(0), c(8)), Width::U32)),
            ],
            c(0),
        );
        let (graph, found) = accesses(&source);
        assert!(matches!(
            found[0].address,
            AddressShape::Base {
                offset: 8,
                index: Some(ScaledIndex { stride: 4, .. }),
                ..
            }
        ));
        assert_ne!(base(found[0].address), base(found[2].address));
        assert_eq!(base(found[2].address), definition(&graph, 3));
    }
    #[test]
    fn aliases_are_trusted_only_after_bounds_and_ssa_validation() {
        let source = program(
            vec![
                set(2, r(0)),
                set(3, load(r(0), Width::U32)),
                set(4, load(r(2), Width::U32)),
            ],
            c(0),
        );
        let (graph, mut ids) = graph(&source);
        let first = graph
            .point(Site {
                instruction: 0,
                assignment: Some(0),
            })
            .unwrap()
            .reads[0]
            .value;
        ids[definition(&graph, 0).0] = first;
        let found = collect(&source, &graph, &ids).unwrap();
        assert_eq!(found[0].address, found[1].address);
        assert!(collect(&source, &graph, &ids[..ids.len() - 1]).is_none());
        ids[0] = ValueId(graph.values.len());
        assert!(collect(&source, &graph, &ids).is_none());
        let mut invalid = graph.clone();
        invalid.blocks[0].points[0].reads.clear();
        assert!(
            collect(
                &source,
                &invalid,
                &(0..graph.values.len()).map(ValueId).collect::<Vec<_>>()
            )
            .is_none()
        );
    }
    #[test]
    fn identical_pointer_loads_remain_distinct_values() {
        let source = program(
            vec![
                set(2, load(r(0), Width::U64)),
                set(3, load(r(0), Width::U64)),
                set(4, load(r(2), Width::U8)),
                set(5, load(r(3), Width::U8)),
            ],
            c(0),
        );
        let (graph, found) = accesses(&source);
        assert_eq!(base(found[2].address), definition(&graph, 0));
        assert_eq!(base(found[3].address), definition(&graph, 1));
        assert_ne!(found[2].address, found[3].address);
    }
    #[test]
    fn nested_loads_lazy_arms_store_addresses_and_control_keep_routes() {
        let source = program(
            vec![store(
                load(r(0), Width::U64),
                Width::U8,
                Expr::select(
                    load(r(1), Width::U8),
                    load(r(2), Width::U16),
                    add(load(r(3), Width::U32), c(1)),
                ),
            )],
            load(load(r(4), Width::U64), Width::U8),
        );
        let (_, found) = accesses(&source);
        assert_eq!(found.len(), 7);
        assert_eq!(
            (found[0].operand, found[0].path.as_slice()),
            (Operand::Destination, &[PathEdge::Address][..])
        );
        assert_eq!(found[1].path, vec![PathEdge::Condition]);
        assert_eq!(found[2].path, vec![PathEdge::Taken]);
        assert_eq!(found[3].path, vec![PathEdge::NotTaken, PathEdge::Left]);
        assert_eq!(found[4].kind, AccessKind::Write);
        assert_eq!(found[4].address, AddressShape::Unknown);
        assert_eq!(found[5].operand, Operand::Control);
        assert_eq!(found[5].path, vec![PathEdge::Address]);
        assert_eq!(found[6].address, AddressShape::Unknown);
        assert!(found.iter().all(|a| a.result.is_none()));
        assert_eq!(found[0].site.assignment, Some(0));
        assert_eq!(found[6].site.assignment, None);
    }
    #[test]
    fn unmodified_root_load_is_the_only_load_with_result_id() {
        let source = program(
            vec![
                set(2, add(load(r(0), Width::U32), c(0))),
                set(3, load(load(r(1), Width::U64), Width::U32)),
            ],
            c(0),
        );
        let (graph, found) = accesses(&source);
        assert_eq!(found[0].result, None);
        assert_eq!(found[1].result, None);
        assert_eq!(found[2].result, Some(definition(&graph, 1)));
    }
    #[test]
    fn interval_endpoint_overflow_is_visible_and_negative_offsets_overlap() {
        let source = program(
            vec![
                set(2, load(add(r(0), c(i64::MAX as u64)), Width::U64)),
                set(3, load(add(r(0), c(u64::MAX - 3)), Width::U64)),
                set(4, load(r(0), Width::U32)),
            ],
            c(0),
        );
        let (_, found) = accesses(&source);
        let groups = layouts(&found).unwrap();
        assert!(groups[0].ambiguous_intervals);
        assert_eq!(groups[0].overlaps, vec![(1, 2)]);
    }
    #[test]
    fn unsupported_address_still_preserves_load_evidence() {
        let source = program(
            vec![
                set(
                    2,
                    load(Expr::binary(BinaryOp::And, r(0), c(255)), Width::U8),
                ),
                set(3, load(Expr::select(c(1), r(0), r(1)), Width::U8)),
            ],
            c(0),
        );
        let (_, found) = accesses(&source);
        assert_eq!(found.len(), 2);
        assert!(found.iter().all(|a| a.address == AddressShape::Unknown));
    }
    #[test]
    fn access_and_term_caps_decline_without_partial_results() {
        let source = program(
            (0..MAX_ACCESSES / 2 + 1)
                .map(|_| store(c(0), Width::U8, load(c(0), Width::U8)))
                .collect(),
            c(0),
        );
        let (graph, ids) = graph(&source);
        assert!(collect(&source, &graph, &ids).is_none());
        let mut form = Affine::default();
        let mut budget = Budget(MAX_WORK);
        for n in 0..MAX_TERMS {
            form = form
                .add(Affine::atom(ValueId(n)), false, &mut budget)
                .unwrap();
        }
        assert!(
            form.add(Affine::atom(ValueId(MAX_TERMS)), false, &mut budget)
                .is_err()
        );
        let access = MemoryAccess {
            site: Site {
                instruction: 0,
                assignment: None,
            },
            operand: Operand::Control,
            path: vec![],
            kind: AccessKind::Read,
            width: Width::U8,
            address: AddressShape::Absolute(0),
            result: None,
        };
        assert!(layouts(&vec![access; MAX_ACCESSES + 1]).is_none());
    }
    #[test]
    fn layout_work_and_overlap_limits_decline_atomically() {
        fn evidence(base: usize, offset: u64, width: Width) -> MemoryAccess {
            MemoryAccess {
                site: Site {
                    instruction: 0,
                    assignment: None,
                },
                operand: Operand::Control,
                path: vec![],
                kind: AccessKind::Read,
                width,
                address: AddressShape::Base {
                    base: ValueId(base),
                    offset,
                    index: None,
                },
                result: None,
            }
        }
        // More than eight million pair comparisons, despite no intersections.
        let sparse: Vec<_> = (0..4096).map(|n| evidence(0, n * 8, Width::U8)).collect();
        assert!(layouts(&sparse).is_none());
        // Many bounded groups keep pair work small but exceed total overlap
        // output capacity. No incomplete prefix of groups may escape.
        let mut dense = Vec::new();
        for base in 0..12 {
            for offset in 0..128 {
                for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
                    dense.push(evidence(base, offset, width));
                }
            }
        }
        assert!(layouts(&dense).is_none());
        assert!(Affine::atom(ValueId(0)).scale(4, &mut Budget(0)).is_err());
    }
    #[test]
    fn affine_cancellation_and_literal_products_follow_modular_arithmetic() {
        let source = program(
            vec![
                set(
                    2,
                    load(
                        Expr::binary(
                            BinaryOp::Sub,
                            add(r(0), mul(r(1), u64::MAX)),
                            mul(r(1), u64::MAX),
                        ),
                        Width::U8,
                    ),
                ),
                set(2, load(add(r(0), mul(r(1), 1u64 << 63)), Width::U8)),
                set(2, load(mul(c(u64::MAX), 2), Width::U8)),
                set(2, load(shl(c(3), 65), Width::U8)),
            ],
            c(0),
        );
        let (_, found) = accesses(&source);
        assert!(matches!(
            found[0].address,
            AddressShape::Base {
                offset: 0,
                index: None,
                ..
            }
        ));
        assert!(
            matches!(found[1].address, AddressShape::Base { index: Some(ScaledIndex { stride, .. }), .. } if stride == 1u64 << 63)
        );
        assert_eq!(found[2].address, AddressShape::Absolute(u64::MAX - 1));
        assert_eq!(found[3].address, AddressShape::Absolute(6));
    }
    fn and(a: Expr, mask: u64) -> Expr {
        Expr::binary(BinaryOp::And, a, c(mask))
    }

    #[test]
    fn mask_elision_requires_the_entire_atom_bit_hull() {
        let source = program(
            vec![
                set(2, load(and(r(0), 255), Width::U8)),
                set(2, load(and(r(0), 247), Width::U8)),
                set(2, load(and(r(0), 256), Width::U8)),
                set(2, load(and(add(r(0), c(1)), 255), Width::U8)),
            ],
            c(0),
        );
        let (graph, ids) = graph(&source);
        let input = graph
            .point(Site {
                instruction: 0,
                assignment: Some(0),
            })
            .unwrap()
            .reads[0]
            .value;
        let mut bits = vec![64; graph.values.len()];
        bits[input.0] = 8;
        let found = collect_with_bounds(&source, &graph, &ids, &bits).unwrap();
        assert!(
            matches!(found[0].address, AddressShape::Base { base, offset: 0, index: None } if base == input)
        );
        assert!(
            found[1..]
                .iter()
                .all(|a| a.address == AddressShape::Unknown)
        );
        bits[input.0] = 64;
        assert!(
            collect_with_bounds(&source, &graph, &ids, &bits)
                .unwrap()
                .iter()
                .all(|a| a.address == AddressShape::Unknown)
        );
        bits[input.0] = 0;
        assert!(matches!(
            collect_with_bounds(&source, &graph, &ids, &bits).unwrap()[2].address,
            AddressShape::Base { .. }
        ));
        bits[input.0] = 65;
        assert!(collect_with_bounds(&source, &graph, &ids, &bits).is_none());
        assert!(collect_with_bounds(&source, &graph, &ids, &bits[..bits.len() - 1]).is_none());
    }
    #[test]
    fn loaded_u32_proof_links_masked_index_to_loaded_pointer_layout() {
        let source = program(
            vec![
                set(2, load(add(r(0), c(8)), Width::U64)),
                set(3, load(r(1), Width::U32)),
                set(
                    4,
                    load(add(r(2), mul(and(r(3), u32::MAX as u64), 4)), Width::U32),
                ),
            ],
            c(0),
        );
        let (graph, ids) = graph(&source);
        let pointer = definition(&graph, 0);
        let index = definition(&graph, 1);
        let mut bits = vec![64; graph.values.len()];
        bits[index.0] = 32;
        let found = collect_with_bounds(&source, &graph, &ids, &bits).unwrap();
        assert_eq!(
            found[2].address,
            AddressShape::Base {
                base: pointer,
                offset: 0,
                index: Some(ScaledIndex {
                    value: index,
                    stride: 4
                })
            }
        );
        assert_eq!(
            layouts(&found)
                .unwrap()
                .iter()
                .find(|l| l.base == pointer)
                .unwrap()
                .arrays[0]
                .stride,
            4
        );
        bits[index.0] = 64;
        assert_eq!(
            collect_with_bounds(&source, &graph, &ids, &bits).unwrap()[2].address,
            AddressShape::Unknown
        );
    }
    #[test]
    fn mask_identity_and_definition_expansion_are_pure_and_canonical() {
        let source = program(
            vec![
                set(2, and(r(0), 255)),
                set(3, load(r(2), Width::U8)),
                set(4, load(and(add(r(0), mul(r(1), 4)), u64::MAX), Width::U8)),
                set(5, load(and(load(r(0), Width::U64), u64::MAX), Width::U8)),
            ],
            c(0),
        );
        let (graph, ids) = graph(&source);
        let input = graph
            .point(Site {
                instruction: 0,
                assignment: Some(0),
            })
            .unwrap()
            .reads[0]
            .value;
        let mut bits = vec![64; graph.values.len()];
        bits[input.0] = 8;
        let found = collect_with_bounds(&source, &graph, &ids, &bits).unwrap();
        assert_eq!(base(found[0].address), input);
        assert!(matches!(
            found[1].address,
            AddressShape::Base {
                index: Some(ScaledIndex { stride: 4, .. }),
                ..
            }
        ));
        assert_eq!(found[3].address, AddressShape::Unknown);
        let copies = program(
            vec![set(2, r(0)), set(3, load(and(r(2), 255), Width::U8))],
            c(0),
        );
        let (graph, mut ids) = self::graph(&copies);
        let root = graph
            .point(Site {
                instruction: 0,
                assignment: Some(0),
            })
            .unwrap()
            .reads[0]
            .value;
        let copy = definition(&graph, 0);
        ids[copy.0] = root;
        let mut bits = vec![64; graph.values.len()];
        bits[copy.0] = 8;
        assert_eq!(
            collect_with_bounds(&copies, &graph, &ids, &bits).unwrap()[0].address,
            AddressShape::Unknown
        );
    }
}
