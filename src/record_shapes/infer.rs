use super::*;
use crate::ir::{AccessKind, BinaryOp as B, Control, Expr};
use crate::ssa::{Definition, PointValues};
use crate::type_infer::{AddressShape, Operand, TypeAnalysis};
use std::collections::{BTreeMap, BTreeSet};

const MAX_WORK: usize = 8_000_000;
const MAX_MEMBERS: usize = 1_000_000;
const MAX_CONSTRAINTS: usize = 262_144;
const MAX_RECORDS: usize = 2048;
const MAX_FIELD_END: u64 = 4096;

struct Builder<'a> {
    types: &'a TypeAnalysis,
    parent: Vec<usize>,
    constraints: Vec<Constraint>,
    nullable: BTreeSet<ValueId>,
    tests: Vec<(ValueId, Site)>,
    work: usize,
    members: usize,
}

impl Builder<'_> {
    fn spend(&mut self, n: usize) -> Result<(), String> {
        self.work = self.work.checked_sub(n).ok_or("record shape work limit")?;
        Ok(())
    }
    fn reserve(&mut self, n: usize) -> Result<(), String> {
        self.spend(n)?;
        self.members = self
            .members
            .checked_add(n)
            .filter(|&n| n <= MAX_MEMBERS)
            .ok_or("record shape membership limit")?;
        Ok(())
    }
    fn root(&mut self, mut id: usize) -> Result<usize, String> {
        while self.parent[id] != id {
            self.spend(1)?;
            let next = self.parent[id];
            self.parent[id] = self.parent[next];
            id = next;
        }
        Ok(id)
    }
    fn connect(
        &mut self,
        from: ValueId,
        to: ValueId,
        kind: ConstraintKind,
        site: Option<Site>,
    ) -> Result<(), String> {
        self.reserve(1)?;
        if self.constraints.len() >= MAX_CONSTRAINTS {
            return Err("record constraint limit".into());
        }
        self.constraints.push(Constraint {
            from,
            to,
            kind,
            site,
        });
        Ok(())
    }

    fn apply_connections(&mut self) -> Result<(), String> {
        let proposals = std::mem::take(&mut self.constraints);
        self.reserve(self.parent.len())?;
        let mut inputs = vec![Vec::new(); self.parent.len()];
        for c in &proposals {
            self.reserve(1)?;
            inputs[c.to.0].push(c.from.0);
            if c.kind == ConstraintKind::Copy {
                self.reserve(1)?;
                inputs[c.from.0].push(c.to.0);
            }
        }
        let mut needed = vec![false; self.parent.len()];
        let mut pending = Vec::new();
        for access in self.types.accesses() {
            if let AddressShape::Base { base, .. } = access.address {
                pending.push(base.0);
            }
        }
        while let Some(id) = pending.pop() {
            self.spend(1)?;
            if std::mem::replace(&mut needed[id], true) {
                continue;
            }
            self.spend(inputs[id].len())?;
            pending.extend_from_slice(&inputs[id]);
        }
        for c in proposals {
            self.spend(1)?;
            // Dead phi/select/stack outputs impose no record compatibility:
            // unpruned SSA also has phis for unrelated, unused register values.
            if c.kind != ConstraintKind::Copy && !needed[c.to.0] {
                continue;
            }
            if self.types.values()[c.from.0].maximum_bits == 0 {
                self.nullable.insert(c.to);
            } else if self.types.values()[c.to.0].maximum_bits == 0 {
                self.nullable.insert(c.from);
            } else {
                let a = self.root(c.from.0)?;
                let b = self.root(c.to.0)?;
                self.parent[a.max(b)] = a.min(b);
            }
            self.constraints.push(c);
        }
        Ok(())
    }
    fn flow(
        &mut self,
        expression: &Expr,
        reads: &BTreeMap<usize, ValueId>,
        to: ValueId,
        kind: ConstraintKind,
        site: Site,
    ) -> Result<(), String> {
        self.spend(1)?;
        if let Some(from) = identity(expression, reads, self.types.aliases(), &mut self.work)? {
            let from = if kind == ConstraintKind::Stack {
                self.types.aliases()[from.0]
            } else {
                from
            };
            return self.connect(from, to, kind, Some(site));
        }
        match expression {
            Expr::Const(0) => {
                self.reserve(1)?;
                self.nullable.insert(to);
            }
            Expr::Select {
                taken, not_taken, ..
            } => {
                let kind = if kind == ConstraintKind::Stack {
                    kind
                } else {
                    ConstraintKind::Select
                };
                self.flow(taken, reads, to, kind, site)?;
                self.flow(not_taken, reads, to, kind, site)?;
            }
            _ => {}
        }
        Ok(())
    }
    fn null_tests(
        &mut self,
        expression: &Expr,
        reads: &BTreeMap<usize, ValueId>,
        site: Site,
    ) -> Result<(), String> {
        let mut pending = vec![expression];
        while let Some(e) = pending.pop() {
            self.spend(1)?;
            match e {
                Expr::Binary(op, a, b) => {
                    if matches!(op, B::Eq | B::Ne) {
                        for (value, other) in [(&**a, &**b), (&**b, &**a)] {
                            if matches!(other, Expr::Const(0))
                                && let Some(id) =
                                    identity(value, reads, self.types.aliases(), &mut self.work)?
                            {
                                self.reserve(1)?;
                                self.tests.push((id, site));
                            }
                        }
                    }
                    pending.extend([&**a, &**b]);
                }
                Expr::Load { address, .. } => pending.push(address),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**condition, &**taken, &**not_taken]),
                _ => {}
            }
        }
        Ok(())
    }
}

// Only representation-preserving forms get identity edges. Select/phi edges
// separately express compatibility between alternatives, not equal values.
fn identity(
    e: &Expr,
    reads: &BTreeMap<usize, ValueId>,
    aliases: &[ValueId],
    work: &mut usize,
) -> Result<Option<ValueId>, String> {
    *work = work.checked_sub(1).ok_or("record identity work limit")?;
    Ok(match e {
        Expr::Register(r) => reads.get(&r.0).copied(),
        Expr::Binary(op, a, b) => {
            let constant = |e: &Expr| {
                if let Expr::Const(n) = e {
                    Some(*n)
                } else {
                    None
                }
            };
            let left = identity(a, reads, aliases, work)?;
            let right = identity(b, reads, aliases, work)?;
            match op {
                B::Add | B::Or | B::Xor if constant(b) == Some(0) => left,
                B::Add | B::Or | B::Xor if constant(a) == Some(0) => right,
                B::Sub if constant(b) == Some(0) => left,
                B::And if constant(b) == Some(u64::MAX) => left,
                B::And if constant(a) == Some(u64::MAX) => right,
                B::Mul if constant(b) == Some(1) => left,
                B::Mul if constant(a) == Some(1) => right,
                B::Shl | B::Shr if constant(b).is_some_and(|n| n & 63 == 0) => left,
                B::And | B::Or
                    if left
                        .zip(right)
                        .is_some_and(|(a, b)| aliases[a.0] == aliases[b.0]) =>
                {
                    left
                }
                _ => None,
            }
        }
        _ => None,
    })
}

fn read_map(point: &PointValues) -> BTreeMap<usize, ValueId> {
    point
        .reads
        .iter()
        .map(|r| (r.register.0, r.value))
        .collect()
}

pub(super) fn analyze(
    source: &Program,
    types: &TypeAnalysis,
    stack: Option<Reg>,
) -> Result<Analysis, String> {
    if stack.is_some_and(|r| r.0 >= source.register_count()) {
        return Err("record stack register out of bounds".into());
    }
    let graph = types.graph();
    let mut builder = Builder {
        types,
        parent: (0..graph.values.len()).collect(),
        constraints: Vec::new(),
        nullable: BTreeSet::new(),
        tests: Vec::new(),
        work: MAX_WORK,
        members: 0,
    };
    builder.reserve(graph.values.len())?;
    let points: BTreeMap<_, _> = graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect();
    for (index, definition) in graph.values.iter().enumerate() {
        builder.spend(1)?;
        if let Definition::Phi { inputs, .. } = definition {
            for input in inputs {
                builder.connect(input.value, ValueId(index), ConstraintKind::Phi, None)?;
            }
        }
    }
    for instruction in source.instructions() {
        for (index, assignment) in instruction.assignments.iter().enumerate() {
            let site = Site {
                instruction: instruction.address,
                assignment: Some(index),
            };
            let Some(point) = points.get(&site) else {
                continue;
            };
            builder.spend(point.reads.len() + 1)?;
            let reads = read_map(point);
            if let Some(to) = point.definition {
                builder.flow(&assignment.value, &reads, to, ConstraintKind::Copy, site)?;
            }
            builder.null_tests(&assignment.value, &reads, site)?;
        }
        let site = Site {
            instruction: instruction.address,
            assignment: None,
        };
        if let Some(point) = points.get(&site) {
            builder.spend(point.reads.len() + 1)?;
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                builder.null_tests(condition, &read_map(point), site)?;
            }
        }
    }
    let skipped_stack_flows = stack_flow(source, types, stack, &points, &mut builder)?;
    builder.apply_connections()?;
    let mut roots = Vec::with_capacity(graph.values.len());
    for i in 0..graph.values.len() {
        roots.push(builder.root(i)?);
    }
    let mut by_root = BTreeMap::new();
    for access in types.accesses() {
        builder.spend(1)?;
        if let AddressShape::Base { base, .. } = access.address {
            let root = roots[base.0];
            if !by_root.contains_key(&root) {
                if by_root.len() >= MAX_RECORDS {
                    return Err("record candidate limit".into());
                }
                by_root.insert(root, BTreeSet::new());
            }
            builder.reserve(1)?;
            by_root.get_mut(&root).unwrap().insert(base);
        }
    }
    let ids: BTreeMap<_, _> = by_root
        .keys()
        .enumerate()
        .map(|(id, &root)| (root, id))
        .collect();
    let mut records: Vec<_> = by_root
        .into_iter()
        .enumerate()
        .map(|(id, (_, bases))| Record {
            id,
            bases: bases.into_iter().collect(),
            values: Vec::new(),
            fields: Vec::new(),
            null_alternatives: Vec::new(),
            null_tests: Vec::new(),
            overlaps: Vec::new(),
            excluded_offsets: 0,
        })
        .collect();
    for (index, &root) in roots.iter().enumerate() {
        if let Some(&id) = ids.get(&root) {
            builder.reserve(1)?;
            records[id].values.push(ValueId(index));
            if builder.nullable.contains(&ValueId(index)) {
                builder.spend(1)?;
                records[id].null_alternatives.push(ValueId(index));
            }
        }
    }
    for &(value, site) in &builder.tests {
        if let Some(&id) = ids.get(&roots[value.0]) {
            records[id].null_tests.push(site);
        }
    }
    for access in types.accesses() {
        builder.spend(1)?;
        let AddressShape::Base {
            base,
            offset,
            index,
        } = access.address
        else {
            continue;
        };
        let record = &mut records[ids[&roots[base.0]]];
        if index.is_some() {
            continue;
        }
        if offset
            .checked_add(access.width.bytes() as u64)
            .is_none_or(|end| end > MAX_FIELD_END)
        {
            record.excluded_offsets += 1;
            continue;
        }
        builder.spend(record.fields.len())?;
        let field = if let Some(i) = record
            .fields
            .iter()
            .position(|f| f.offset == offset && f.width == access.width)
        {
            &mut record.fields[i]
        } else {
            builder.reserve(1)?;
            record.fields.push(Field {
                offset,
                width: access.width,
                reads: false,
                writes: false,
                loaded_values: Vec::new(),
                pointer_targets: Vec::new(),
            });
            record.fields.last_mut().unwrap()
        };
        field.reads |= access.kind == AccessKind::Read;
        field.writes |= access.kind == AccessKind::Write;
        if let Some(value) = access.result {
            builder.reserve(1)?;
            field.loaded_values.push(value);
            if access.width == Width::U64
                && let Some(&target) = ids.get(&roots[value.0])
            {
                field.pointer_targets.push(target);
            }
        }
    }
    for record in &mut records {
        builder.spend(
            record.fields.len() * (record.fields.len().checked_ilog2().unwrap_or(0) as usize + 1),
        )?;
        record.fields.sort_by_key(|f| (f.offset, f.width.bytes()));
        record.null_tests.sort_unstable();
        record.null_tests.dedup();
        for field in &mut record.fields {
            builder.spend(field.loaded_values.len() * 20 + field.pointer_targets.len() * 20)?;
            field.loaded_values.sort_unstable();
            field.loaded_values.dedup();
            field.pointer_targets.sort_unstable();
            field.pointer_targets.dedup();
        }
        for a in 0..record.fields.len() {
            for b in a + 1..record.fields.len() {
                builder.spend(1)?;
                let x = &record.fields[a];
                let y = &record.fields[b];
                if x.offset < y.offset + y.width.bytes() as u64
                    && y.offset < x.offset + x.width.bytes() as u64
                {
                    builder.reserve(1)?;
                    record.overlaps.push((a, b));
                }
            }
        }
    }
    Ok(Analysis {
        records,
        constraints: builder.constraints,
        skipped_stack_flows,
    })
}

fn stack_flow(
    source: &Program,
    types: &TypeAnalysis,
    stack: Option<Reg>,
    points: &BTreeMap<Site, &PointValues>,
    builder: &mut Builder<'_>,
) -> Result<usize, String> {
    let Some(stack) = stack else { return Ok(0) };
    let Some(initial) = types
        .graph()
        .values
        .iter()
        .position(|d| matches!(d,Definition::Initial {register} if *register==stack))
    else {
        return Ok(0);
    };
    let base = types.aliases()[initial];
    let Some(values) = crate::stack_values::StackValues::analyze(source, stack) else {
        return Ok(1);
    };
    let source_indices: BTreeMap<_, _> = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let mut access_by_site: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for access in types.accesses() {
        if access.operand == Operand::Value && access.path.is_empty() && access.result.is_some() {
            access_by_site.entry(access.site).or_default().push(access);
        }
    }
    let mut skipped = 0;
    for read in values.reads() {
        builder.spend(1)?;
        let site = Site {
            instruction: read.instruction,
            assignment: Some(read.assignment),
        };
        let Some(accesses) = access_by_site.get(&site) else {
            continue;
        };
        for access in accesses {
            builder.spend(1)?;
            if access.width != read.location.width
                || !matches!(access.address,AddressShape::Base {base:b,offset,index:None} if b==base && offset==read.location.offset as u64)
            {
                continue;
            }
            let to = access.result.unwrap();
            if read.has_unknown {
                skipped += 1;
                continue;
            }
            for &definition in &read.definitions {
                builder.spend(1)?;
                let definition = &values.definitions()[definition];
                let source_site = Site {
                    instruction: definition.instruction,
                    assignment: Some(definition.assignment),
                };
                let assignment =
                    &source_indices[&definition.instruction].assignments[definition.assignment];
                let Some(point) = points.get(&source_site) else {
                    skipped += 1;
                    continue;
                };
                builder.spend(point.reads.len() + 1)?;
                builder.flow(
                    &assignment.value,
                    &read_map(point),
                    to,
                    ConstraintKind::Stack,
                    source_site,
                )?;
            }
        }
    }
    Ok(skipped)
}
