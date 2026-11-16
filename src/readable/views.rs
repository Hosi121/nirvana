//! Stack-view discovery and register dependencies for C rendering.

use crate::ir::{AccessKind, Control, Expr, Place, Program, Reg, Width};
use crate::provenance::AddressAnalysis;
use crate::stack::StackAnalysis;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StackView {
    pub name: String,
    pub offset: i64,
    /// Maximum observed access width; no object extent or ownership is inferred.
    pub byte_size: usize,
    pub read_sites: usize,
    pub write_sites: usize,
    /// Indices of other views sharing at least one observed byte.
    pub overlaps: Vec<usize>,
}

/// An observed byte offset from a proven input-register base, not a source type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectField {
    pub name: String,
    pub offset: i64,
    pub byte_size: usize,
    pub read_sites: usize,
    pub write_sites: usize,
    pub overlaps: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectView {
    pub name: String,
    pub register: Reg,
    pub fields: Vec<ObjectField>,
}

pub(super) struct MemoryViews {
    stack: Option<StackViews>,
    origins: Option<AddressAnalysis>,
    pub(super) objects: Vec<ObjectView>,
    by_origin: BTreeMap<(usize, i64), (usize, usize)>,
}

impl MemoryViews {
    pub(super) fn recover(
        program: &Program,
        parameters: &[Reg],
        options: super::ReadableOptions,
    ) -> Option<Self> {
        let stack = options
            .stack_register
            .filter(|r| parameters.contains(r))
            .and_then(|r| StackViews::recover(program, r));
        let origins = options
            .recover_objects
            .then(|| AddressAnalysis::analyze(program, parameters));
        let mut fields: BTreeMap<(usize, i64), ObjectField> = BTreeMap::new();
        if let Some(origins) = &origins {
            for access in memory_sites(program).unwrap_or_default() {
                let Some(origin) =
                    origins.origin_before(access.instruction, access.assignment, access.address)
                else {
                    continue;
                };
                if options.stack_register == Some(origin.register) {
                    continue;
                }
                let field = fields
                    .entry((origin.register.0, origin.offset))
                    .or_insert_with(|| ObjectField {
                        name: String::new(),
                        offset: origin.offset,
                        byte_size: 0,
                        read_sites: 0,
                        write_sites: 0,
                        overlaps: Vec::new(),
                    });
                field.byte_size = field.byte_size.max(access.width.bytes());
                match access.kind {
                    AccessKind::Read => field.read_sites += 1,
                    AccessKind::Write => field.write_sites += 1,
                }
                if fields.len() > 256 {
                    fields.clear();
                    break;
                }
            }
        }
        let mut objects: Vec<ObjectView> = Vec::new();
        for ((register, _), mut field) in fields {
            if objects.last().is_none_or(|o| o.register.0 != register) {
                objects.push(ObjectView {
                    name: format!("object_{}", objects.len()),
                    register: Reg(register),
                    fields: Vec::new(),
                });
            }
            field.name = if field.offset < 0 {
                format!("field_m{}", field.offset.unsigned_abs())
            } else {
                format!("field_{}", field.offset)
            };
            objects.last_mut().unwrap().fields.push(field);
        }
        for object in &mut objects {
            for a in 0..object.fields.len() {
                for b in a + 1..object.fields.len() {
                    if byte_overlap(
                        object.fields[a].offset,
                        object.fields[a].byte_size,
                        object.fields[b].offset,
                        object.fields[b].byte_size,
                    ) {
                        object.fields[a].overlaps.push(b);
                        object.fields[b].overlaps.push(a);
                    }
                }
            }
        }
        let by_origin = objects
            .iter()
            .enumerate()
            .flat_map(|(o, object)| {
                object
                    .fields
                    .iter()
                    .enumerate()
                    .map(move |(f, field)| ((object.register.0, field.offset), (o, f)))
            })
            .collect();
        if stack.is_none() && objects.is_empty() {
            return None;
        }
        Some(Self {
            stack,
            origins,
            objects,
            by_origin,
        })
    }

    pub(super) fn at(&self, point: Option<(u64, usize)>, address: &Expr) -> Option<String> {
        if let Some(view) = self
            .stack
            .as_ref()
            .and_then(|stack| stack.at(point, address))
        {
            return Some(view.name.clone());
        }
        let (instruction, assignment) = point?;
        let origin = self
            .origins
            .as_ref()?
            .origin_before(instruction, assignment, address)?;
        let &(o, f) = self.by_origin.get(&(origin.register.0, origin.offset))?;
        Some(format!(
            "{}.{}",
            self.objects[o].name, self.objects[o].fields[f].name
        ))
    }

    pub(super) fn stack_views(&self) -> &[StackView] {
        self.stack
            .as_ref()
            .map(|s| s.views.as_slice())
            .unwrap_or_default()
    }

    pub(super) fn registers(&self) -> impl Iterator<Item = Reg> + '_ {
        self.stack
            .iter()
            .map(|s| s.register)
            .chain(self.objects.iter().map(|o| o.register))
    }
}

fn byte_overlap(a: i64, a_size: usize, b: i64, b_size: usize) -> bool {
    (0..a_size).any(|i| (0..b_size).any(|j| a.wrapping_add(i as i64) == b.wrapping_add(j as i64)))
}

struct MemorySite<'a> {
    instruction: u64,
    assignment: usize,
    address: &'a Expr,
    width: Width,
    kind: AccessKind,
}

// Collect executable assignment accesses, rather than trusting analysis access
// summaries whose successful-value facts may include impure addresses. Query
// each address at its exact original point before permitting a replacement.
fn memory_sites(program: &Program) -> Option<Vec<MemorySite<'_>>> {
    fn expression<'a>(
        expr: &'a Expr,
        point: (u64, usize),
        depth: usize,
        result: &mut Vec<MemorySite<'a>>,
    ) -> Option<()> {
        if depth > 256 || result.len() >= 100_000 {
            return None;
        }
        match expr {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, a, b) => {
                expression(a, point, depth + 1, result)?;
                expression(b, point, depth + 1, result)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                expression(condition, point, depth + 1, result)?;
                expression(taken, point, depth + 1, result)?;
                expression(not_taken, point, depth + 1, result)?;
            }
            Expr::Load { address, width } => {
                expression(address, point, depth + 1, result)?;
                result.push(MemorySite {
                    instruction: point.0,
                    assignment: point.1,
                    address,
                    width: *width,
                    kind: AccessKind::Read,
                });
            }
        }
        Some(())
    }
    let mut result = Vec::new();
    for id in program.cfg().reachable_blocks() {
        for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()] {
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                let point = (instruction.address, index);
                if let Place::Memory { address, width } = &assignment.destination {
                    expression(address, point, 0, &mut result)?;
                    if result.len() >= 100_000 {
                        return None;
                    }
                    result.push(MemorySite {
                        instruction: point.0,
                        assignment: point.1,
                        address,
                        width: *width,
                        kind: AccessKind::Write,
                    });
                }
                expression(&assignment.value, point, 0, &mut result)?;
            }
        }
    }
    Some(result)
}

pub(super) struct StackViews {
    analysis: StackAnalysis,
    pub(super) views: Vec<StackView>,
    by_offset: BTreeMap<i64, usize>,
    pub(super) register: Reg,
}

impl StackViews {
    pub(super) fn recover(program: &Program, register: Reg) -> Option<Self> {
        if register.0 >= program.register_count() {
            return None;
        }
        let analysis = StackAnalysis::analyze(program, register);
        let lengths: BTreeMap<_, _> = program
            .instructions()
            .iter()
            .map(|i| (i.address, i.assignments.len()))
            .collect();
        let mut slots: BTreeMap<i64, StackView> = BTreeMap::new();
        for access in analysis.accesses() {
            // Structured control expressions currently have no instruction-site
            // annotation after compacting; leave those accesses unchanged.
            if access.assignment >= lengths[&access.instruction] {
                continue;
            }
            let view = slots.entry(access.offset).or_insert_with(|| StackView {
                name: String::new(),
                offset: access.offset,
                byte_size: 0,
                read_sites: 0,
                write_sites: 0,
                overlaps: Vec::new(),
            });
            view.byte_size = view.byte_size.max(access.width.bytes());
            match access.kind {
                AccessKind::Read => view.read_sites += 1,
                AccessKind::Write => view.write_sites += 1,
            }
            // Naming is optional; bound overlap reporting and generated code.
            if slots.len() > 256 {
                return None;
            }
        }
        let mut views: Vec<_> = slots.into_values().collect();
        if views.is_empty() {
            return None;
        }
        for (index, view) in views.iter_mut().enumerate() {
            view.name = format!("stack_{index}");
        }
        for a in 0..views.len() {
            for b in a + 1..views.len() {
                let overlaps = byte_overlap(
                    views[a].offset,
                    views[a].byte_size,
                    views[b].offset,
                    views[b].byte_size,
                );
                if overlaps {
                    views[a].overlaps.push(b);
                    views[b].overlaps.push(a);
                }
            }
        }
        let by_offset = views
            .iter()
            .enumerate()
            .map(|(i, v)| (v.offset, i))
            .collect();
        Some(Self {
            analysis,
            views,
            by_offset,
            register,
        })
    }

    pub(super) fn at(&self, point: Option<(u64, usize)>, address: &Expr) -> Option<&StackView> {
        let (instruction, assignment) = point?;
        let offset = self
            .analysis
            .offset_before(instruction, assignment, address)?;
        self.by_offset.get(&offset).map(|&index| &self.views[index])
    }
}

pub(super) const VIEW_HELPERS: &str = r#"
/* Views retain checked guest-memory accesses and may overlap or alias. */
struct nirvana_view { uint64_t address; };
static inline uint64_t nirvana_view_load(struct nirvana_memory *m, struct nirvana_view view, unsigned width) {
    return nirvana_load(m, view.address, width);
}
static inline void nirvana_view_store(struct nirvana_memory *m, struct nirvana_view view, unsigned width, uint64_t value) {
    nirvana_store(m, view.address, width, value);
}
"#;

// Replacing a pure address by a view can make its register computations dead.
// Follow register definitions from rendered reads and all faulting expressions;
// omit only pure assignments with no remaining consumer. This is conservative
// across ordering and CFG edges and does not promote or remove memory effects.
pub(super) fn rendered_reads(program: &Program, views: &Option<MemoryViews>) -> BTreeSet<usize> {
    fn read(
        expr: &Expr,
        point: Option<(u64, usize)>,
        views: &Option<MemoryViews>,
        result: &mut BTreeSet<usize>,
    ) {
        match expr {
            Expr::Const(_) => {}
            Expr::Register(reg) => {
                result.insert(reg.0);
            }
            Expr::Load { address, .. } => {
                if views.as_ref().and_then(|v| v.at(point, address)).is_none() {
                    read(address, point, views, result);
                }
            }
            Expr::Binary(_, l, r) => {
                read(l, point, views, result);
                read(r, point, views, result);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                read(condition, point, views, result);
                read(taken, point, views, result);
                read(not_taken, point, views, result);
            }
        }
    }
    let mut result = BTreeSet::new();
    type Definition<'a> = ((u64, usize), &'a Expr);
    let mut definitions: BTreeMap<usize, Vec<Definition<'_>>> = BTreeMap::new();
    for id in program.cfg().reachable_blocks() {
        for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()] {
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                let point = (instruction.address, index);
                match &assignment.destination {
                    Place::Register(reg) => {
                        definitions
                            .entry(reg.0)
                            .or_default()
                            .push((point, &assignment.value));
                        if assignment.value.uses_memory() {
                            read(&assignment.value, Some(point), views, &mut result);
                        }
                    }
                    Place::Memory { address, .. } => {
                        if views
                            .as_ref()
                            .and_then(|v| v.at(Some(point), address))
                            .is_none()
                        {
                            read(address, Some(point), views, &mut result);
                        }
                        read(&assignment.value, Some(point), views, &mut result);
                    }
                }
            }
            match &instruction.control {
                Control::Branch { condition, .. } => read(condition, None, views, &mut result),
                Control::Return(value) => read(value, None, views, &mut result),
                _ => {}
            }
        }
    }
    if let Some(views) = views {
        result.extend(views.registers().map(|r| r.0));
    }
    let mut pending: Vec<_> = result.iter().copied().collect();
    while let Some(reg) = pending.pop() {
        if let Some(defs) = definitions.get(&reg) {
            for &(point, expr) in defs {
                let mut dependencies = BTreeSet::new();
                read(expr, Some(point), views, &mut dependencies);
                for dependency in dependencies {
                    if result.insert(dependency) {
                        pending.push(dependency);
                    }
                }
            }
        }
    }
    result
}
