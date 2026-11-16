//! Stack-view discovery and register dependencies for C rendering.

use crate::ir::{AccessKind, Control, Expr, Place, Program, Reg};
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
                let overlaps = (0..views[a].byte_size).any(|i| {
                    (0..views[b].byte_size).any(|j| {
                        views[a].offset.wrapping_add(i as i64)
                            == views[b].offset.wrapping_add(j as i64)
                    })
                });
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
pub(super) fn rendered_reads(program: &Program, views: &Option<StackViews>) -> BTreeSet<usize> {
    fn read(
        expr: &Expr,
        point: Option<(u64, usize)>,
        views: &Option<StackViews>,
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
        result.insert(views.register.0);
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
