//! Plan C locals separately from expression/control printing.
//!
//! Storage coloring proves which values may share a C variable. Identity
//! evidence only splits those colors; it never introduces additional sharing.

use std::collections::{BTreeMap, BTreeSet};

use crate::allocation::allocate_locals;
use crate::ir::{Program, Reg, Width};
use crate::structure::Node;
use crate::value_role::infer;
use crate::value_width::ValueWidths;

use super::{LocalPlanStats, LocalValue, ReadableOptions};

pub(super) struct LocalPlan {
    pub names: BTreeMap<usize, String>,
    pub widths: BTreeMap<usize, Width>,
    pub slots: BTreeMap<usize, usize>,
    pub initial_slots: Vec<usize>,
    pub locals: Vec<LocalValue>,
    pub value_count: usize,
    pub stats: LocalPlanStats,
}

impl LocalPlan {
    pub fn build(
        program: &Program,
        parameters: &[Reg],
        read: &BTreeSet<usize>,
        mut names: BTreeMap<usize, String>,
        widths: &ValueWidths,
        nodes: &[Node],
        options: ReadableOptions,
    ) -> Self {
        let eligible: Vec<_> = read
            .iter()
            .filter(|reg| !names.contains_key(reg))
            .map(|&reg| Reg(reg))
            .collect();
        let storage = storage_colors(program, &eligible, widths, options.coalesce_locals);
        let storage_slots = storage.iter().copied().collect::<BTreeSet<_>>().len();
        let pairs: Vec<_> = eligible
            .iter()
            .copied()
            .zip(storage.iter().copied())
            .collect();
        let identities = options
            .coalesce_locals
            .then(|| crate::local_identity::refine(program, &pairs))
            .flatten();
        let refined = identities.as_ref().and_then(|ids| {
            // An independent consumer check: no missing value, invalid group,
            // or identity spanning two original storage colors is accepted.
            let groups = ids.groups();
            if groups > pairs.len() {
                return None;
            }
            let mut origins = BTreeMap::new();
            let mut result = Vec::with_capacity(pairs.len());
            for &(reg, origin) in &pairs {
                let group = ids.group(reg)?;
                if group >= groups
                    || origins
                        .insert(group, origin)
                        .is_some_and(|old| old != origin)
                {
                    return None;
                }
                result.push(group);
            }
            (origins.len() == groups).then_some(result)
        });
        let identity_groups = refined
            .as_ref()
            .map(|_| identities.as_ref().unwrap().groups());
        let colors = refined
            .as_ref()
            .map(|refined| semantic_colors(&eligible, &storage, refined, nodes))
            .unwrap_or_else(|| storage.clone());
        let mut groups: BTreeMap<usize, Vec<Reg>> = BTreeMap::new();
        let mut origins: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for ((&reg, &color), &origin) in eligible.iter().zip(&colors).zip(&storage) {
            groups.entry(color).or_default().push(reg);
            origins.entry(origin).or_default().insert(color);
        }
        let mut slots: BTreeMap<usize, usize> = eligible
            .iter()
            .zip(colors)
            .map(|(reg, color)| (reg.0, color))
            .collect();
        let roles = infer(nodes, |reg| slots.get(&reg.0).copied());
        let mut role_counts = BTreeMap::new();
        for role in roles.values() {
            *role_counts.entry(role.stem()).or_insert(0usize) += 1;
        }
        let single_local = groups.len() == 1;
        let mut serials = BTreeMap::new();
        let mut local_widths = BTreeMap::new();
        let mut locals = Vec::new();
        for (color, registers) in groups {
            let width = registers
                .iter()
                .map(|&reg| widths.width(reg))
                .max_by_key(|width| width.bits())
                .unwrap_or(Width::U64);
            let role = roles.get(&color).copied();
            let name = if options.compact_memory {
                if let Some(role) = role {
                    let stem = role.stem();
                    if role_counts[stem] == 1 {
                        stem.into()
                    } else {
                        let serial = serials.entry(stem).or_insert(0usize);
                        let name = format!("{stem}{serial}");
                        *serial += 1;
                        name
                    }
                } else if single_local {
                    "value".into()
                } else {
                    format!("value{color}")
                }
            } else {
                format!("v{color}")
            };
            for reg in &registers {
                names.insert(reg.0, name.clone());
                local_widths.insert(reg.0, width);
            }
            locals.push(LocalValue {
                register: registers[0],
                registers,
                name,
                width,
                role,
            });
        }
        let stats = LocalPlanStats {
            storage_slots,
            identity_groups,
            local_variables: locals.len(),
            split_storage_groups: origins.values().filter(|colors| colors.len() > 1).count(),
        };
        let mut initial_slots = Vec::new();
        for (index, reg) in parameters.iter().enumerate() {
            if read.contains(&reg.0) {
                let slot = locals.len() + index;
                slots.insert(reg.0, slot);
                initial_slots.push(slot);
            }
        }
        Self {
            names,
            widths: local_widths,
            slots,
            initial_slots,
            locals,
            value_count: eligible.len(),
            stats,
        }
    }
}

fn storage_colors(
    program: &Program,
    eligible: &[Reg],
    widths: &ValueWidths,
    coalesce: bool,
) -> Vec<usize> {
    let mut colors: Vec<_> = (0..eligible.len()).collect();
    if coalesce {
        let mut next_color = 0;
        for width in [Width::U64, Width::U32, Width::U16, Width::U8] {
            let members: Vec<_> = eligible
                .iter()
                .enumerate()
                .filter(|(_, reg)| widths.width(**reg) == width)
                .map(|(index, &reg)| (index, reg))
                .collect();
            let registers: Vec<_> = members.iter().map(|(_, reg)| *reg).collect();
            let allocated = allocate_locals(program, &registers).and_then(|allocation| {
                registers
                    .iter()
                    .map(|&reg| allocation.color(reg))
                    .collect::<Option<Vec<_>>>()
            });
            let palette = allocated.unwrap_or_else(|| (0..members.len()).collect());
            let size = palette.iter().max().map_or(0, |color| color + 1);
            for ((index, _), color) in members.into_iter().zip(palette) {
                colors[index] = next_color + color;
            }
            next_color += size;
        }
    }
    colors
}

// Keep anonymous components in their original shared storage. Separate a
// component only when its own uses provide positive role evidence. In
// particular, a byte read used before loop initialization must not inherit the
// later invariant limit's name just because both fit one storage color.
fn semantic_colors(
    eligible: &[Reg],
    storage: &[usize],
    identities: &[usize],
    nodes: &[Node],
) -> Vec<usize> {
    let slots: BTreeMap<_, _> = eligible
        .iter()
        .zip(identities)
        .map(|(r, &id)| (r.0, id))
        .collect();
    let roles = infer(nodes, |reg| slots.get(&reg.0).copied());
    let keys: BTreeSet<_> = storage
        .iter()
        .zip(identities)
        .map(|(&origin, &id)| (origin, roles.contains_key(&id).then_some(id)))
        .collect();
    let palette: BTreeMap<_, _> = keys
        .into_iter()
        .enumerate()
        .map(|(index, key)| (key, index))
        .collect();
    storage
        .iter()
        .zip(identities)
        .map(|(&origin, &id)| palette[&(origin, roles.contains_key(&id).then_some(id))])
        .collect()
}
