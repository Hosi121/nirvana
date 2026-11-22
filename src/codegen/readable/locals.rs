//! Plan C locals separately from expression/control printing.
//!
//! Storage coloring proves which values may share a C variable. Identity
//! evidence only splits those colors; it never introduces additional sharing.

use std::collections::{BTreeMap, BTreeSet};

use crate::control_flow::structure::Node;
use crate::dataflow::allocation::allocate_locals_with_hints;
use crate::dataflow::stack_cells::CellBindings;
use crate::dataflow::stack_role::StackRoles;
use crate::dataflow::value_role::{ValueRole, infer};
use crate::dataflow::value_width::ValueWidths;
use crate::model::ir::{BinaryOp, Expr, Place, Program, Reg, Width};

use super::{LocalPlanStats, LocalValue, ReadableOptions};

pub(super) struct LocalPlan {
    pub names: BTreeMap<usize, String>,
    pub widths: BTreeMap<usize, Width>,
    pub slots: BTreeMap<usize, usize>,
    pub initial_slots: Vec<usize>,
    pub locals: Vec<LocalValue>,
    pub value_count: usize,
    pub stats: LocalPlanStats,
    pub stack_roles: Option<StackRoles>,
    pub stack_cells: Option<CellBindings>,
}
pub(super) struct LayoutOptions {
    pub readable: ReadableOptions,
    pub prefer_updates: bool,
}

impl LocalPlan {
    pub fn build(
        program: &Program,
        parameters: &[Reg],
        read: &BTreeSet<usize>,
        mut names: BTreeMap<usize, String>,
        widths: &ValueWidths,
        nodes: &[Node],
        layout: LayoutOptions,
    ) -> Self {
        let LayoutOptions {
            readable: options,
            prefer_updates,
        } = layout;
        let eligible: Vec<_> = read
            .iter()
            .filter(|reg| !names.contains_key(reg))
            .map(|&reg| Reg(reg))
            .collect();
        let stack_roles = options
            .stack_register
            .filter(|_| options.coalesce_locals)
            .and_then(|stack| StackRoles::analyze(program, stack, nodes));
        let stack_cells = options
            .stack_register
            .filter(|_| options.coalesce_locals)
            .and_then(|stack| CellBindings::analyze(program, stack, &eligible));
        let StorageColors {
            colors: storage,
            verified: verified_storage_pools,
            fallbacks: storage_verification_fallbacks,
            update_hint_pairs,
        } = storage_colors(
            program,
            &eligible,
            widths,
            options.coalesce_locals,
            stack_roles.as_ref(),
            prefer_updates,
        );
        let storage_slots = storage.iter().copied().collect::<BTreeSet<_>>().len();
        let pairs: Vec<_> = eligible
            .iter()
            .copied()
            .zip(storage.iter().copied())
            .collect();
        let identities = options
            .coalesce_locals
            .then(|| crate::dataflow::local_identity::refine(program, &pairs))
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
            .map(|refined| {
                semantic_colors(&eligible, &storage, refined, nodes, stack_roles.as_ref())
            })
            .unwrap_or_else(|| storage.clone());
        let source_candidate = (stack_roles.is_some() || stack_cells.is_some())
            .then(|| {
                let initial: Vec<_> = eligible
                    .iter()
                    .copied()
                    .zip(colors.iter().copied())
                    .collect();
                let lineages =
                    source_lineages(&eligible, stack_roles.as_ref(), stack_cells.as_ref());
                crate::dataflow::source_locals::recover(program, &initial, &lineages)
            })
            .flatten();
        // The candidate covers every eligible register and is independently
        // checked as a whole. Width selection below uses the maximum member
        // width, including when a candidate spans old width pools/colors.
        let colors = source_candidate
            .as_ref()
            .and_then(|candidate| eligible.iter().map(|&reg| candidate.color(reg)).collect())
            .unwrap_or(colors);
        // A direct copy is only a sharing preference. The same independent
        // storage and pure-comparison checks authorize this complete map.
        let copy_candidate = options
            .coalesce_locals
            .then(|| {
                let initial: Vec<_> = eligible
                    .iter()
                    .copied()
                    .zip(colors.iter().copied())
                    .collect();
                let by_register: BTreeMap<_, _> = initial.iter().map(|(r, c)| (r.0, *c)).collect();
                let inferred = crate::dataflow::value_role::infer_with_arithmetic(nodes, |r| {
                    by_register.get(&r.0).copied()
                });
                let roles: Vec<_> = initial
                    .iter()
                    .filter_map(|(r, c)| Some((*r, *inferred.get(c)?)))
                    .collect();
                let widths: Vec<_> = eligible.iter().map(|&r| (r, widths.width(r))).collect();
                crate::dataflow::source_locals::recover_copies(
                    program,
                    &initial,
                    &widths,
                    &roles,
                    &source_lineages(&eligible, stack_roles.as_ref(), stack_cells.as_ref()),
                )
            })
            .flatten();
        let colors = copy_candidate
            .as_ref()
            .and_then(|candidate| eligible.iter().map(|&reg| candidate.color(reg)).collect())
            .unwrap_or(colors);
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
        let inferred = crate::dataflow::value_role::infer_with_arithmetic(nodes, |reg| {
            slots.get(&reg.0).copied()
        });
        let roles: BTreeMap<_, _> = groups
            .iter()
            .filter_map(|(&color, registers)| {
                let candidate = inferred.get(&color).copied();
                let candidate = if candidate == Some(ValueRole::Quotient)
                    && stack_roles.as_ref().is_some_and(|stack| {
                        registers
                            .iter()
                            .any(|&reg| stack.register_role(reg).is_some())
                    }) {
                    None
                } else {
                    candidate
                };
                Some((
                    color,
                    local_role(
                        candidate,
                        registers,
                        stack_roles.as_ref(),
                        stack_cells.as_ref(),
                    )?,
                ))
            })
            .collect();
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
                address_width: None,
                role,
            });
        }
        let stats = LocalPlanStats {
            storage_slots,
            identity_groups,
            local_variables: locals.len(),
            split_storage_groups: origins.values().filter(|colors| colors.len() > 1).count(),
            verified_storage_pools,
            storage_verification_fallbacks,
            update_hint_pairs,
            source_allocation: source_candidate.as_ref().map(|candidate| candidate.stats()),
            copy_allocation: copy_candidate.as_ref().map(|candidate| candidate.stats()),
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
            stack_roles,
            stack_cells,
        }
    }
}

struct StorageColors {
    colors: Vec<usize>,
    verified: usize,
    fallbacks: usize,
    update_hint_pairs: usize,
}

fn storage_colors(
    program: &Program,
    eligible: &[Reg],
    widths: &ValueWidths,
    coalesce: bool,
    stack_roles: Option<&StackRoles>,
    prefer_updates: bool,
) -> StorageColors {
    let mut colors: Vec<_> = (0..eligible.len()).collect();
    let mut verified = 0;
    let mut fallbacks = 0;
    let mut update_hint_pairs = 0;
    if coalesce {
        let mut next_color = 0;
        for width in [Width::U64, Width::U32, Width::U16, Width::U8] {
            let members: Vec<_> = eligible
                .iter()
                .enumerate()
                .filter(|(_, reg)| widths.width(**reg) == width)
                .map(|(index, &reg)| (index, reg))
                .collect();
            if members.is_empty() {
                continue;
            }
            let registers: Vec<_> = members.iter().map(|(_, reg)| *reg).collect();
            let mut lineages = BTreeMap::<usize, Vec<Reg>>::new();
            if let Some(roles) = stack_roles {
                for &reg in &registers {
                    if let Some(web) = roles.register_web(reg) {
                        lineages.entry(web).or_default().push(reg);
                    }
                }
            }
            let mut hints: Vec<_> = lineages
                .values()
                .flat_map(|members| members.windows(2).map(|pair| (pair[0], pair[1])))
                .collect();
            // Existing spill/reload lineages keep their preference set. An
            // optional layout instead connects register-only arithmetic roots.
            if prefer_updates && hints.is_empty() {
                hints = update_hints(program, &registers).unwrap_or_default();
                update_hint_pairs += hints.len();
            }
            let allocated = checked_colors(program, &registers, &hints).or_else(|| {
                fallbacks += 1;
                if hints.is_empty() {
                    None
                } else {
                    checked_colors(program, &registers, &[])
                }
            });
            verified += usize::from(allocated.is_some());
            let palette = allocated.unwrap_or_else(|| (0..members.len()).collect());
            let size = palette.iter().max().map_or(0, |color| color + 1);
            for ((index, _), color) in members.into_iter().zip(palette) {
                colors[index] = next_color + color;
            }
            next_color += size;
        }
    }
    StorageColors {
        colors,
        verified,
        fallbacks,
        update_hint_pairs,
    }
}

fn update_hints(program: &Program, registers: &[Reg]) -> Option<Vec<(Reg, Reg)>> {
    let eligible: BTreeSet<_> = registers.iter().map(|r| r.0).collect();
    let mut hints = BTreeSet::new();
    let mut work = 100_000usize;
    for instruction in program.instructions() {
        for assignment in &instruction.assignments {
            work = work.checked_sub(1)?;
            let Place::Register(destination) = assignment.destination else {
                continue;
            };
            if !eligible.contains(&destination.0) {
                continue;
            }
            let Expr::Binary(op, left, right) = &assignment.value else {
                continue;
            };
            let commutative = matches!(
                op,
                BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor
            );
            if !commutative
                && !matches!(
                    op,
                    BinaryOp::Sub | BinaryOp::Shl | BinaryOp::Shr | BinaryOp::AShr
                )
            {
                continue;
            }
            let source = match (left.as_ref(), right.as_ref()) {
                (Expr::Register(source), _) if eligible.contains(&source.0) => *source,
                (_, Expr::Register(source)) if commutative && eligible.contains(&source.0) => {
                    *source
                }
                _ => continue,
            };
            if source != destination {
                hints.insert((destination.0.min(source.0), destination.0.max(source.0)));
            }
            if hints.len() > 8192 {
                return None;
            }
        }
    }
    Some(hints.into_iter().map(|(a, b)| (Reg(a), Reg(b))).collect())
}

fn checked_colors(
    program: &Program,
    registers: &[Reg],
    hints: &[(Reg, Reg)],
) -> Option<Vec<usize>> {
    let allocation = allocate_locals_with_hints(program, registers, hints)?;
    let colors: Vec<_> = registers
        .iter()
        .map(|&reg| allocation.color(reg))
        .collect::<Option<_>>()?;
    if colors.iter().any(|&color| color >= registers.len()) {
        return None;
    }
    let mapping: Vec<_> = registers
        .iter()
        .copied()
        .zip(colors.iter().copied())
        .collect();
    crate::dataflow::allocation_verify::validate(program, &mapping).ok()?;
    Some(colors)
}

// Share components with the same role within their original storage color.
// Split incompatible roles and anonymous values, rather than giving every
// pointer reload a new C declaration. A byte used before loop initialization
// must not inherit the later invariant limit's name merely because both fit.
fn semantic_colors(
    eligible: &[Reg],
    storage: &[usize],
    identities: &[usize],
    nodes: &[Node],
    stack_roles: Option<&StackRoles>,
) -> Vec<usize> {
    let slots: BTreeMap<_, _> = eligible
        .iter()
        .zip(identities)
        .map(|(r, &id)| (r.0, id))
        .collect();
    let roles = infer(nodes, |reg| slots.get(&reg.0).copied());
    let role = |reg, id| {
        combine_roles(
            roles.get(&id).copied(),
            stack_roles.and_then(|stack| stack.register_role(reg)),
        )
        .map(ValueRole::stem)
    };
    let keys: BTreeSet<_> = storage
        .iter()
        .zip(identities)
        .zip(eligible)
        .map(|((&origin, &id), &reg)| (origin, role(reg, id)))
        .collect();
    let palette: BTreeMap<_, _> = keys
        .into_iter()
        .enumerate()
        .map(|(index, key)| (key, index))
        .collect();
    storage
        .iter()
        .zip(identities)
        .zip(eligible)
        .map(|((&origin, &id), &reg)| palette[&(origin, role(reg, id))])
        .collect()
}

fn combine_roles(a: Option<ValueRole>, b: Option<ValueRole>) -> Option<ValueRole> {
    match (a, b) {
        (Some(a), Some(b)) if a != b => None,
        (Some(role), _) | (_, Some(role)) => Some(role),
        _ => None,
    }
}

fn local_role(
    inferred: Option<ValueRole>,
    registers: &[Reg],
    stack: Option<&StackRoles>,
    cells: Option<&CellBindings>,
) -> Option<ValueRole> {
    let Some(stack) = stack else {
        return inferred;
    };
    if registers
        .iter()
        .any(|&reg| matches!((inferred, stack.register_role(reg)), (Some(a), Some(b)) if a != b))
    {
        return None;
    }
    let location = registers
        .first()
        .and_then(|&reg| binding_location(Some(stack), cells, reg));
    if location.is_some_and(|location| {
        registers
            .iter()
            .all(|&reg| binding_location(Some(stack), cells, reg) == Some(location))
    }) {
        let mut agreed = None;
        for &reg in registers {
            if let Some(role) = stack.register_role(reg) {
                if agreed.is_some_and(|old| old != role) {
                    return None;
                }
                agreed = Some(role);
            }
        }
        return combine_roles(inferred, agreed);
    }
    let first = stack.register_role(*registers.first()?);
    let unanimous = registers
        .iter()
        .all(|&reg| stack.register_role(reg) == first);
    combine_roles(inferred, if unanimous { first } else { None })
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum SourceKey {
    Location(crate::dataflow::stack_values::StackLocation),
    Web(usize),
    Register(usize),
}

// Distinct reaching-store webs can be updates of one source variable. A shared
// exact cell is a broader naming preference when its known roles agree. Reused
// cells remain ambiguous source identities; the allocation checker, not this
// heuristic, determines whether their values may share C storage.
fn source_lineages(
    eligible: &[Reg],
    roles: Option<&StackRoles>,
    cells: Option<&CellBindings>,
) -> Vec<(Reg, usize)> {
    let bindings: Vec<_> = eligible
        .iter()
        .filter_map(|&reg| {
            let web = roles.and_then(|roles| roles.register_web(reg));
            Some((reg, web, binding_location(roles, cells, reg)?))
        })
        .collect();
    let mut by_location = BTreeMap::<_, BTreeSet<_>>::new();
    for &(reg, _, location) in &bindings {
        let known = by_location.entry(location).or_default();
        if let Some(role) = roles.and_then(|roles| roles.register_role(reg)) {
            known.insert(role.stem());
        }
    }
    let mut labels = BTreeMap::new();
    bindings
        .into_iter()
        .map(|(reg, web, location)| {
            let key = if by_location[&location].len() <= 1 {
                SourceKey::Location(location)
            } else {
                web.map_or(SourceKey::Register(reg.0), SourceKey::Web)
            };
            let next = labels.len();
            (reg, *labels.entry(key).or_insert(next))
        })
        .collect()
}

fn binding_location(
    roles: Option<&StackRoles>,
    cells: Option<&CellBindings>,
    register: Reg,
) -> Option<crate::dataflow::stack_values::StackLocation> {
    roles
        .and_then(|roles| roles.web_location(roles.register_web(register)?))
        .or_else(|| cells.and_then(|cells| cells.location(register)))
}
