//! Bounded associations between local values and exact stack load locations.
//!
//! A binding describes the location of a successful direct load, possibly
//! followed by exact register copies. It says nothing about the loaded value,
//! reaching stores, memory equality, allocation, source names/types or ownership.
//! Unknown/overlapping stores deliberately do not invalidate load locations.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::allocation_verify;
use crate::ir::{Control, Expr, Place, Program, Reg};
use crate::stack::StackAnalysis;
use crate::stack_values::StackLocation;

const MAX_ELIGIBLE: usize = 4_096;
const MAX_REGISTERS: usize = 65_536;
const MAX_ACTIVE: usize = 8_192;
const MAX_BLOCKS: usize = 4_096;
const MAX_POINTS: usize = 100_000;
const MAX_ITEMS: usize = 250_000;
const MAX_DEPTH: usize = 128;
const MAX_WORK: usize = 2_000_000;

/// Location candidates for exactly the supplied eligible registers.
///
/// These are weaker than reaching-store/value relations. They do not authorize
/// sharing C storage or replacing a load with a previous value. The executable
/// IR and every actual memory access remain unchanged.
#[derive(Clone, Debug, Default)]
pub struct CellBindings {
    locations: BTreeMap<usize, StackLocation>,
}

impl CellBindings {
    /// Inputs/parameters must be excluded by the caller. The independent
    /// allocation checker validates identity storage first, rejecting any
    /// reachable eligible read without a prior definition, including entry
    /// backedges. Invalid inputs or own/upstream exhaustion return None; no
    /// partial set of associations is returned.
    pub fn analyze(program: &Program, stack_register: Reg, eligible: &[Reg]) -> Option<Self> {
        if eligible.len() > MAX_ELIGIBLE
            || program.register_count() > MAX_REGISTERS
            || stack_register.0 >= program.register_count()
        {
            return None;
        }
        let mut indices = BTreeMap::new();
        for &reg in eligible {
            if reg.0 >= program.register_count() || indices.insert(reg.0, 0).is_some() {
                return None;
            }
        }
        for (index, value) in indices.values_mut().enumerate() {
            *value = index;
        }
        let mut work = Work(MAX_WORK);
        validate_program(program, &mut work)?;
        let identity: Vec<_> = indices.keys().map(|&id| (Reg(id), id)).collect();
        allocation_verify::validate(program, &identity).ok()?;
        let stack = StackAnalysis::try_analyze(program, stack_register)?;

        // References, not cloned expressions. Every reachable static write
        // counts, even when an equal expression writes the same register twice.
        let mut writes = vec![Writes::None; indices.len()];
        for id in program.cfg().reachable_blocks() {
            work.spend(1)?;
            for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()]
            {
                for (assignment, value) in instruction.assignments.iter().enumerate() {
                    work.spend(1)?;
                    if let Place::Register(reg) = value.destination
                        && let Some(&index) = indices.get(&reg.0)
                    {
                        writes[index] = match writes[index] {
                            Writes::None => Writes::Once {
                                instruction: instruction.address,
                                assignment,
                                value: &value.value,
                            },
                            Writes::Once { .. } | Writes::Multiple => Writes::Multiple,
                        };
                    }
                }
            }
        }
        let mut bindings = vec![None; indices.len()];
        let mut copies: Vec<Vec<usize>> = (0..indices.len()).map(|_| Vec::new()).collect();
        let mut pending = VecDeque::new();
        for (index, definition) in writes.iter().enumerate() {
            work.spend(1)?;
            let Writes::Once {
                instruction,
                assignment,
                value,
            } = definition
            else {
                continue;
            };
            match value {
                Expr::Load { address, width } => {
                    if pure_address(address, &mut work)?
                        && let Some(offset) =
                            stack.offset_before(*instruction, *assignment, address)
                    {
                        bindings[index] = Some(StackLocation {
                            offset,
                            width: *width,
                        });
                        pending.push_back(index);
                    }
                }
                Expr::Register(source) => {
                    if let Some(&source) = indices.get(&source.0)
                        && matches!(writes[source], Writes::Once { .. })
                    {
                        copies[source].push(index);
                    }
                }
                Expr::Const(_) | Expr::Binary(_, _, _) | Expr::Select { .. } => {}
            }
        }
        // Each copy has one predecessor. Only seeded forward paths are
        // followed; unseeded cycles cannot manufacture an association.
        while let Some(source) = pending.pop_front() {
            work.spend(1)?;
            for &destination in &copies[source] {
                work.spend(1)?;
                if bindings[destination].is_none() {
                    bindings[destination] = bindings[source];
                    pending.push_back(destination);
                }
            }
        }
        Some(Self {
            locations: indices
                .into_iter()
                .filter_map(|(reg, index)| Some((reg, bindings[index]?)))
                .collect(),
        })
    }

    pub fn location(&self, register: Reg) -> Option<StackLocation> {
        self.locations.get(&register.0).copied()
    }
}

#[derive(Clone, Copy)]
enum Writes<'a> {
    None,
    Once {
        instruction: u64,
        assignment: usize,
        value: &'a Expr,
    },
    Multiple,
}

struct Work(usize);
impl Work {
    fn spend(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}

// Validate all syntax, including unreachable instructions and lazy branches,
// before invoking analyses that retain point states or traverse recursively.
// Neither register IDs nor register_count are used as dense indices here.
fn validate_program(program: &Program, work: &mut Work) -> Option<()> {
    if program.instructions().len() > MAX_POINTS || program.cfg().blocks().len() > MAX_BLOCKS {
        return None;
    }
    let mut points = program.instructions().len();
    let mut items = points;
    let mut active = BTreeSet::new();
    for instruction in program.instructions() {
        work.spend(1)?;
        points = points.checked_add(instruction.assignments.len())?;
        if points > MAX_POINTS {
            return None;
        }
        for assignment in &instruction.assignments {
            work.spend(1)?;
            items = items.checked_add(1)?;
            if items > MAX_ITEMS {
                return None;
            }
            match &assignment.destination {
                Place::Register(reg) => {
                    if reg.0 >= program.register_count() {
                        return None;
                    }
                    active.insert(reg.0);
                    if active.len() > MAX_ACTIVE {
                        return None;
                    }
                }
                Place::Memory { address, .. } => {
                    validate_expression(address, program, &mut items, &mut active, work)?;
                }
            }
            validate_expression(&assignment.value, program, &mut items, &mut active, work)?;
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &instruction.control
        {
            validate_expression(condition, program, &mut items, &mut active, work)?;
        }
    }
    Some(())
}

fn validate_expression(
    root: &Expr,
    program: &Program,
    items: &mut usize,
    active: &mut BTreeSet<usize>,
    work: &mut Work,
) -> Option<()> {
    let mut pending = vec![(root, 1usize)];
    while let Some((expression, depth)) = pending.pop() {
        work.spend(1)?;
        *items = items.checked_add(1)?;
        if depth > MAX_DEPTH || *items > MAX_ITEMS {
            return None;
        }
        match expression {
            Expr::Const(_) => {}
            Expr::Register(reg) => {
                if reg.0 >= program.register_count() {
                    return None;
                }
                active.insert(reg.0);
                if active.len() > MAX_ACTIVE {
                    return None;
                }
            }
            Expr::Binary(_, left, right) => {
                pending.extend([(right.as_ref(), depth + 1), (left.as_ref(), depth + 1)]);
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (not_taken.as_ref(), depth + 1),
                (taken.as_ref(), depth + 1),
                (condition.as_ref(), depth + 1),
            ]),
        }
    }
    Some(())
}

fn pure_address(root: &Expr, work: &mut Work) -> Option<bool> {
    let mut pending = vec![root];
    let mut nodes = 0usize;
    while let Some(expression) = pending.pop() {
        work.spend(1)?;
        nodes = nodes.checked_add(1)?;
        match expression {
            Expr::Load { .. } => return Some(false),
            Expr::Binary(_, left, right) => pending.extend([right.as_ref(), left.as_ref()]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([not_taken.as_ref(), taken.as_ref(), condition.as_ref()]),
            Expr::Const(_) | Expr::Register(_) => {}
        }
    }
    // Reserve the bounded affine query's traversal as part of this pass too.
    work.spend(nodes)?;
    Some(true)
}
