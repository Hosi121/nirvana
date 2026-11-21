//! Recover candidate source-local storage groups, independently validated.
//!
//! Lineage labels are naming hints, not equal-value facts or recovered source
//! identities. A proposal may merge across old colors, but only the independent
//! allocation correspondence checker can authorize the resulting storage map.
//! Executable IR, memory operations, order and control flow remain unchanged.

use std::collections::{BTreeMap, BTreeSet};

use crate::dataflow::allocation_verify::{self, AllocationError, AllocationEvidence};
use crate::model::ir::{BinaryOp, Control, Expr, Place, Program, Reg};

const MAX_REGISTERS: usize = 4096;
const MAX_LINEAGES: usize = 4096;
const MAX_VALIDATIONS: usize = 16;
const MAX_WORK: usize = 1_000_000;

/// Lexicographic heuristic cost, not measured accuracy against source code.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct SourceScore {
    /// Excess distinct known lineage classes occupying each slot. Unknown
    /// registers contribute no source identity evidence to this count.
    pub mixed: usize,
    /// Excess distinct slots occupied by each known lineage.
    pub fragments: usize,
    pub locals: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceStats {
    pub before: SourceScore,
    pub after: SourceScore,
    /// Number of distinct lineages restored to their initial-color partition.
    pub rollbacks: usize,
}

#[derive(Clone, Debug)]
pub struct SourceAllocation {
    colors: BTreeMap<usize, usize>,
    stats: SourceStats,
    evidence: AllocationEvidence,
}

impl SourceAllocation {
    pub fn color(&self, register: Reg) -> Option<usize> {
        self.colors.get(&register.0).copied()
    }

    pub fn stats(&self) -> SourceStats {
        self.stats
    }

    /// Evidence for the complete returned mapping, returned by value.
    pub fn evidence(&self) -> AllocationEvidence {
        self.evidence
    }
}

/// Propose one slot per known lineage and separate unknown occupants by their
/// old color. Invalid inputs, exhausted resources, no strict score improvement,
/// and unexpected checker failures all return None: callers keep `initial`.
///
/// A failed read, or a newly identical pair of pure comparison operands,
/// blocks that entire lineage from merging across initial colors.
/// Such a partition refines the validated initial mapping; other lineage merges
/// can still survive. At most 16 proposal/check rounds, including the initial
/// check, are performed. The checker independently bounds each invocation. Storage
/// widths and C rendering are the consumer's responsibility.
pub fn recover(
    program: &Program,
    initial: &[(Reg, usize)],
    lineages: &[(Reg, usize)],
) -> Option<SourceAllocation> {
    if initial.len() > MAX_REGISTERS || lineages.len() > MAX_LINEAGES {
        return None;
    }
    allocation_verify::validate(program, initial).ok()?;
    let mut work = Work(MAX_WORK);
    work.spend(initial.len())?;
    // The checker has already checked distinct valid original registers.
    let initial: BTreeMap<_, _> = initial.iter().map(|(reg, color)| (reg.0, *color)).collect();
    let mut known = BTreeMap::new();
    for &(reg, lineage) in lineages {
        work.spend(1)?;
        if !initial.contains_key(&reg.0) || known.insert(reg.0, lineage).is_some() {
            return None;
        }
    }
    let before = score(&initial, &known, &mut work)?;
    let mut blocked = BTreeSet::new();
    for _ in 1..MAX_VALIDATIONS {
        let candidate = propose(&initial, &known, &blocked, &mut work)?;
        let after = score(&candidate, &known, &mut work)?;
        if after >= before {
            return None;
        }
        if let Some(lineage) =
            comparison_rollback(program, &initial, &candidate, &known, &mut work)?
        {
            work.spend(1)?;
            if !blocked.insert(lineage) {
                return None;
            }
            continue;
        }
        work.spend(candidate.len())?;
        let mapping: Vec<_> = candidate
            .iter()
            .map(|(&reg, &color)| (Reg(reg), color))
            .collect();
        match allocation_verify::validate(program, &mapping) {
            Ok(evidence) => {
                return Some(SourceAllocation {
                    colors: candidate,
                    stats: SourceStats {
                        before,
                        after,
                        rollbacks: blocked.len(),
                    },
                    evidence,
                });
            }
            Err(AllocationError::ReadCorrespondence { register, .. }) => {
                let lineage = *known.get(&register.0)?;
                work.spend(1)?;
                if !blocked.insert(lineage) {
                    return None;
                }
            }
            Err(_) => return None,
        }
    }
    None
}

/// Prefer sharing current C colors connected by direct register copies.
/// Copies provide proposal hints only; `recover` retains the unchanged MUST
/// correspondence check and pure-comparison rollback. Existing color groups
/// stay whole, and merges preserve their maximum width, compatible roles and
/// previously known source/stack lineage classes. Copy classes are hints only.
/// Any malformed metadata or exhausted bound discards the entire proposal.
pub fn recover_copies(
    program: &Program,
    initial: &[(Reg, usize)],
    widths: &[(Reg, crate::model::ir::Width)],
    roles: &[(Reg, crate::dataflow::value_role::ValueRole)],
    lineages: &[(Reg, usize)],
) -> Option<SourceAllocation> {
    const MAX_COPIES: usize = 4096;
    if initial.len() > MAX_REGISTERS
        || widths.len() != initial.len()
        || roles.len() > MAX_REGISTERS
        || lineages.len() > MAX_LINEAGES
        || program.instructions().len() > allocation_verify::MAX_POINTS
        || program.cfg().blocks().len() > allocation_verify::MAX_BLOCKS
    {
        return None;
    }
    let mut work = Work(MAX_WORK);
    let mut by_register = BTreeMap::new();
    let mut color_ids = BTreeMap::new();
    for &(reg, color) in initial {
        work.spend(1)?;
        if reg.0 >= program.register_count() || by_register.insert(reg.0, color).is_some() {
            return None;
        }
        let next = color_ids.len();
        color_ids.entry(color).or_insert(next);
    }
    let mut group_widths = vec![0; color_ids.len()];
    let mut seen = BTreeSet::new();
    for &(reg, width) in widths {
        work.spend(1)?;
        let color = *by_register.get(&reg.0)?;
        if !seen.insert(reg.0) {
            return None;
        }
        let index = color_ids[&color];
        group_widths[index] = group_widths[index].max(width.bits());
    }
    let mut group_roles = vec![None; color_ids.len()];
    let mut conflicts = vec![false; color_ids.len()];
    seen.clear();
    for &(reg, role) in roles {
        work.spend(1)?;
        let color = *by_register.get(&reg.0)?;
        if !seen.insert(reg.0) {
            return None;
        }
        let index = color_ids[&color];
        if group_roles[index].is_some_and(|old| old != role) {
            conflicts[index] = true;
        }
        group_roles[index] = Some(role);
    }
    let mut group_lineages = vec![None; color_ids.len()];
    seen.clear();
    for &(reg, lineage) in lineages {
        work.spend(1)?;
        let color = *by_register.get(&reg.0)?;
        if !seen.insert(reg.0) {
            return None;
        }
        let index = color_ids[&color];
        if group_lineages[index].is_some_and(|old| old != lineage) {
            conflicts[index] = true;
        }
        group_lineages[index] = Some(lineage);
    }
    let mut parents: Vec<_> = (0..color_ids.len()).collect();
    let mut copies = 0usize;
    let mut merged = false;
    let cfg = program.cfg();
    work.spend(cfg.blocks().len().checked_mul(3)?)?;
    for block in cfg.reachable_blocks() {
        for instruction in &program.instructions()[cfg.block(block).instructions.clone()] {
            work.spend(1)?;
            for assignment in &instruction.assignments {
                work.spend(1)?;
                let (Place::Register(destination), Expr::Register(source)) =
                    (&assignment.destination, &assignment.value)
                else {
                    continue;
                };
                let (Some(a), Some(b)) =
                    (by_register.get(&destination.0), by_register.get(&source.0))
                else {
                    continue;
                };
                copies = copies.checked_add(1)?;
                if copies > MAX_COPIES {
                    return None;
                }
                let a = copy_root(&mut parents, color_ids[a], &mut work)?;
                let b = copy_root(&mut parents, color_ids[b], &mut work)?;
                if a == b
                    || group_widths[a] != group_widths[b]
                    || conflicts[a]
                    || conflicts[b]
                    || matches!((group_roles[a], group_roles[b]), (Some(a), Some(b)) if a != b)
                    || matches!((group_lineages[a], group_lineages[b]), (Some(a), Some(b)) if a != b)
                {
                    continue;
                }
                let (keep, remove) = if a < b { (a, b) } else { (b, a) };
                parents[remove] = keep;
                group_roles[keep] = group_roles[keep].or(group_roles[remove]);
                group_lineages[keep] = group_lineages[keep].or(group_lineages[remove]);
                merged = true;
            }
        }
    }
    if !merged {
        return None;
    }
    let mut lineages = Vec::with_capacity(initial.len());
    for &(reg, color) in initial {
        work.spend(1)?;
        lineages.push((reg, copy_root(&mut parents, color_ids[&color], &mut work)?));
    }
    recover(program, initial, &lineages)
}

fn copy_root(parents: &mut [usize], mut index: usize, work: &mut Work) -> Option<usize> {
    while parents[index] != index {
        work.spend(1)?;
        parents[index] = parents[parents[index]];
        index = parents[index];
    }
    Some(index)
}

// Equal-value copies may legally share abstract u64 storage, but a new C
// spelling such as `value == value` is rejected by strict C compilers. Preserve
// the initial partition for the responsible lineage instead of rewriting the
// expression: folding it could discard reads or create unused C declarations.
// The successful initial checker call bounds the whole program and expression
// depth before this recursive traversal; every additional visit has its own
// shared work charge, including comparisons repeated in nested expressions.
fn comparison_rollback(
    program: &Program,
    initial: &BTreeMap<usize, usize>,
    candidate: &BTreeMap<usize, usize>,
    known: &BTreeMap<usize, usize>,
    work: &mut Work,
) -> Option<Option<usize>> {
    let cfg = program.cfg();
    // Bounds cover all input, but only reachable blocks contribute emitted C.
    // Charge the reachability traversal and its bounded temporary collection.
    work.spend(cfg.blocks().len().checked_mul(3)?)?;
    for instruction in cfg
        .reachable_blocks()
        .into_iter()
        .flat_map(|block| program.instructions()[cfg.block(block).instructions.clone()].iter())
    {
        work.spend(1)?;
        for assignment in &instruction.assignments {
            work.spend(1)?;
            if let Place::Memory { address, .. } = &assignment.destination
                && let Some(lineage) =
                    expression_rollback(address, initial, candidate, known, work)?
            {
                return Some(Some(lineage));
            }
            if let Some(lineage) =
                expression_rollback(&assignment.value, initial, candidate, known, work)?
            {
                return Some(Some(lineage));
            }
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &instruction.control
            && let Some(lineage) = expression_rollback(condition, initial, candidate, known, work)?
        {
            return Some(Some(lineage));
        }
    }
    Some(None)
}

fn expression_rollback(
    expression: &Expr,
    initial: &BTreeMap<usize, usize>,
    candidate: &BTreeMap<usize, usize>,
    known: &BTreeMap<usize, usize>,
    work: &mut Work,
) -> Option<Option<usize>> {
    work.spend(1)?;
    if let Expr::Binary(BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule, a, b) =
        expression
        && same_pure_expression(a, b, candidate, work)?
        && !same_pure_expression(a, b, initial, work)?
    {
        return Some(Some(collapsed_lineage(
            a, b, initial, candidate, known, work,
        )?));
    }
    match expression {
        Expr::Unary(_, value) => expression_rollback(value, initial, candidate, known, work),
        Expr::Binary(_, a, b) => {
            if let Some(lineage) = expression_rollback(a, initial, candidate, known, work)? {
                return Some(Some(lineage));
            }
            expression_rollback(b, initial, candidate, known, work)
        }
        Expr::Load { address, .. } => expression_rollback(address, initial, candidate, known, work),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            for arm in [condition, taken, not_taken] {
                if let Some(lineage) = expression_rollback(arm, initial, candidate, known, work)? {
                    return Some(Some(lineage));
                }
            }
            Some(None)
        }
        Expr::Const(_) | Expr::Register(_) => Some(None),
    }
}

fn same_storage(a: Reg, b: Reg, colors: &BTreeMap<usize, usize>) -> bool {
    a == b
        || match (colors.get(&a.0), colors.get(&b.0)) {
            (Some(a), Some(b)) => a == b,
            _ => false, // Unmapped registers have their own storage namespace.
        }
}

fn same_pure_expression(
    a: &Expr,
    b: &Expr,
    colors: &BTreeMap<usize, usize>,
    work: &mut Work,
) -> Option<bool> {
    work.spend(1)?;
    Some(match (a, b) {
        (Expr::Const(a), Expr::Const(b)) => a == b,
        (Expr::Register(a), Expr::Register(b)) => same_storage(*a, *b, colors),
        (Expr::Unary(a, x), Expr::Unary(b, y)) => {
            a == b && same_pure_expression(x, y, colors, work)?
        }
        (Expr::Binary(op_a, a, b), Expr::Binary(op_b, x, y)) => {
            op_a == op_b
                && same_pure_expression(a, x, colors, work)?
                && same_pure_expression(b, y, colors, work)?
        }
        (
            Expr::Select {
                condition: a,
                taken: b,
                not_taken: c,
            },
            Expr::Select {
                condition: x,
                taken: y,
                not_taken: z,
            },
        ) => {
            same_pure_expression(a, x, colors, work)?
                && same_pure_expression(b, y, colors, work)?
                && same_pure_expression(c, z, colors, work)?
        }
        // Even identical Load syntax can fault or observe a different value;
        // this preference guard neither equates loads nor rewrites effects.
        _ => false,
    })
}

fn collapsed_lineage(
    a: &Expr,
    b: &Expr,
    initial: &BTreeMap<usize, usize>,
    candidate: &BTreeMap<usize, usize>,
    known: &BTreeMap<usize, usize>,
    work: &mut Work,
) -> Option<usize> {
    work.spend(1)?;
    match (a, b) {
        (Expr::Unary(_, a), Expr::Unary(_, b)) => {
            collapsed_lineage(a, b, initial, candidate, known, work)
        }
        (Expr::Register(a), Expr::Register(b))
            if same_storage(*a, *b, candidate) && !same_storage(*a, *b, initial) =>
        {
            known
                .get(&a.0)
                .filter(|lineage| known.get(&b.0) == Some(lineage))
                .copied()
        }
        (Expr::Binary(_, a, b), Expr::Binary(_, x, y)) => {
            collapsed_lineage(a, x, initial, candidate, known, work)
                .or_else(|| collapsed_lineage(b, y, initial, candidate, known, work))
        }
        (
            Expr::Select {
                condition: a,
                taken: b,
                not_taken: c,
            },
            Expr::Select {
                condition: x,
                taken: y,
                not_taken: z,
            },
        ) => collapsed_lineage(a, x, initial, candidate, known, work)
            .or_else(|| collapsed_lineage(b, y, initial, candidate, known, work))
            .or_else(|| collapsed_lineage(c, z, initial, candidate, known, work)),
        _ => None,
    }
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum Group {
    Known(usize),
    RolledBack { lineage: usize, initial: usize },
    Unknown(usize),
}

fn propose(
    initial: &BTreeMap<usize, usize>,
    known: &BTreeMap<usize, usize>,
    blocked: &BTreeSet<usize>,
    work: &mut Work,
) -> Option<BTreeMap<usize, usize>> {
    let mut labels = BTreeMap::new();
    let mut colors = BTreeMap::new();
    // Dense labels follow the first member in ascending register order, so
    // input ordering and sparse labels cannot affect the returned grouping.
    for (&register, &initial) in initial {
        work.spend(1)?;
        let group = match known.get(&register) {
            Some(&lineage) if blocked.contains(&lineage) => Group::RolledBack { lineage, initial },
            Some(&lineage) => Group::Known(lineage),
            None => Group::Unknown(initial),
        };
        let next = labels.len();
        let color = *labels.entry(group).or_insert(next);
        colors.insert(register, color);
    }
    Some(colors)
}

fn score(
    colors: &BTreeMap<usize, usize>,
    known: &BTreeMap<usize, usize>,
    work: &mut Work,
) -> Option<SourceScore> {
    let mut by_color = BTreeMap::<usize, BTreeSet<usize>>::new();
    let mut by_lineage = BTreeMap::<usize, BTreeSet<usize>>::new();
    let mut locals = BTreeSet::new();
    for (&register, &color) in colors {
        work.spend(1)?;
        locals.insert(color);
        if let Some(&lineage) = known.get(&register) {
            by_color.entry(color).or_default().insert(lineage);
            by_lineage.entry(lineage).or_default().insert(color);
        }
    }
    let mut mixed = 0usize;
    let mut fragments = 0usize;
    for classes in by_color.values() {
        work.spend(classes.len() + 1)?;
        mixed = mixed.checked_add(classes.len().saturating_sub(1))?;
    }
    for slots in by_lineage.values() {
        work.spend(slots.len() + 1)?;
        fragments = fragments.checked_add(slots.len().saturating_sub(1))?;
    }
    Some(SourceScore {
        mixed,
        fragments,
        locals: locals.len(),
    })
}

struct Work(usize);
impl Work {
    fn spend(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}
