//! Recover candidate source-local storage groups, independently validated.
//!
//! Lineage labels are naming hints, not equal-value facts or recovered source
//! identities. A proposal may merge across old colors, but only the independent
//! allocation correspondence checker can authorize the resulting storage map.
//! Executable IR, memory operations, order and control flow remain unchanged.

use std::collections::{BTreeMap, BTreeSet};

use crate::allocation_verify::{self, AllocationError, AllocationEvidence};
use crate::ir::{Program, Reg};

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
/// A failed read blocks that entire lineage from merging across initial colors.
/// Such a partition refines the validated initial mapping; other lineage merges
/// can still survive. At most 16 checker calls, including the initial check,
/// are performed. The checker independently bounds each invocation. Storage
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
