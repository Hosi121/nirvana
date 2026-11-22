//! Consolidate roots with an immutable direct proof as a witness. Proposal
//! composes slices; verification independently follows individual bit origins.
use super::analyze::Context;
use super::*;
#[cfg(test)]
mod tests;

fn canonical(base: &MemoryValuePlan, original: Key, budget: &mut Budget) -> Option<Key> {
    let mut key = original;
    let mut seen = BTreeSet::new();
    loop {
        budget.spend(1).ok()?;
        if !seen.insert(key) {
            return Some(original);
        }
        let SavedValue::Register(value) = key.value else {
            return Some(key);
        };
        let Some(alias) = base.facts.get(value.0).copied().flatten() else {
            return Some(key);
        };
        if u32::from(key.start) + key.width.bits() > alias.width.bits() {
            return Some(key);
        }
        let next = Key {
            value: alias.value,
            start: alias.start.checked_add(key.start)?,
            width: key.width,
        };
        if next == key {
            return Some(key);
        }
        key = next;
    }
}
pub(super) fn propose(
    source: &Program,
    base: &MemoryValuePlan,
    context: &Context<'_>,
) -> Option<MemoryValuePlan> {
    let mut budget = Budget::new();
    let proofs: Vec<_> = base
        .proofs
        .iter()
        .map(|p| {
            Some(LoadProof {
                site: p.site,
                key: canonical(base, p.key, &mut budget)?,
            })
        })
        .collect::<Option<_>>()?;
    let used: BTreeSet<_> = proofs.iter().map(|p| p.key.value).collect();
    let captures: Vec<_> = base
        .captures
        .iter()
        .filter(|c| used.contains(&c.value))
        .copied()
        .collect();
    if captures.len() >= base.captures.len() || captures.len() != used.len() {
        return None;
    }
    let facts = value_facts::solve(context, &proofs).ok()?;
    let mut plan = MemoryValuePlan {
        source_registers: base.source_registers,
        proofs,
        captures,
        facts,
        evidence: MemoryValueEvidence {
            snapshot_values: used.len(),
            ..base.evidence
        },
        basis: Some(Box::new(base.clone())),
    };
    let (candidate, count) = rewrite::construct(source, &plan, context)?;
    plan.evidence.replaced_reads = count;
    verify::check(source, &plan, &candidate, context).ok()?;
    Some(plan)
}

pub(super) fn check_alias(
    base: &MemoryValuePlan,
    original: Key,
    actual: Key,
    budget: &mut Budget,
) -> Result<bool, SsaError> {
    if original.width != actual.width
        || u32::from(original.start) + original.width.bits() > 64
        || u32::from(actual.start) + actual.width.bits() > 64
    {
        return Ok(false);
    }
    for offset in 0..original.width.bits() as u8 {
        let target = (actual.value, actual.start + offset);
        let mut origin = (original.value, original.start + offset);
        let mut seen = BTreeSet::new();
        while origin != target {
            budget.spend(1)?;
            if !seen.insert(origin) {
                return Ok(false);
            }
            let SavedValue::Register(value) = origin.0 else {
                return Ok(false);
            };
            let Some(alias) = base.facts.get(value.0).copied().flatten() else {
                return Ok(false);
            };
            if u32::from(origin.1) >= alias.width.bits() {
                return Ok(false);
            }
            let Some(bit) = alias.start.checked_add(origin.1).filter(|bit| *bit < 64) else {
                return Ok(false);
            };
            origin = (alias.value, bit);
        }
    }
    Ok(true)
}
