//! Runtime-guarded local destinations for near tail transfers. Candidate sets
//! choose fast paths; the original computed target and residual dispatch remain.

use crate::codegen::module_outline;
use crate::model::module_ir::{Instruction, Module, Program};
use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};

pub const MAX_CASES_PER_TRANSFER: usize = 64;
pub const MAX_TOTAL_CASES: usize = 8192;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Plan {
    pub transfers: BTreeMap<u64, Transfer>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Transfer {
    pub function: u64,
    /// Actual guest PC -> first checked source label in the owning function.
    pub cases: BTreeMap<u64, usize>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Evidence {
    pub transfers: usize,
    pub cases: usize,
}

/// Recover optional guards from open hints. Correctness depends on original
/// decoded PCs and checked reentry labels, not on a complete target inventory.
pub fn recover(module: &Module, outline: &module_outline::Plan) -> Result<Plan, String> {
    let mut plan = Plan::default();
    if module.jump_tables.is_empty() || module.jump_tables.len() > 8192 {
        return Ok(plan);
    }
    if outline.functions.len() != module.program.functions().len() || outline.functions.len() > 512
    {
        return Err("local tail function catalog limit/mismatch".into());
    }
    let instructions: BTreeMap<_, _> = module
        .program
        .instructions()
        .iter()
        .map(|i| (i.address(), i))
        .collect();
    let imports: BTreeSet<_> = module.program.imports().iter().map(|i| i.address).collect();
    let mut total = 0;
    for table in &module.jump_tables {
        if table.entries.len() > crate::binary::jump_tables::MAX_ENTRIES
            || total == MAX_TOTAL_CASES
            || imports.contains(&table.branch)
        {
            continue;
        }
        if !matches!(
            instructions.get(&table.branch),
            Some(Instruction::Transfer { link: None, .. })
        ) {
            continue;
        }
        let Some(function) = outline
            .functions
            .iter()
            .find(|f| f.resumes.contains_key(&table.branch))
        else {
            continue;
        };
        for entry in &table.entries {
            if total == MAX_TOTAL_CASES {
                break;
            }
            if imports.contains(&entry.target) {
                continue;
            }
            let Some(&label) = function.resumes.get(&entry.target) else {
                continue;
            };
            let transfer = plan
                .transfers
                .entry(table.branch)
                .or_insert_with(|| Transfer {
                    function: function.function.address,
                    cases: BTreeMap::new(),
                });
            if transfer.cases.len() < MAX_CASES_PER_TRANSFER
                && transfer.cases.insert(entry.target, label).is_none()
            {
                total += 1;
            }
        }
    }
    validate(&module.program, outline, &plan)?;
    Ok(plan)
}

/// Check the tail witness against original instructions and the checked
/// outline's first labels. This checks neither table immutability nor target
/// completeness. Every lowering must retain residual dispatch after its guard.
pub fn validate(
    program: &Program,
    outline: &module_outline::Plan,
    plan: &Plan,
) -> Result<Evidence, String> {
    if program.instructions().len() > 65_536
        || plan.transfers.len() > MAX_TOTAL_CASES
        || outline.functions.len() != program.functions().len()
        || outline.functions.len() > 512
    {
        return Err("local tail instruction/transfer limit".into());
    }
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address(), i))
        .collect();
    if instructions.len() != program.instructions().len() {
        return Err("local tail duplicate source PC".into());
    }
    let imports: BTreeSet<_> = program.imports().iter().map(|i| i.address).collect();
    let mut evidence = Evidence::default();
    let mut checked = BTreeMap::new();
    for (&pc, transfer) in &plan.transfers {
        if !matches!(
            instructions.get(&pc),
            Some(Instruction::Transfer { link: None, .. })
        ) {
            return Err("local tail source is not a near tail transfer".into());
        }
        if let Entry::Vacant(slot) = checked.entry(transfer.function) {
            let function = program
                .functions()
                .iter()
                .find(|f| f.address == transfer.function)
                .ok_or("local tail function missing")?;
            let end = function
                .address
                .checked_add(function.size)
                .ok_or("local tail function overflow")?;
            let range = function.address..end;
            let body = outline
                .functions
                .iter()
                .find(|f| f.function.address == transfer.function)
                .ok_or("local tail checked outline missing")?;
            if &body.function != function {
                return Err("local tail function metadata mismatch".into());
            }
            let mut first = BTreeMap::new();
            if body.sites.len() > instructions.len() * 2 {
                return Err("local tail source-site limit".into());
            }
            for (label, site) in body.sites.iter().enumerate() {
                if site.label != label
                    || !range.contains(&site.address)
                    || !instructions.contains_key(&site.address)
                {
                    return Err("local tail source-site identity mismatch".into());
                }
                first.entry(site.address).or_insert(label);
            }
            if first != body.resumes || first.len() != instructions.range(range.clone()).count() {
                return Err("local tail first-label map mismatch".into());
            }
            slot.insert((range, first));
        }
        let (range, first) = &checked[&transfer.function];
        if !range.contains(&pc) || !first.contains_key(&pc) || imports.contains(&pc) {
            return Err("local tail source ownership mismatch".into());
        }
        if transfer.cases.is_empty() || transfer.cases.len() > MAX_CASES_PER_TRANSFER {
            return Err("local tail case limit".into());
        }
        for (&target, &label) in &transfer.cases {
            if !range.contains(&target)
                || !instructions.contains_key(&target)
                || imports.contains(&target)
            {
                return Err("local tail target is not an original PC in the same function".into());
            }
            if first.get(&target) != Some(&label) {
                return Err("local tail target label mismatch".into());
            }
        }
        evidence.transfers += 1;
        evidence.cases += transfer.cases.len();
        if evidence.cases > MAX_TOTAL_CASES {
            return Err("local tail total case limit".into());
        }
    }
    Ok(evidence)
}
