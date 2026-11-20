//! Pure selector snapshots for guarded local tail cases.
//! A hint can be stale: every selected case also checks the actual target.
use crate::ir::{Expr, Width};
use crate::module_ir::{Module, Program, REGISTER_COUNT};
use crate::{module_outline, module_tail_dispatch};
use std::collections::{BTreeMap, btree_map::Entry};

pub const MAX_SNAPSHOTS_PER_FUNCTION: usize = 16;
pub const MAX_KEY_CASES: usize = 8192;
const MAX_EXPR_NODES: usize = 64;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Snapshot {
    pub function: u64,
    pub producer: u64,
    pub address: Expr,
    pub table: u64,
    pub width: Width,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyUse {
    pub snapshot: usize,
    /// (normalized index, actual target) -> checked reentry label.
    pub cases: BTreeMap<(u64, u64), usize>,
}
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Plan {
    pub snapshots: Vec<Snapshot>,
    pub branches: BTreeMap<u64, Vec<KeyUse>>,
    by_producer: BTreeMap<u64, Vec<usize>>,
}
impl Plan {
    pub fn at(&self, pc: u64) -> impl Iterator<Item = (usize, &Snapshot)> {
        self.by_producer
            .get(&pc)
            .into_iter()
            .flatten()
            .filter_map(|id| self.snapshots.get(*id).map(|s| (*id, s)))
    }
}

pub fn recover(
    module: &Module,
    outline: &module_outline::Plan,
    tails: &module_tail_dispatch::Plan,
) -> Result<Plan, String> {
    let mut plan = Plan::default();
    let instructions: BTreeMap<_, _> = module
        .program
        .instructions()
        .iter()
        .map(|i| (i.address(), i))
        .collect();
    let mut by_function = BTreeMap::<u64, Vec<usize>>::new();
    let mut total = 0;
    if module.jump_tables.len() > 8192 {
        return Ok(plan);
    }
    for table in &module.jump_tables {
        if total == MAX_KEY_CASES {
            break;
        }
        let Some(tail) = tails.transfers.get(&table.branch) else {
            continue;
        };
        if table.entries.len() > crate::jump_tables::MAX_ENTRIES
            || table.read_sites.len() > crate::jump_tables::MAX_READ_SITES
        {
            continue;
        }
        for site in &table.read_sites {
            if total == MAX_KEY_CASES {
                break;
            }
            let Some(source) = instructions.get(&site.instruction) else {
                continue;
            };
            if source.address().checked_add(u64::from(source.size())) != Some(site.next)
                || site.width != table.width
            {
                continue;
            }
            let Some(address) = site.address_expr() else {
                continue;
            };
            let snapshot = Snapshot {
                function: tail.function,
                producer: site.instruction,
                address,
                table: table.table,
                width: table.width,
            };
            let existing = by_function
                .get(&tail.function)
                .and_then(|ids| ids.iter().find(|&&id| plan.snapshots[id] == snapshot))
                .copied();
            let id = if let Some(id) = existing {
                id
            } else {
                if by_function
                    .get(&tail.function)
                    .is_some_and(|ids| ids.len() == MAX_SNAPSHOTS_PER_FUNCTION)
                {
                    continue;
                }
                let Some(f) = module
                    .program
                    .functions()
                    .iter()
                    .find(|f| f.address == tail.function)
                else {
                    continue;
                };
                let Some(end) = f.address.checked_add(f.size) else {
                    continue;
                };
                if !(f.address..end).contains(&site.instruction) {
                    continue;
                }
                let id = plan.snapshots.len();
                plan.snapshots.push(snapshot);
                plan.by_producer
                    .entry(site.instruction)
                    .or_default()
                    .push(id);
                by_function.entry(tail.function).or_default().push(id);
                id
            };
            let uses = plan.branches.entry(table.branch).or_default();
            let position = if let Some(position) = uses.iter().position(|u| u.snapshot == id) {
                position
            } else {
                uses.push(KeyUse {
                    snapshot: id,
                    cases: BTreeMap::new(),
                });
                uses.len() - 1
            };
            let use_ = &mut uses[position];
            for entry in &table.entries {
                if total == MAX_KEY_CASES
                    || use_.cases.len() == module_tail_dispatch::MAX_CASES_PER_TRANSFER
                {
                    break;
                }
                let Some(&label) = tail.cases.get(&entry.target) else {
                    continue;
                };
                let Some(offset) = entry.address.checked_sub(table.table) else {
                    continue;
                };
                let stride = table.width.bytes() as u64;
                if offset % stride != 0 {
                    continue;
                }
                if let Entry::Vacant(slot) = use_.cases.entry((offset / stride, entry.target)) {
                    slot.insert(label);
                    total += 1;
                }
            }
        }
    }
    plan.branches
        .values_mut()
        .for_each(|uses| uses.retain(|u| !u.cases.is_empty()));
    plan.branches.retain(|_, uses| !uses.is_empty());
    let used: std::collections::BTreeSet<_> = plan
        .branches
        .values()
        .flatten()
        .map(|u| u.snapshot)
        .collect();
    let mut remap = BTreeMap::new();
    let mut snapshots = Vec::new();
    plan.by_producer.clear();
    for (old, snapshot) in plan.snapshots.into_iter().enumerate() {
        if used.contains(&old) {
            let id = snapshots.len();
            remap.insert(old, id);
            plan.by_producer
                .entry(snapshot.producer)
                .or_default()
                .push(id);
            snapshots.push(snapshot);
        }
    }
    plan.snapshots = snapshots;
    for use_ in plan.branches.values_mut().flatten() {
        use_.snapshot = remap[&use_.snapshot];
    }
    validate(&module.program, outline, tails, &plan)?;
    Ok(plan)
}

/// Snapshot purity and source identity are checked independently of inference.
/// Case values need no correctness premise: actual-target equality guards them.
pub fn validate(
    program: &Program,
    outline: &module_outline::Plan,
    tails: &module_tail_dispatch::Plan,
    plan: &Plan,
) -> Result<(), String> {
    module_tail_dispatch::validate(program, outline, tails)?;
    if plan.snapshots.len() > 512 * MAX_SNAPSHOTS_PER_FUNCTION
        || plan.branches.len() > MAX_KEY_CASES
    {
        return Err("selector plan collection limit".into());
    }
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address(), i))
        .collect();
    let mut counts = BTreeMap::<u64, usize>::new();
    let mut producers = BTreeMap::<u64, Vec<usize>>::new();
    for (id, snapshot) in plan.snapshots.iter().enumerate() {
        let function = program
            .functions()
            .iter()
            .find(|f| f.address == snapshot.function)
            .ok_or("selector function missing")?;
        let end = function
            .address
            .checked_add(function.size)
            .ok_or("selector function overflow")?;
        if !(function.address..end).contains(&snapshot.producer)
            || !instructions.contains_key(&snapshot.producer)
        {
            return Err("selector producer is not an original owned PC".into());
        }
        pure(&snapshot.address)?;
        let count = counts.entry(snapshot.function).or_default();
        *count += 1;
        if *count > MAX_SNAPSHOTS_PER_FUNCTION {
            return Err("selector function snapshot limit".into());
        }
        producers.entry(snapshot.producer).or_default().push(id);
    }
    if producers != plan.by_producer {
        return Err("selector producer map mismatch".into());
    }
    let mut total = 0;
    for (&branch, uses) in &plan.branches {
        let tail = tails
            .transfers
            .get(&branch)
            .ok_or("selector branch lacks a checked tail guard")?;
        if uses.len() > MAX_SNAPSHOTS_PER_FUNCTION {
            return Err("selector branch snapshot limit".into());
        }
        let mut used = std::collections::BTreeSet::new();
        for use_ in uses {
            let snapshot = plan
                .snapshots
                .get(use_.snapshot)
                .ok_or("selector snapshot index invalid")?;
            if snapshot.function != tail.function || !used.insert(use_.snapshot) {
                return Err("selector snapshot ownership/identity mismatch".into());
            }
            if use_.cases.is_empty()
                || use_.cases.len() > module_tail_dispatch::MAX_CASES_PER_TRANSFER
            {
                return Err("selector use case limit".into());
            }
            for (&(_, target), &label) in &use_.cases {
                if tail.cases.get(&target) != Some(&label) {
                    return Err("selector case is not a checked target label".into());
                }
            }
            total += use_.cases.len();
            if total > MAX_KEY_CASES {
                return Err("selector total case limit".into());
            }
        }
    }
    Ok(())
}
fn pure(expression: &Expr) -> Result<(), String> {
    let mut pending = vec![expression];
    let mut nodes = 0;
    while let Some(e) = pending.pop() {
        nodes += 1;
        if nodes > MAX_EXPR_NODES {
            return Err("selector expression limit".into());
        }
        match e {
            Expr::Const(_) => {}
            Expr::Register(r) if r.0 < REGISTER_COUNT => {}
            Expr::Binary(_, a, b) => {
                pending.push(a);
                pending.push(b);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(condition);
                pending.push(taken);
                pending.push(not_taken);
            }
            _ => return Err("selector snapshot must be pure with valid guest registers".into()),
        }
    }
    Ok(())
}
