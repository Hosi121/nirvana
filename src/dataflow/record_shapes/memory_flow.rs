//! Whole-word Store-to-Load origins for tentative record compatibility.
//!
//! MemorySSA keeps all possible writers, including initial memory and partial
//! or may-alias contributions. Only complete, exact Store alternatives cross
//! this boundary; register aliases and executable memory operations stay intact.
use super::MemoryFlowStats;
use crate::dataflow::memory_ssa::{self, Alias, Definition};
use crate::dataflow::ssa::{Budget, Site, ValueId};
use crate::dataflow::type_infer::{Operand, TypeAnalysis};
use crate::model::ir::{AccessKind, Program, Width};
use std::collections::{BTreeMap, BTreeSet};

const MAX_TRANSFERS: usize = 65536;

pub(super) struct Transfer {
    pub to: ValueId,
    pub store: Site,
}

pub(super) fn collect(
    source: &Program,
    types: &TypeAnalysis,
) -> Result<(MemoryFlowStats, Vec<Transfer>), String> {
    let eligible: BTreeMap<_, _> = types
        .accesses()
        .iter()
        .filter(|a| {
            a.kind == AccessKind::Read
                && a.width == Width::U64
                && a.operand == Operand::Value
                && a.path.is_empty()
        })
        .filter_map(|a| a.result.map(|value| (a.site, value)))
        .collect();
    let mut stats = MemoryFlowStats {
        considered_loads: eligible.len(),
        complete_loads: 0,
    };
    if eligible.is_empty() {
        return Ok((stats, Vec::new()));
    }
    let memory = memory_ssa::analyze(source, types.graph())?;
    let queries = memory.queries().as_ref().map_err(Clone::clone)?;
    let mut budget = Budget::new();
    let mut seen = BTreeSet::new();
    let mut transfers = Vec::new();
    for query in queries {
        budget.spend(1).map_err(|e| e.to_string())?;
        let load = &memory.accesses()[query.access].source;
        let Some(&to) = eligible.get(&load.site) else {
            continue;
        };
        // A nested Load at the same assignment is a separate read, not its
        // result. Require the actual root access and its source SSA value.
        if load.operand != Operand::Value || !load.path.is_empty() {
            continue;
        }
        if load.width != Width::U64 || load.result != Some(to) || !seen.insert(load.site) {
            return Err("record memory load/source mismatch".into());
        }
        if query.address_widened || query.candidates.is_empty() {
            continue;
        }
        let mut stores = BTreeSet::new();
        let mut complete = true;
        for candidate in &query.candidates {
            budget.spend(20).map_err(|e| e.to_string())?;
            let Definition::Store { access, .. } = &memory.definitions()[candidate.definition.0]
            else {
                complete = false;
                break;
            };
            let store = &memory.accesses()[*access].source;
            if candidate.alias != Alias::Exact
                || candidate.byte_mask != u8::MAX
                || store.width != Width::U64
            {
                complete = false;
                break;
            }
            stores.insert(store.site);
        }
        if !complete {
            continue;
        }
        if transfers.len().saturating_add(stores.len()) > MAX_TRANSFERS {
            return Err("record memory transfer limit".into());
        }
        stats.complete_loads += 1;
        transfers.extend(stores.into_iter().map(|store| Transfer { to, store }));
    }
    if seen.len() != eligible.len() {
        return Err("record memory load coverage mismatch".into());
    }
    Ok((stats, transfers))
}
