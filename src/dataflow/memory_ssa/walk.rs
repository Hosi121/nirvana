use super::*;
use crate::dataflow::address_identity::ModularAddress;

const MAX_CANDIDATES: usize = 262144;
const MAX_LOCATIONS_PER_VERSION: usize = 16;
const MAX_LOCATION_STATES: usize = 32768;

pub(super) fn queries(
    analysis: &Analysis,
    graph: &SsaFunction,
    values: &BTreeMap<crate::dataflow::ssa::ValueId, ModularAddress>,
) -> Result<Vec<Query>, String> {
    let translation = super::translate::Translation::new(graph, values);
    let mut remaining = MAX_WORK;
    let mut retained = 0usize;
    let mut queries = Vec::new();
    for (index, access) in analysis.accesses.iter().enumerate() {
        if access.source.kind != AccessKind::Read {
            continue;
        }
        let mut candidates: BTreeMap<MemoryId, Clobber> = BTreeMap::new();
        let mut translated_edges = 0usize;
        let mut address_widened = false;
        let all_bytes = ((1u16 << access.source.width.bytes()) - 1) as u8;
        let mut pending = vec![(access.incoming, access.address.clone(), all_bytes)];
        let mut seen: BTreeMap<(MemoryId, Option<ModularAddress>), u8> = BTreeMap::new();
        let mut locations: BTreeMap<MemoryId, BTreeSet<Option<ModularAddress>>> = BTreeMap::new();
        while let Some((id, mut location, bytes)) = pending.pop() {
            remaining = remaining
                .checked_sub(1)
                .ok_or("memory SSA query work limit")?;
            remaining = remaining
                .checked_sub(location.as_ref().map_or(1, |a| a.terms.len() + 1))
                .ok_or("memory SSA location work limit")?;
            let previous_locations = locations.entry(id).or_default();
            if previous_locations.contains(&None)
                || (previous_locations.len() >= MAX_LOCATIONS_PER_VERSION
                    && !previous_locations.contains(&location))
            {
                address_widened |= location.is_some();
                location = None;
            }
            previous_locations.insert(location.clone());
            if seen.len() >= MAX_LOCATION_STATES && !seen.contains_key(&(id, location.clone())) {
                return Err("memory SSA location state limit".into());
            }
            let visited = seen.entry((id, location.clone())).or_default();
            let bytes = bytes & !*visited;
            if bytes == 0 {
                continue;
            }
            *visited |= bytes;
            let mut record = |alias, byte_mask| {
                candidates
                    .entry(id)
                    .and_modify(|old| {
                        old.alias = std::cmp::max(old.alias, alias);
                        old.byte_mask |= byte_mask;
                    })
                    .or_insert(Clobber {
                        definition: id,
                        alias,
                        byte_mask,
                    });
            };
            match &analysis.definitions[id.0] {
                Definition::Initial => record(Alias::May, bytes),
                Definition::Phi { block, inputs } => {
                    remaining = remaining
                        .checked_sub(inputs.len())
                        .ok_or("memory SSA query edge limit")?;
                    if pending.len().saturating_add(inputs.len()) > MAX_LOCATION_STATES {
                        return Err("memory SSA pending location limit".into());
                    }
                    for input in inputs {
                        let address = translation.edge(
                            location.as_ref(),
                            *block,
                            input.predecessor,
                            &mut remaining,
                        )?;
                        translated_edges += 1;
                        address_widened |= location.is_some() && address.is_none();
                        pending.push((input.memory, address, bytes));
                    }
                }
                Definition::Opaque { previous, .. } => {
                    record(Alias::May, bytes);
                    pending.push((*previous, location, bytes));
                }
                Definition::Store {
                    access: store,
                    previous,
                } => {
                    let (alias, mask) = relation(
                        location.as_ref(),
                        analysis.accesses[*store].address.as_ref(),
                        access.source.width,
                        analysis.accesses[*store].source.width,
                    );
                    let overlap = mask.unwrap_or(all_bytes) & bytes;
                    if overlap != 0 {
                        record(alias, overlap);
                    }
                    let pending_bytes = bytes & !mask.unwrap_or(0);
                    if pending_bytes != 0 {
                        pending.push((*previous, location, pending_bytes));
                    }
                }
            }
        }
        retained = retained
            .checked_add(candidates.len())
            .ok_or("memory SSA candidate limit")?;
        if retained > MAX_CANDIDATES {
            return Err("memory SSA candidate storage limit".into());
        }
        queries.push(Query {
            access: index,
            candidates: candidates.into_values().collect(),
            translated_edges,
            address_widened,
        });
    }
    Ok(queries)
}

fn relation(
    read: Option<&ModularAddress>,
    store: Option<&ModularAddress>,
    read_width: crate::model::ir::Width,
    store_width: crate::model::ir::Width,
) -> (Alias, Option<u8>) {
    let (Some(read), Some(store)) = (read, store) else {
        return (Alias::May, None);
    };
    if read.terms != store.terms {
        return (Alias::May, None);
    }
    let (a, b) = (read.offset, store.offset);
    let (ra, rb) = (read_width.bytes() as u64, store_width.bytes() as u64);
    let mask = (0..ra).fold(0u8, |mask, byte| {
        mask | if a.wrapping_add(byte).wrapping_sub(b) < rb {
            1 << byte
        } else {
            0
        }
    });
    let alias = if a == b && ra == rb {
        Alias::Exact
    } else if mask == 0 {
        Alias::Disjoint
    } else {
        Alias::Overlap
    };
    (alias, Some(mask))
}
