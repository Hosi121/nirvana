use super::*;
use crate::type_infer::AddressShape;

const MAX_CANDIDATES: usize = 262144;

pub(super) fn queries(analysis: &Analysis, graph: &SsaFunction) -> Result<Vec<Query>, String> {
    let mut remaining = MAX_WORK;
    let mut retained = 0usize;
    let mut queries = Vec::new();
    for (index, access) in analysis.accesses.iter().enumerate() {
        if access.source.kind != AccessKind::Read {
            continue;
        }
        let mut candidates: BTreeMap<MemoryId, Clobber> = BTreeMap::new();
        let all_bytes = ((1u16 << access.source.width.bytes()) - 1) as u8;
        let mut pending = vec![(access.incoming, false, all_bytes)];
        let mut seen: BTreeMap<(MemoryId, bool), u8> = BTreeMap::new();
        while let Some((id, crossed_phi, bytes)) = pending.pop() {
            remaining = remaining
                .checked_sub(1)
                .ok_or("memory SSA query work limit")?;
            let visited = seen.entry((id, crossed_phi)).or_default();
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
                Definition::Phi { inputs, .. } => {
                    remaining = remaining
                        .checked_sub(inputs.len())
                        .ok_or("memory SSA query edge limit")?;
                    pending.extend(inputs.iter().map(|i| (i.memory, true, bytes)));
                }
                Definition::Opaque { previous, .. } => {
                    record(Alias::May, bytes);
                    pending.push((*previous, crossed_phi, bytes));
                }
                Definition::Store {
                    access: store,
                    previous,
                } => {
                    let (alias, mask) = relation(
                        &access.source,
                        &analysis.accesses[*store].source,
                        crossed_phi,
                        graph,
                    );
                    let overlap = mask.unwrap_or(all_bytes) & bytes;
                    if overlap != 0 {
                        record(alias, overlap);
                    }
                    let remaining = bytes & !mask.unwrap_or(0);
                    if remaining != 0 {
                        pending.push((*previous, crossed_phi, remaining));
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
        });
    }
    Ok(queries)
}

fn invariant(shape: AddressShape, graph: &SsaFunction) -> bool {
    let initial = |id: crate::ssa::ValueId| {
        matches!(
            graph.values.get(id.0),
            Some(crate::ssa::Definition::Initial { .. })
        )
    };
    match shape {
        AddressShape::Absolute(_) => true,
        AddressShape::Base { base, index, .. } => {
            initial(base) && index.is_none_or(|i| initial(i.value))
        }
        AddressShape::Unknown => false,
    }
}

fn relation(
    read: &MemoryAccess,
    store: &MemoryAccess,
    crossed_phi: bool,
    graph: &SsaFunction,
) -> (Alias, Option<u8>) {
    // A loop phi denotes different dynamic values on different iterations.
    // Across memory phis only input-rooted or absolute forms are invariant.
    // Other symbolic comparisons need edge translation before proving alias
    // or separation; retaining May also covers forward joins conservatively.
    if crossed_phi && (!invariant(read.address, graph) || !invariant(store.address, graph)) {
        return (Alias::May, None);
    }
    let offsets = match (read.address, store.address) {
        (AddressShape::Absolute(a), AddressShape::Absolute(b)) => Some((a, b)),
        (
            AddressShape::Base {
                base: a,
                offset: x,
                index: i,
            },
            AddressShape::Base {
                base: b,
                offset: y,
                index: j,
            },
        ) if a == b && i == j => Some((x, y)),
        _ => None,
    };
    let Some((a, b)) = offsets else {
        return (Alias::May, None);
    };
    let (ra, rb) = (read.width.bytes() as u64, store.width.bytes() as u64);
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
