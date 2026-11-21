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
        let mut candidates = BTreeMap::new();
        let mut pending = vec![(access.incoming, false)];
        let mut seen = BTreeSet::new();
        while let Some((id, crossed_phi)) = pending.pop() {
            remaining = remaining
                .checked_sub(1)
                .ok_or("memory SSA query work limit")?;
            if !seen.insert((id, crossed_phi)) {
                continue;
            }
            let mut record = |alias| {
                candidates
                    .entry(id)
                    .and_modify(|old| *old = std::cmp::max(*old, alias))
                    .or_insert(alias);
            };
            match &analysis.definitions[id.0] {
                Definition::Initial => record(Alias::May),
                Definition::Phi { inputs, .. } => {
                    remaining = remaining
                        .checked_sub(inputs.len())
                        .ok_or("memory SSA query edge limit")?;
                    pending.extend(inputs.iter().map(|i| (i.memory, true)));
                }
                Definition::Opaque { previous, .. } => {
                    record(Alias::May);
                    pending.push((*previous, crossed_phi));
                }
                Definition::Store {
                    access: store,
                    previous,
                } => {
                    let alias = relation(
                        &access.source,
                        &analysis.accesses[*store].source,
                        crossed_phi,
                        graph,
                    );
                    if alias != Alias::Disjoint {
                        record(alias);
                    }
                    if alias != Alias::Exact {
                        pending.push((*previous, crossed_phi));
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
            candidates: candidates
                .into_iter()
                .map(|(definition, alias)| Clobber { definition, alias })
                .collect(),
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
) -> Alias {
    // A loop phi denotes different dynamic values on different iterations.
    // Across memory phis only input-rooted or absolute forms are invariant.
    // Other symbolic comparisons need edge translation before proving alias
    // or separation; retaining May also covers forward joins conservatively.
    if crossed_phi && (!invariant(read.address, graph) || !invariant(store.address, graph)) {
        return Alias::May;
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
        return Alias::May;
    };
    let (ra, rb) = (read.width.bytes() as u64, store.width.bytes() as u64);
    if a == b && ra == rb {
        Alias::Exact
    } else if a.wrapping_sub(b) >= rb && b.wrapping_sub(a) >= ra {
        Alias::Disjoint
    } else {
        Alias::Overlap
    }
}
