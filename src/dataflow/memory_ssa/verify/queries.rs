//! Check a closed set of backwards byte obligations. For each reachable
//! state, every predecessor obligation is covered, and every possible writer
//! contribution is included. None-address states conservatively cover every
//! location. Induction along any finite execution reaches Initial or a Store;
//! loop backedges require no bound on the number of iterations.
use super::*;
use crate::dataflow::address_identity::ModularAddress;
use crate::dataflow::ssa::{Definition as RegisterDefinition, ValueId};

const MAX_TERMS: usize = 16;
type States = BTreeMap<(MemoryId, Option<ModularAddress>), u8>;
type RelationKey = (Option<ModularAddress>, Option<ModularAddress>, u32, u32);
type Relations = BTreeMap<RelationKey, (Alias, u8, [u8; 8])>;

struct EdgeValues<'a> {
    registers: &'a SsaFunction,
    values: &'a BTreeMap<ValueId, ModularAddress>,
    owners: Vec<Option<u64>>,
}
impl EdgeValues<'_> {
    fn translate(
        &self,
        address: Option<&ModularAddress>,
        block: u64,
        predecessor: Option<u64>,
        budget: &mut Budget,
    ) -> Result<Option<ModularAddress>, ValidationError> {
        let Some(address) = address else {
            return Ok(None);
        };
        let mut offset = address.offset;
        let mut terms = BTreeMap::<ValueId, u64>::new();
        for &(value, scale) in &address.terms {
            budget.spend(1)?;
            let incoming = match &self.registers.values[value.0] {
                RegisterDefinition::Phi {
                    block: owner,
                    inputs,
                    ..
                } if *owner == block => {
                    budget.spend(inputs.len())?;
                    let input = inputs
                        .iter()
                        .find(|i| i.predecessor == predecessor)
                        .ok_or(Invalid("register phi incoming edge"))?;
                    Some(
                        self.values
                            .get(&input.value)
                            .ok_or(Unavailable("phi input address identity"))?,
                    )
                }
                RegisterDefinition::Assignment { .. } if self.owners[value.0] == Some(block) => {
                    return Ok(None);
                }
                _ => None,
            };
            if let Some(form) = incoming {
                budget.spend(form.terms.len() + 1)?;
                offset = offset.wrapping_add(scale.wrapping_mul(form.offset));
                for &(atom, coefficient) in &form.terms {
                    let slot = terms.entry(atom).or_default();
                    *slot = slot.wrapping_add(scale.wrapping_mul(coefficient));
                }
            } else {
                let slot = terms.entry(value).or_default();
                *slot = slot.wrapping_add(scale);
            }
        }
        terms.retain(|_, scale| *scale != 0);
        if terms.len() > MAX_TERMS {
            return Ok(None);
        }
        Ok(Some(ModularAddress {
            offset,
            terms: terms.into_iter().collect(),
        }))
    }
}

fn cover(
    states: &States,
    memory: MemoryId,
    address: Option<&ModularAddress>,
    bytes: u8,
) -> Result<(), ValidationError> {
    let broad = states.get(&(memory, None)).copied().unwrap_or(0);
    let bytes = bytes & !broad;
    if bytes != 0 {
        let Some(address) = address else {
            return Err(Invalid("uncovered unknown-address state"));
        };
        let exact = states
            .get(&(memory, Some(address.clone())))
            .copied()
            .unwrap_or(0);
        if bytes & !exact != 0 {
            return Err(Invalid("uncovered predecessor bytes"));
        }
    }
    Ok(())
}

fn source_mask(width: crate::model::ir::Width) -> u8 {
    ((1u16 << width.bytes()) - 1) as u8
}

/// Independent byte-by-byte equalities, rather than the producer's offset
/// subtraction/range test. Modular equality also handles wrapping offsets.
fn relation(
    read: Option<&ModularAddress>,
    store: Option<&ModularAddress>,
    read_width: crate::model::ir::Width,
    store_width: crate::model::ir::Width,
) -> (Alias, u8, [u8; 8]) {
    let mut sources = [0; 8];
    let (Some(read), Some(store)) = (read, store) else {
        sources[..read_width.bytes()].fill(source_mask(store_width));
        return (Alias::May, 0, sources);
    };
    if read.terms != store.terms {
        sources[..read_width.bytes()].fill(source_mask(store_width));
        return (Alias::May, 0, sources);
    }
    let mut definite = 0;
    for (byte, bits) in sources.iter_mut().enumerate().take(read_width.bytes()) {
        for source in 0..store_width.bytes() {
            if read.offset.wrapping_add(byte as u64) == store.offset.wrapping_add(source as u64) {
                *bits |= 1 << source;
                definite |= 1 << byte;
            }
        }
    }
    let alias = if read.offset == store.offset && read_width == store_width {
        Alias::Exact
    } else if definite == 0 {
        Alias::Disjoint
    } else {
        Alias::Overlap
    };
    (alias, definite, sources)
}

fn candidates<'a>(
    query: &'a Query,
    analysis: &Analysis,
    budget: &mut Budget,
) -> Result<BTreeMap<MemoryId, &'a Clobber>, ValidationError> {
    let width = analysis.accesses[query.access].source.width;
    let mut result = BTreeMap::new();
    budget.retain(query.candidates.len())?;
    for c in &query.candidates {
        budget.spend(9)?;
        if c.definition.0 >= analysis.definitions.len()
            || c.byte_mask == 0
            || c.byte_mask & !source_mask(width) != 0
            || c.unknown_bytes & !c.byte_mask != 0
            || c.alias == Alias::Disjoint
            || result.insert(c.definition, c).is_some()
        {
            return Err(Invalid("candidate definition or byte mask"));
        }
        match &analysis.definitions[c.definition.0] {
            Definition::Initial | Definition::Opaque { .. } => {
                if c.alias != Alias::May
                    || c.unknown_bytes != c.byte_mask
                    || c.byte_sources != [0; 8]
                {
                    return Err(Invalid("unconstrained writer bytes"));
                }
            }
            Definition::Store { access, .. } => {
                if c.unknown_bytes != 0 {
                    return Err(Invalid("store has unconstrained initial/opaque bytes"));
                }
                let valid = source_mask(analysis.accesses[*access].source.width);
                for (byte, &bits) in c.byte_sources.iter().enumerate() {
                    if bits & !valid != 0 || (c.byte_mask & (1 << byte) == 0) != (bits == 0) {
                        return Err(Invalid("candidate source byte positions"));
                    }
                }
            }
            Definition::Phi { .. } => return Err(Invalid("phi claimed as a writer")),
        }
    }
    Ok(result)
}

fn cached_relation(
    read: Option<&ModularAddress>,
    store: Option<&ModularAddress>,
    read_width: crate::model::ir::Width,
    store_width: crate::model::ir::Width,
    relations: &mut Relations,
    budget: &mut Budget,
) -> Result<(Alias, u8, [u8; 8]), ValidationError> {
    let terms = read.map_or(0, |a| a.terms.len()) + store.map_or(0, |a| a.terms.len());
    budget.spend(terms + 1)?;
    let key = (
        read.cloned(),
        store.cloned(),
        read_width.bits(),
        store_width.bits(),
    );
    if let Some(&result) = relations.get(&key) {
        return Ok(result);
    }
    budget.retain(terms + 1)?;
    budget.spend(read_width.bytes() * store_width.bytes() + 1)?;
    let result = relation(read, store, read_width, store_width);
    relations.insert(key, result);
    Ok(result)
}

fn contribution(
    candidates: &BTreeMap<MemoryId, &Clobber>,
    memory: MemoryId,
    alias: Alias,
    mask: u8,
    sources: [u8; 8],
    unknown: u8,
    budget: &mut Budget,
) -> Result<usize, ValidationError> {
    if mask == 0 {
        return Ok(0);
    }
    budget.spend(9)?;
    let candidate = candidates
        .get(&memory)
        .ok_or(Invalid("missing reaching writer"))?;
    if candidate.alias < alias
        || mask & !candidate.byte_mask != 0
        || unknown & !candidate.unknown_bytes != 0
    {
        return Err(Invalid("missing writer byte contribution"));
    }
    for (byte, bits) in sources.into_iter().enumerate() {
        if mask & (1 << byte) != 0 && bits & !candidate.byte_sources[byte] != 0 {
            return Err(Invalid("missing store source byte"));
        }
    }
    Ok(mask.count_ones() as usize)
}

pub(super) fn validate(
    analysis: &Analysis,
    registers: &SsaFunction,
    values: &BTreeMap<ValueId, ModularAddress>,
) -> Result<QueryEvidence, ValidationError> {
    let queries = analysis
        .queries
        .as_ref()
        .map_err(|_| Invalid("unavailable queries"))?;
    let reads = analysis
        .accesses
        .iter()
        .filter(|a| a.source.kind == AccessKind::Read)
        .count();
    if queries.len() != reads || analysis.query_certificates.len() != reads {
        return Err(Invalid("query/certificate read coverage"));
    }
    let mut budget = Budget::new();
    budget.retain(queries.len() + analysis.query_certificates.len())?;
    let mut by_access = BTreeMap::new();
    for query in queries {
        if analysis
            .accesses
            .get(query.access)
            .is_none_or(|a| a.source.kind != AccessKind::Read)
            || by_access.insert(query.access, query).is_some()
        {
            return Err(Invalid("query access correspondence"));
        }
    }
    let mut owners = vec![None; registers.values.len()];
    for block in &registers.blocks {
        for point in &block.points {
            if let Some(id) = point.definition {
                owners[id.0] = Some(block.start);
            }
        }
    }
    let edges = EdgeValues {
        registers,
        values,
        owners,
    };
    let mut evidence = QueryEvidence {
        queries: reads,
        states: 0,
        links: 0,
        candidate_bytes: 0,
    };
    // The relation is a pure function of two forms and widths. Reusing it
    // across loads keeps repeated-join certificates inside the same budget;
    // every state, predecessor obligation and writer contribution is checked.
    let mut relations = Relations::new();
    for proof in &analysis.query_certificates {
        let query = by_access
            .remove(&proof.access)
            .ok_or(Invalid("certificate access correspondence"))?;
        let read = &analysis.accesses[query.access];
        let candidates = candidates(query, analysis, &mut budget)?;
        let mut states = States::new();
        budget.retain(proof.states.len())?;
        for state in &proof.states {
            if state.memory.0 >= analysis.definitions.len()
                || state.byte_mask == 0
                || state.byte_mask & !source_mask(read.source.width) != 0
            {
                return Err(Invalid("certificate state or byte mask"));
            }
            if let Some(address) = &state.address {
                budget.retain(address.terms.len())?;
                if address.terms.len() > MAX_TERMS
                    || address
                        .terms
                        .iter()
                        .any(|&(id, scale)| id.0 >= registers.values.len() || scale == 0)
                    || address.terms.windows(2).any(|p| p[0].0 >= p[1].0)
                {
                    return Err(Invalid("certificate address form"));
                }
            } else if read.address.is_some() && !query.address_widened {
                return Err(Invalid("missing query widening marker"));
            }
            if states
                .insert((state.memory, state.address.clone()), state.byte_mask)
                .is_some()
            {
                return Err(Invalid("duplicate certificate state"));
            }
        }
        cover(
            &states,
            read.incoming,
            read.address.as_ref(),
            source_mask(read.source.width),
        )?;
        evidence.links += 1;
        evidence.states += states.len();
        for state in &proof.states {
            budget.spend(state.address.as_ref().map_or(1, |a| a.terms.len() + 1))?;
            let memory = state.memory;
            let bytes = state.byte_mask;
            match &analysis.definitions[memory.0] {
                Definition::Initial => {
                    evidence.candidate_bytes += contribution(
                        &candidates,
                        memory,
                        Alias::May,
                        bytes,
                        [0; 8],
                        bytes,
                        &mut budget,
                    )?
                }
                Definition::Opaque { previous, .. } => {
                    evidence.candidate_bytes += contribution(
                        &candidates,
                        memory,
                        Alias::May,
                        bytes,
                        [0; 8],
                        bytes,
                        &mut budget,
                    )?;
                    cover(&states, *previous, state.address.as_ref(), bytes)?;
                    evidence.links += 1;
                }
                Definition::Store { access, previous } => {
                    let store = &analysis.accesses[*access];
                    let (alias, definite, sources) = cached_relation(
                        state.address.as_ref(),
                        store.address.as_ref(),
                        read.source.width,
                        store.source.width,
                        &mut relations,
                        &mut budget,
                    )?;
                    let possible = sources.iter().enumerate().fold(0, |mask, (byte, &s)| {
                        mask | if s != 0 { 1 << byte } else { 0 }
                    });
                    evidence.candidate_bytes += contribution(
                        &candidates,
                        memory,
                        alias,
                        bytes & possible,
                        sources,
                        0,
                        &mut budget,
                    )?;
                    let pending = bytes & !definite;
                    if pending != 0 {
                        cover(&states, *previous, state.address.as_ref(), pending)?;
                        evidence.links += 1;
                    }
                }
                Definition::Phi { block, inputs } => {
                    budget.spend(inputs.len())?;
                    for input in inputs {
                        let address = edges.translate(
                            state.address.as_ref(),
                            *block,
                            input.predecessor,
                            &mut budget,
                        )?;
                        cover(&states, input.memory, address.as_ref(), bytes)?;
                        evidence.links += 1;
                    }
                }
            }
        }
    }
    Ok(evidence)
}
