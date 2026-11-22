//! Checked refinement of memory results. Proposals change only Load facts;
//! the checker reconstructs the unrefined source and recomputes byte consensus.
use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MemoryEvidence {
    pub loads: usize,
    pub proved_loads: usize,
    pub refined_loads: usize,
    pub unavailable_reason: Option<String>,
}

impl Function {
    pub fn recover_memory_constants(&self) -> Result<(Self, MemoryEvidence), Error> {
        validate_constants(self)?;
        let facts = self.memory_facts()?;
        let constants: BTreeMap<_, _> = facts
            .loads()
            .filter_map(|load| facts.constant_load(load.value).map(|v| (load.value, v)))
            .collect();
        let mut candidate = self.clone();
        walk::visit_mut(&mut candidate, |binding| {
            if let Operation::Load { address, width } = binding.operation
                && let Some(&value) = constants.get(&binding.id)
            {
                binding.operation = Operation::KnownLoad {
                    address,
                    width,
                    value,
                };
            }
        });
        let evidence = self.validate_memory_recovery(&candidate)?;
        Ok((candidate, evidence))
    }

    /// Validate a proposed refinement against this snapshot. Base instructions,
    /// storage, CFG, value IDs and all non-load operations stay source-bound.
    pub fn validate_memory_recovery(&self, candidate: &Self) -> Result<MemoryEvidence, Error> {
        validate_constants(self)?;
        let source = lower::program(self, false)?;
        let restored = lower::program(candidate, false)?;
        if source.register_count() != restored.register_count()
            || self.entry != candidate.entry
            || source.instructions() != restored.instructions()
        {
            return Err(Error::Invalid("memory recovery changed source"));
        }
        let known = known_constants(candidate)?;
        let mut expected = self.clone();
        walk::visit_mut(&mut expected, |binding| {
            if let Operation::Load { address, width } | Operation::KnownLoad { address, width, .. } =
                binding.operation
                && let Some(&value) = known.get(&binding.id)
            {
                binding.operation = Operation::KnownLoad {
                    address,
                    width,
                    value,
                };
            }
        });
        if expected.blocks != candidate.blocks
            || self.storages != candidate.storages
            || self.value_count != candidate.value_count
            || self.source_value_count != candidate.source_value_count
        {
            return Err(Error::Invalid("memory recovery changed MIR structure"));
        }
        let facts = candidate.memory_facts()?;
        check(&facts, &known)?;
        // Ensure the effect-preserving materialization also respects limits.
        lower::program(candidate, true)?;
        Ok(MemoryEvidence {
            loads: facts.loads().count(),
            proved_loads: known.len(),
            refined_loads: known.len().saturating_sub(known_constants(self)?.len()),
            unavailable_reason: facts.analysis().queries().as_ref().err().cloned(),
        })
    }
}

pub(super) fn validate_constants(function: &Function) -> Result<(), Error> {
    let known = known_constants(function)?;
    if !known.is_empty() {
        check(&function.memory_facts()?, &known)?;
    }
    Ok(())
}
fn check(facts: &MemoryFacts<'_>, known: &BTreeMap<ValueId, u64>) -> Result<(), Error> {
    for (&id, &value) in known {
        if facts.constant_load(id) != Some(value) {
            return Err(Error::Invalid("unproved KnownLoad value"));
        }
    }
    Ok(())
}
fn known_constants(function: &Function) -> Result<BTreeMap<ValueId, u64>, Error> {
    let mut known = BTreeMap::new();
    walk::visit(function, |binding| {
        if let Operation::KnownLoad { value, .. } = binding.operation
            && known.insert(binding.id, value).is_some()
        {
            return Err(Error::Invalid("duplicate KnownLoad ID"));
        }
        Ok(())
    })?;
    Ok(known)
}
