use super::*;
use crate::address_identity::ModularAddress;
use crate::ssa::ValueId;

const MAX_TERMS: usize = 16;

pub(super) struct Translation<'a> {
    graph: &'a SsaFunction,
    values: &'a BTreeMap<ValueId, ModularAddress>,
    owners: Vec<Option<u64>>,
}

impl<'a> Translation<'a> {
    pub(super) fn new(
        graph: &'a SsaFunction,
        values: &'a BTreeMap<ValueId, ModularAddress>,
    ) -> Self {
        let mut owners = vec![None; graph.values.len()];
        for block in &graph.blocks {
            for point in &block.points {
                if let Some(id) = point.definition {
                    owners[id.0] = Some(block.start);
                }
            }
        }
        Self {
            graph,
            values,
            owners,
        }
    }

    /// Simultaneous substitution: incoming forms name the predecessor's
    /// dynamic values. A loop-header phi inside an incoming form therefore
    /// belongs to the previous iteration and is translated on the next edge.
    pub(super) fn edge(
        &self,
        address: Option<&ModularAddress>,
        block: u64,
        predecessor: Option<u64>,
        budget: &mut usize,
    ) -> Result<Option<ModularAddress>, String> {
        let Some(address) = address else {
            return Ok(None);
        };
        let mut offset = address.offset;
        let mut terms: BTreeMap<ValueId, u64> = BTreeMap::new();
        for &(id, coefficient) in &address.terms {
            spend(budget, 1)?;
            let replacement = match &self.graph.values[id.0] {
                crate::ssa::Definition::Phi {
                    block: owner,
                    inputs,
                    ..
                } if *owner == block => {
                    spend(budget, inputs.len())?;
                    let input = inputs
                        .iter()
                        .find(|i| i.predecessor == predecessor)
                        .ok_or("memory SSA phi edge has no register input")?;
                    Some(
                        self.values
                            .get(&input.value)
                            .ok_or("memory SSA phi input lacks an address fact")?,
                    )
                }
                crate::ssa::Definition::Assignment { .. } if self.owners[id.0] == Some(block) => {
                    // A fresh load, opaque result or non-affine computation
                    // inside this block has no value in its predecessor.
                    return Ok(None);
                }
                _ => None,
            };
            if let Some(form) = replacement {
                spend(budget, form.terms.len() + 1)?;
                offset = offset.wrapping_add(coefficient.wrapping_mul(form.offset));
                for &(value, scale) in &form.terms {
                    let old = terms.entry(value).or_default();
                    *old = old.wrapping_add(coefficient.wrapping_mul(scale));
                }
            } else {
                let old = terms.entry(id).or_default();
                *old = old.wrapping_add(coefficient);
            }
            terms.retain(|_, coefficient| *coefficient != 0);
            if terms.len() > MAX_TERMS {
                return Ok(None);
            }
        }
        Ok(Some(ModularAddress {
            offset,
            terms: terms.into_iter().collect(),
        }))
    }
}

fn spend(budget: &mut usize, amount: usize) -> Result<(), String> {
    *budget = budget
        .checked_sub(amount)
        .ok_or("memory SSA address translation work limit")?;
    Ok(())
}
