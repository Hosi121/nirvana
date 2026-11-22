//! An immutable MemorySSA view attached to one MIR snapshot. MIR value IDs
//! are linked by source paths, not merely by the order/width of nearby loads.
use super::*;
use crate::dataflow::{address_identity as address, memory_ssa as mem, ssa_constants};
use crate::model::ir::AccessKind;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Load {
    pub value: ValueId,
    pub address: ValueId,
    pub width: Width,
    pub origin: Origin,
    /// None denotes an entry-unreachable memory operation.
    pub access: Option<usize>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Store {
    pub site: ssa::Site,
    pub address: ValueId,
    pub value: ValueId,
    pub width: Width,
    pub access: Option<usize>,
    /// The RHS value on successful completion, when known from scalar operands.
    pub constant: Option<u64>,
}
#[derive(Debug)]
pub enum LoadFlow<'a> {
    Unreachable,
    Unavailable(&'a str),
    Reaching {
        incoming: mem::MemoryId,
        candidates: &'a [mem::Clobber],
    },
}
#[derive(Debug)]
pub struct MemoryFacts<'a> {
    function: &'a Function,
    analysis: mem::Analysis,
    loads: BTreeMap<ValueId, Load>,
    stores: BTreeMap<ssa::Site, Store>,
    store_accesses: BTreeMap<usize, ssa::Site>,
    queries: BTreeMap<usize, usize>,
}
impl Function {
    pub fn memory_facts(&self) -> Result<MemoryFacts<'_>, Error> {
        // Analyze the original read, independent of any claimed KnownLoad.
        let source = lower::program(self, false)?;
        let analysis = mem::analyze(&source, &self.ssa).map_err(Error::Memory)?;
        let constants = ssa_constants::ConstantPlan::analyze(&source).filter(|plan| {
            ssa_constants::validate_facts(&source, &self.ssa, plan.values()).is_ok()
        });
        let constants = constants.as_ref().map_or(&[][..], |plan| plan.values());
        let mut facts = MemoryFacts {
            function: self,
            analysis,
            loads: BTreeMap::new(),
            stores: BTreeMap::new(),
            store_accesses: BTreeMap::new(),
            queries: BTreeMap::new(),
        };
        let mut index = Index::new(&facts.analysis)?;
        for block in &self.blocks {
            for step in &block.steps {
                for (n, statement) in step.statements.iter().enumerate() {
                    let site = ssa::Site {
                        instruction: step.address,
                        assignment: Some(n),
                    };
                    match statement {
                        Statement::WriteStorage { value, .. } => {
                            index.region(value, &mut Vec::new(), &mut facts.loads)?
                        }
                        Statement::Store {
                            address,
                            width,
                            value,
                        } => {
                            index.region(
                                address,
                                &mut vec![address::PathEdge::Address],
                                &mut facts.loads,
                            )?;
                            index.region(value, &mut Vec::new(), &mut facts.loads)?;
                            let access = index.link(
                                site,
                                address::Operand::Destination,
                                &[],
                                AccessKind::Write,
                                *width,
                            )?;
                            if let Some(access) = access {
                                facts.store_accesses.insert(access, site);
                            }
                            facts.stores.insert(
                                site,
                                Store {
                                    site,
                                    address: address.result,
                                    value: value.result,
                                    width: *width,
                                    access,
                                    constant: constant(value, constants),
                                },
                            );
                        }
                    }
                }
            }
            match &block.terminator {
                Terminator::Branch { condition, .. } | Terminator::Return(condition) => {
                    index.region(condition, &mut Vec::new(), &mut facts.loads)?
                }
                _ => {}
            }
        }
        let reachable: std::collections::BTreeSet<_> = self
            .ssa
            .blocks
            .iter()
            .flat_map(|b| &b.points)
            .map(|p| p.site)
            .collect();
        if facts
            .loads
            .values()
            .any(|l| reachable.contains(&l.origin.site) != l.access.is_some())
            || facts
                .stores
                .values()
                .any(|s| reachable.contains(&s.site) != s.access.is_some())
        {
            return Err(Error::Invalid("missing or unreachable memory access"));
        }
        if index.used.len() != facts.analysis.accesses().len() {
            return Err(Error::Invalid("unmapped MemorySSA access"));
        }
        if let Ok(queries) = facts.analysis.queries() {
            for (n, query) in queries.iter().enumerate() {
                if facts.queries.insert(query.access, n).is_some() {
                    return Err(Error::Invalid("duplicate memory query"));
                }
            }
            if facts.loads.values().filter(|l| l.access.is_some()).count() != facts.queries.len() {
                return Err(Error::Invalid("missing memory query"));
            }
        }
        Ok(facts)
    }
}
impl MemoryFacts<'_> {
    pub fn function(&self) -> &Function {
        self.function
    }
    pub fn analysis(&self) -> &mem::Analysis {
        &self.analysis
    }
    pub fn loads(&self) -> impl Iterator<Item = &Load> {
        self.loads.values()
    }
    pub fn stores(&self) -> impl Iterator<Item = &Store> {
        self.stores.values()
    }
    pub fn load(&self, id: ValueId) -> Option<&Load> {
        self.loads.get(&id)
    }
    pub fn store(&self, definition: mem::MemoryId) -> Option<&Store> {
        let mem::Definition::Store { access, .. } =
            self.analysis.definitions().get(definition.0)?
        else {
            return None;
        };
        self.stores.get(self.store_accesses.get(access)?)
    }
    pub fn flow(&self, id: ValueId) -> Result<LoadFlow<'_>, Error> {
        let load = self
            .loads
            .get(&id)
            .ok_or(Error::Invalid("not a MIR Load"))?;
        let Some(access) = load.access else {
            return Ok(LoadFlow::Unreachable);
        };
        let queries = match self.analysis.queries() {
            Ok(queries) => queries,
            Err(reason) => return Ok(LoadFlow::Unavailable(reason)),
        };
        let query = &queries[*self
            .queries
            .get(&access)
            .ok_or(Error::Invalid("missing memory query"))?];
        Ok(LoadFlow::Reaching {
            incoming: self.analysis.accesses()[access].incoming,
            candidates: &query.candidates,
        })
    }
    /// Require every possible source of each byte to agree. Unknown initial or
    /// opaque bytes and missing coverage keep the value unknown.
    pub fn constant_load(&self, id: ValueId) -> Option<u64> {
        let load = self.load(id)?;
        let LoadFlow::Reaching { candidates, .. } = self.flow(id).ok()? else {
            return None;
        };
        let mut result = 0u64;
        for byte in 0..load.width.bytes() {
            let mut agreed = None;
            for writer in candidates.iter().filter(|w| w.byte_mask & (1 << byte) != 0) {
                if writer.unknown_bytes & (1 << byte) != 0 {
                    return None;
                }
                let store = self.store(writer.definition)?;
                let value = store.constant?;
                let sources = writer.byte_sources[byte];
                if sources == 0 || u16::from(sources) >= (1u16 << store.width.bytes()) {
                    return None;
                }
                for source in 0..store.width.bytes() {
                    if sources & (1 << source) == 0 {
                        continue;
                    }
                    let value = ((value >> (8 * source)) & 255) as u8;
                    if agreed.is_some_and(|old| old != value) {
                        return None;
                    }
                    agreed = Some(value);
                }
            }
            result |= u64::from(agreed?) << (8 * byte);
        }
        Some(result)
    }
}

/// Scalar facts concern the result after successful region evaluation; no
/// effect is removed. Region scoping and SSA validation are checked by lifting.
fn constant(region: &Region, constants: &[ssa_constants::ConstantValue]) -> Option<u64> {
    let mut values = BTreeMap::<ValueId, Option<u64>>::new();
    for binding in &region.bindings {
        let value = match &binding.operation {
            Operation::Pure(Pure::Constant(n)) => Some(*n),
            Operation::Pure(Pure::Unary(op, id)) => values[id].map(|n| op.evaluate(n)),
            Operation::Pure(Pure::Binary(op, a, b)) => {
                values[a].zip(values[b]).map(|(a, b)| op.evaluate(a, b))
            }
            Operation::Select {
                condition,
                taken,
                not_taken,
            } => match values[condition] {
                Some(n) => constant(if n != 0 { taken } else { not_taken }, constants),
                None => constant(taken, constants)
                    .filter(|value| Some(*value) == constant(not_taken, constants)),
            },
            Operation::ReadStorage {
                version: Some(id), ..
            }
            | Operation::ReadSaved {
                version: Some(id), ..
            } => match constants.get(id.0) {
                Some(ssa_constants::ConstantValue::Known(value)) => Some(*value),
                _ => None,
            },
            Operation::ReadStorage { version: None, .. }
            | Operation::ReadSaved { version: None, .. }
            | Operation::Load { .. }
            | Operation::KnownLoad { .. } => None,
        };
        values.insert(binding.id, value);
    }
    values[&region.result]
}

// Local ordinal tags avoid imposing ordering on the public source enums.
type AccessKey = (ssa::Site, u8, Vec<u8>, u8);
fn key(
    site: ssa::Site,
    operand: address::Operand,
    path: &[address::PathEdge],
    kind: AccessKind,
) -> AccessKey {
    (
        site,
        operand as u8,
        path.iter().map(|edge| *edge as u8).collect(),
        kind as u8,
    )
}

struct Index<'a> {
    analysis: &'a mem::Analysis,
    // Paths are keyed within each original site/operand; comparison is exact.
    by_path: BTreeMap<AccessKey, usize>,
    used: std::collections::BTreeSet<usize>,
    work: ssa::Budget,
}
impl<'a> Index<'a> {
    fn new(analysis: &'a mem::Analysis) -> Result<Self, Error> {
        let mut by_path = BTreeMap::new();
        let mut work = ssa::Budget::new();
        for (index, access) in analysis.accesses().iter().enumerate() {
            let a = &access.source;
            work.spend(a.path.len() + 1).map_err(Error::Ssa)?;
            if by_path
                .insert(key(a.site, a.operand, &a.path, a.kind), index)
                .is_some()
            {
                return Err(Error::Invalid("duplicate MemorySSA source path"));
            }
        }
        Ok(Self {
            analysis,
            by_path,
            used: Default::default(),
            work,
        })
    }
    fn link(
        &mut self,
        site: ssa::Site,
        operand: address::Operand,
        path: &[address::PathEdge],
        kind: AccessKind,
        width: Width,
    ) -> Result<Option<usize>, Error> {
        self.work.spend(path.len() + 1).map_err(Error::Ssa)?;
        // Sites absent from MemorySSA can be either memory-free or unreachable.
        // The caller separately checks reachability for each Load/Store.
        let Some(&index) = self.by_path.get(&key(site, operand, path, kind)) else {
            return Ok(None);
        };
        if self.analysis.accesses()[index].source.width != width || !self.used.insert(index) {
            return Err(Error::Invalid("MIR/MemorySSA width or duplicate access"));
        }
        Ok(Some(index))
    }
    fn region(
        &mut self,
        region: &Region,
        path: &mut Vec<address::PathEdge>,
        loads: &mut BTreeMap<ValueId, Load>,
    ) -> Result<(), Error> {
        let values = region
            .bindings
            .iter()
            .map(|v| (v.id, v))
            .collect::<BTreeMap<_, _>>();
        self.value(region.result, &values, path, loads)
    }
    fn child(
        &mut self,
        id: ValueId,
        values: &BTreeMap<ValueId, &Binding>,
        path: &mut Vec<address::PathEdge>,
        edge: address::PathEdge,
        loads: &mut BTreeMap<ValueId, Load>,
    ) -> Result<(), Error> {
        path.push(edge);
        let result = self.value(id, values, path, loads);
        path.pop();
        result
    }
    fn value(
        &mut self,
        id: ValueId,
        values: &BTreeMap<ValueId, &Binding>,
        path: &mut Vec<address::PathEdge>,
        loads: &mut BTreeMap<ValueId, Load>,
    ) -> Result<(), Error> {
        self.work.spend(path.len() + 1).map_err(Error::Ssa)?;
        let binding = values
            .get(&id)
            .ok_or(Error::Invalid("memory view value scope"))?;
        match &binding.operation {
            Operation::Pure(Pure::Unary(_, input)) => {
                self.child(*input, values, path, address::PathEdge::Unary, loads)?
            }
            Operation::Pure(Pure::Binary(_, a, b)) => {
                self.child(*a, values, path, address::PathEdge::Left, loads)?;
                self.child(*b, values, path, address::PathEdge::Right, loads)?;
            }
            Operation::Load {
                address: input,
                width,
            }
            | Operation::KnownLoad {
                address: input,
                width,
                ..
            } => {
                self.child(*input, values, path, address::PathEdge::Address, loads)?;
                let operand = match binding.origin.operand {
                    Operand::Address => address::Operand::Destination,
                    Operand::Value => address::Operand::Value,
                    Operand::Control => address::Operand::Control,
                };
                let access =
                    self.link(binding.origin.site, operand, path, AccessKind::Read, *width)?;
                if loads
                    .insert(
                        id,
                        Load {
                            value: id,
                            address: *input,
                            width: *width,
                            origin: binding.origin,
                            access,
                        },
                    )
                    .is_some()
                {
                    return Err(Error::Invalid("duplicated MIR Load"));
                }
            }
            Operation::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.child(
                    *condition,
                    values,
                    path,
                    address::PathEdge::Condition,
                    loads,
                )?;
                path.push(address::PathEdge::Taken);
                self.region(taken, path, loads)?;
                path.pop();
                path.push(address::PathEdge::NotTaken);
                self.region(not_taken, path, loads)?;
                path.pop();
            }
            _ => {}
        }
        Ok(())
    }
}
