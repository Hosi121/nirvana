//! Extra SSA dependencies justified by exact reaching stores. Construction
//! always uses the current source and graph; bindings are private and immutable.
//! Loads remain effectful expressions at their original source sites.
use super::*;
use crate::dataflow::address_identity::Operand;
use crate::dataflow::memory_ssa::{self, Alias, Definition as MemoryDefinition};
use crate::model::ir::AccessKind;

const MAX_INPUTS: usize = 262_144;

#[derive(Clone, Debug)]
struct Load {
    width: Width,
    writers: Vec<Site>,
    dependencies: Vec<ValueId>,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct LoadInputs {
    loads: BTreeMap<Site, Load>,
    pub(crate) available: bool,
    pub(crate) store_edges: usize,
}
impl LoadInputs {
    /// Analyze the actual source, including virtual entry and every phi edge.
    /// A local memory-analysis limit yields the register-only fact domain.
    pub(crate) fn analyze(source: &Program, graph: &SsaFunction) -> Self {
        Self::try_analyze(source, graph, MAX_INPUTS).unwrap_or_default()
    }
    fn try_analyze(source: &Program, graph: &SsaFunction, limit: usize) -> Option<Self> {
        let limit = limit.min(MAX_INPUTS);
        let memory = memory_ssa::analyze(source, graph).ok()?;
        let points = point_map(graph);
        let mut budget = Budget::new();
        let mut result = Self {
            available: true,
            ..Self::default()
        };
        let mut retained = 0usize;
        for query in memory.queries().as_ref().ok()? {
            budget.spend(1).ok()?;
            let load = memory.accesses().get(query.access)?;
            let access = &load.source;
            if access.kind != AccessKind::Read
                || access.operand != Operand::Value
                || !access.path.is_empty()
                || access.result.is_none()
                || query.address_widened
                || query.candidates.is_empty()
            {
                continue;
            }
            let site = access.site;
            if !matches!(source_expr(source, site).ok()?, Expr::Load { width, .. } if *width == access.width)
                || points.get(&site)?.definition != access.result
            {
                continue;
            }
            let all_bytes = ((1u16 << access.width.bytes()) - 1) as u8;
            let mut writers = BTreeSet::new();
            let mut dependencies = BTreeSet::new();
            let mut exact = true;
            for clobber in &query.candidates {
                budget.spend(1).ok()?;
                if clobber.alias != Alias::Exact || clobber.byte_mask != all_bytes {
                    exact = false;
                    break;
                }
                let MemoryDefinition::Store { access: store, .. } =
                    memory.definitions().get(clobber.definition.0)?
                else {
                    exact = false;
                    break;
                };
                let store = &memory.accesses().get(*store)?.source;
                if store.kind != AccessKind::Write
                    || store.operand != Operand::Destination
                    || !store.path.is_empty()
                    || store.width != access.width
                {
                    exact = false;
                    break;
                }
                writers.insert(store.site);
                if retained.checked_add(writers.len())? > limit {
                    return None;
                }
                let point = points.get(&store.site)?;
                for read in &point.reads {
                    budget.spend(1).ok()?;
                    dependencies.insert(read.value);
                    if retained
                        .checked_add(writers.len())?
                        .checked_add(dependencies.len())?
                        > limit
                    {
                        return None;
                    }
                }
            }
            if !exact {
                continue;
            }
            retained = retained
                .checked_add(writers.len())?
                .checked_add(dependencies.len())?;
            if retained > limit {
                return None;
            }
            result.store_edges = result.store_edges.checked_add(writers.len())?;
            result.loads.insert(
                site,
                Load {
                    width: access.width,
                    writers: writers.into_iter().collect(),
                    dependencies: dependencies.into_iter().collect(),
                },
            );
        }
        Some(result)
    }
    pub(crate) fn len(&self) -> usize {
        self.loads.len()
    }
    pub(crate) fn bindings(&self) -> impl Iterator<Item = (Site, Width, &[Site])> {
        self.loads
            .iter()
            .map(|(&site, load)| (site, load.width, load.writers.as_slice()))
    }
    pub(super) fn dependencies(&self, site: Site) -> &[ValueId] {
        self.loads.get(&site).map_or(&[], |load| &load.dependencies)
    }
    pub(super) fn value<D: Domain>(
        &self,
        source: &Program,
        site: Site,
        points: &BTreeMap<Site, &PointValues>,
        values: &[D],
        budget: &mut Budget,
    ) -> Result<Option<D>, SsaError> {
        let Some(load) = self.loads.get(&site) else {
            return Ok(None);
        };
        let mut result = D::bottom();
        for &writer in &load.writers {
            budget.spend(1)?;
            let point = points
                .get(&writer)
                .ok_or(SsaError::Malformed("memory fact store point"))?;
            let index = source
                .instructions()
                .binary_search_by_key(&writer.instruction, |i| i.address)
                .map_err(|_| SsaError::Malformed("memory fact store instruction"))?;
            let assignment = source.instructions()[index]
                .assignments
                .get(
                    writer
                        .assignment
                        .ok_or(SsaError::Malformed("memory fact store site"))?,
                )
                .ok_or(SsaError::Malformed("memory fact store assignment"))?;
            let Place::Memory { address, width } = &assignment.destination else {
                return Err(SsaError::Malformed("memory fact store destination"));
            };
            if *width != load.width {
                return Err(SsaError::Malformed("memory fact store width"));
            }
            let mut cursor = 0;
            evaluate(address, point, values, &mut cursor, budget)?;
            let (value, _) = evaluate(&assignment.value, point, values, &mut cursor, budget)?;
            if cursor != point.reads.len() {
                return Err(SsaError::Malformed("memory fact store reads"));
            }
            let mask = D::constant(width.mask());
            budget.spend(D::binary_cost(B::And, value, mask))?;
            result = result.join(D::binary(B::And, value, mask));
        }
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{Assignment, IrInstruction, Reg};
    #[test]
    fn late_input_limit_discards_previously_completed_load_bindings() {
        let mut assignments = Vec::new();
        for address in [4096, 4104] {
            assignments.push(Assignment {
                destination: Place::Memory {
                    address: Expr::Const(address),
                    width: Width::U64,
                },
                value: Expr::Const(128),
            });
        }
        for (register, address) in [4096, 4104].into_iter().enumerate() {
            assignments.push(Assignment {
                destination: Reg(register).into(),
                value: Expr::load(Expr::Const(address), Width::U64),
            });
        }
        let source = Program::new(
            0,
            2,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(Expr::Register(Reg(1))),
            }],
        )
        .unwrap();
        let graph = SsaFunction::build(&source).unwrap();
        let full = LoadInputs::analyze(&source, &graph);
        assert!(full.available);
        assert_eq!((full.len(), full.store_edges), (2, 2));
        assert!(LoadInputs::try_analyze(&source, &graph, 1).is_none());
        let fallback = LoadInputs::try_analyze(&source, &graph, 1).unwrap_or_default();
        assert!(!fallback.available);
        assert_eq!((fallback.len(), fallback.store_edges), (0, 0));
    }
}
