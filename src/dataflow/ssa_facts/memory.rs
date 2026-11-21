//! Extra SSA dependencies justified by byte reaching-store provenance. Construction
//! always uses the current source and graph; bindings are private and immutable.
//! Loads remain effectful expressions at their original source sites.
use super::*;
use crate::dataflow::address_identity::Operand;
use crate::dataflow::memory_ssa::{self, Definition as MemoryDefinition};
use crate::model::ir::AccessKind;

const MAX_INPUTS: usize = 262_144;

#[derive(Clone, Debug)]
pub(crate) struct Writer {
    pub(crate) site: Site,
    pub(crate) width: Width,
    pub(crate) sources: [u8; 8],
}
#[derive(Clone, Debug)]
struct Load {
    width: Width,
    writers: Vec<Writer>,
    unknown_bytes: u8,
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
            let mut writers = Vec::new();
            let mut dependencies = BTreeSet::new();
            let mut unknown_bytes = 0;
            let mut coverage = 0;
            for clobber in &query.candidates {
                budget.spend(1).ok()?;
                if clobber.byte_mask == 0
                    || clobber.byte_mask & !all_bytes != 0
                    || clobber.unknown_bytes & !clobber.byte_mask != 0
                {
                    return None;
                }
                coverage |= clobber.byte_mask;
                unknown_bytes |= clobber.unknown_bytes;
                let MemoryDefinition::Store { access: store, .. } =
                    memory.definitions().get(clobber.definition.0)?
                else {
                    unknown_bytes |= clobber.byte_mask;
                    continue;
                };
                let store = &memory.accesses().get(*store)?.source;
                if store.kind != AccessKind::Write
                    || store.operand != Operand::Destination
                    || !store.path.is_empty()
                {
                    return None;
                }
                let mut sources = clobber.byte_sources;
                let store_bytes = ((1u16 << store.width.bytes()) - 1) as u8;
                for (byte, source) in sources.iter_mut().enumerate() {
                    budget.spend(1).ok()?;
                    let mask = 1 << byte;
                    if *source & !store_bytes != 0 || clobber.byte_mask & mask == 0 && *source != 0
                    {
                        return None;
                    }
                    if clobber.byte_mask & mask != 0
                        && *source == 0
                        && clobber.unknown_bytes & mask == 0
                    {
                        return None;
                    }
                    if clobber.unknown_bytes & mask != 0 {
                        *source = 0;
                    }
                }
                writers.push(Writer {
                    site: store.site,
                    width: store.width,
                    sources,
                });
                if retained.checked_add(writers.len())? > limit {
                    return None;
                }
            }
            if coverage != all_bytes {
                return None;
            }
            for writer in &mut writers {
                for (byte, source) in writer.sources.iter_mut().enumerate() {
                    if unknown_bytes & (1 << byte) != 0 {
                        *source = 0;
                    }
                }
            }
            writers.retain(|writer| writer.sources.iter().any(|s| *s != 0));
            if writers.is_empty() {
                continue;
            }
            for writer in &writers {
                let point = points.get(&writer.site)?;
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
                    writers,
                    unknown_bytes,
                    dependencies: dependencies.into_iter().collect(),
                },
            );
        }
        Some(result)
    }
    pub(crate) fn len(&self) -> usize {
        self.loads.len()
    }
    pub(crate) fn bindings(&self) -> impl Iterator<Item = (Site, Width, &[Writer])> {
        self.loads.iter().filter_map(|(&site, load)| {
            (load.unknown_bytes == 0).then_some((site, load.width, load.writers.as_slice()))
        })
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
        let mut bytes = [D::bottom(); 8];
        for (index, byte) in bytes.iter_mut().enumerate().take(load.width.bytes()) {
            if load.unknown_bytes & (1 << index) != 0 {
                *byte = D::load(Width::U8);
            }
        }
        for writer in &load.writers {
            budget.spend(1)?;
            let point = points
                .get(&writer.site)
                .ok_or(SsaError::Malformed("memory fact store point"))?;
            let index = source
                .instructions()
                .binary_search_by_key(&writer.site.instruction, |i| i.address)
                .map_err(|_| SsaError::Malformed("memory fact store instruction"))?;
            let assignment = source.instructions()[index]
                .assignments
                .get(
                    writer
                        .site
                        .assignment
                        .ok_or(SsaError::Malformed("memory fact store site"))?,
                )
                .ok_or(SsaError::Malformed("memory fact store assignment"))?;
            let Place::Memory { address, width } = &assignment.destination else {
                return Err(SsaError::Malformed("memory fact store destination"));
            };
            if *width != writer.width {
                return Err(SsaError::Malformed("memory fact store width"));
            }
            let mut cursor = 0;
            evaluate(address, point, values, &mut cursor, budget)?;
            let (value, _) = evaluate(&assignment.value, point, values, &mut cursor, budget)?;
            if cursor != point.reads.len() {
                return Err(SsaError::Malformed("memory fact store reads"));
            }
            for (index, byte) in bytes.iter_mut().enumerate().take(load.width.bytes()) {
                for source in 0..width.bytes() {
                    budget.spend(1)?;
                    if writer.sources[index] & (1 << source) != 0 {
                        let value = D::unary(
                            UnaryOp::Extract {
                                start: (source * 8) as u8,
                                width: Width::U8,
                            },
                            value,
                        );
                        *byte = byte.join(value);
                    }
                }
            }
        }
        let mut result = D::constant(0);
        for (index, byte) in bytes.into_iter().enumerate().take(load.width.bytes()) {
            let count = D::constant((index * 8) as u64);
            budget.spend(D::binary_cost(B::Shl, byte, count))?;
            let value = D::binary(B::Shl, byte, count);
            budget.spend(D::binary_cost(B::Or, result, value))?;
            result = D::binary(B::Or, result, value);
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
