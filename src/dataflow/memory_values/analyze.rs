use super::*;
use crate::dataflow::address_identity;
pub(super) struct Context<'a> {
    pub source: &'a Program,
    pub graph: SsaFunction,
    pub aliases: Vec<ValueId>,
    pub loads: LoadInputs,
    pub evidence: SsaEvidence,
    points: BTreeMap<Site, (usize, usize)>,
    single_visit: Vec<bool>,
}
impl<'a> Context<'a> {
    pub fn new(source: &'a Program) -> Option<Self> {
        let graph = SsaFunction::build(source)?;
        let evidence = ssa::validate(source, &graph).ok()?;
        let aliases = address_identity::aliases(source, &graph, &BTreeSet::new())?;
        let loads = LoadInputs::analyze(source, &graph);
        if !loads.available {
            return None;
        }
        let mut budget = Budget::new();
        let single_visit = super::single_visit::blocks(source, &mut budget)?;
        let mut points = BTreeMap::new();
        for (b, block) in graph.blocks.iter().enumerate() {
            for (p, point) in block.points.iter().enumerate() {
                budget.spend(1).ok()?;
                points.insert(point.site, (b, p));
            }
        }
        Some(Self {
            source,
            graph,
            aliases,
            loads,
            evidence,
            points,
            single_visit,
        })
    }
    pub fn point(&self, site: Site) -> Option<&PointValues> {
        let &(b, p) = self.points.get(&site)?;
        self.graph.blocks.get(b)?.points.get(p)
    }
    pub fn assignment(&self, site: Site) -> Option<&Assignment> {
        let i = self
            .source
            .instructions()
            .binary_search_by_key(&site.instruction, |i| i.address)
            .ok()?;
        self.source.instructions()[i]
            .assignments
            .get(site.assignment?)
    }
    pub fn capture(&self, value: ValueId) -> Option<Capture> {
        let entry = self.source.cfg().block(self.source.cfg().entry()).start;
        let (source, point, block) = match *self.graph.values.get(value.0)? {
            Definition::Initial { register } => (
                register,
                CapturePoint {
                    instruction: entry,
                    after: None,
                },
                entry,
            ),
            Definition::Assignment { site, register } => {
                let &(b, _) = self.points.get(&site)?;
                (
                    register,
                    CapturePoint {
                        instruction: site.instruction,
                        after: site.assignment,
                    },
                    self.graph.blocks[b].start,
                )
            }
            Definition::Phi {
                block, register, ..
            } => (
                register,
                CapturePoint {
                    instruction: block,
                    after: None,
                },
                block,
            ),
        };
        let id = self.source.cfg().block_at(block)?;
        self.single_visit[id.index()].then_some(Capture {
            value,
            point,
            source,
        })
    }
    pub fn root_class(&self, site: Site) -> Option<ValueId> {
        self.aliases.get(self.point(site)?.definition?.0).copied()
    }
    pub fn load_key(
        &self,
        site: Site,
        width: Width,
        writers: &[ReachingWriter],
        prefer_expand: bool,
        budget: &mut Budget,
    ) -> Option<Key> {
        for expand in [true, false]
            .into_iter()
            .filter(|expand| prefer_expand || !expand)
        {
            if let Some(key) = self.byte_key(width, writers, expand, budget)
                && self.capture(key.value).is_some()
                && self.root_class(site).is_some()
            {
                return Some(key);
            }
        }
        None
    }
    fn byte_key(
        &self,
        width: Width,
        writers: &[ReachingWriter],
        expand: bool,
        budget: &mut Budget,
    ) -> Option<Key> {
        let mut key = None;
        for byte in 0..width.bytes() {
            let mut found = false;
            for writer in writers {
                for source in 0..writer.width.bytes() {
                    budget.spend(1).ok()?;
                    if writer.sources[byte] & (1 << source) == 0 {
                        continue;
                    }
                    let (value, start) =
                        super::projection::stored_byte(self, writer.site, source, expand, budget)?;
                    let start = start.checked_sub((byte * 8) as u8)?;
                    let candidate = Key {
                        value,
                        start,
                        width,
                    };
                    if key.is_some_and(|old| old != candidate) {
                        return None;
                    }
                    key = Some(candidate);
                    found = true;
                }
            }
            if !found {
                return None;
            }
        }
        let key = key?;
        Some(key)
    }
}
pub(super) fn collect(
    context: &Context<'_>,
    prefer_expand: bool,
) -> Option<(Vec<LoadProof>, Vec<Capture>)> {
    let mut budget = Budget::new();
    let mut proofs = Vec::new();
    let mut classes = BTreeMap::new();
    for (site, width, writers) in context.loads.bindings() {
        let key = context.load_key(site, width, writers, prefer_expand, &mut budget);
        // Matching spends one unit at a time. A failed match must not hide
        // exhaustion and publish bindings collected earlier in the pass.
        budget.spend(1).ok()?;
        let Some(key) = key else {
            continue;
        };
        let class = context.root_class(site)?;
        classes
            .entry(class)
            .and_modify(|old| {
                if *old != Some(key) {
                    *old = None;
                }
            })
            .or_insert(Some(key));
        proofs.push(LoadProof { site, key });
    }
    proofs.retain(|proof| {
        context
            .root_class(proof.site)
            .is_some_and(|c| classes.get(&c) == Some(&Some(proof.key)))
    });
    let keys = proofs.iter().map(|p| p.key.value).collect::<BTreeSet<_>>();
    if keys.is_empty()
        || keys.len() > MAX_CAPTURES
        || context.source.register_count().checked_add(keys.len())? > ssa::MAX_REGISTERS
    {
        return None;
    }
    let captures = keys
        .into_iter()
        .map(|value| context.capture(value))
        .collect::<Option<Vec<_>>>()?;
    Some((proofs, captures))
}
