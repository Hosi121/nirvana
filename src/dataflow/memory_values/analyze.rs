use super::*;
use crate::control_flow::cfg::Target;
use crate::dataflow::address_identity;
use crate::model::ir::BinaryOp as B;
pub(super) struct Context<'a> {
    pub source: &'a Program,
    pub graph: SsaFunction,
    pub aliases: Vec<ValueId>,
    pub loads: LoadInputs,
    pub evidence: SsaEvidence,
    points: BTreeMap<Site, (usize, usize)>,
    prefix: Vec<bool>,
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
        let prefix = entry_prefix(source, &mut budget)?;
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
            prefix,
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
    pub fn capture(&self, key: Key) -> Option<Capture> {
        let entry = self.source.cfg().block(self.source.cfg().entry()).start;
        let (source, point, block) = match *self.graph.values.get(key.value.0)? {
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
        self.prefix[id.index()].then_some(Capture { key, point, source })
    }
    pub fn root_class(&self, site: Site) -> Option<ValueId> {
        self.aliases.get(self.point(site)?.definition?.0).copied()
    }
    pub fn stored_value(&self, site: Site, width: Width, budget: &mut Budget) -> Option<ValueId> {
        let register = projected_register(&self.assignment(site)?.value, width, budget)?;
        let read = self.point(site)?.reads.last()?;
        if read.register != register {
            return None;
        }
        self.aliases.get(read.value.0).copied()
    }
    pub fn load_key(
        &self,
        site: Site,
        width: Width,
        writers: &[Site],
        budget: &mut Budget,
    ) -> Option<Key> {
        let mut source = None;
        for &writer in writers {
            budget.spend(1).ok()?;
            let value = self.stored_value(writer, width, budget)?;
            if source.is_some_and(|old| old != value) {
                return None;
            }
            source = Some(value);
        }
        let key = Key {
            value: source?,
            width,
        };
        self.capture(key)?;
        self.root_class(site)?;
        Some(key)
    }
}
// Kahn removal identifies the entry region preceding every cycle. Each
// removed block executes at most once. Cycle successors stay conservative.
fn entry_prefix(source: &Program, budget: &mut Budget) -> Option<Vec<bool>> {
    let cfg = source.cfg();
    let reachable = cfg.reachable_blocks();
    let mut degree = vec![0usize; cfg.blocks().len()];
    for &id in &reachable {
        for edge in &cfg.block(id).successors {
            budget.spend(1).ok()?;
            let Target::Block(to) = edge.target else {
                return None;
            };
            degree[to.index()] = degree[to.index()].checked_add(1)?;
        }
    }
    let mut pending: VecDeque<_> = reachable
        .iter()
        .copied()
        .filter(|id| degree[id.index()] == 0)
        .collect();
    let mut prefix = vec![false; degree.len()];
    while let Some(id) = pending.pop_front() {
        budget.spend(1).ok()?;
        prefix[id.index()] = true;
        for edge in &cfg.block(id).successors {
            budget.spend(1).ok()?;
            let Target::Block(to) = edge.target else {
                return None;
            };
            degree[to.index()] = degree[to.index()].checked_sub(1)?;
            if degree[to.index()] == 0 {
                pending.push_back(to);
            }
        }
    }
    Some(prefix)
}
fn projected_register(mut e: &Expr, width: Width, budget: &mut Budget) -> Option<Reg> {
    loop {
        budget.spend(1).ok()?;
        e = match e {
            Expr::Register(r) => return Some(*r),
            Expr::Unary(UnaryOp::SignExtend(w), value) if *w >= width => value,
            Expr::Unary(UnaryOp::Extract { start: 0, width: w }, value) if *w >= width => value,
            Expr::Binary(B::And, value, mask) if matches!(&**mask, Expr::Const(n) if n & width.mask() == width.mask()) => {
                value
            }
            Expr::Binary(B::And, mask, value) if matches!(&**mask, Expr::Const(n) if n & width.mask() == width.mask()) => {
                value
            }
            _ => return None,
        };
    }
}
pub(super) fn collect(context: &Context<'_>) -> Option<(Vec<LoadProof>, Vec<Capture>)> {
    let mut budget = Budget::new();
    let mut proofs = Vec::new();
    let mut classes = BTreeMap::new();
    for (site, width, writers) in context.loads.bindings() {
        let key = context.load_key(site, width, writers, &mut budget);
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
    let keys = proofs.iter().map(|p| p.key).collect::<BTreeSet<_>>();
    if keys.is_empty()
        || keys.len() > MAX_CAPTURES
        || context.source.register_count().checked_add(keys.len())? > ssa::MAX_REGISTERS
    {
        return None;
    }
    let captures = keys
        .into_iter()
        .map(|key| context.capture(key))
        .collect::<Option<Vec<_>>>()?;
    Some((proofs, captures))
}
