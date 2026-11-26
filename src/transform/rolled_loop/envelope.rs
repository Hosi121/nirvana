use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Envelope {
    pub header: u64,
    pub first_lane: u64,
    pub latch: u64,
    pub abrupt: Vec<u64>,
    pub lane_entries: Vec<u64>,
}
impl Envelope {
    pub fn stops(&self) -> Vec<u64> {
        let mut stops = BTreeSet::from([self.header, self.latch]);
        stops.extend(self.abrupt.iter().copied());
        stops.into_iter().collect()
    }
}
fn containing(source: &Program, pc: u64) -> Option<BlockId> {
    let index = source.instructions().iter().position(|i| i.address == pc)?;
    source
        .cfg()
        .blocks()
        .iter()
        .find(|block| block.instructions.contains(&index))
        .map(|block| block.id)
}
pub(super) fn locate(source: &Program, group: &LaneGroup) -> Result<Envelope, Error> {
    let cfg = source.cfg();
    let analysis = ControlFlowAnalysis::compute(cfg).map_err(|_| Error::Boundary)?;
    let members: Vec<_> = group
        .kernels
        .iter()
        .map(|k| containing(source, k.load.instruction).ok_or(Error::Boundary))
        .collect::<Result<_, _>>()?;
    if members.iter().copied().collect::<BTreeSet<_>>().len() != members.len() {
        return Err(Error::Boundary);
    }
    let natural = analysis
        .natural_loops()
        .iter()
        .filter(|natural| members.iter().all(|id| natural.body.contains(id)))
        .min_by_key(|natural| natural.body.len())
        .ok_or(Error::Boundary)?;
    if natural.latches.len() != 1
        || members
            .iter()
            .any(|&id| !analysis.dominates(members[0], id))
    {
        return Err(Error::Boundary);
    }
    let latch = *natural.latches.first().unwrap();
    let mut abrupt = BTreeSet::new();
    for &id in &natural.body {
        if natural.latches.contains(&id) {
            continue;
        }
        for edge in &cfg.block(id).successors {
            let Target::Block(mut target) = edge.target else {
                return Err(Error::Boundary);
            };
            if natural.body.contains(&target) {
                continue;
            }
            let mut seen = BTreeSet::new();
            while seen.insert(target) {
                let instructions = &source.instructions()[cfg.block(target).instructions.clone()];
                if instructions.iter().flat_map(|i|&i.assignments).any(|a|!matches!((&a.destination,&a.value),(Place::Register(d),Expr::Register(s))if d==s)){break;}
                let Control::Jump(pc) = instructions.last().ok_or(Error::Boundary)?.control else {
                    break;
                };
                let next = cfg.block_at(pc).ok_or(Error::Boundary)?;
                if natural.body.contains(&next) {
                    break;
                }
                target = next;
            }
            abrupt.insert(cfg.block(target).start);
        }
    }
    if abrupt.len() > extraction::live_out::MAX_CONTINUATIONS - 2 {
        return Err(Error::Limit);
    }
    Ok(Envelope {
        header: cfg.block(natural.header).start,
        first_lane: cfg.block(members[0]).start,
        latch: cfg.block(latch).start,
        abrupt: abrupt.into_iter().collect(),
        lane_entries: members.iter().map(|&id| cfg.block(id).start).collect(),
    })
}
