//! Entry-execution predicate invariants for closed DAGs. SSA values are immutable
//! on this domain. Loads produce opaque values; source memory effects and guest
//! steps stay unchanged. Claimed facts are checked on every original CFG edge.
//! The contract covers executions from the source entry, including prefixes;
//! resumption from an arbitrary externally supplied mid-function state requires
//! establishing the corresponding path facts first.
use crate::{
    cfg::{BlockId, EdgeKind, Target},
    ir::{Control, Expr, Place, Program},
    ssa,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
mod facts;
mod symbolic;
mod verify;
use facts::{Facts, Word};
use symbolic::Values;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PredicateEvidence {
    pub source_ssa: ssa::SsaEvidence,
    pub pruned_branches: usize,
    pub constant_assignments: usize,
    pub constant_returns: usize,
    pub blocks_before: usize,
    pub blocks_after: usize,
}
#[derive(Clone, Debug)]
pub struct PredicatePlan {
    graph: ssa::SsaFunction,
    entries: Vec<Option<Facts>>,
}
fn invalid(message: &'static str) -> ssa::SsaError {
    ssa::SsaError::Malformed(message)
}

fn order(source: &Program) -> Result<Vec<BlockId>, ssa::SsaError> {
    let reachable = source.cfg().reachable_blocks();
    let mut degrees = vec![0; source.cfg().blocks().len()];
    for &id in &reachable {
        for e in &source.cfg().block(id).successors {
            let Target::Block(target) = e.target else {
                return Err(ssa::SsaError::Unavailable("predicate open CFG"));
            };
            degrees[target.index()] += 1;
        }
    }
    let mut pending: VecDeque<_> = reachable
        .iter()
        .copied()
        .filter(|id| degrees[id.index()] == 0)
        .collect();
    let mut result = Vec::new();
    while let Some(id) = pending.pop_front() {
        result.push(id);
        for e in &source.cfg().block(id).successors {
            let Target::Block(target) = e.target else {
                unreachable!()
            };
            degrees[target.index()] -= 1;
            if degrees[target.index()] == 0 {
                pending.push_back(target);
            }
        }
    }
    if result.len() != reachable.len() {
        return Err(ssa::SsaError::Unavailable("predicate cyclic CFG"));
    }
    Ok(result)
}
fn condition(
    source: &Program,
    values: &Values,
    id: BlockId,
    kind: EdgeKind,
) -> Option<(usize, bool)> {
    if !matches!(kind, EdgeKind::Taken | EdgeKind::NotTaken) {
        return None;
    }
    let last = &source.instructions()[source.cfg().block(id).instructions.end - 1];
    Some((values.controls[&last.address], kind == EdgeKind::Taken))
}
impl PredicatePlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        let order = order(source).ok()?;
        let graph = ssa::SsaFunction::build(source)?;
        let values = Values::build(source, &graph, &order).ok()?;
        let mut incoming = vec![Vec::new(); source.cfg().blocks().len()];
        let mut entries = vec![None; incoming.len()];
        let mut work = ssa::Budget::new();
        let mut cells = 0;
        for id in order {
            let state = if id == source.cfg().entry() {
                Facts::empty()
            } else {
                Facts::intersection(&incoming[id.index()], &mut work).ok()?
            };
            cells += state.len();
            if cells > ssa::MAX_STATE_CELLS {
                return None;
            }
            entries[id.index()] = Some(state.clone());
            for e in &source.cfg().block(id).successors {
                let Target::Block(target) = e.target else {
                    unreachable!()
                };
                incoming[target.index()].push(
                    state
                        .edge(
                            &values.nodes,
                            condition(source, &values, id, e.kind),
                            &mut work,
                        )
                        .ok()?,
                );
            }
        }
        let plan = Self { graph, entries };
        let (_, evidence) = plan.lower(source)?;
        (evidence.pruned_branches > 0).then_some(plan)
    }
    pub fn lower(&self, source: &Program) -> Option<(Program, PredicateEvidence)> {
        ssa::validate(source, &self.graph).ok()?;
        let order = order(source).ok()?;
        let values = Values::build(source, &self.graph, &order).ok()?;
        let mut instructions = source.instructions().to_vec();
        let mut work = ssa::Budget::new();
        for id in order {
            let state = self.entries.get(id.index())?.as_ref()?;
            if matches!(state, Facts::Unreachable) {
                continue;
            }
            let words = state.evaluate(&values.nodes, &mut work).ok()?;
            for instruction in &mut instructions[source.cfg().block(id).instructions.clone()] {
                for (n, a) in instruction.assignments.iter_mut().enumerate() {
                    let site = ssa::Site {
                        instruction: instruction.address,
                        assignment: Some(n),
                    };
                    if matches!(a.destination, Place::Register(_))
                        && !a.value.uses_memory()
                        && let Word::Constant(value) = words[values.definitions[&site]]
                    {
                        a.value = Expr::Const(value);
                    }
                }
                match &instruction.control {
                    Control::Branch { condition, target } if !condition.uses_memory() => {
                        if let Some(truth) = words[values.controls[&instruction.address]].truth() {
                            instruction.control = if truth {
                                Control::Jump(*target)
                            } else {
                                Control::Next
                            };
                        }
                    }
                    Control::Return(value) if !value.uses_memory() => {
                        if let Word::Constant(value) = words[values.controls[&instruction.address]]
                        {
                            instruction.control = Control::Return(Expr::Const(value));
                        }
                    }
                    _ => {}
                }
            }
        }
        let candidate =
            Program::new(self.graph.entry, source.register_count(), instructions).ok()?;
        let evidence = validate(source, self, &candidate).ok()?;
        Some((candidate, evidence))
    }
}
pub fn validate(
    source: &Program,
    plan: &PredicatePlan,
    candidate: &Program,
) -> Result<PredicateEvidence, ssa::SsaError> {
    verify::validate(source, plan, candidate)
}
