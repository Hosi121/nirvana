//! Check entry facts on every original edge, then inspect each actual rewrite.
//! Symbolic value numbering and scalar primitives are the shared encoding base.
use super::*;

pub(super) fn validate(
    source: &Program,
    plan: &PredicatePlan,
    candidate: &Program,
) -> Result<PredicateEvidence, ssa::SsaError> {
    let source_ssa = ssa::validate(source, &plan.graph)?;
    let order = order(source)?;
    let values = Values::build(source, &plan.graph, &order)?;
    if plan.entries.len() != source.cfg().blocks().len() {
        return Err(invalid("predicate entry dimensions"));
    }
    let mut work = ssa::Budget::new();
    let mut cells = 0;
    for &id in &order {
        let state = plan.entries[id.index()]
            .as_ref()
            .ok_or(invalid("missing predicate entry"))?;
        cells += state.len();
        if cells > ssa::MAX_STATE_CELLS {
            return Err(ssa::SsaError::Unavailable("predicate fact cells"));
        }
        if let Facts::Known(facts) = state
            && facts.keys().any(|id| *id >= values.nodes.len())
        {
            return Err(invalid("predicate fact value"));
        }
        if id == source.cfg().entry() {
            if *state != Facts::empty() {
                return Err(invalid("predicate virtual entry"));
            }
            continue;
        }
        for &predecessor in &source.cfg().block(id).predecessors {
            let Some(before) = plan.entries[predecessor.index()].as_ref() else {
                continue;
            };
            for edge in source
                .cfg()
                .block(predecessor)
                .successors
                .iter()
                .filter(|e| e.target == Target::Block(id))
            {
                let incoming = before.close_edge(
                    &values.nodes,
                    condition(source, &values, predecessor, edge.kind),
                    &mut work,
                )?;
                if matches!(incoming, Facts::Unreachable) {
                    continue;
                }
                let Facts::Known(claims) = state else {
                    return Err(invalid("unproved predicate reachability"));
                };
                let words = incoming.evaluate(&values.nodes, &mut work)?;
                if claims
                    .iter()
                    .any(|(id, truth)| words[*id].truth() != Some(*truth))
                {
                    return Err(invalid("predicate predecessor implication"));
                }
            }
        }
    }
    if source.register_count() != candidate.register_count()
        || source.cfg().block(source.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
        || source.instructions().len() != candidate.instructions().len()
    {
        return Err(invalid("predicate candidate layout"));
    }
    let mut evidence = PredicateEvidence {
        source_ssa,
        blocks_before: source.cfg().reachable_blocks().len(),
        blocks_after: candidate.cfg().reachable_blocks().len(),
        ..PredicateEvidence::default()
    };
    for block in source.cfg().blocks() {
        let words = match plan.entries.get(block.id.index()).and_then(Option::as_ref) {
            Some(state @ Facts::Known(_)) => Some(state.evaluate(&values.nodes, &mut work)?),
            _ => None,
        };
        for index in block.instructions.clone() {
            let original = &source.instructions()[index];
            let actual = &candidate.instructions()[index];
            work.spend(1)?;
            if original.address != actual.address
                || original.size != actual.size
                || original.assignments.len() != actual.assignments.len()
            {
                return Err(invalid("predicate instruction layout"));
            }
            if original == actual {
                continue;
            }
            let words = words
                .as_ref()
                .ok_or(invalid("predicate change outside proved entry"))?;
            for (n, (a, b)) in original
                .assignments
                .iter()
                .zip(&actual.assignments)
                .enumerate()
            {
                if a.destination != b.destination {
                    return Err(invalid("predicate destination"));
                }
                if a.value == b.value {
                    continue;
                }
                let site = ssa::Site {
                    instruction: original.address,
                    assignment: Some(n),
                };
                if !matches!(a.destination, Place::Register(_)) || a.value.uses_memory() {
                    return Err(invalid("predicate memory rewrite"));
                }
                let Expr::Const(value) = b.value else {
                    return Err(invalid("predicate nonconstant rewrite"));
                };
                if words[values.definitions[&site]] != Word::Constant(value) {
                    return Err(invalid("predicate assignment value"));
                }
                evidence.constant_assignments += 1;
            }
            if original.control == actual.control {
                continue;
            }
            match (&original.control, &actual.control) {
                (Control::Branch { condition, target }, changed) if !condition.uses_memory() => {
                    let truth = words[values.controls[&original.address]]
                        .truth()
                        .ok_or(invalid("unproved predicate branch"))?;
                    let expected = if truth {
                        Control::Jump(*target)
                    } else {
                        Control::Next
                    };
                    if *changed != expected {
                        return Err(invalid("predicate branch destination"));
                    }
                    evidence.pruned_branches += 1;
                }
                (Control::Return(before), Control::Return(Expr::Const(value)))
                    if !before.uses_memory() =>
                {
                    if words[values.controls[&original.address]] != Word::Constant(*value) {
                        return Err(invalid("predicate return value"));
                    }
                    evidence.constant_returns += 1;
                }
                _ => return Err(invalid("predicate control rewrite")),
            }
        }
    }
    Ok(evidence)
}
