//! An inductive correspondence check, independent of SSA construction.
//!
//! A phi denotes the raw register on block entry, provided all incoming edges
//! supply that register's predecessor-exit value. Sequential reads then use the
//! current identity and writes replace it only after checking their operands.
//! Cycles need no fixed-point guessing: this is induction over executed edges,
//! including the virtual initial edge. Expressions, loads, stores and faults
//! stay at the source sites; this checker neither evaluates nor moves them.
use super::*;
use crate::model::ir::Place;

fn malformed(message: &'static str) -> SsaError {
    SsaError::Malformed(message)
}
fn bounded(
    total: &mut usize,
    count: usize,
    limit: usize,
    what: &'static str,
) -> Result<(), SsaError> {
    *total = total
        .checked_add(count)
        .ok_or(SsaError::Unavailable(what))?;
    if *total > limit {
        return Err(SsaError::Unavailable(what));
    }
    Ok(())
}
fn valid_id(id: ValueId, count: usize) -> Result<(), SsaError> {
    if id.0 >= count {
        Err(malformed("value index"))
    } else {
        Ok(())
    }
}

/// Inspect all untrusted collection lengths and indices before allocating
/// value-indexed storage or following any candidate reference.
fn candidate_bounds(candidate: &SsaFunction, budget: &mut Budget) -> Result<(), SsaError> {
    if candidate.register_count > MAX_REGISTERS
        || candidate.blocks.len() > MAX_BLOCKS
        || candidate.values.len() > MAX_VALUES
    {
        return Err(SsaError::Unavailable("candidate size"));
    }
    let (mut phis, mut points, mut reads, mut exits, mut inputs) = (0, 0, 0, 0, 0);
    for node in &candidate.values {
        budget.spend(1)?;
        let register = match node {
            Definition::Initial { register } | Definition::Assignment { register, .. } => register,
            Definition::Phi {
                register,
                inputs: edges,
                ..
            } => {
                bounded(&mut inputs, edges.len(), MAX_PHI_INPUTS, "phi inputs")?;
                budget.spend(edges.len())?;
                for edge in edges {
                    valid_id(edge.value, candidate.values.len())?;
                }
                register
            }
        };
        if register.0 >= candidate.register_count {
            return Err(malformed("definition register"));
        }
    }
    for block in &candidate.blocks {
        budget.spend(1)?;
        bounded(&mut phis, block.phis.len(), MAX_VALUES, "phi listings")?;
        bounded(
            &mut points,
            block.points.len(),
            MAX_ASSIGNMENTS + MAX_INSTRUCTIONS,
            "points",
        )?;
        bounded(
            &mut exits,
            block.exit_values.len(),
            MAX_STATE_CELLS,
            "exit state",
        )?;
        budget.spend(block.phis.len())?;
        for &id in &block.phis {
            valid_id(id, candidate.values.len())?;
        }
        for point in &block.points {
            budget.spend(1)?;
            if let Some(id) = point.definition {
                valid_id(id, candidate.values.len())?;
            }
            bounded(&mut reads, point.reads.len(), MAX_NODES, "register reads")?;
            budget.spend(point.reads.len())?;
            for read in &point.reads {
                if read.register.0 >= candidate.register_count {
                    return Err(malformed("read register"));
                }
                valid_id(read.value, candidate.values.len())?;
            }
        }
        budget.spend(block.exit_values.len())?;
        for exit in &block.exit_values {
            if exit.register.0 >= candidate.register_count {
                return Err(malformed("exit register"));
            }
            valid_id(exit.value, candidate.values.len())?;
        }
    }
    Ok(())
}

fn claim(claimed: &mut [bool], id: ValueId) -> Result<(), SsaError> {
    if std::mem::replace(&mut claimed[id.0], true) {
        return Err(malformed("duplicate definition"));
    }
    Ok(())
}

fn check_reads(
    expr: &Expr,
    point: &PointValues,
    cursor: &mut usize,
    current: &[Option<ValueId>],
    budget: &mut Budget,
) -> Result<(), SsaError> {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        budget.spend(1)?;
        match expr {
            Expr::Const(_) => {}
            Expr::Register(register) => {
                let value = current[register.0]
                    .ok_or(malformed("read has no entry or preceding definition"))?;
                if point.reads.get(*cursor)
                    != Some(&RegisterValue {
                        register: *register,
                        value,
                    })
                {
                    return Err(malformed("ordered register correspondence"));
                }
                *cursor += 1;
            }
            Expr::Binary(_, left, right) => pending.extend([&**right, &**left]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**not_taken, &**taken, &**condition]),
        }
    }
    Ok(())
}

pub(super) fn validate(source: &Program, candidate: &SsaFunction) -> Result<SsaEvidence, SsaError> {
    let mut budget = Budget::new();
    preflight(source, &mut budget)?;
    candidate_bounds(candidate, &mut budget)?;
    let cfg = source.cfg();
    if candidate.entry != cfg.block(cfg.entry()).start
        || candidate.register_count != source.register_count()
    {
        return Err(malformed("source entry or register count"));
    }
    let reachable = cfg.reachable_blocks();
    if candidate.blocks.len() != reachable.len() {
        return Err(malformed("reachable block count"));
    }
    // All allocations below are bounded by the two preflight checks above.
    let mut block_index = vec![None; cfg.blocks().len()];
    let mut claimed = vec![false; candidate.values.len()];
    let mut initials = vec![None; source.register_count()];
    for (index, block) in candidate.blocks.iter().enumerate() {
        budget.spend(1)?;
        let id = cfg.block_at(block.start).ok_or(malformed("block start"))?;
        if !reachable.contains(&id) || block_index[id.index()].replace(index).is_some() {
            return Err(malformed("duplicate or unreachable block"));
        }
    }
    for (index, node) in candidate.values.iter().enumerate() {
        budget.spend(1)?;
        if let Definition::Initial { register } = node {
            if initials[register.0].replace(ValueId(index)).is_some() {
                return Err(malformed("duplicate initial register"));
            }
            claimed[index] = true;
        }
    }
    let mut evidence = SsaEvidence {
        blocks: reachable.len(),
        definitions: candidate.values.len(),
        ..SsaEvidence::default()
    };
    for id in &reachable {
        let block = &candidate.blocks
            [block_index[id.index()].ok_or(malformed("missing reachable block"))?];
        budget.spend(source.register_count())?;
        let mut current = vec![None; source.register_count()];
        for &value in &block.phis {
            budget.spend(1)?;
            let Definition::Phi {
                block: owner,
                register,
                ..
            } = &candidate.values[value.0]
            else {
                return Err(malformed("phi listing is not a phi"));
            };
            if *owner != block.start || current[register.0].replace(value).is_some() {
                return Err(malformed("phi owner or duplicate register"));
            }
            claim(&mut claimed, value)?;
            evidence.phis += 1;
        }
        let mut points = block.points.iter();
        for instruction in &source.instructions()[cfg.block(*id).instructions.clone()] {
            for (assignment_index, assignment) in instruction.assignments.iter().enumerate() {
                budget.spend(1)?;
                let site = Site {
                    instruction: instruction.address,
                    assignment: Some(assignment_index),
                };
                let point = points.next().ok_or(malformed("missing assignment point"))?;
                if point.site != site {
                    return Err(malformed("assignment site or order"));
                }
                let mut cursor = 0;
                if let Place::Memory { address, .. } = &assignment.destination {
                    check_reads(address, point, &mut cursor, &current, &mut budget)?;
                }
                check_reads(&assignment.value, point, &mut cursor, &current, &mut budget)?;
                if cursor != point.reads.len() {
                    return Err(malformed("extra register reads"));
                }
                evidence.register_reads += cursor;
                match &assignment.destination {
                    Place::Register(register) => {
                        let value = point
                            .definition
                            .ok_or(malformed("missing assignment definition"))?;
                        if candidate.values[value.0]
                            != (Definition::Assignment {
                                site,
                                register: *register,
                            })
                        {
                            return Err(malformed("assignment definition origin"));
                        }
                        claim(&mut claimed, value)?;
                        current[register.0] = Some(value);
                    }
                    Place::Memory { .. } => {
                        if point.definition.is_some() {
                            return Err(malformed("store defines register"));
                        }
                    }
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                let point = points.next().ok_or(malformed("missing control point"))?;
                if point.site
                    != (Site {
                        instruction: instruction.address,
                        assignment: None,
                    })
                    || point.definition.is_some()
                {
                    return Err(malformed("control point origin"));
                }
                let mut cursor = 0;
                check_reads(condition, point, &mut cursor, &current, &mut budget)?;
                if cursor != point.reads.len() {
                    return Err(malformed("extra control reads"));
                }
                evidence.register_reads += cursor;
            }
        }
        if points.next().is_some() {
            return Err(malformed("extra points"));
        }
        let mut previous = None;
        for exit in &block.exit_values {
            budget.spend(1)?;
            if previous.is_some_and(|register| register >= exit.register.0)
                || current[exit.register.0] != Some(exit.value)
            {
                return Err(malformed("exit correspondence or order"));
            }
            previous = Some(exit.register.0);
        }
    }
    if claimed.iter().any(|claimed| !claimed) {
        return Err(malformed("orphan definition"));
    }
    // Check edge equations only after each predecessor's exit has been proved.
    // CFG predecessors are already unique, including coincident branch arms.
    for id in &reachable {
        let block = &candidate.blocks[block_index[id.index()].ok_or(malformed("missing block"))?];
        let mut expected = Vec::new();
        if *id == cfg.entry() {
            expected.push(None);
        }
        for predecessor in &cfg.block(*id).predecessors {
            budget.spend(1)?;
            if reachable.contains(predecessor) {
                expected.push(Some(cfg.block(*predecessor).start));
            }
        }
        for &phi in &block.phis {
            let Definition::Phi {
                register, inputs, ..
            } = &candidate.values[phi.0]
            else {
                return Err(malformed("phi node"));
            };
            if inputs.len() != expected.len() {
                return Err(malformed("incomplete phi edges"));
            }
            budget.spend(expected.len())?;
            let mut seen = vec![false; expected.len()];
            for input in inputs {
                budget.spend(1)?;
                let edge_index = expected
                    .binary_search(&input.predecessor)
                    .map_err(|_| malformed("non-predecessor phi edge"))?;
                if std::mem::replace(&mut seen[edge_index], true) {
                    return Err(malformed("duplicate phi edge"));
                }
                let value = match input.predecessor {
                    None => initials[register.0].ok_or(malformed("missing initial definition"))?,
                    Some(start) => {
                        let predecessor =
                            cfg.block_at(start).ok_or(malformed("phi predecessor"))?;
                        let predecessor = &candidate.blocks[block_index[predecessor.index()]
                            .ok_or(malformed("unreachable predecessor"))?];
                        let exit_index = predecessor
                            .exit_values
                            .binary_search_by_key(&register.0, |exit| exit.register.0)
                            .map_err(|_| malformed("missing predecessor exit"))?;
                        predecessor.exit_values[exit_index].value
                    }
                };
                if input.value != value {
                    return Err(malformed("phi edge correspondence"));
                }
                evidence.phi_inputs += 1;
            }
        }
    }
    Ok(evidence)
}
