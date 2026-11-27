use super::super::extraction::{self, Exit, Region};
use super::*;

fn entry(program: &Program) -> u64 {
    program.cfg().block(program.cfg().entry()).start
}

fn invariants(values: &[Assignment], count: usize) -> Result<(), BuildError> {
    if values.len() > MAX_REGISTERS {
        return Err(BuildError::Limit);
    }
    let mut work = 0usize;
    for assignment in values {
        if !matches!(assignment.destination, Place::Register(Reg(id)) if id < count) {
            return Err(BuildError::Invariant);
        }
        let mut pending = vec![(&assignment.value, 0usize)];
        while let Some((value, depth)) = pending.pop() {
            work += 1;
            if work > MAX_EXPRESSIONS || depth > MAX_DEPTH {
                return Err(BuildError::Limit);
            }
            match value {
                Expr::Load { .. } => return Err(BuildError::Invariant),
                Expr::Register(Reg(id)) if *id >= count => return Err(BuildError::Invariant),
                Expr::Unary(_, value) => pending.push((value, depth + 1)),
                Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([
                    (&**condition, depth + 1),
                    (&**taken, depth + 1),
                    (&**not_taken, depth + 1),
                ]),
                _ => {}
            }
        }
    }
    Ok(())
}

fn extraction_error(error: extraction::ExtractionError) -> BuildError {
    match error {
        extraction::ExtractionError::Region(error) => BuildError::Region(error),
        extraction::ExtractionError::Boundary => BuildError::Boundary,
        _ => BuildError::Projection,
    }
}

/// Keep the checked region projection, normalize only its fresh entry and
/// rename its disjoint continuation/function-return namespace injectively.
fn chunk(
    source: &Program,
    start: u64,
    points: &BTreeMap<u64, usize>,
    equations: &[Assignment],
    returned: &BTreeMap<u64, u64>,
) -> Result<Program, BuildError> {
    let stops: Vec<_> = points.keys().copied().collect();
    let region: Region =
        extraction::extract(source, start, &stops, None).map_err(extraction_error)?;
    region.validate().map_err(extraction_error)?;
    let mut body = region.program().instructions().to_vec();
    let prefix = body.iter_mut().find(|i| i.address == 0).unwrap();
    prefix.assignments.extend_from_slice(equations);
    for instruction in &mut body {
        let Control::Return(Expr::Const(tag)) = instruction.control else {
            continue;
        };
        let mapped = match region.exit(tag).ok_or(BuildError::Projection)? {
            Exit::ContinueAt(pc) => *points.get(&pc).ok_or(BuildError::Projection)? as u64,
            Exit::FunctionReturn => {
                let Some(Assignment {
                    destination: Place::Register(capture),
                    value: Expr::Const(value),
                }) = instruction.assignments.last()
                else {
                    return Err(BuildError::DynamicReturn);
                };
                if *capture != region.return_register() {
                    return Err(BuildError::Projection);
                }
                *returned.get(value).ok_or(BuildError::Projection)?
            }
        };
        instruction.control = Control::Return(Expr::Const(mapped));
    }
    Program::new(0, region.program().register_count(), body).map_err(|_| BuildError::Projection)
}

fn bad(equations: &[Assignment]) -> Expr {
    equations.iter().fold(Expr::Const(0), |previous, equation| {
        let Place::Register(register) = equation.destination else {
            unreachable!("invariants are preflighted register equations")
        };
        Expr::binary(
            BinaryOp::Or,
            previous,
            Expr::binary(
                BinaryOp::Ne,
                Expr::Register(register),
                equation.value.clone(),
            ),
        )
    })
}

/// A pure fresh marker checks every destination equation at its actual cut.
/// The twin differs only by replacing that marker with zero. A SAT witness is
/// replayed in these local programs and is labelled a failed postcondition.
fn postconditions(
    program: &Program,
    cuts: &[Cut],
    before: bool,
) -> Result<Option<Query>, BuildError> {
    let marker = Reg(program.register_count());
    let mut changed = false;
    let mut left = program.instructions().to_vec();
    let mut right = program.instructions().to_vec();
    for (a, b) in left.iter_mut().zip(&mut right) {
        let Control::Return(Expr::Const(tag)) = a.control else {
            continue;
        };
        let value = cuts.get(tag as usize).map_or(Expr::Const(0), |cut| {
            let equations = if before {
                &cut.before_invariants
            } else {
                &cut.after_invariants
            };
            changed |= !equations.is_empty();
            bad(equations)
        });
        a.assignments.push(Assignment {
            destination: marker.into(),
            value,
        });
        b.assignments.push(Assignment {
            destination: marker.into(),
            value: Expr::Const(0),
        });
    }
    if !changed {
        return Ok(None);
    }
    let left = Program::new(0, marker.0 + 1, left).map_err(|_| BuildError::Projection)?;
    let right = Program::new(0, marker.0 + 1, right).map_err(|_| BuildError::Projection)?;
    let shared: Vec<_> = (0..marker.0).map(Reg).collect();
    Ok(Some(query(&left, &right, &shared, &[marker])?))
}

pub(super) fn problem(original: &Query, cuts: &[Cut]) -> Result<Problem, BuildError> {
    if cuts.is_empty()
        || cuts.len() > MAX_CUTS
        || original.before.register_count() > MAX_REGISTERS - 2
        || original.after.register_count() > MAX_REGISTERS - 2
    {
        return Err(BuildError::Limit);
    }
    shape::inspect(&original.before)?;
    shape::inspect(&original.after)?;
    let common = original
        .before
        .register_count()
        .min(original.after.register_count());
    let mut left_points = BTreeMap::new();
    let mut right_points = BTreeMap::new();
    for (index, cut) in cuts.iter().enumerate() {
        if cut.shared.len() > common
            || cut.shared.iter().any(|r| r.0 >= common)
            || cut.shared.windows(2).any(|pair| pair[0].0 >= pair[1].0)
            || left_points.insert(cut.before, index).is_some()
            || right_points.insert(cut.after, index).is_some()
        {
            return Err(BuildError::Boundary);
        }
        invariants(&cut.before_invariants, original.before.register_count())?;
        invariants(&cut.after_invariants, original.after.register_count())?;
    }
    let root = &cuts[0];
    if root.before != entry(&original.before)
        || root.after != entry(&original.after)
        || root.shared != original.shared
        || !root.before_invariants.is_empty()
        || !root.after_invariants.is_empty()
    {
        return Err(BuildError::Boundary);
    }
    let mut values = BTreeSet::new();
    for program in [&original.before, &original.after] {
        for instruction in program.instructions() {
            if let Control::Return(value) = &instruction.control {
                let Expr::Const(value) = value else {
                    return Err(BuildError::DynamicReturn);
                };
                values.insert(*value);
            }
        }
    }
    if cuts.len() + values.len() > MAX_INSTRUCTIONS {
        return Err(BuildError::Limit);
    }
    let returned: BTreeMap<_, _> = values
        .iter()
        .enumerate()
        .map(|(n, &value)| (value, (cuts.len() + n) as u64))
        .collect();
    let mut outputs: Vec<_> = cuts
        .iter()
        .enumerate()
        .map(|(n, cut)| ReturnOutputs {
            value: n as u64,
            registers: cut.shared.clone(),
        })
        .collect();
    outputs.extend(returned.iter().map(|(&value, &tag)| ReturnOutputs {
        value: tag,
        registers: original.outputs.at(&RunStatus::Returned(value)).to_vec(),
    }));
    let mut obligations = Vec::new();
    let mut bytes = 0usize;
    for (index, cut) in cuts.iter().enumerate() {
        let left = chunk(
            &original.before,
            cut.before,
            &left_points,
            &cut.before_invariants,
            &returned,
        )?;
        let right = chunk(
            &original.after,
            cut.after,
            &right_points,
            &cut.after_invariants,
            &returned,
        )?;
        let correspondence = query_at_returns(&left, &right, &cut.shared, &outputs)?;
        let candidates = [
            (
                Kind::BeforePostconditions,
                postconditions(&left, cuts, true)?,
            ),
            (
                Kind::AfterPostconditions,
                postconditions(&right, cuts, false)?,
            ),
            (Kind::Correspondence, Some(correspondence)),
        ];
        for (kind, query) in candidates {
            if let Some(query) = query {
                bytes = bytes
                    .checked_add(query.smt2().len())
                    .filter(|&total| total <= MAX_TOTAL_SCRIPT)
                    .ok_or(BuildError::Limit)?;
                obligations.push(Obligation {
                    cut: index,
                    kind,
                    query,
                });
            }
        }
    }
    Ok(Problem {
        original: original.clone(),
        cuts: cuts.to_vec(),
        obligations,
    })
}
