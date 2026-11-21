//! Check proofs against the current source and inspect the actual candidate.
//! Capture initialization is checked independently on the candidate's SSA.
use super::analyze::Context;
use super::*;
use crate::model::ir::{Control, Place};
mod origins;
fn invalid(message: &'static str) -> SsaError {
    SsaError::Malformed(message)
}

pub(super) fn plan(
    source: &Program,
    plan: &MemoryValuePlan,
    context: &Context<'_>,
) -> Result<(), SsaError> {
    if source.register_count() != plan.source_registers
        || plan.captures.is_empty()
        || plan.captures.len() > MAX_CAPTURES
        || plan.evidence.ssa != context.evidence
        || plan.evidence.proved_loads != plan.proofs.len()
        || plan.evidence.snapshot_values != plan.captures.len()
    {
        return Err(invalid("memory value plan dimensions"));
    }
    let mut keys = BTreeSet::new();
    for &capture in &plan.captures {
        if matches!(capture.value, SavedValue::Register(value) if context.aliases.get(value.0) != Some(&value))
            || context.capture(capture.value) != Some(capture)
            || !keys.insert(capture.value)
        {
            return Err(invalid("memory value capture source"));
        }
    }
    if !plan.captures.windows(2).all(|p| p[0].value < p[1].value) {
        return Err(invalid("memory value capture order"));
    }
    let loads = context
        .loads
        .bindings()
        .map(|(site, width, writers)| (site, (width, writers)))
        .collect::<BTreeMap<_, _>>();
    let mut origins = origins::Values::default();
    let mut sites = BTreeSet::new();
    let mut used = BTreeSet::new();
    let mut budget = Budget::new();
    for proof in &plan.proofs {
        budget.spend(1)?;
        let (width, writers) = loads
            .get(&proof.site)
            .ok_or(invalid("memory value reaching stores"))?;
        if !sites.insert(proof.site)
            || *width != proof.key.width
            || !keys.contains(&proof.key.value)
            || !origins.matches(context, proof.key, writers, &mut budget)?
        {
            return Err(invalid("memory value store identity"));
        }
        used.insert(proof.key.value);
    }
    if used != keys || rewrite::mapping(plan, context).is_none() {
        return Err(invalid("memory value source classes"));
    }
    Ok(())
}
pub(super) fn check(
    source: &Program,
    plan: &MemoryValuePlan,
    candidate: &Program,
    context: &Context<'_>,
) -> Result<MemoryValueEvidence, SsaError> {
    self::plan(source, plan, context)?;
    let mut budget = Budget::new();
    ssa::preflight(candidate, &mut budget)?;
    if candidate.register_count() != source.register_count() + plan.captures.len()
        || source.instructions().len() != candidate.instructions().len()
        || source.cfg().block(source.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
    {
        return Err(invalid("memory value candidate layout"));
    }
    let mapping = rewrite::mapping(plan, context).ok_or(invalid("memory value mapping"))?;
    let captures =
        rewrite::capture_map(plan, context).ok_or(invalid("memory value capture expression"))?;
    let mut count = 0;
    for (original, actual) in source.instructions().iter().zip(candidate.instructions()) {
        budget.spend(1)?;
        if original.address != actual.address || original.size != actual.size {
            return Err(invalid("memory value instruction"));
        }
        let mut next = 0;
        check_captures(
            &captures,
            CapturePoint {
                instruction: original.address,
                after: None,
            },
            &actual.assignments,
            &mut next,
        )?;
        for (index, assignment) in original.assignments.iter().enumerate() {
            let other = actual
                .assignments
                .get(next)
                .ok_or(invalid("memory value assignment missing"))?;
            next += 1;
            let site = Site {
                instruction: original.address,
                assignment: Some(index),
            };
            if let Some(point) = context.point(site) {
                let mut cursor = 0;
                match (&assignment.destination, &other.destination) {
                    (Place::Register(a), Place::Register(b)) if a == b => {}
                    (
                        Place::Memory {
                            address: a,
                            width: aw,
                        },
                        Place::Memory {
                            address: b,
                            width: bw,
                        },
                    ) if aw == bw => {
                        count +=
                            expression(a, b, point, context, &mapping, &mut cursor, &mut budget)?;
                    }
                    _ => return Err(invalid("memory value destination")),
                }
                count += expression(
                    &assignment.value,
                    &other.value,
                    point,
                    context,
                    &mapping,
                    &mut cursor,
                    &mut budget,
                )?;
                if cursor != point.reads.len() {
                    return Err(invalid("memory value source reads"));
                }
            } else if assignment != other {
                return Err(invalid("memory value unreachable assignment"));
            }
            check_captures(
                &captures,
                CapturePoint {
                    instruction: original.address,
                    after: Some(index),
                },
                &actual.assignments,
                &mut next,
            )?;
        }
        if next != actual.assignments.len() {
            return Err(invalid("memory value extra assignment"));
        }
        let site = Site {
            instruction: original.address,
            assignment: None,
        };
        match (&original.control, &actual.control) {
            (Control::Return(a), Control::Return(b))
            | (Control::Branch { condition: a, .. }, Control::Branch { condition: b, .. }) => {
                if let (Control::Branch { target: a, .. }, Control::Branch { target: b, .. }) =
                    (&original.control, &actual.control)
                    && a != b
                {
                    return Err(invalid("memory value branch target"));
                }
                if let Some(point) = context.point(site) {
                    let mut cursor = 0;
                    count += expression(a, b, point, context, &mapping, &mut cursor, &mut budget)?;
                    if cursor != point.reads.len() {
                        return Err(invalid("memory value control reads"));
                    }
                } else if a != b {
                    return Err(invalid("memory value unreachable control"));
                }
            }
            (a, b) if a == b => {}
            _ => return Err(invalid("memory value control")),
        }
    }
    if count != plan.evidence.replaced_reads {
        return Err(invalid("memory value replacement count"));
    }
    initialized(candidate, source.register_count())?;
    Ok(plan.evidence)
}
fn check_captures(
    captures: &BTreeMap<CapturePoint, Vec<Assignment>>,
    point: CapturePoint,
    actual: &[Assignment],
    next: &mut usize,
) -> Result<(), SsaError> {
    if let Some(expected) = captures.get(&point) {
        let end = next
            .checked_add(expected.len())
            .ok_or(invalid("memory value capture count"))?;
        if actual.get(*next..end) != Some(expected.as_slice()) {
            return Err(invalid("memory value capture assignment"));
        }
        *next = end;
    }
    Ok(())
}
fn expression(
    a: &Expr,
    b: &Expr,
    point: &PointValues,
    context: &Context<'_>,
    mapping: &BTreeMap<ValueId, Expr>,
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<usize, SsaError> {
    budget.spend(1)?;
    Ok(match (a, b) {
        (Expr::Const(a), Expr::Const(b)) if a == b => 0,
        (Expr::Register(a), b) => {
            let read = point
                .reads
                .get(*cursor)
                .ok_or(invalid("memory value missing read"))?;
            *cursor += 1;
            if *a != read.register {
                return Err(invalid("memory value read source"));
            }
            let class = context
                .aliases
                .get(read.value.0)
                .ok_or(invalid("memory value read identity"))?;
            let expected = mapping.get(class).cloned().unwrap_or(Expr::Register(*a));
            if *b != expected {
                return Err(invalid("memory value wrong replacement"));
            }
            usize::from(Expr::Register(*a) != *b)
        }
        (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => {
            expression(x, y, point, context, mapping, cursor, budget)?
        }
        (Expr::Binary(a, l, r), Expr::Binary(b, x, y)) if a == b => {
            expression(l, x, point, context, mapping, cursor, budget)?
                + expression(r, y, point, context, mapping, cursor, budget)?
        }
        (
            Expr::Load {
                address: a,
                width: aw,
            },
            Expr::Load {
                address: b,
                width: bw,
            },
        ) if aw == bw => expression(a, b, point, context, mapping, cursor, budget)?,
        (
            Expr::Select {
                condition: a,
                taken: b,
                not_taken: c,
            },
            Expr::Select {
                condition: x,
                taken: y,
                not_taken: z,
            },
        ) => {
            expression(a, x, point, context, mapping, cursor, budget)?
                + expression(b, y, point, context, mapping, cursor, budget)?
                + expression(c, z, point, context, mapping, cursor, budget)?
        }
        _ => return Err(invalid("memory value changed expression effects")),
    })
}
// Only sanctioned captures write the suffix registers. An initial suffix
// value reaching any suffix read through phi edges means uninitialized use.
fn initialized(candidate: &Program, prefix: usize) -> Result<(), SsaError> {
    let graph = SsaFunction::build(candidate)
        .ok_or(SsaError::Unavailable("memory value initialization SSA"))?;
    let mut budget = Budget::new();
    let mut bad = vec![false; graph.values.len()];
    let mut users = vec![Vec::new(); graph.values.len()];
    let mut pending = VecDeque::new();
    for (index, definition) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        match definition {
            Definition::Initial { register } if register.0 >= prefix => {
                bad[index] = true;
                pending.push_back(index);
            }
            Definition::Phi { inputs, .. } => {
                for input in inputs {
                    budget.spend(1)?;
                    users[input.value.0].push(index);
                }
            }
            _ => {}
        }
    }
    while let Some(index) = pending.pop_front() {
        for &user in &users[index] {
            budget.spend(1)?;
            if !std::mem::replace(&mut bad[user], true) {
                pending.push_back(user);
            }
        }
    }
    for point in graph.blocks.iter().flat_map(|b| &b.points) {
        for read in &point.reads {
            budget.spend(1)?;
            if read.register.0 >= prefix && bad[read.value.0] {
                return Err(invalid("memory value capture used before initialization"));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::IrInstruction;
    fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
        IrInstruction {
            address,
            size: 1,
            assignments,
            control,
        }
    }
    fn set(value: u64) -> Assignment {
        Assignment {
            destination: Reg(1).into(),
            value: Expr::Const(value),
        }
    }
    #[test]
    fn initialization_checks_every_phi_input_and_virtual_entry_backedges() {
        let branch = |assigned| {
            Program::new(
                0,
                2,
                vec![
                    ins(
                        0,
                        vec![],
                        Control::Branch {
                            condition: Expr::Register(Reg(0)),
                            target: 2,
                        },
                    ),
                    ins(
                        1,
                        if assigned { vec![set(1)] } else { vec![] },
                        Control::Jump(3),
                    ),
                    ins(2, vec![set(2)], Control::Jump(3)),
                    ins(3, vec![], Control::Return(Expr::Register(Reg(1)))),
                ],
            )
            .unwrap()
        };
        assert!(initialized(&branch(false), 1).is_err());
        assert!(initialized(&branch(true), 1).is_ok());
        let looped = Program::new(
            0,
            2,
            vec![
                ins(
                    0,
                    vec![],
                    Control::Branch {
                        condition: Expr::Register(Reg(1)),
                        target: 2,
                    },
                ),
                ins(1, vec![], Control::Return(Expr::Register(Reg(1)))),
                ins(2, vec![set(1)], Control::Jump(0)),
            ],
        )
        .unwrap();
        assert!(initialized(&looped, 1).is_err());
    }
}

#[cfg(test)]
mod byte_mutants {
    use super::*;
    use crate::model::ir::{IrInstruction, Width};
    #[test]
    fn independent_origins_reject_wrong_source_and_offset_despite_matching_capture_schema() {
        let r = |i| Expr::Register(Reg(i));
        let source = Program::new(
            0,
            8,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Place::Memory {
                            address: r(7),
                            width: Width::U8,
                        },
                        value: r(0),
                    },
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::Const(0),
                    },
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(r(7), Width::U8),
                    },
                ],
                control: Control::Return(r(2)),
            }],
        )
        .unwrap();
        let context = analyze::Context::new(&source).unwrap();
        let good = MemoryValuePlan::analyze(&source).unwrap();
        for wrong_source in [false, true] {
            let mut plan = good.clone();
            let mut key = plan.proofs[0].key;
            if wrong_source {
                let id=context.graph.values.iter().position(|definition|matches!(definition,Definition::Initial{register} if *register==Reg(7))).unwrap();
                key.value = SavedValue::Register(context.aliases[id]);
            } else {
                key.start = 8;
            }
            plan.proofs[0].key = key;
            plan.captures[0] = context.capture(key.value).unwrap();
            let (candidate, _) = rewrite::construct(&source, &plan, &context).unwrap();
            assert!(matches!(
                check(&source, &plan, &candidate, &context),
                Err(SsaError::Malformed("memory value store identity"))
            ));
            let mut initial = vec![0; 8];
            initial[0] = 0x3412;
            initial[6] = 0x5678;
            initial[7] = 4096;
            let expected = source
                .execute_with_memory(&initial, 4096, &[0; 32], 1)
                .unwrap();
            initial.resize(candidate.register_count(), u64::MAX);
            let wrong = candidate
                .execute_with_memory(&initial, 4096, &[0; 32], 1)
                .unwrap();
            assert_ne!(expected.value, wrong.value);
        }
    }
}

#[cfg(test)]
mod stored_mutants {
    use super::*;
    use crate::model::ir::{BinaryOp as B, IrInstruction};
    #[test]
    fn opaque_results_of_distinct_store_expressions_are_not_equal() {
        let r = |n| Expr::Register(Reg(n));
        let source = Program::new(
            0,
            8,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Place::Memory {
                            address: r(7),
                            width: Width::U64,
                        },
                        value: Expr::binary(B::Add, r(0), r(1)),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: Expr::binary(B::Add, r(7), Expr::Const(16)),
                            width: Width::U64,
                        },
                        value: Expr::binary(B::Mul, r(0), r(1)),
                    },
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(Expr::binary(B::Add, r(7), Expr::Const(1)), Width::U16),
                    },
                ],
                control: Control::Return(r(2)),
            }],
        )
        .unwrap();
        let context = Context::new(&source).unwrap();
        let mut plan = MemoryValuePlan::analyze(&source).unwrap();
        assert!(matches!(plan.proofs[0].key.value, SavedValue::Stored(_)));
        let wrong = SavedValue::Stored(Site {
            instruction: 0,
            assignment: Some(1),
        });
        plan.proofs[0].key.value = wrong;
        plan.captures[0] = context.capture(wrong).unwrap();
        let (candidate, _) = rewrite::construct(&source, &plan, &context).unwrap();
        assert!(matches!(
            check(&source, &plan, &candidate, &context),
            Err(SsaError::Malformed("memory value store identity"))
        ));
        let mut initial = vec![0; 8];
        initial[0] = 256;
        initial[1] = 2;
        initial[7] = 4096;
        let before = source
            .execute_with_memory(&initial, 4096, &[0; 32], 1)
            .unwrap();
        initial.resize(candidate.register_count(), u64::MAX);
        let after = candidate
            .execute_with_memory(&initial, 4096, &[0; 32], 1)
            .unwrap();
        assert_ne!(before.value, after.value);
    }
}
