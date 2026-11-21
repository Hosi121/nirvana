//! Values that have the same bits on every dynamic visit to their definition.
//! A one-shot definition is a seed; repeated pure definitions inherit stability
//! from all SSA inputs. Cyclic phis and checked memory reads form barriers.
use super::analyze::Context;
use super::*;
use crate::model::ir::Place;
#[derive(Default)]
pub(super) struct Stability {
    pub(super) values: Vec<bool>,
    pub(super) stored: BTreeSet<Site>,
}
fn invalid() -> SsaError {
    SsaError::Malformed("memory capture stability")
}
// Return only the RHS suffix of SSA reads; Store address reads come first.
fn pure_inputs(
    context: &Context<'_>,
    site: Site,
    value: &Expr,
    budget: &mut Budget,
) -> Result<Option<Vec<ValueId>>, SsaError> {
    let mut pending = vec![value];
    let mut registers = Vec::new();
    while let Some(value) = pending.pop() {
        budget.spend(1)?;
        match value {
            Expr::Register(r) => registers.push(*r),
            Expr::Const(_) => {}
            Expr::Load { .. } => return Ok(None),
            Expr::Unary(_, v) => pending.push(v),
            Expr::Binary(_, a, b) => pending.extend([&**b, &**a]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**not_taken, &**taken, &**condition]),
        }
    }
    let point = context.point(site).ok_or_else(invalid)?;
    let start = point
        .reads
        .len()
        .checked_sub(registers.len())
        .ok_or_else(invalid)?;
    let mut result = Vec::with_capacity(registers.len());
    for (register, read) in registers.into_iter().zip(&point.reads[start..]) {
        budget.spend(1)?;
        if register != read.register {
            return Err(invalid());
        }
        result.push(*context.aliases.get(read.value.0).ok_or_else(invalid)?);
    }
    result.sort_unstable();
    result.dedup();
    Ok(Some(result))
}
pub(super) fn analyze(context: &Context<'_>) -> Result<Stability, SsaError> {
    let mut budget = Budget::new();
    let n = context.graph.values.len();
    let mut result = Stability {
        values: vec![false; n],
        stored: BTreeSet::new(),
    };
    let mut remaining = vec![None; n];
    let mut users = vec![Vec::new(); n];
    let mut pending = VecDeque::new();
    for (i, definition) in context.graph.values.iter().enumerate() {
        budget.spend(1)?;
        if context.aliases[i] != ValueId(i) {
            continue;
        }
        if context.single_value(ValueId(i)).ok_or_else(invalid)? {
            result.values[i] = true;
            pending.push_back(i);
            continue;
        }
        if let Definition::Assignment { site, .. } = definition {
            let assignment = context.assignment(*site).ok_or_else(invalid)?;
            if let Some(inputs) = pure_inputs(context, *site, &assignment.value, &mut budget)? {
                remaining[i] = Some(inputs.len());
                if inputs.is_empty() {
                    result.values[i] = true;
                    pending.push_back(i);
                }
                for input in inputs {
                    users[input.0].push(i);
                }
            }
        }
    }
    while let Some(value) = pending.pop_front() {
        for &user in &users[value] {
            budget.spend(1)?;
            let count = remaining[user].as_mut().ok_or_else(invalid)?;
            *count = count.checked_sub(1).ok_or_else(invalid)?;
            if *count == 0 && !std::mem::replace(&mut result.values[user], true) {
                pending.push_back(user);
            }
        }
    }
    for block in &context.graph.blocks {
        for point in &block.points {
            budget.spend(1)?;
            let Some(assignment) = context.assignment(point.site) else {
                continue;
            };
            if matches!(assignment.destination, Place::Memory { .. })
                && pure_inputs(context, point.site, &assignment.value, &mut budget)?
                    .is_some_and(|inputs| inputs.into_iter().all(|v| result.values[v.0]))
            {
                result.stored.insert(point.site);
            }
        }
    }
    Ok(result)
}
// Recheck the published true claims from actual syntax and every SSA read;
// this does not use the worklist, dependency counts or proposed Store set.
pub(super) fn validate(context: &Context<'_>, claims: &Stability) -> Result<(), SsaError> {
    let mut budget = Budget::new();
    if claims.values.len() != context.graph.values.len() {
        return Err(invalid());
    }
    for (i, &stable) in claims.values.iter().enumerate() {
        budget.spend(1)?;
        if !stable {
            continue;
        }
        if context.aliases[i] != ValueId(i) {
            return Err(invalid());
        }
        if context.single_value(ValueId(i)).ok_or_else(invalid)? {
            continue;
        }
        let Some(Definition::Assignment { site, .. }) = context.graph.values.get(i) else {
            return Err(invalid());
        };
        let assignment = context.assignment(*site).ok_or_else(invalid)?;
        if assignment.value.uses_memory() {
            return Err(invalid());
        }
        let point = context.point(*site).ok_or_else(invalid)?;
        if point
            .reads
            .iter()
            .any(|r| !claims.values[context.aliases[r.value.0].0])
        {
            return Err(invalid());
        }
    }
    for &site in &claims.stored {
        budget.spend(1)?;
        let assignment = context.assignment(site).ok_or_else(invalid)?;
        let Place::Memory { address, .. } = &assignment.destination else {
            return Err(invalid());
        };
        if assignment.value.uses_memory() {
            return Err(invalid());
        }
        let mut pending = vec![address];
        let mut count = 0;
        while let Some(e) = pending.pop() {
            budget.spend(1)?;
            match e {
                Expr::Register(_) => count += 1,
                Expr::Const(_) => {}
                Expr::Unary(_, v) => pending.push(v),
                Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
                Expr::Load { address, .. } => pending.push(address),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**condition, &**taken, &**not_taken]),
            }
        }
        let point = context.point(site).ok_or_else(invalid)?;
        if point
            .reads
            .get(count..)
            .ok_or_else(invalid)?
            .iter()
            .any(|r| !claims.values[context.aliases[r.value.0].0])
        {
            return Err(invalid());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{BinaryOp as B, Control, IrInstruction};
    fn r(n: usize) -> Expr {
        Expr::Register(Reg(n))
    }
    fn b(op: B, a: Expr, z: Expr) -> Expr {
        Expr::binary(op, a, z)
    }
    fn set(n: usize, value: Expr) -> Assignment {
        Assignment {
            destination: Reg(n).into(),
            value,
        }
    }
    #[test]
    fn independent_closed_claims_reject_cyclic_phis_loads_and_mutable_store_inputs() {
        let store = |value| Assignment {
            destination: Place::Memory {
                address: r(7),
                width: Width::U64,
            },
            value,
        };
        let source = Program::new(
            0,
            8,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![set(6, Expr::load(r(7), Width::U64))],
                    control: Control::Jump(1),
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![
                        set(2, Expr::load(r(7), Width::U64)),
                        set(4, b(B::Add, r(6), r(1))),
                        store(b(B::Add, r(6), r(1))),
                        store(b(B::Add, r(6), r(0))),
                        Assignment {
                            destination: Place::Memory {
                                address: b(B::Add, r(7), r(0)),
                                width: Width::U64,
                            },
                            value: b(B::Add, r(6), r(1)),
                        },
                        set(0, b(B::Add, r(0), Expr::Const(1))),
                    ],
                    control: Control::Branch {
                        condition: r(0),
                        target: 1,
                    },
                },
                IrInstruction {
                    address: 2,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(r(4)),
                },
            ],
        )
        .unwrap();
        let context = Context::new(&source).unwrap();
        let claims = analyze(&context).unwrap();
        validate(&context, &claims).unwrap();
        let stable = context
            .point(Site {
                instruction: 1,
                assignment: Some(1),
            })
            .unwrap()
            .definition
            .unwrap();
        assert!(claims.values[stable.0]);
        assert!(claims.stored.contains(&Site {
            instruction: 1,
            assignment: Some(2)
        }));
        assert!(
            claims.stored.contains(&Site {
                instruction: 1,
                assignment: Some(4)
            }),
            "mutable addresses are separate from stable RHS inputs"
        );
        let mut rejected = 0;
        for (i, d) in context.graph.values.iter().enumerate() {
            if context.aliases[i] != ValueId(i) || claims.values[i] {
                continue;
            }
            if matches!(d, Definition::Phi { .. } | Definition::Assignment { .. }) {
                let mut changed = Stability {
                    values: claims.values.clone(),
                    stored: claims.stored.clone(),
                };
                changed.values[i] = true;
                assert!(validate(&context, &changed).is_err(), "{d:?}");
                rejected += 1;
            }
        }
        let mut changed = claims;
        changed.stored.insert(Site {
            instruction: 1,
            assignment: Some(3),
        });
        assert!(validate(&context, &changed).is_err());
        assert!(rejected >= 3);
        // Initial SSA symbols remain immutable, but a physical input register
        // at a cyclic entry can already contain a later iteration's value.
        let mut rows = source.instructions().to_vec();
        rows[1].control = Control::Branch {
            condition: r(0),
            target: 0,
        };
        let reentry = Program::new(0, 8, rows).unwrap();
        let context = Context::new(&reentry).unwrap();
        let initial = context
            .graph
            .values
            .iter()
            .position(|d| matches!(d,Definition::Initial {register} if *register==Reg(0)))
            .unwrap();
        assert!(context.stable.values[context.aliases[initial].0]);
        assert!(
            context
                .capture(SavedValue::Register(context.aliases[initial]))
                .is_none()
        );
    }
}
