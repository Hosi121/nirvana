use super::analyze::Context;
use super::*;
use crate::model::ir::{Control, IrInstruction, Place};

pub(super) fn mapping(plan: &MemoryValuePlan) -> Option<BTreeMap<ValueId, Expr>> {
    let captures = plan
        .captures
        .iter()
        .enumerate()
        .map(|(index, capture)| (capture.value, Reg(plan.source_registers + index)))
        .collect::<BTreeMap<_, _>>();
    let mut result = BTreeMap::new();
    for (id, key) in plan.facts.iter().enumerate() {
        if let Some(key) = key {
            let register = *captures.get(&key.value)?;
            result.insert(ValueId(id), word(*key, Expr::Register(register)));
        }
    }
    Some(result)
}
pub(super) fn capture_map(
    plan: &MemoryValuePlan,
    context: &Context<'_>,
) -> Option<BTreeMap<CapturePoint, Vec<Assignment>>> {
    let mut result = BTreeMap::<_, Vec<_>>::new();
    for (index, capture) in plan.captures.iter().enumerate() {
        result.entry(capture.point).or_default().push(Assignment {
            destination: Reg(plan.source_registers + index).into(),
            value: capture.expression(context)?,
        });
    }
    Some(result)
}
pub(super) fn construct(
    source: &Program,
    plan: &MemoryValuePlan,
    context: &Context<'_>,
) -> Option<(Program, usize)> {
    let registers = source.register_count().checked_add(plan.captures.len())?;
    if registers > ssa::MAX_REGISTERS {
        return None;
    }
    let mapping = mapping(plan)?;
    let captures = capture_map(plan, context)?;
    let mut instructions = Vec::with_capacity(source.instructions().len());
    let mut count = 0;
    let mut budget = Budget::new();
    for original in source.instructions() {
        budget.spend(1).ok()?;
        let mut assignments = captures
            .get(&CapturePoint {
                instruction: original.address,
                after: None,
            })
            .cloned()
            .unwrap_or_default();
        for (index, assignment) in original.assignments.iter().enumerate() {
            let site = Site {
                instruction: original.address,
                assignment: Some(index),
            };
            let mapped = if let Some(point) = context.point(site) {
                let mut cursor = 0;
                let destination = match &assignment.destination {
                    Place::Register(r) => (*r).into(),
                    Place::Memory { address, width } => Place::Memory {
                        address: expression(
                            address,
                            point,
                            &mapping,
                            &mut cursor,
                            &mut count,
                            &mut budget,
                        )?,
                        width: *width,
                    },
                };
                let value = expression(
                    &assignment.value,
                    point,
                    &mapping,
                    &mut cursor,
                    &mut count,
                    &mut budget,
                )?;
                if cursor != point.reads.len() {
                    return None;
                }
                Assignment { destination, value }
            } else {
                assignment.clone()
            };
            assignments.push(mapped);
            if let Some(after) = captures.get(&CapturePoint {
                instruction: original.address,
                after: Some(index),
            }) {
                assignments.extend_from_slice(after);
            }
        }
        let site = Site {
            instruction: original.address,
            assignment: None,
        };
        let control = if let Some(point) = context.point(site) {
            let mut cursor = 0;
            let control = match &original.control {
                Control::Return(e) => Control::Return(expression(
                    e,
                    point,
                    &mapping,
                    &mut cursor,
                    &mut count,
                    &mut budget,
                )?),
                Control::Branch { condition, target } => Control::Branch {
                    condition: expression(
                        condition,
                        point,
                        &mapping,
                        &mut cursor,
                        &mut count,
                        &mut budget,
                    )?,
                    target: *target,
                },
                other => other.clone(),
            };
            if cursor != point.reads.len() {
                return None;
            }
            control
        } else {
            original.control.clone()
        };
        instructions.push(IrInstruction {
            address: original.address,
            size: original.size,
            assignments,
            control,
        });
    }
    let candidate = Program::new(
        source.cfg().block(source.cfg().entry()).start,
        registers,
        instructions,
    )
    .ok()?;
    let mut preflight = Budget::new();
    ssa::preflight(&candidate, &mut preflight).ok()?;
    Some((candidate, count))
}
fn expression(
    e: &Expr,
    point: &PointValues,
    mapping: &BTreeMap<ValueId, Expr>,
    cursor: &mut usize,
    count: &mut usize,
    budget: &mut Budget,
) -> Option<Expr> {
    budget.spend(1).ok()?;
    Some(match e {
        Expr::Const(_) => e.clone(),
        Expr::Register(register) => {
            let read = point.reads.get(*cursor)?;
            *cursor += 1;
            if *register != read.register {
                return None;
            }
            if let Some(target) = mapping.get(&read.value) {
                *count += 1;
                target.clone()
            } else {
                e.clone()
            }
        }
        Expr::Unary(op, value) => Expr::unary(
            *op,
            expression(value, point, mapping, cursor, count, budget)?,
        ),
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            expression(a, point, mapping, cursor, count, budget)?,
            expression(b, point, mapping, cursor, count, budget)?,
        ),
        Expr::Load { address, width } => Expr::load(
            expression(address, point, mapping, cursor, count, budget)?,
            *width,
        ),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            expression(condition, point, mapping, cursor, count, budget)?,
            expression(taken, point, mapping, cursor, count, budget)?,
            expression(not_taken, point, mapping, cursor, count, budget)?,
        ),
    })
}
