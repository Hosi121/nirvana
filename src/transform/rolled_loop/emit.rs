use super::*;

// A low-word subtraction is zero exactly when two values already within that
// word are equal. Keep this narrow shape; the final region check still decides.
fn condition(expression: &Expr) -> Expr {
    use crate::model::ir::UnaryOp;
    let Expr::Binary(op, left, right) = expression else {
        return expression.clone();
    };
    if !matches!(op, BinaryOp::Eq | BinaryOp::Ne) || **right != Expr::Const(0) {
        return expression.clone();
    }
    let Expr::Unary(UnaryOp::Extract { start: 0, width }, value) = &**left else {
        return expression.clone();
    };
    let Expr::Binary(BinaryOp::Sub, a, b) = &**value else {
        return expression.clone();
    };
    let Expr::Binary(BinaryOp::And, _, mask) = &**a else {
        return expression.clone();
    };
    let (Expr::Const(mask), Expr::Const(value)) = (&**mask, &**b) else {
        return expression.clone();
    };
    let bits = width.bytes() * 8;
    if bits < 64 && (*mask >> bits != 0 || *value >> bits != 0) {
        return expression.clone();
    }
    Expr::binary(*op, (**a).clone(), (**b).clone())
}

pub(super) fn candidate(
    source: &Program,
    group: &LaneGroup,
    envelope: &Envelope,
    before: &Region,
    controls: &controls::Controls,
    counter: Reg,
) -> Result<(Program, u64), Error> {
    let selected = controls.first.source_to_region();
    let blocks: Vec<_> = source
        .cfg()
        .blocks()
        .iter()
        .filter(|block| selected.contains_key(&block.start))
        .collect();
    if blocks.iter().any(|block| {
        source.instructions()[block.instructions.clone()]
            .iter()
            .any(|i| !selected.contains_key(&i.address))
    }) {
        return Err(Error::Projection);
    }
    let redirects:BTreeMap<_,_>=blocks.iter().filter_map(|block| {
        let body=&source.instructions()[block.instructions.clone()];
        if body.iter().flat_map(|i|&i.assignments).all(|a|matches!((&a.destination,&a.value),(Place::Register(d),Expr::Register(s))if d==s))
            && let Control::Jump(to)=body.last()?.control { return Some((block.start,to)); }

        None
    }).collect();
    let blocks: Vec<_> = blocks
        .into_iter()
        .filter(|block| !redirects.contains_key(&block.start))
        .collect();
    let by_pc: BTreeMap<_, _> = blocks.iter().map(|&block| (block.start, block)).collect();
    let thread = |mut pc| -> Result<u64, Error> {
        let mut seen = BTreeSet::new();
        while let Some(&to) = redirects.get(&pc) {
            if !seen.insert(pc) {
                return Err(Error::Projection);
            }
            pc = to;
        }
        Ok(pc)
    };
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut pending = vec![(envelope.first_lane, false)];
    while let Some((pc, done)) = pending.pop() {
        let pc = thread(pc)?;
        let Some(block) = by_pc.get(&pc) else {
            continue;
        };
        if done {
            order.push(pc);
            continue;
        }
        if !seen.insert(pc) {
            continue;
        }
        pending.push((pc, true));
        let last = &source.instructions()[block.instructions.end - 1];
        let successors = match &last.control {
            Control::Jump(to) => vec![*to],
            Control::Next => vec![last.address + u64::from(last.size)],
            Control::Branch {
                condition: original,
                target,
            } => {
                if last.address == controls.limit.site && controls.staging.is_some() {
                    vec![]
                } else {
                    let mut children = vec![*target, last.address + u64::from(last.size)];
                    if matches!(condition(original), Expr::Binary(BinaryOp::Ne, _, _)) {
                        children.swap(0, 1);
                    }
                    children
                }
            }
            Control::Return(_) => return Err(Error::Boundary),
        };
        pending.extend(successors.into_iter().rev().map(|to| (to, false)));
    }
    order.reverse();
    let blocks: Vec<_> = order.iter().map(|pc| by_pc[pc]).collect();
    let base = source
        .instructions()
        .iter()
        .map(|i| i.address.checked_add(u64::from(i.size)).ok_or(Error::Limit))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .max()
        .ok_or(Error::Source)?
        .checked_add(16)
        .ok_or(Error::Limit)?;
    base.checked_add(2 * blocks.len() as u64 + 2)
        .ok_or(Error::Limit)?;
    let labels: BTreeMap<_, _> = blocks
        .iter()
        .enumerate()
        .map(|(n, block)| (block.start, base + 2 * n as u64))
        .collect();
    let init = base + 2 * blocks.len() as u64;
    let increment = init + 1;
    let feedback = *labels.get(&envelope.first_lane).ok_or(Error::Projection)?;
    let route = |pc: u64| -> Result<u64, Error> {
        let mut pc = pc;
        let mut seen = BTreeSet::new();
        while let Some(&to) = redirects.get(&pc) {
            if !seen.insert(pc) {
                return Err(Error::Projection);
            }
            pc = to;
        }
        if pc == envelope.lane_entries[1] {
            Ok(increment)
        } else if let Some(&label) = labels.get(&pc) {
            Ok(label)
        } else if controls.first.continuations().contains(&pc) {
            Ok(pc)
        } else {
            Err(Error::Projection)
        }
    };
    let mut instructions = source.instructions().to_vec();
    for i in &mut instructions {
        if i.address == envelope.header {
            let mut masks: Vec<_> = before
                .input_bit_caps()
                .iter()
                .enumerate()
                .filter(|(_, bits)| **bits < 64)
                .map(|(reg, &bits)| Assignment {
                    destination: Reg(reg).into(),
                    value: Expr::binary(
                        BinaryOp::And,
                        Expr::Register(Reg(reg)),
                        Expr::Const((1u64 << bits) - 1),
                    ),
                })
                .collect();
            masks.append(&mut i.assignments);
            i.assignments = masks;
        }
        if i.address == envelope.first_lane {
            i.assignments.clear();
            i.control = Control::Jump(init);
        }
    }
    for block in blocks {
        let body = &source.instructions()[block.instructions.clone()];
        let mut assignments = Vec::new();
        for i in body {
            for (n, assignment) in i.assignments.iter().enumerate() {
                let site = Site {
                    instruction: i.address,
                    assignment: Some(n),
                };
                let mut assignment = assignment.clone();
                if let Some((changed, _, temporary)) = controls.staging
                    && site == changed
                {
                    assignment.destination = temporary.into();
                }
                if site == group.kernels[0].load {
                    let Expr::Load { address, .. } = &mut assignment.value else {
                        return Err(Error::Pattern);
                    };
                    **address = controls.load_address.clone();
                }
                if let Some((changed, dest, index)) = &controls.break_update
                    && site == *changed
                {
                    assignment.value =
                        Expr::binary(BinaryOp::Xor, Expr::Register(*dest), index.clone());
                }
                if site == group.kernels[0].update
                    && let Expr::Binary(BinaryOp::Add, a, b) = &mut assignment.value
                    && **b == Expr::Register(group.kernels[0].accumulator)
                {
                    std::mem::swap(a, b);
                }
                if !matches!((&assignment.destination,&assignment.value),(Place::Register(d),Expr::Register(s))if d==s)
                {
                    assignments.push(assignment);
                }
            }
        }
        let last = body.last().ok_or(Error::Projection)?;
        let pc = labels[&block.start];
        let fall = last.address + u64::from(last.size);
        let mut size = 1;
        let control = match &last.control {
            Control::Jump(to) => Control::Jump(route(*to)?),
            Control::Next => Control::Jump(route(fall)?),
            Control::Branch { condition, target } => {
                let mut condition = if last.address == controls.limit.site {
                    Expr::binary(
                        if controls.limit.equal {
                            BinaryOp::Eq
                        } else {
                            BinaryOp::Ne
                        },
                        Expr::Register(counter),
                        controls.limit.lhs.clone(),
                    )
                } else {
                    self::condition(condition)
                };
                let (mut target, mut fall) =
                    if last.address == controls.limit.site && controls.staging.is_some() {
                        condition = Expr::binary(
                            BinaryOp::Eq,
                            Expr::Register(counter),
                            controls.limit.lhs.clone(),
                        );
                        (envelope.latch, increment)
                    } else {
                        (route(*target)?, route(fall)?)
                    };
                if let Expr::Binary(BinaryOp::Ne, a, b) = condition {
                    condition = Expr::binary(BinaryOp::Eq, *a, *b);
                    std::mem::swap(&mut target, &mut fall);
                }
                if fall == pc + 2 {
                    size = 2;
                } else {
                    instructions.push(IrInstruction {
                        address: pc + 1,
                        size: 1,
                        assignments: vec![],
                        control: Control::Jump(fall),
                    });
                }
                Control::Branch { condition, target }
            }
            Control::Return(_) => return Err(Error::Boundary),
        };
        instructions.push(IrInstruction {
            address: pc,
            size,
            assignments,
            control,
        });
    }
    instructions.push(IrInstruction {
        address: init,
        size: 1,
        assignments: vec![Assignment {
            destination: counter.into(),
            value: Expr::Const(group.offsets[0]),
        }],
        control: Control::Jump(feedback),
    });
    let mut increment_assignments = Vec::new();
    if let Some((_, mark, temporary)) = controls.staging {
        increment_assignments.push(Assignment {
            destination: mark.into(),
            value: Expr::Register(temporary),
        });
    }
    increment_assignments.push(Assignment {
        destination: counter.into(),
        value: Expr::binary(
            BinaryOp::Add,
            Expr::Register(counter),
            Expr::Const(group.step),
        ),
    });
    instructions.push(IrInstruction {
        address: increment,
        size: 1,
        assignments: increment_assignments,
        control: Control::Jump(feedback),
    });
    let entry = source.cfg().block(source.cfg().entry()).start;
    let program = Program::new(entry, source.register_count(), instructions)
        .map_err(|_| Error::Projection)?;
    let reachable = program.cfg().reachable_blocks();
    let retained: BTreeSet<_> = reachable
        .iter()
        .flat_map(|&id| program.cfg().block(id).instructions.clone())
        .collect();
    let instructions = program
        .instructions()
        .iter()
        .enumerate()
        .filter(|(n, _)| retained.contains(n))
        .map(|(_, i)| i.clone())
        .collect();
    let program = Program::new(entry, source.register_count(), instructions)
        .map_err(|_| Error::Projection)?;
    if program.instructions().len() > region::MAX_INSTRUCTIONS {
        return Err(Error::Limit);
    }
    let program = super::linear::fuse(program, base, feedback)?;
    let reduced = crate::transform::display_dce::propose(&program).ok_or(Error::Limit)?;
    let mut instructions = reduced.instructions().to_vec();
    for (i, original) in instructions.iter_mut().zip(program.instructions()) {
        if i.address < base {
            i.assignments = original.assignments.clone();
        }
    }
    let reduced = Program::new(entry, program.register_count(), instructions)
        .map_err(|_| Error::Projection)?;
    let program = if crate::transform::display_dce::validate(&program, &reduced) {
        reduced
    } else {
        program
    };
    Ok((program, feedback))
}
