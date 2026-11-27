//! Guarded SSA states over a checked topological instruction order.
use super::*;

struct Path {
    guard: String,
    state: State,
    constants: Vec<Option<u64>>,
}

#[derive(Clone, Copy)]
enum Merge {
    All,
    Effects,
    NormalValues,
}

fn merge(builder: &mut Builder, paths: &[Path], initial: &State, fields: Merge) -> State {
    // At a reachable join one of these guards holds. The first incoming state
    // supplies a harmless default, avoiding arbitrary inputs on every linear edge.
    let mut out = paths.first().map_or(initial, |p| &p.state).clone();
    for path in paths.iter().skip(1) {
        let guard = &path.guard;
        let state = &path.state;
        if !matches!(fields, Merge::Effects) {
            for (value, next) in out.registers.iter_mut().zip(&state.registers) {
                if value != next {
                    *value = builder.value(format!("(ite {guard} {next} {value})"));
                }
            }
        }
        if !matches!(fields, Merge::NormalValues) {
            out.memory = builder.define(
                ARRAY,
                format!("(ite {guard} {} {})", state.memory, out.memory),
            );
            out.alive = builder.bool(format!("(ite {guard} {} {})", state.alive, out.alive));
            for (value, next) in [
                (&mut out.fault_access, &state.fault_access),
                (&mut out.fault_address, &state.fault_address),
                (&mut out.fault_width, &state.fault_width),
            ] {
                if value != next {
                    *value = builder.value(format!("(ite {guard} {next} {value})"));
                }
            }
        }
        if !matches!(fields, Merge::Effects) {
            for (value, next) in [
                (&mut out.exit_kind, &state.exit_kind),
                (&mut out.exit_value, &state.exit_value),
            ] {
                if value != next {
                    *value = builder.value(format!("(ite {guard} {next} {value})"));
                }
            }
        }
    }
    out
}

fn known(expression: &Expr, values: &[Option<u64>]) -> Option<u64> {
    match expression {
        Expr::Const(value) => Some(*value),
        Expr::Register(Reg(id)) => values[*id],
        Expr::Unary(op, value) => Some(op.evaluate(known(value, values)?)),
        Expr::Binary(op, a, b) => Some(op.evaluate(known(a, values)?, known(b, values)?)),
        Expr::Load { .. } => None,
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let yes = known(taken, values);
            let no = known(not_taken, values);
            match known(condition, values) {
                Some(0) => no,
                Some(_) => yes,
                None => {
                    if yes == no {
                        yes
                    } else {
                        None
                    }
                }
            }
        }
    }
}

fn may_load(expression: &Expr) -> bool {
    match expression {
        Expr::Load { .. } => true,
        Expr::Const(_) | Expr::Register(_) => false,
        Expr::Unary(_, value) => may_load(value),
        Expr::Binary(_, left, right) => may_load(left) || may_load(right),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => may_load(condition) || may_load(taken) || may_load(not_taken),
    }
}

fn may_fault(instruction: &IrInstruction) -> bool {
    instruction.assignments.iter().any(|assignment| {
        matches!(assignment.destination, Place::Memory { .. }) || may_load(&assignment.value)
    }) || match &instruction.control {
        Control::Branch { condition, .. } => may_load(condition),
        Control::Return(value) => may_load(value),
        Control::Next | Control::Jump(_) => false,
    }
}

pub(super) fn dag(
    builder: &mut Builder,
    program: &Program,
    order: &[u64],
    shared: &Registers,
    prefix: &str,
) -> Result<(State, String, Vec<String>), Error> {
    dag_impl(builder, program, order, shared, prefix, true)
}

#[cfg(test)]
pub(super) fn reference_dag(
    builder: &mut Builder,
    program: &Program,
    order: &[u64],
    shared: &Registers,
    prefix: &str,
) -> Result<(State, String, Vec<String>), Error> {
    dag_impl(builder, program, order, shared, prefix, false)
}

fn dag_impl(
    builder: &mut Builder,
    program: &Program,
    order: &[u64],
    shared: &Registers,
    prefix: &str,
    compact: bool,
) -> Result<(State, String, Vec<String>), Error> {
    builder.canonical_binary = compact;
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let (initial, names) = builder.initial(program.register_count(), shared, prefix);
    let entry = program.cfg().block(program.cfg().entry()).start;
    let mut incoming: BTreeMap<u64, Vec<Path>> = BTreeMap::new();
    incoming.insert(
        entry,
        vec![Path {
            guard: "true".into(),
            state: initial.clone(),
            constants: vec![None; program.register_count()],
        }],
    );
    let mut exits = Vec::new();
    let mut returns = Vec::new();
    for &pc in order {
        let paths = incoming.remove(&pc).ok_or(Error::OpenEdge)?;
        let reach = builder.bool(format!(
            "(or false {})",
            paths
                .iter()
                .map(|p| p.guard.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        ));
        let mut constants = vec![None; program.register_count()];
        for (reg, constant) in constants.iter_mut().enumerate() {
            if let Some(first) = paths.first().and_then(|p| p.constants[reg])
                && paths.iter().all(|p| p.constants[reg] == Some(first))
            {
                *constant = Some(first);
            }
        }
        let mut state = merge(builder, &paths, &initial, Merge::All);
        state.alive = reach.clone();
        let instruction = instructions[&pc];
        let branch = if compact {
            builder.instruction_with_branch(instruction, &mut state)?
        } else {
            builder.instruction(instruction, &mut state)?;
            None
        };
        // Keep expression evaluation and its faults in the symbolic primitive
        // kernel. Exact facts simplify only the resulting normal register values.
        for assignment in &instruction.assignments {
            if let Place::Register(Reg(id)) = assignment.destination {
                constants[id] = known(&assignment.value, &constants);
            }
        }
        for (reg, value) in constants.iter().enumerate() {
            if let Some(value) = value {
                state.registers[reg] = word(*value);
            }
        }
        if !compact || may_fault(instruction) {
            let fault = builder.bool(format!("(and {reach} (not {}))", state.alive));
            exits.push(Path {
                guard: fault,
                state: state.clone(),
                constants: vec![],
            });
        }
        if matches!(instruction.control, Control::Return(_)) {
            if compact {
                returns.push(Path {
                    guard: state.alive.clone(),
                    state: state.clone(),
                    constants: vec![],
                });
            }
            exits.push(Path {
                guard: state.alive.clone(),
                state,
                constants: vec![],
            });
        } else {
            let fall = pc + u64::from(instruction.size);
            let targets = match instruction.control {
                Control::Next => vec![fall],
                Control::Jump(to) => vec![to],
                Control::Branch { target, .. } => {
                    if target == fall {
                        vec![target]
                    } else {
                        vec![target, fall]
                    }
                }
                Control::Return(_) => unreachable!(),
            };
            for to in targets {
                let guard = if compact {
                    // Routing a normal path needs the Boolean condition, rather
                    // than a word-valued next PC followed by a PC comparison.
                    // Same-target branches still evaluated their condition and
                    // any faulting loads in instruction_with_branch above.
                    match (&instruction.control, &branch) {
                        (Control::Branch { target, .. }, Some(value)) if *target != fall => {
                            let truth = format!("(distinct {value} {})", word(0));
                            let condition = if to == *target {
                                truth
                            } else {
                                format!("(not {truth})")
                            };
                            builder.bool(format!("(and {} {condition})", state.alive))
                        }
                        _ => state.alive.clone(),
                    }
                } else {
                    builder.bool(format!(
                        "(and {} (= {} {}))",
                        state.alive,
                        state.exit_value,
                        word(to)
                    ))
                };
                incoming.entry(to).or_default().push(Path {
                    guard,
                    state: state.clone(),
                    constants: constants.clone(),
                });
            }
        }
    }
    let complete = builder.bool(format!(
        "(or false {})",
        exits
            .iter()
            .map(|p| p.guard.as_str())
            .collect::<Vec<_>>()
            .join(" ")
    ));
    let state = if compact {
        // Registers and returned values are observed only after normal Return.
        // Fault paths retain all RAM, status and first-fault fields separately.
        let mut effects = merge(builder, &exits, &initial, Merge::Effects);
        let normal = merge(builder, &returns, &initial, Merge::NormalValues);
        effects.registers = normal.registers;
        effects.exit_kind = normal.exit_kind;
        effects.exit_value = normal.exit_value;
        effects
    } else {
        merge(builder, &exits, &initial, Merge::All)
    };
    Ok((state, complete, names))
}
