//! Independent bounded symbolic execution for load/store-free test programs.
//! It expands actual paths, without SSA, value numbering or predicate facts.
//! Observable layout: status, return, attempted PC, trace length, padded PCs,
//! then every machine register. Scalar operations share the IR primitives.
use nirvana::ir::{Control, Expr, Place, Program, RunReport, RunStatus};
pub const MODEL_ID: &str = "pure-dag-entry-prefix-v1";

fn substitute(value: &Expr, registers: &[Expr]) -> Expr {
    match value {
        Expr::Const(n) => Expr::Const(*n),
        Expr::Register(r) => registers[r.0].clone(),
        Expr::Unary(op, x) => Expr::unary(*op, substitute(x, registers)),
        Expr::Binary(op, a, b) => {
            Expr::binary(*op, substitute(a, registers), substitute(b, registers))
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            substitute(condition, registers),
            substitute(taken, registers),
            substitute(not_taken, registers),
        ),
        Expr::Load { .. } => panic!("pure prefix model: Load"),
    }
}

pub fn symbolic(program: &Program, budget: usize) -> Vec<Expr> {
    fn run(
        program: &Program,
        pc: u64,
        registers: Vec<Expr>,
        trace: Vec<u64>,
        budget: usize,
        total: usize,
        work: &mut usize,
    ) -> Vec<Expr> {
        *work += 1;
        assert!(*work <= 4096, "pure prefix path budget");
        let finish = |registers: Vec<Expr>, trace: Vec<u64>, status, value| {
            let mut words = vec![
                Expr::Const(status),
                value,
                Expr::Const(pc),
                Expr::Const(trace.len() as u64),
            ];
            words.extend((0..total).map(|n| Expr::Const(trace.get(n).copied().unwrap_or(0))));
            words.extend(registers);
            words
        };
        if budget == 0 {
            return finish(registers, trace, 1, Expr::Const(0));
        }
        let instruction = program
            .instructions()
            .iter()
            .find(|i| i.address == pc)
            .expect("closed prefix CFG");
        let mut registers = registers;
        for assignment in &instruction.assignments {
            let Place::Register(to) = assignment.destination else {
                panic!("pure prefix model: Store")
            };
            registers[to.0] = substitute(&assignment.value, &registers);
        }
        let mut trace = trace;
        trace.push(pc);
        let next = pc + u64::from(instruction.size);
        match &instruction.control {
            Control::Return(value) => {
                let value = substitute(value, &registers);
                finish(registers, trace, 0, value)
            }
            Control::Next => run(program, next, registers, trace, budget - 1, total, work),
            Control::Jump(target) => {
                run(program, *target, registers, trace, budget - 1, total, work)
            }
            Control::Branch { condition, target } => {
                let condition = substitute(condition, &registers);
                let yes = run(
                    program,
                    *target,
                    registers.clone(),
                    trace.clone(),
                    budget - 1,
                    total,
                    work,
                );
                let no = run(program, next, registers, trace, budget - 1, total, work);
                yes.into_iter()
                    .zip(no)
                    .map(|(a, b)| Expr::select(condition.clone(), a, b))
                    .collect()
            }
        }
    }
    assert!(budget <= 32 && program.register_count() <= 16);
    let entry = program.cfg().block(program.cfg().entry()).start;
    run(
        program,
        entry,
        (0..program.register_count())
            .map(|n| Expr::Register(nirvana::ir::Reg(n)))
            .collect(),
        vec![],
        budget,
        budget,
        &mut 0,
    )
}

pub fn concrete(report: &RunReport, budget: usize) -> Vec<u64> {
    let (status, value) = match report.status {
        RunStatus::Returned(n) => (0, n),
        RunStatus::Suspended => (1, 0),
        _ => panic!("pure prefix fault"),
    };
    let mut words = vec![
        status,
        value,
        report.state.instruction.unwrap(),
        report.state.trace.len() as u64,
    ];
    words.extend((0..budget).map(|n| report.state.trace.get(n).copied().unwrap_or(0)));
    words.extend(&report.state.registers);
    words
}

pub fn evaluate(expr: &Expr, inputs: &[u64]) -> u64 {
    match expr {
        Expr::Const(n) => *n,
        Expr::Register(r) => inputs[r.0],
        Expr::Unary(op, x) => op.evaluate(evaluate(x, inputs)),
        Expr::Binary(op, a, b) => op.evaluate(evaluate(a, inputs), evaluate(b, inputs)),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => evaluate(
            if evaluate(condition, inputs) != 0 {
                taken
            } else {
                not_taken
            },
            inputs,
        ),
        Expr::Load { .. } => panic!("pure prefix model: Load"),
    }
}
