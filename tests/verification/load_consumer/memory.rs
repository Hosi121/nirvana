//! Free-word/RAM checks bind the whole memory expression to its source point.
use super::*;

fn source_producer(producer: Expr) -> Program {
    let source = source(b(B::Add, r(1), r(4)));
    let mut rows = source.instructions().to_vec();
    rows[0].assignments[1].value = producer;
    Program::new(0, 8, rows).unwrap()
}

#[test]
#[ignore = "requires NIRVANA_Z3 and NIRVANA_MEMORY_VALUE_OUT"]
fn memory_value_consumer_checks_whole_effects_and_replays_bad_hoists() {
    let out = std::path::PathBuf::from(std::env::var_os("NIRVANA_MEMORY_VALUE_OUT").unwrap());
    std::fs::create_dir_all(&out).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap());
    let load = || Expr::load(r(0), Width::U64);
    let other = || Expr::load(r(7), Width::U8);
    for (n, producer) in [
        b(B::And, load(), c(255)),
        Expr::unary(UnaryOp::SignExtend(Width::U8), load()),
        b(B::Add, load(), other()),
        Expr::select(r(5), load(), other()),
        b(
            B::Xor,
            Expr::load(Expr::load(r(7), Width::U64), Width::U8),
            c(7),
        ),
        b(B::Add, load(), c(7)),
    ]
    .into_iter()
    .enumerate()
    {
        let source = source_producer(producer);
        let lower =
            load_consumer::lower_memory_values(&source, &[Reg(0), Reg(4), Reg(5), Reg(7)]).unwrap();
        lower.validate().unwrap();
        let query = compare(&source, lower.program());
        std::fs::write(out.join(format!("memory-{n}.smt2")), query.smt2()).unwrap();
        assert_eq!(query.check(&solver), Verdict::EquivalentUnderModel);
    }
    let producer = b(B::Xor, load(), other());
    let source = source_producer(producer.clone());
    let lower = load_consumer::lower_memory_values(&source, &[]).unwrap();
    for (n, wrong_producer) in [
        b(B::Xor, other(), load()),
        load(),
        b(B::Xor, producer.clone(), Expr::load(r(4), Width::U8)),
    ]
    .into_iter()
    .enumerate()
    {
        let mut rows = lower.program().instructions().to_vec();
        rows[0].assignments[1].value = b(B::Add, wrong_producer, r(4));
        let wrong = Program::new(0, 8, rows).unwrap();
        assert!(load_consumer::validate_memory_values(&source, &wrong, &[]).is_err());
        let query = compare(&source, &wrong);
        std::fs::write(out.join(format!("wrong-{n}.smt2")), query.smt2()).unwrap();
        let Verdict::Counterexample(witness) = query.check(&solver) else {
            panic!("changed memory evaluation must replay an observable difference")
        };
        assert_ne!(witness.before.status, witness.after.status);
        std::fs::write(
            out.join(format!("wrong-{n}.txt")),
            format!("{witness:#?}\n"),
        )
        .unwrap();
    }
    let source = Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: r(5),
                    target: 2,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(1, producer.clone())],
                control: Control::Next,
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![set(2, b(B::Add, r(1), r(4)))],
                control: Control::Return(r(2)),
            },
        ],
    )
    .unwrap();
    let mut rows = source.instructions().to_vec();
    rows[1].assignments[0].value = b(B::Add, producer, r(4));
    rows[2].assignments[0].value = r(1);
    let wrong = Program::new(0, 8, rows).unwrap();
    assert!(load_consumer::propose_memory_values(&source, &[]).is_none());
    assert!(load_consumer::validate_memory_values(&source, &wrong, &[]).is_err());
    let query = compare(&source, &wrong);
    std::fs::write(out.join("wrong-3.smt2"), query.smt2()).unwrap();
    let Verdict::Counterexample(witness) = query.check(&solver) else {
        panic!("bypass path must replay a different return")
    };
    assert_ne!(witness.before.status, witness.after.status);
    std::fs::write(out.join("wrong-3.txt"), format!("{witness:#?}\n")).unwrap();
    println!(
        "MEMORY-VALUE-CONSUMER 6 free-word/RAM UNSAT; 4 IR-replayed subtree/order/bypass SAT controls"
    );
}
