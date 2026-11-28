//! The actual stable-input constructor, with free context words and RAM.
use super::*;

#[test]
#[ignore = "requires NIRVANA_Z3 and NIRVANA_STABLE_LOAD_OUT"]
fn stable_load_consumer_checks_free_inputs_ram_and_replays_intervening_writers() {
    let out = std::path::PathBuf::from(std::env::var_os("NIRVANA_STABLE_LOAD_OUT").unwrap());
    std::fs::create_dir_all(&out).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap());
    for (n, value) in [
        b(B::Add, r(2), b(B::Xor, r(1), r(4))),
        b(B::Sub, r(4), r(1)),
        b(B::UDiv, r(1), r(5)),
        b(B::SMulHigh, r(4), r(1)),
        b(
            B::Xor,
            Expr::unary(UnaryOp::SignExtend(Width::U16), r(1)),
            r(5),
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let source = source(value);
        let lower = load_consumer::lower_with_stable_inputs(
            &source,
            &[Reg(0), Reg(2), Reg(4), Reg(5), Reg(7)],
        )
        .unwrap();
        lower.validate().unwrap();
        assert_eq!(lower.model_id(), load_consumer::STABLE_MODEL_ID);
        let query = compare(&source, lower.program());
        std::fs::write(out.join(format!("stable-{n}.smt2")), query.smt2()).unwrap();
        assert_eq!(query.check(&solver), Verdict::EquivalentUnderModel);
    }
    let source = source(b(B::Add, r(2), b(B::Xor, r(1), r(4))));
    let lower = load_consumer::lower_with_stable_inputs(&source, &[]).unwrap();
    for (n, register) in [Reg(2), Reg(4)].into_iter().enumerate() {
        let writer = set(register.0, b(B::Add, r(register.0), c(1)));
        let mut original = source.instructions().to_vec();
        original[1].assignments.insert(0, writer.clone());
        let original = Program::new(0, 8, original).unwrap();
        let mut wrong = lower.program().instructions().to_vec();
        wrong[1].assignments.insert(0, writer);
        let wrong = Program::new(0, 8, wrong).unwrap();
        assert!(load_consumer::propose_with_stable_inputs(&original, &[]).is_none());
        assert!(load_consumer::validate_with_stable_inputs(&original, &wrong, &[]).is_err());
        let query = compare(&original, &wrong);
        std::fs::write(out.join(format!("writer-{n}.smt2")), query.smt2()).unwrap();
        let Verdict::Counterexample(witness) = query.check(&solver) else {
            panic!("intervening source definitions must change an observable return")
        };
        assert_ne!(witness.before.status, witness.after.status);
        std::fs::write(
            out.join(format!("writer-{n}.txt")),
            format!("{witness:#?}\n"),
        )
        .unwrap();
    }
    println!(
        "STABLE-LOAD-CONSUMER 5 free-word/RAM UNSAT; 2 IR-replayed intervening-writer SAT controls"
    );
}
