use nirvana::ir::{BinaryOp, Control, Expr, IrInstruction, Program, Reg, Width};
use nirvana::simplify::simplify;
use nirvana::verify::{Solver, UnknownReason, Verdict, pure_query};

use crate::support::rewrite_cases;

// Executable fixture files can return ETXTBSY when written while another test
// spawns a child. Keep file creation and solver spawns in one test at a time so
// these tests exercise the intended solver protocol and timeout paths.
static SOLVER_FIXTURE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[test]
fn memory_and_resource_limits_are_explicit_unknowns() {
    let load = Expr::load(Expr::Const(0), Width::U64);
    assert_eq!(
        pure_query(&load, &Expr::Const(0)).unwrap_err(),
        UnknownReason::MemoryExpression
    );
    // Even an unselected Load is outside this deliberately small proof model.
    let select = Expr::select(Expr::Const(0), load, Expr::Const(0));
    assert_eq!(
        pure_query(&select, &Expr::Const(0)).unwrap_err(),
        UnknownReason::MemoryExpression
    );
    assert_eq!(
        pure_query(&Expr::Register(Reg(4096)), &Expr::Const(0)).unwrap_err(),
        UnknownReason::ResourceLimit
    );
    let mut deep = Expr::Const(0);
    for _ in 0..258 {
        deep = Expr::binary(BinaryOp::Add, deep, Expr::Const(1));
    }
    assert_eq!(
        pure_query(&deep, &Expr::Const(258)).unwrap_err(),
        UnknownReason::ResourceLimit
    );
}

#[test]
fn missing_solver_and_unmodeled_operations_never_accept_a_candidate() {
    let _guard = SOLVER_FIXTURE_LOCK.lock().unwrap();
    let solver = Solver::new("/nirvana-no-such-solver");
    let before = Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(0));
    let checked = solver.checked_rewrite(&before, &simplify(&before));
    assert_eq!(checked.expression, before);
    assert!(matches!(
        checked.verdict,
        Verdict::Unknown(UnknownReason::SolverUnavailable(_))
    ));
    let before = Expr::load(Expr::Const(0), Width::U8);
    let checked = solver.checked_rewrite(&before, &Expr::Const(0));
    assert_eq!(checked.expression, before);
    assert_eq!(
        checked.verdict,
        Verdict::Unknown(UnknownReason::MemoryExpression)
    );
}

#[cfg(unix)]
mod protocol {
    use super::*;
    use std::io::Write;
    use std::os::unix::fs::PermissionsExt;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    struct Script(PathBuf);
    static NEXT_SCRIPT: AtomicU64 = AtomicU64::new(0);
    impl Script {
        fn new(body: &str) -> Self {
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let serial = NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "nirvana-solver-{}-{nonce}-{serial}",
                std::process::id()
            ));
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .unwrap();
            writeln!(
                file,
                "#!/usr/bin/env python3\nimport sys\nscript = sys.stdin.read()\n{body}"
            )
            .unwrap();
            file.set_permissions(std::fs::Permissions::from_mode(0o700))
                .unwrap();
            drop(file);
            Self(path)
        }
    }
    impl Drop for Script {
        fn drop(&mut self) {
            std::fs::remove_file(&self.0).unwrap();
        }
    }

    #[test]
    fn solver_unknown_errors_and_extra_output_are_not_proofs() {
        let _guard = SOLVER_FIXTURE_LOCK.lock().unwrap();
        for body in [
            "print('unknown')",
            "print('unsat'); sys.exit(7)",
            "print('unsat'); print('diagnostic', file=sys.stderr)",
            "print('unsat'); print('(error bad)')",
        ] {
            let script = Script::new(body);
            assert!(matches!(
                Solver::new(&script.0).check(&Expr::Const(0), &Expr::Const(0)),
                Verdict::Unknown(_)
            ));
        }
    }

    #[test]
    fn counterexamples_must_parse_completely_and_replay_in_the_ir() {
        let _guard = SOLVER_FIXTURE_LOCK.lock().unwrap();
        let zero_model = Script::new(
            "print('sat')\nif '(get-value' in script: print('((r0 #x0000000000000000))')",
        );
        let solver = Solver::new(&zero_model.0);
        let r0 = Expr::Register(Reg(0));
        assert_eq!(
            solver.check(&r0, &r0),
            Verdict::Unknown(UnknownReason::InvalidCounterexample)
        );
        let after = Expr::binary(BinaryOp::Add, r0.clone(), Expr::Const(1));
        let checked = solver.checked_rewrite(&r0, &after);
        assert_eq!(checked.expression, r0);
        assert!(matches!(checked.verdict, Verdict::Counterexample(_)));
        let missing = Expr::binary(BinaryOp::Add, r0.clone(), Expr::Register(Reg(1)));
        assert!(matches!(
            solver.check(&r0, &missing),
            Verdict::Unknown(UnknownReason::InvalidResponse(_))
        ));
    }

    #[test]
    fn a_stalled_solver_is_killed_and_reported_as_unknown() {
        let _guard = SOLVER_FIXTURE_LOCK.lock().unwrap();
        let script = Script::new("import time\ntime.sleep(10)");
        let solver = Solver::new(&script.0).with_timeout(Duration::from_millis(5));
        assert_eq!(
            solver.check(&Expr::Const(0), &Expr::Const(0)),
            Verdict::Unknown(UnknownReason::SolverTimeout)
        );
    }
}

fn solver() -> Solver {
    Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn symbolic_rewrites_are_equal_for_all_u64_inputs_and_mutants_have_witnesses() {
    let _guard = SOLVER_FIXTURE_LOCK.lock().unwrap();
    let solver = solver();
    let mut checked = 0;
    for (name, before) in rewrite_cases::cases() {
        let after = simplify(&before);
        assert_ne!(
            before, after,
            "case should exercise an actual rewrite: {name}"
        );
        let result = solver.checked_rewrite(&before, &after);
        assert_eq!(result.verdict, Verdict::EquivalentUnderModel, "{name}");
        assert_eq!(result.expression, after);
        let mutant = Expr::binary(BinaryOp::Add, after, Expr::Const(1));
        let result = solver.checked_rewrite(&before, &mutant);
        assert!(
            matches!(result.verdict, Verdict::Counterexample(_)),
            "{name}: {:?}",
            result.verdict
        );
        assert_eq!(result.expression, before);
        checked += 1;
    }
    for (name, before, after) in rewrite_cases::semantic_mutants() {
        let result = solver.checked_rewrite(&before, &after);
        let Verdict::Counterexample(witness) = result.verdict else {
            panic!("{name}: {:?}", result.verdict)
        };
        assert_eq!(result.expression, before);
        let value = |index| {
            witness
                .registers
                .iter()
                .find(|(reg, _)| reg.0 == index)
                .unwrap()
                .1
        };
        match name {
            "wrong-shift-width" => assert!(value(1) & 63 >= 32),
            "ignore-overflow" => assert_eq!(value(0), u64::MAX),
            "truthiness-as-value" => assert!(value(0) > 1),
            "wrong-signedness" => assert_ne!(value(0) >> 63, value(1) >> 63),
            _ => unreachable!(),
        }
    }
    println!(
        "{checked} actual simplifications proved under pure-u64-v1; {checked} mutations rejected with IR-replayed counterexamples"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn bitvector_encoding_matches_the_ir_at_integer_boundaries_for_every_operator() {
    let _guard = SOLVER_FIXTURE_LOCK.lock().unwrap();
    use BinaryOp::*;
    let solver = solver();
    let values = [0, 1, 63, 64, 65, 1 << 63, u64::MAX];
    for op in [
        Add, Sub, Mul, And, Or, Xor, Shl, Shr, Eq, Ne, Ult, Ule, UMulHigh, SMulHigh, AShr,
    ] {
        for left in values {
            for right in values {
                let expression = Expr::binary(op, Expr::Const(left), Expr::Const(right));
                let p = Program::new(
                    0,
                    0,
                    vec![IrInstruction {
                        address: 0,
                        size: 1,
                        assignments: vec![],
                        control: Control::Return(expression.clone()),
                    }],
                )
                .unwrap();
                let expected = p.execute(&[], 1).unwrap().value;
                assert_eq!(
                    solver.check(&expression, &Expr::Const(expected)),
                    Verdict::EquivalentUnderModel,
                    "{op:?}, {left}, {right}"
                );
            }
        }
    }
}
