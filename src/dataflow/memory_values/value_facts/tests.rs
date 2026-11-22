use super::*;
use crate::model::ir::{BinaryOp as B, Control, IrInstruction, Place};

fn source(offset: u64, initialized: bool) -> Program {
    let r = |n| Expr::Register(Reg(n));
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let ins = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![
                    Assignment {
                        destination: Place::Memory {
                            address: r(7),
                            width: Width::U64,
                        },
                        value: r(0),
                    },
                    set(0, Expr::Const(0)),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            ins(
                1,
                vec![set(2, Expr::load(r(7), Width::U8))],
                Control::Jump(3),
            ),
            ins(
                2,
                if initialized {
                    vec![set(
                        2,
                        Expr::load(Expr::binary(B::Add, r(7), Expr::Const(offset)), Width::U8),
                    )]
                } else {
                    vec![]
                },
                Control::Jump(3),
            ),
            ins(3, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap()
}

#[test]
fn independent_checker_rejects_a_forged_phi_and_replays_its_wrong_return() {
    for initialized in [false, true] {
        let source = source(1, initialized);
        let context = Context::new(&source).unwrap();
        let (proofs, captures) = analyze::collect(&context, RecoveryPolicy::Source, true).unwrap();
        let mut facts = solve(&context, &proofs).unwrap();
        let key = proofs.iter().find(|p| p.site.instruction == 1).unwrap().key;
        let phi = context
            .graph
            .values
            .iter()
            .position(|d| {
                matches!(
                    d,
                    Definition::Phi {
                        block: 3,
                        register: Reg(2),
                        ..
                    }
                )
            })
            .unwrap();
        assert_eq!(facts[phi], None);
        facts[phi] = Some(key);
        assert!(matches!(
            validate(&context, &proofs, &facts),
            Err(SsaError::Malformed("saved slice phi input"))
        ));
        let mut plan = MemoryValuePlan {
            source_registers: source.register_count(),
            evidence: MemoryValueEvidence {
                ssa: context.evidence,
                proved_loads: proofs.len(),
                snapshot_values: captures.len(),
                replaced_reads: 0,
            },
            proofs,
            captures,
            facts,
        };
        let (candidate, count) = rewrite::construct(&source, &plan, &context).unwrap();
        plan.evidence.replaced_reads = count;
        assert!(super::super::verify::check(&source, &plan, &candidate, &context).is_err());
        let mut input = vec![0; 8];
        input[0] = 0x3412;
        input[1] = 1;
        input[2] = 0x56;
        input[7] = 4096;
        let expected = source
            .execute_with_memory(&input, 4096, &[0; 32], 4)
            .unwrap();
        input.resize(candidate.register_count(), u64::MAX);
        let actual = candidate
            .execute_with_memory(&input, 4096, &[0; 32], 4)
            .unwrap();
        assert_ne!(expected.value, actual.value);
    }
}

#[test]
fn seed_claims_and_arbitrary_initial_values_have_independent_checks() {
    let source = source(0, true);
    let context = Context::new(&source).unwrap();
    let plan = MemoryValuePlan::analyze(&source).unwrap();
    let mut facts = vec![None; plan.facts.len()];
    let seed = context
        .point(plan.proofs[0].site)
        .unwrap()
        .definition
        .unwrap()
        .0;
    let mut key = plan.facts[seed].unwrap();
    key.start += 8;
    facts[seed] = Some(key);
    assert!(matches!(
        validate(&context, &plan.proofs, &facts),
        Err(SsaError::Malformed("saved slice changed seed"))
    ));
    let mut facts = plan.facts.clone();
    let initial = context
        .graph
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { register: Reg(2) }))
        .unwrap();
    facts[initial] = Some(plan.proofs[0].key);
    assert!(matches!(
        validate(&context, &plan.proofs, &facts),
        Err(SsaError::Malformed("saved slice arbitrary initial value"))
    ));
}

#[test]
fn saved_slices_keep_zero_extension_and_reject_shifted_or_wider_claims() {
    for (loaded, start, width, wrong_start, wrong_width) in [
        (Width::U16, 8, Width::U8, 16, Width::U8),
        (Width::U8, 0, Width::U64, 0, Width::U16),
        (Width::U8, 4, Width::U8, 4, Width::U8),
    ] {
        let mut rows = source(0, true).instructions().to_vec();
        for row in &mut rows[1..=2] {
            let Expr::Load { width, .. } = &mut row.assignments[0].value else {
                unreachable!()
            };
            *width = loaded;
        }
        rows[3].assignments.push(Assignment {
            destination: Reg(6).into(),
            value: Expr::unary(UnaryOp::Extract { start, width }, Expr::Register(Reg(2))),
        });
        rows[3].control = Control::Return(Expr::Register(Reg(6)));
        let source = Program::new(0, 8, rows).unwrap();
        let context = Context::new(&source).unwrap();
        let mut plan = MemoryValuePlan::analyze(&source).unwrap();
        let projected = context
            .point(Site {
                instruction: 3,
                assignment: Some(0),
            })
            .unwrap()
            .definition
            .unwrap()
            .0;
        if start == 4 {
            assert!(
                plan.facts[projected].is_none(),
                "the high bits of this result come from zero padding"
            );
        } else {
            assert!(plan.facts[projected].is_some());
        }
        let good = plan.lower(&source).unwrap();
        let mut input = vec![0; 8];
        input[0] = 0x123456;
        input[7] = 4096;
        let expected = source
            .execute_with_memory(&input, 4096, &[0; 32], 4)
            .unwrap();
        input.resize(good.register_count(), u64::MAX);
        assert_eq!(
            good.execute_with_memory(&input, 4096, &[0; 32], 4)
                .unwrap()
                .value,
            expected.value
        );
        let root = plan.proofs[0].key.value;
        plan.facts[projected] = Some(Key {
            value: root,
            start: wrong_start,
            width: wrong_width,
        });
        let (bad, count) = rewrite::construct(&source, &plan, &context).unwrap();
        plan.evidence.replaced_reads = count;
        assert!(matches!(
            super::super::verify::check(&source, &plan, &bad, &context),
            Err(SsaError::Malformed("saved slice extraction identity"))
        ));
        assert_ne!(
            bad.execute_with_memory(&input, 4096, &[0; 32], 4)
                .unwrap()
                .value,
            expected.value
        );
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn accepted_saved_slice_transfers_have_universal_checks_and_replayed_padding_mutants() {
    use crate::verification::verify::{self, Solver, Verdict};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/saved-slice-facts");
    std::fs::create_dir_all(&root).unwrap();
    let extract = |start, width, value| Expr::unary(UnaryOp::Extract { start, width }, value);
    let check = |name: &str, before: &Expr, after: &Expr| {
        let query = verify::pure_query(before, after).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        verdict
    };
    let mut proved = 0;
    for from in [0, 1, 8, 16, 32, 56] {
        for input in [Width::U8, Width::U16, Width::U32, Width::U64] {
            if u32::from(from) + input.bits() > 64 {
                continue;
            }
            let key = Key {
                value: SavedValue::Register(ValueId(0)),
                start: from,
                width: input,
            };
            for start in [0, 1, 7, 8, 16, 32, 56] {
                for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
                    let Some(next) = project(key, start, width) else {
                        continue;
                    };
                    let before = extract(start, width, word(key, Expr::Register(Reg(0))));
                    let after = word(next, Expr::Register(Reg(0)));
                    let name = format!("{from}-{}-{start}-{}", input.bits(), width.bits());
                    assert_eq!(
                        check(&name, &before, &after),
                        Verdict::EquivalentUnderModel,
                        "{name}"
                    );
                    proved += 1;
                }
            }
        }
    }
    for (name, start, width, wrong_start) in [
        ("lost-padding", 0, Width::U16, 8),
        ("crossed-padding", 4, Width::U8, 12),
    ] {
        let key = Key {
            value: SavedValue::Register(ValueId(0)),
            start: 8,
            width: Width::U8,
        };
        let before = extract(start, width, word(key, Expr::Register(Reg(0))));
        let wrong = extract(wrong_start, width, Expr::Register(Reg(0)));
        let Verdict::Counterexample(witness) = check(name, &before, &wrong) else {
            panic!("padding witness")
        };
        assert_ne!(witness.before, witness.after);
    }
    assert!(proved > 100);
    println!(
        "{proved} universal actual saved-slice transfer checks; 2 replayed zero-padding SAT controls"
    );
}
