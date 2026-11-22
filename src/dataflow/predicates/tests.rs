use super::*;
use crate::ir::{Assignment, BinaryOp as B, IrInstruction, Reg, Width};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn bit() -> Expr {
    b(B::And, r(0), c(1))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn source(mut rows: Vec<(u64, Vec<Assignment>, Control)>) -> Program {
    rows.sort_by_key(|x| x.0);
    Program::new(
        0,
        8,
        rows.into_iter()
            .map(|(address, assignments, control)| IrInstruction {
                address,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}
fn repeated() -> Program {
    source(vec![
        (0, vec![set(0, Expr::load(r(7), Width::U8))], Control::Next),
        (
            1,
            vec![],
            Control::Branch {
                condition: b(B::Ne, bit(), c(0)),
                target: 6,
            },
        ),
        (
            2,
            vec![Assignment {
                destination: Place::Memory {
                    address: r(7),
                    width: Width::U8,
                },
                value: c(0),
            }],
            Control::Next,
        ),
        (3, vec![set(1, b(B::Eq, bit(), c(0)))], Control::Next),
        (
            4,
            vec![],
            Control::Branch {
                condition: b(B::Ne, r(1), c(0)),
                target: 7,
            },
        ),
        (5, vec![], Control::Return(c(99))),
        (6, vec![], Control::Return(c(10))),
        (
            7,
            vec![set(2, Expr::select(bit(), c(12), c(13)))],
            Control::Return(r(2)),
        ),
    ])
}
fn edited(source: &Program, edit: impl FnOnce(&mut [IrInstruction])) -> Program {
    let mut instructions = source.instructions().to_vec();
    edit(&mut instructions);
    Program::new(0, source.register_count(), instructions).unwrap()
}

#[test]
fn repeated_cached_load_keeps_every_machine_prefix_and_first_fault() {
    let source = repeated();
    let plan = PredicatePlan::analyze(&source).unwrap();
    let (candidate, evidence) = plan.lower(&source).unwrap();
    let original_middle = crate::middle_ir::Function::from_low(&source).unwrap();
    let (middle, middle_evidence) = original_middle.recover_predicates().unwrap().unwrap();
    assert_eq!(evidence, middle_evidence);
    assert_eq!(
        candidate.instructions(),
        middle.lower().unwrap().instructions()
    );
    assert_eq!(evidence.pruned_branches, 1);
    assert!(evidence.constant_assignments >= 2);
    assert!(evidence.blocks_after < evidence.blocks_before);
    assert_eq!(candidate.instructions()[4].control, Control::Jump(7));
    let mut observations = 0;
    for byte in 0..=255 {
        for pointer in [4096, 4097, 4098, u64::MAX] {
            let mut input = vec![0xdeadbeef; 8];
            input[7] = pointer;
            for budget in 0..=10 {
                let expected = source
                    .run_with_memory(&input, 4096, &[byte, 7], budget)
                    .unwrap();
                assert_eq!(
                    middle
                        .run_with_memory(&input, 4096, &[byte, 7], budget)
                        .unwrap(),
                    expected
                );
                assert_eq!(
                    candidate
                        .run_with_memory(&input, 4096, &[byte, 7], budget)
                        .unwrap(),
                    expected,
                    "byte={byte}, pointer={pointer}, budget={budget}"
                );
                observations += 1;
            }
        }
    }
    assert_eq!(observations, 11264);
}

#[test]
fn distinct_loads_and_redefinitions_keep_unknown_predicates() {
    let source = source(vec![
        (0, vec![set(0, Expr::load(r(7), Width::U8))], Control::Next),
        (
            1,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 5,
            },
        ),
        (2, vec![set(0, Expr::load(r(7), Width::U8))], Control::Next),
        (
            3,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 5,
            },
        ),
        (4, vec![], Control::Return(c(0))),
        (5, vec![], Control::Return(c(1))),
    ]);
    assert!(PredicatePlan::analyze(&source).is_none());
    let changed = edited(&source, |s| s[2].assignments[0].value = r(2));
    assert!(PredicatePlan::analyze(&changed).is_none());
}

#[test]
fn masked_load_results_keep_lazy_reads_and_first_fault_state() {
    let masked = |value| b(B::Or, b(B::And, value, c(0)), c(7));
    let source = source(vec![
        (
            0,
            vec![set(
                0,
                Expr::select(
                    r(1),
                    masked(Expr::load(r(7), Width::U64)),
                    masked(Expr::load(c(u64::MAX), Width::U64)),
                ),
            )],
            Control::Next,
        ),
        (
            1,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 3,
            },
        ),
        (2, vec![], Control::Return(c(99))),
        (3, vec![], Control::Return(r(0))),
    ]);
    let plan = PredicatePlan::analyze(&source).unwrap();
    let (candidate, e) = plan.lower(&source).unwrap();
    assert_eq!(e.pruned_branches, 1);
    assert_eq!(candidate.instructions()[0], source.instructions()[0]);
    let wrong = edited(&candidate, |s| s[0].assignments[0].value = c(7));
    assert!(validate(&source, &plan, &wrong).is_err());
    for flag in [0, 1, 2, u64::MAX] {
        for pointer in [4096, 4097, u64::MAX] {
            let input = [u64::MAX, flag, 2, 3, 4, 5, 6, pointer];
            for budget in 0..=5 {
                let expected = source
                    .run_with_memory(&input, 4096, &[0xa5; 8], budget)
                    .unwrap();
                assert_eq!(
                    candidate
                        .run_with_memory(&input, 4096, &[0xa5; 8], budget)
                        .unwrap(),
                    expected
                );
            }
        }
    }
}

#[test]
fn equal_phi_values_carry_identity_but_distinct_inputs_remain_distinct() {
    let source = source(vec![
        (
            0,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 3,
            },
        ),
        (1, vec![set(1, r(2))], Control::Jump(4)),
        (3, vec![set(1, r(2))], Control::Jump(4)),
        (
            4,
            vec![],
            Control::Branch {
                condition: r(1),
                target: 7,
            },
        ),
        (
            5,
            vec![],
            Control::Branch {
                condition: r(2),
                target: 8,
            },
        ),
        (6, vec![], Control::Return(c(0))),
        (7, vec![], Control::Return(c(1))),
        (8, vec![], Control::Return(c(2))),
    ]);
    let plan = PredicatePlan::analyze(&source).unwrap();
    let (candidate, evidence) = plan.lower(&source).unwrap();
    assert_eq!(evidence.pruned_branches, 1);
    for a in [0, 1, u64::MAX] {
        for x in [0, 1, 2, u64::MAX] {
            let input = [a, 123, x, 7, 0, 0, 0, 0];
            assert_eq!(
                source.run_with_memory(&input, 0, &[], 20),
                candidate.run_with_memory(&input, 0, &[], 20)
            );
        }
    }
    let changed = edited(&source, |s| s[2].assignments[0].value = r(3));
    assert!(PredicatePlan::analyze(&changed).is_none());
}

#[test]
fn verifier_rejects_forged_paths_targets_memory_and_source_versions() {
    let source = repeated();
    let plan = PredicatePlan::analyze(&source).unwrap();
    let (candidate, _) = plan.lower(&source).unwrap();
    let wrong = edited(&candidate, |s| s[4].control = Control::Jump(6));
    assert!(validate(&source, &plan, &wrong).is_err());
    let mut input = vec![0; 8];
    input[7] = 4096;
    assert_ne!(
        source.run_with_memory(&input, 4096, &[0], 20).unwrap(),
        wrong.run_with_memory(&input, 4096, &[0], 20).unwrap()
    );
    let wrong = edited(&candidate, |s| s[2].assignments[0].value = c(123));
    assert!(validate(&source, &plan, &wrong).is_err());
    let wrong = edited(&candidate, |s| s[0].assignments[0].value = c(0));
    assert!(validate(&source, &plan, &wrong).is_err());
    let wrong = edited(&candidate, |s| s[5].control = Control::Return(c(123)));
    assert!(validate(&source, &plan, &wrong).is_err());
    let mut forged = plan.clone();
    let id = source
        .cfg()
        .blocks()
        .iter()
        .find(|b| b.start == 2)
        .unwrap()
        .id;
    forged.entries[id.index()] = Some(Facts::Unreachable);
    assert!(validate(&source, &forged, &candidate).is_err());
    let mut forged = plan.clone();
    let order = order(&source).unwrap();
    let values = Values::build(&source, &plan.graph, &order).unwrap();
    forged.entries[id.index()] = Some(Facts::Known(BTreeMap::from([(values.controls[&1], true)])));
    assert!(validate(&source, &forged, &candidate).is_err());
    let changed = edited(&source, |s| s[0].assignments[0].value = c(9));
    assert!(plan.lower(&changed).is_none());
    assert!(validate(&changed, &plan, &candidate).is_err());
    let source = edited(&source, |s| s[1].control = Control::Jump(6));
    let graph = ssa::SsaFunction::build(&source).unwrap();
    let mut entries = vec![None; source.cfg().blocks().len()];
    for id in super::order(&source).unwrap() {
        entries[id.index()] = Some(Facts::empty());
    }
    let unreachable = source.cfg().block_at(2).unwrap();
    entries[unreachable.index()] = Some(Facts::Known(BTreeMap::from([(usize::MAX, false)])));
    let forged = PredicatePlan { graph, entries };
    assert!(validate(&source, &forged, &source).is_err());
}

#[test]
fn cyclic_cfg_keeps_the_original_representation() {
    let cycle = source(vec![
        (
            0,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 0,
            },
        ),
        (1, vec![], Control::Return(r(1))),
    ]);
    assert!(PredicatePlan::analyze(&cycle).is_none());
}

#[test]
fn xor_inverts_comparison_truth_but_keeps_general_word_bits() {
    let make = |condition| {
        source(vec![
            (
                0,
                vec![],
                Control::Branch {
                    condition,
                    target: 3,
                },
            ),
            (1, vec![], Control::Return(c(2))),
            (
                3,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 5,
                },
            ),
            (4, vec![], Control::Return(c(3))),
            (5, vec![], Control::Return(r(0))),
        ])
    };
    let general = make(b(B::Xor, r(0), c(1)));
    assert!(PredicatePlan::analyze(&general).is_none());
    let boolean = make(b(B::Xor, b(B::Eq, r(0), c(0)), c(1)));
    let plan = PredicatePlan::analyze(&boolean).unwrap();
    let (candidate, e) = plan.lower(&boolean).unwrap();
    assert_eq!(e.pruned_branches, 1);
    // A true word keeps its full numeric value, including bits above bit zero.
    for n in (0..=255).chain([1 << 63, u64::MAX]) {
        let input = [n, 0, 0, 0, 0, 0, 0, 0];
        for budget in 0..=4 {
            assert_eq!(
                boolean.run_with_memory(&input, 0, &[], budget),
                candidate.run_with_memory(&input, 0, &[], budget)
            );
        }
    }
}
