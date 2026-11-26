//! Actual solver verdicts and concrete full-memory/first-fault counterexamples.
use super::*;
use std::path::PathBuf;

fn all_shared(program: &Program) -> Vec<Reg> {
    (0..program.register_count()).map(Reg).collect()
}

fn fixture(lanes: u64, rolled: bool, wrong_store: bool) -> Program {
    use crate::model::ir::{Assignment, BinaryOp};
    let r = |id| Expr::Register(Reg(id));
    let k = Expr::Const;
    let op = Expr::binary;
    let assign = |id, value| Assignment {
        destination: Reg(id).into(),
        value,
    };
    let mut prefix = vec![assign(
        6,
        op(BinaryOp::Add, op(BinaryOp::And, r(1), k(lanes - 1)), k(1)),
    )];
    if rolled {
        prefix.push(assign(5, k(0)));
    }
    let mut instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: prefix,
        control: Control::Jump(10),
    }];
    for lane in 0..lanes {
        let pc = 10 + lane * 10;
        let index = op(BinaryOp::Add, r(0), if rolled { r(5) } else { k(lane) });
        let address = op(
            BinaryOp::Add,
            r(2),
            op(BinaryOp::Mul, op(BinaryOp::And, index.clone(), k(3)), k(8)),
        );
        let update = assign(
            3,
            op(
                BinaryOp::Add,
                r(3),
                op(
                    BinaryOp::Xor,
                    Expr::load(address, Width::U64),
                    op(BinaryOp::Add, r(0), k(1)),
                ),
            ),
        );
        let store = Assignment {
            destination: Place::Memory {
                address: op(BinaryOp::Add, r(2), k(16)),
                width: Width::U64,
            },
            value: r(3),
        };
        let assignments = if wrong_store && lane == 0 {
            vec![store, update]
        } else {
            vec![update, store]
        };
        instructions.push(IrInstruction {
            address: pc,
            size: 1,
            assignments,
            control: Control::Branch {
                condition: op(
                    BinaryOp::Eq,
                    op(BinaryOp::And, op(BinaryOp::Xor, r(3), r(4)), k(7)),
                    k(0),
                ),
                target: 1001,
            },
        });
        instructions.push(IrInstruction {
            address: pc + 1,
            size: 1,
            assignments: vec![],
            control: Control::Branch {
                condition: op(BinaryOp::Eq, op(BinaryOp::And, r(3), k(3)), k(1)),
                target: pc + 4,
            },
        });
        let mut assignments = vec![assign(
            4,
            op(BinaryOp::Add, r(4), op(BinaryOp::And, r(3), k(15))),
        )];
        if rolled {
            assignments.push(assign(5, op(BinaryOp::Add, r(5), k(1))));
        }
        let control = if lane + 1 == lanes && !rolled {
            Control::Jump(1000)
        } else {
            Control::Branch {
                condition: op(BinaryOp::Ult, if rolled { r(5) } else { k(lane + 1) }, r(6)),
                target: if lane + 1 == lanes { 1003 } else { pc + 10 },
            }
        };
        instructions.push(IrInstruction {
            address: pc + 2,
            size: 1,
            assignments,
            control,
        });
        instructions.push(IrInstruction {
            address: pc + 3,
            size: 1,
            assignments: vec![],
            control: Control::Jump(1000),
        });
        instructions.push(IrInstruction {
            address: pc + 4,
            size: 1,
            assignments: vec![assign(4, op(BinaryOp::Xor, r(4), index))],
            control: Control::Jump(1002),
        });
    }
    for tag in 0..4 {
        instructions.push(IrInstruction {
            address: 1000 + tag,
            size: 1,
            assignments: vec![],
            control: Control::Return(k(tag)),
        });
    }
    instructions.sort_by_key(|i| i.address);
    Program::new(0, 7, instructions).unwrap()
}

fn changed(program: &Program, edit: impl FnOnce(&mut Vec<IrInstruction>)) -> Program {
    let mut instructions = program.instructions().to_vec();
    edit(&mut instructions);
    Program::new(0, program.register_count(), instructions).unwrap()
}
fn join_case(value: u64) -> Program {
    use crate::model::ir::Assignment;
    let assign = |value| Assignment {
        destination: Reg(5).into(),
        value: Expr::Const(value),
    };
    Program::new(
        0,
        7,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: Expr::Register(Reg(0)),
                    target: 3,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![assign(0)],
                control: Control::Jump(4),
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![assign(value)],
                control: Control::Jump(4),
            },
            IrInstruction {
                address: 4,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(3).into(),
                    value: Expr::Register(Reg(5)),
                }],
                control: Control::Return(Expr::Const(0)),
            },
        ],
    )
    .unwrap()
}
fn post_fault(value: u64) -> Program {
    use crate::model::ir::Assignment;
    let store = |at, value| Assignment {
        destination: Place::Memory {
            address: Expr::Const(at),
            width: Width::U8,
        },
        value: Expr::Const(value),
    };
    Program::new(
        0,
        7,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    store(0, 1),
                    Assignment {
                        destination: Reg(5).into(),
                        value: Expr::load(Expr::Const(u64::MAX), Width::U64),
                    },
                ],
                control: Control::Next,
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![store(1, value)],
                control: Control::Return(Expr::Const(0)),
            },
        ],
    )
    .unwrap()
}

fn same_target(condition: Expr) -> Program {
    Program::new(
        0,
        7,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition,
                    target: 1,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            },
        ],
    )
    .unwrap()
}

#[test]
#[ignore = "requires Z3; validates positive regions and replays negative witnesses"]
fn memory_regions_cover_unrolling_aliases_faults_exits_and_join_constants() {
    use crate::model::ir::BinaryOp;
    let seconds = std::env::var("NIRVANA_REGION_SECONDS").map_or(5, |value| value.parse().unwrap());
    let solver = Solver::new(
        std::env::var_os("NIRVANA_Z3").map_or_else(|| PathBuf::from("z3"), PathBuf::from),
    )
    .with_timeout(std::time::Duration::from_secs(seconds));
    let directory = std::env::var_os("NIRVANA_REGION_REPORT").map(PathBuf::from);
    if let Some(path) = &directory {
        std::fs::create_dir_all(path).unwrap();
    }
    let good = fixture(1, true, false);
    let mut cases = Vec::new();
    for (label, lanes, rolled) in [
        ("identity", 4, false),
        ("one-lane", 1, true),
        ("two-lanes", 2, true),
        ("four-lanes", 4, true),
    ] {
        cases.push((
            label,
            fixture(lanes, false, false),
            fixture(lanes, rolled, false),
            false,
        ));
    }
    let wide_before = fixture(4, false, false);
    let wide_after = fixture(4, true, false);
    cases.push((
        "four-lanes-80-registers",
        Program::new(0, 80, wide_before.instructions().to_vec()).unwrap(),
        Program::new(0, 80, wide_after.instructions().to_vec()).unwrap(),
        false,
    ));
    cases.push((
        "lazy-dead-load",
        fixture(1, false, false),
        changed(&good, |i| {
            i[0].assignments.push(Assignment {
                destination: Reg(5).into(),
                value: Expr::select(
                    Expr::Const(0),
                    Expr::load(Expr::Const(u64::MAX), Width::U64),
                    Expr::Register(Reg(5)),
                ),
            })
        }),
        false,
    ));
    cases.push(("post-fault-effects", post_fault(2), post_fault(9), false));
    cases.push((
        "reordered-store",
        fixture(1, false, false),
        fixture(1, true, true),
        true,
    ));
    cases.push((
        "missing-store",
        fixture(1, false, false),
        changed(&good, |i| {
            i.iter_mut()
                .find(|i| i.address == 10)
                .unwrap()
                .assignments
                .remove(1);
        }),
        true,
    ));
    cases.push((
        "eager-dead-load",
        fixture(1, false, false),
        changed(&good, |i| {
            i[0].assignments.push(Assignment {
                destination: Reg(5).into(),
                value: Expr::load(Expr::Const(u64::MAX), Width::U64),
            })
        }),
        true,
    ));
    cases.push((
        "wrong-exit",
        fixture(1, false, false),
        changed(&good, |i| {
            let Control::Branch { target, .. } =
                &mut i.iter_mut().find(|i| i.address == 10).unwrap().control
            else {
                unreachable!()
            };
            *target = 1000;
        }),
        true,
    ));
    cases.push((
        "wrong-mark",
        fixture(1, false, false),
        changed(&good, |i| {
            let assignment = &mut i.iter_mut().find(|i| i.address == 14).unwrap().assignments[0];
            assignment.value =
                Expr::binary(BinaryOp::Add, assignment.value.clone(), Expr::Const(1));
        }),
        true,
    ));
    cases.push(("join-constants", join_case(1), join_case(2), true));
    let condition = Expr::load(
        Expr::binary(BinaryOp::Add, Expr::Register(Reg(2)), Expr::Const(64)),
        Width::U8,
    );
    cases.push((
        "same-target-preserved",
        same_target(condition.clone()),
        same_target(Expr::binary(
            BinaryOp::Eq,
            condition.clone(),
            Expr::Const(0),
        )),
        false,
    ));
    cases.push((
        "same-target-dropped",
        same_target(condition),
        same_target(Expr::Const(0)),
        true,
    ));
    for (label, before, after, negative) in cases {
        let shared = all_shared(&before);
        let query = query(&before, &after, &shared, &[Reg(3), Reg(4)]).unwrap();
        if let Some(path) = &directory {
            std::fs::write(path.join(format!("{label}.smt2")), query.smt2()).unwrap();
            std::fs::write(
                path.join(format!("{label}.before.ir")),
                format!(
                    "entry={} registers={}\n{:#?}\n",
                    before.cfg().block(before.cfg().entry()).start,
                    before.register_count(),
                    before.instructions()
                ),
            )
            .unwrap();
            std::fs::write(
                path.join(format!("{label}.after.ir")),
                format!(
                    "entry={} registers={}\n{:#?}\n",
                    after.cfg().block(after.cfg().entry()).start,
                    after.register_count(),
                    after.instructions()
                ),
            )
            .unwrap();
        }
        let started = std::time::Instant::now();
        let verdict = query.check(&solver);
        let elapsed = started.elapsed().as_millis();
        if negative {
            let Verdict::Counterexample(witness) = verdict else {
                panic!("{label}: {verdict:?}");
            };
            assert!(differs(&witness.before, &witness.after, &[Reg(3), Reg(4)]));
            if let Some(path) = &directory {
                std::fs::write(path.join(format!("{label}.memory.bin")), &witness.memory).unwrap();
                std::fs::write(
                    path.join(format!("{label}.inputs.txt")),
                    format!(
                        "base={}\nbefore={:?}\nafter={:?}\nbefore_status={:?}\nafter_status={:?}\n",
                        witness.memory_base,
                        witness.before_registers,
                        witness.after_registers,
                        witness.before.status,
                        witness.after.status
                    ),
                )
                .unwrap();
            }
            let limited = format!(
                "{}(assert (= base {}))\n(assert (= size {}))\n(assert (= r2 {}))\n(assert (= r0 {}))\n",
                query.smt2(),
                word(0),
                word(64),
                word(0),
                word(2)
            );
            let response = solver.run_smt(&limited, &query.names).unwrap();
            let model = parse_named_values(&response, &query.names).unwrap();
            let alias = query.replay(&model).unwrap();
            assert!(differs(&alias.before, &alias.after, &[Reg(3), Reg(4)]));
            if let Some(path) = &directory {
                std::fs::write(path.join(format!("{label}.alias-model.txt")), &response).unwrap();
            }
            println!(
                "DAG-REGION {label} verdict=counterexample replay=true constrained_replay=true bytes={} ms={elapsed}",
                query.smt2().len()
            );
        } else {
            assert_eq!(verdict, Verdict::EquivalentUnderModel, "{label}");
            println!(
                "DAG-REGION {label} verdict=equivalent bytes={} ms={elapsed}",
                query.smt2().len()
            );
        }
    }
    let wide = |value| {
        Program::new(
            0,
            1,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::load(Expr::Const(0), Width::U8),
                    },
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::load(Expr::Const(REPLAY_BYTES), Width::U8),
                    },
                ],
                control: Control::Return(Expr::Const(value)),
            }],
        )
        .unwrap()
    };
    let q = query(&wide(0), &wide(1), &[Reg(0)], &[]).unwrap();
    let started = std::time::Instant::now();
    assert_eq!(
        q.check(&solver),
        Verdict::Unknown(UnknownReason::ReplayLimit)
    );
    if let Some(path) = &directory {
        std::fs::write(path.join("oversized-witness.smt2"), q.smt2()).unwrap();
    }
    println!(
        "DAG-REGION oversized-witness verdict=replay_limit bytes={} ms={}",
        q.smt2().len(),
        started.elapsed().as_millis()
    );
}
