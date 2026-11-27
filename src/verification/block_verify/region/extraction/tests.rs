use super::*;
use crate::model::ir::{BlockExit, Place, RunStatus, Width};

fn fixture() -> Program {
    let step = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        0,
        6,
        vec![
            step(
                0,
                vec![Assignment {
                    destination: Reg(5).into(),
                    value: Expr::binary(BinaryOp::And, Expr::Register(Reg(5)), Expr::Const(3)),
                }],
                Control::Jump(10),
            ),
            step(
                10,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(Expr::Register(Reg(1)), Width::U64),
                }],
                Control::Next,
            ),
            step(
                11,
                vec![Assignment {
                    destination: Place::Memory {
                        address: Expr::Register(Reg(1)),
                        width: Width::U64,
                    },
                    value: Expr::binary(BinaryOp::Add, Expr::Register(Reg(2)), Expr::Const(1)),
                }],
                Control::Next,
            ),
            step(
                12,
                vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
                }],
                Control::Branch {
                    condition: Expr::binary(BinaryOp::And, Expr::Register(Reg(0)), Expr::Const(1)),
                    target: 10,
                },
            ),
            step(
                13,
                vec![],
                Control::Return(Expr::select(
                    Expr::Register(Reg(3)),
                    Expr::Register(Reg(3)),
                    Expr::load(Expr::Register(Reg(4)), Width::U64),
                )),
            ),
        ],
    )
    .unwrap()
}

fn compare(source: &Program, region: &Region, input: &[u64], base: u64, memory: &[u8]) {
    let mut expected_registers = input.to_vec();
    let mut expected_memory = memory.to_vec();
    let mut pc = region.source_entry();
    let expected = loop {
        let report = source
            .run_block_with_memory(pc, &expected_registers, base, &expected_memory)
            .unwrap();
        expected_registers = report.state.registers;
        expected_memory = report.state.memory;
        match report.exit {
            BlockExit::Next(to) if region.stops.contains(&to) => {
                break Ok((Exit::ContinueAt(to), 0));
            }
            BlockExit::Next(to) => pc = to,
            BlockExit::Returned(value) => break Ok((Exit::FunctionReturn, value)),
            BlockExit::Fault(fault) => break Err(fault),
        }
    };
    let mut extended = input.to_vec();
    extended.push(u64::MAX);
    let actual = region
        .program()
        .run_with_memory(
            &extended,
            base,
            memory,
            region.program().instructions().len(),
        )
        .unwrap();
    let observed = match actual.status {
        RunStatus::Returned(tag) => {
            let exit = region.exit(tag).expect("valid terminal tag");
            let value = if exit == Exit::FunctionReturn {
                actual.state.registers[region.return_register().0]
            } else {
                0
            };
            Ok((exit, value))
        }
        RunStatus::Fault(fault) => Err(fault),
        RunStatus::Suspended => panic!("closed DAG suspended"),
    };
    assert_eq!(observed, expected);
    assert_eq!(&actual.state.registers[..input.len()], expected_registers);
    assert_eq!(actual.state.memory, expected_memory);
}

#[test]
fn cuts_preserve_full_effects_faults_and_distinct_function_return_values() {
    let source = fixture();
    let facts = ValueWidths::analyze(&source);
    for stops in [&[10][..], &[13, 10, 10][..]] {
        let region = extract(&source, 10, stops, Some(&facts)).unwrap();
        assert!(region.belongs_to(&source));
        assert_eq!(region.input_bit_caps()[5], 2);
        assert_eq!(region.exit(u64::MAX), None);
        for count in [0, 1, u64::MAX] {
            for pointer in [100, 99, 109, u64::MAX] {
                for result in [0, 1, 2, u64::MAX] {
                    for size in [0, 7, 8, 16] {
                        let memory: Vec<_> = (0..size).map(|n| (n * 23) as u8).collect();
                        compare(
                            &source,
                            &region,
                            &[count, pointer, 99, result, 108, 3],
                            100,
                            &memory,
                        );
                    }
                }
            }
        }
    }
    let arbitrary = extract(&source, 10, &[10], None).unwrap();
    compare(
        &source,
        &arbitrary,
        &[0, 100, 99, u64::MAX, 108, u64::MAX],
        100,
        &[0; 16],
    );
}

#[test]
fn boundaries_cycles_and_foreign_entry_facts_are_checked() {
    let source = fixture();
    assert!(matches!(
        extract(&source, 11, &[10], None),
        Err(ExtractionError::Boundary)
    ));
    assert!(matches!(
        extract(&source, 10, &[11], None),
        Err(ExtractionError::Boundary)
    ));
    assert!(matches!(
        extract(&source, 10, &[13], None),
        Err(ExtractionError::Region(Error::Cycle))
    ));
    let facts = ValueWidths::analyze(&source);
    let mut changed = source.instructions().to_vec();
    changed[0].assignments[0].value =
        Expr::binary(BinaryOp::And, Expr::Register(Reg(5)), Expr::Const(7));
    let changed = Program::new(0, 6, changed).unwrap();
    assert!(matches!(
        extract(&changed, 10, &[10], Some(&facts)),
        Err(ExtractionError::EntryFacts)
    ));
    assert!(
        !extract(&source, 10, &[10], Some(&facts))
            .unwrap()
            .belongs_to(&changed)
    );
    assert!(matches!(
        extract(&source, 10, &[10], Some(&ValueWidths::default())),
        Err(ExtractionError::EntryFacts)
    ));
}

fn alter(region: &Region, change: impl FnOnce(&mut Vec<IrInstruction>)) -> Region {
    let mut altered = region.clone();
    let mut instructions = altered.program.instructions().to_vec();
    change(&mut instructions);
    altered.program = Program::new(0, altered.program.register_count(), instructions).unwrap();
    altered
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn induction_seals_bound_entry_masks_to_source_header_and_unused_extensions() {
    use super::super::invariants;
    use crate::verification::verify::Solver;
    use std::{sync::Arc, time::Duration};
    let source = Program::new(
        0,
        3,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::Const(0),
                }],
                control: Control::Jump(10),
            },
            IrInstruction {
                address: 10,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::binary(
                        BinaryOp::And,
                        Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
                        Expr::Const(3),
                    ),
                }],
                control: Control::Jump(10),
            },
        ],
    )
    .unwrap();
    let normalizer = Assignment {
        destination: Reg(0).into(),
        value: Expr::binary(BinaryOp::And, Expr::Register(Reg(0)), Expr::Const(3)),
    };
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(Duration::from_secs(5));
    let problem = invariants::Problem::new(&source, 10, &[normalizer]).unwrap();
    let invariants::Outcome::Verified(certificate) =
        problem.check(&solver, Duration::from_secs(10))
    else {
        panic!("modular counter invariant")
    };
    let certificate: Arc<_> = certificate.into();
    let plain = extract(&source, 10, &[10], None).unwrap();
    assert_eq!(plain.input_bit_caps()[0], 64);
    let checked = extract_with_invariants(&source, 10, &[10], None, &certificate).unwrap();
    assert_eq!(checked.input_bit_caps()[0], 2);
    assert!(checked.entry_invariants().unwrap().matches(&source, 10));
    checked.validate().unwrap();
    let mut stronger = checked.clone();
    stronger.caps[0] = 1;
    assert_eq!(
        stronger.validate().unwrap_err(),
        ExtractionError::EntryFacts
    );
    let changed = alter(&checked, |code| {
        code[0].assignments[1].value =
            Expr::binary(BinaryOp::And, Expr::Register(Reg(0)), Expr::Const(1))
    });
    assert_eq!(changed.validate().unwrap_err(), ExtractionError::Projection);
    let extended = Program::new(0, 4, source.instructions().to_vec()).unwrap();
    let extended = extract_with_invariants(&extended, 10, &[10], None, &certificate).unwrap();
    assert_eq!(extended.input_bit_caps(), [2, 64, 64, 64]);
    extended.validate().unwrap();
    let reentered = Program::new(10, 3, source.instructions().to_vec()).unwrap();
    assert_eq!(
        extract_with_invariants(&reentered, 10, &[10], None, &certificate).unwrap_err(),
        ExtractionError::EntryFacts
    );
    let mut code = source.instructions().to_vec();
    code[1].control = Control::Return(Expr::Const(0));
    let foreign = Program::new(0, 3, code).unwrap();
    assert_eq!(
        extract_with_invariants(&foreign, 10, &[10], None, &certificate).unwrap_err(),
        ExtractionError::EntryFacts
    );
}

#[test]
fn independent_projection_checker_rejects_changed_effects_routes_caps_and_tags() {
    let source = fixture();
    let region = extract(&source, 10, &[10], Some(&ValueWidths::analyze(&source))).unwrap();
    let store_pc = region.source_to_region()[&11];
    let load_pc = region.source_to_region()[&10];
    let return_pc = region.source_to_region()[&13];
    let terminal = region.terminals[&10];
    for bad in [
        alter(&region, |is| {
            is.iter_mut()
                .find(|i| i.address == store_pc)
                .unwrap()
                .assignments
                .clear()
        }),
        alter(&region, |is| {
            is.iter_mut()
                .find(|i| i.address == load_pc)
                .unwrap()
                .control = Control::Jump(return_pc)
        }),
        alter(&region, |is| {
            is.iter_mut()
                .find(|i| i.address == return_pc)
                .unwrap()
                .assignments
                .last_mut()
                .unwrap()
                .value = Expr::Const(0)
        }),
        alter(&region, |is| {
            is.iter_mut()
                .find(|i| i.address == terminal)
                .unwrap()
                .control = Control::Return(Expr::Const(99))
        }),
        alter(&region, |is| is[0].assignments.pop().map(|_| ()).unwrap()),
    ] {
        assert!(bad.validate().is_err());
    }
    let mut caps = region.clone();
    caps.caps[5] = 1;
    assert_eq!(caps.validate(), Err(ExtractionError::EntryFacts));
    let mut map = region.clone();
    map.body.remove(&11);
    assert_eq!(map.validate(), Err(ExtractionError::Projection));
}

#[test]
fn same_target_branch_still_evaluates_its_faulting_condition() {
    let source = Program::new(
        0,
        1,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: Expr::load(Expr::Register(Reg(0)), Width::U8),
                    target: 1,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(u64::MAX)),
            },
        ],
    )
    .unwrap();
    let region = extract(&source, 0, &[], None).unwrap();
    compare(&source, &region, &[100], 100, &[7]);
    compare(&source, &region, &[99], 100, &[7]);
    let branch = region.source_to_region()[&0];
    let target = region.source_to_region()[&1];
    assert!(
        alter(&region, |is| is
            .iter_mut()
            .find(|i| i.address == branch)
            .unwrap()
            .control = Control::Jump(target))
        .validate()
        .is_err()
    );
}

#[test]
fn source_expression_depth_and_extra_capture_register_are_bounded() {
    let source = Program::new(
        0,
        MAX_REGISTERS,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    assert!(matches!(
        extract(&source, 0, &[], None),
        Err(ExtractionError::Region(Error::Limit))
    ));
    let mut deep = Expr::Const(0);
    for _ in 0..super::super::MAX_DEPTH + 2 {
        deep = Expr::unary(crate::model::ir::UnaryOp::SignExtend(Width::U8), deep);
    }
    let source = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(deep),
        }],
    )
    .unwrap();
    assert!(matches!(
        extract(&source, 0, &[], None),
        Err(ExtractionError::Region(Error::Limit))
    ));
}
