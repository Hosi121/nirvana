use super::*;
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place};

fn source(value: Expr) -> Program {
    Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Place::Memory {
                        address: Expr::Register(Reg(3)),
                        width: Width::U64,
                    },
                    value,
                },
                Assignment {
                    destination: Reg(0).into(),
                    value: Expr::Const(0),
                },
                Assignment {
                    destination: Reg(1).into(),
                    value: Expr::load(Expr::Register(Reg(3)), Width::U16),
                },
            ],
            control: Control::Return(Expr::Register(Reg(1))),
        }],
    )
    .unwrap()
}
fn read(function: &mut Function) -> &mut Operation {
    let Terminator::Return(value) = &mut function.blocks[0].terminator else {
        panic!()
    };
    &mut value.bindings[0].operation
}

#[test]
fn saved_checker_rejects_stale_snapshots_forged_slices_and_missing_plans() {
    let original = Function::from_low(&source(Expr::Register(Reg(0)))).unwrap();
    let (valid, _) = original.recover_saved_values().unwrap().unwrap();
    for change in 0..7 {
        let mut forged = valid.clone();
        match change {
            0..=2 => {
                let Operation::ReadSaved { slice, .. } = read(&mut forged) else {
                    panic!()
                };
                match change {
                    0 => slice.snapshot = SnapshotId(999),
                    1 => slice.start = 8,
                    _ => slice.width = Width::U64,
                }
            }
            3 => forged.saved = None,
            4 => forged.saved.as_mut().unwrap().view.snapshots[0].point.after = Some(2),
            5 => forged.saved.as_mut().unwrap().evidence.annotated_reads += 1,
            _ => {
                let Operation::ReadSaved { version, .. } = read(&mut forged) else {
                    panic!()
                };
                *version = None;
            }
        }
        assert!(forged.lower().is_err(), "mutation {change}");
        assert!(forged.lower_saved_values().is_err(), "mutation {change}");
        assert!(
            original.validate_saved_recovery(&forged).is_err(),
            "mutation {change}"
        );
    }
    let changed = Function::from_low(&source(Expr::Const(7))).unwrap();
    let (changed, _) = changed.recover_saved_values().unwrap().unwrap();
    assert!(original.validate_saved_recovery(&changed).is_err());
}

#[test]
fn saved_identity_and_constant_refinement_compose_in_either_order() {
    let low = source(Expr::Const(0x12345678));
    let original = Function::from_low(&low).unwrap();
    let (saved, _) = original.recover_saved_values().unwrap().unwrap();
    let (saved_first, _) = saved.recover_memory_constants().unwrap();
    let (constants, _) = original.recover_memory_constants().unwrap();
    let (constants_first, _) = constants.recover_saved_values().unwrap().unwrap();
    assert_eq!(
        saved_first.to_text().unwrap(),
        constants_first.to_text().unwrap()
    );
    for candidate in [saved_first, constants_first] {
        for pointer in [4096, 4127, u64::MAX] {
            let input = [11, 13, 17, pointer];
            let expected = low.run_with_memory(&input, 4096, &[0; 32], 1).unwrap();
            assert_eq!(
                candidate
                    .run_with_memory(&input, 4096, &[0; 32], 1)
                    .unwrap(),
                expected
            );
            let lowering = candidate.lower_saved_values().unwrap().unwrap();
            let mut extended = input.to_vec();
            extended.resize(lowering.program().register_count(), u64::MAX);
            let actual = lowering
                .program()
                .run_with_memory(&extended, 4096, &[0; 32], 1)
                .unwrap();
            assert_eq!(lowering.project_report(actual).unwrap(), expected);
        }
    }
}
