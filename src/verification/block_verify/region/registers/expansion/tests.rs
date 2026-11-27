use super::super::tests::fixture;
use super::*;
use crate::model::ir::{Assignment, BinaryOp};

fn candidate(compact: &Compact) -> Program {
    let fresh = Reg(compact.program().register_count());
    let mut body = compact.program().instructions().to_vec();
    body[0].assignments.insert(
        0,
        Assignment {
            destination: fresh.into(),
            value: Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
        },
    );
    let Control::Return(value) = &mut body.last_mut().unwrap().control else {
        unreachable!()
    };
    *value = Expr::binary(BinaryOp::Add, value.clone(), Expr::Register(fresh));
    Program::new(10, fresh.0 + 1, body).unwrap()
}

#[test]
fn expansion_keeps_abi_ids_fresh_storage_and_full_mapped_reports() {
    let compact = compact(&fixture()).unwrap();
    let source = candidate(&compact);
    let expanded = compact.expand_candidate(&source).unwrap();
    expanded.validate().unwrap();
    assert_eq!(
        expanded.registers(),
        &[Reg(0), Reg(7), Reg(300), Reg(319), Reg(739), Reg(740)]
    );
    assert_eq!(expanded.program().register_count(), 741);
    let mapped: BTreeSet<_> = expanded.registers().iter().map(|r| r.0).collect();
    for pointer in [100, 99, u64::MAX] {
        for size in [0, 7, 8, 16, 17, 24] {
            for condition in [0, 1] {
                for value in [0, u64::MAX] {
                    let mut input: Vec<_> = (0..740).map(|i| i as u64 * 0x1234_5678_9abc).collect();
                    input[0] = value;
                    input[7] = pointer;
                    input[319] = condition;
                    let input = expanded.extend_input(&input, u64::MAX).unwrap();
                    let dense = expanded.project_input(&input).unwrap();
                    let memory: Vec<_> = (0..size).map(|n| (n * 29 + 7) as u8).collect();
                    for budget in 0..5 {
                        let expected = source
                            .run_with_memory(&dense, 100, &memory, budget)
                            .unwrap();
                        let mut actual = expanded
                            .program()
                            .run_with_memory(&input, 100, &memory, budget)
                            .unwrap();
                        for (index, value) in input.iter().enumerate() {
                            if !mapped.contains(&index) {
                                assert_eq!(actual.state.registers[index], *value);
                            }
                        }
                        actual.state.registers =
                            expanded.project_input(&actual.state.registers).unwrap();
                        assert_eq!(actual, expected);
                    }
                }
            }
        }
    }
    assert!(expanded.project_input(&vec![0; 740]).is_err());
    assert!(expanded.extend_input(&vec![0; 741], 0).is_err());
}

#[test]
fn expansion_checker_rejects_aliases_changed_effects_and_foreign_namespace_sizes() {
    let compact = compact(&fixture()).unwrap();
    let expanded = compact.expand_candidate(&candidate(&compact)).unwrap();
    let mut aliased = expanded.clone();
    *aliased.registers.last_mut().unwrap() = Reg(7);
    assert_eq!(aliased.validate(), Err(Error::BoundaryMapping));
    let mut dropped = expanded.clone();
    let mut body = dropped.program.instructions().to_vec();
    body[1].control = Control::Jump(12);
    dropped.program = Program::new(10, 741, body).unwrap();
    assert_eq!(dropped.validate(), Err(Error::BoundaryMapping));
    let mut changed = expanded.clone();
    let mut body = changed.program.instructions().to_vec();
    body[0].assignments[0].destination = Reg(739).into();
    changed.program = Program::new(10, 741, body).unwrap();
    assert_eq!(changed.validate(), Err(Error::BoundaryMapping));
    let mut count = expanded.clone();
    count.original_count = 739;
    assert_eq!(count.validate(), Err(Error::BoundaryMapping));
    let smaller = Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    assert!(compact.expand_candidate(&smaller).is_err());
}
