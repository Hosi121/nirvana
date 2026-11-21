use crate::support::programs;

use nirvana::emit::emit_c;
use nirvana::ir::{
    Assignment, BinaryOp, Control, ExecutionError, Expr, IrInstruction, Program, ProgramError, Reg,
};
use nirvana::structure::{StructureError, StructuredFunction};

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

#[test]
fn examples_preserve_registers_returns_and_instruction_traces() {
    for &name in programs::NAMES {
        let program = programs::named(name).unwrap();
        let recovered = StructuredFunction::recover(&program).unwrap();
        for input in [
            [0, 0, 0, 0],
            [1, 2, 3, 4],
            [12, 9, 8, 7],
            [u64::MAX, 65, 64, 63],
        ] {
            assert_eq!(
                program.execute(&input, 1000),
                recovered.execute(&input, 1000),
                "{name}: {input:?}"
            );
        }
        let output = emit_c(&program).unwrap();
        assert!(output.fallback_reason.is_none(), "{name}");
        assert!(!output.code.contains("goto bb"));
    }
}

#[test]
fn recovers_a_simple_infinite_loop_without_inventing_a_return() {
    let program = Program::new(0, 0, vec![instruction(0, vec![], Control::Jump(0))]).unwrap();
    let function = StructuredFunction::recover(&program).unwrap();
    assert_eq!(program.execute(&[], 50), Err(ExecutionError::StepLimit));
    assert_eq!(function.execute(&[], 50), Err(ExecutionError::StepLimit));
    let output = emit_c(&program).unwrap();
    assert!(output.code.contains("while (1)"));
    assert!(!output.code.contains("return"));
}

#[test]
fn falls_back_when_one_arm_has_no_exit_path() {
    let program = Program::new(
        0,
        1,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::Register(Reg(0)),
                    target: 2,
                },
            ),
            instruction(1, vec![], Control::Return(Expr::Const(1))),
            instruction(2, vec![], Control::Jump(2)),
        ],
    )
    .unwrap();
    assert!(matches!(
        StructuredFunction::recover(&program),
        Err(StructureError::MissingJoin(_))
    ));
    assert!(emit_c(&program).unwrap().fallback_reason.is_some());
}

#[test]
fn rejects_invalid_registers_before_execution_or_emission() {
    for (assignments, control) in [
        (
            vec![Assignment {
                destination: Reg(1).into(),
                value: Expr::Const(0),
            }],
            Control::Return(Expr::Const(0)),
        ),
        (vec![], Control::Return(Expr::Register(Reg(1)))),
        (
            vec![],
            Control::Branch {
                condition: Expr::Register(Reg(1)),
                target: 0,
            },
        ),
    ] {
        // Supply a return for the branch's fallthrough so register validation is reached.
        let result = Program::new(
            0,
            1,
            vec![
                instruction(0, assignments, control),
                instruction(1, vec![], Control::Return(Expr::Const(0))),
            ],
        );
        assert!(matches!(
            result,
            Err(ProgramError::InvalidRegister {
                register: Reg(1),
                ..
            })
        ));
    }
}

#[test]
fn unsigned_arithmetic_wraps_and_shift_counts_are_masked() {
    let expressions = [
        (BinaryOp::Add, u64::MAX, 1, 0),
        (BinaryOp::Sub, 0, 1, u64::MAX),
        (BinaryOp::Mul, u64::MAX, 2, u64::MAX - 1),
        (BinaryOp::Shl, 1, 64, 1),
        (BinaryOp::Shl, 1, 65, 2),
        (BinaryOp::Shr, u64::MAX, 64, u64::MAX),
    ];
    for (op, left, right, expected) in expressions {
        let program = Program::new(
            0,
            0,
            vec![instruction(
                0,
                vec![],
                Control::Return(Expr::binary(op, Expr::Const(left), Expr::Const(right))),
            )],
        )
        .unwrap();
        assert_eq!(program.execute(&[], 1).unwrap().value, expected);
    }
}

#[test]
fn assignments_are_sequential_and_precede_branch_conditions() {
    let program = Program::new(
        0,
        2,
        vec![
            instruction(
                0,
                vec![
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::Const(42),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: Expr::Register(Reg(0)),
                    },
                ],
                Control::Branch {
                    condition: Expr::Register(Reg(1)),
                    target: 2,
                },
            ),
            instruction(1, vec![], Control::Return(Expr::Const(0))),
            instruction(2, vec![], Control::Return(Expr::Register(Reg(1)))),
        ],
    )
    .unwrap();
    let output = program.execute(&[0, 0], 2).unwrap();
    assert_eq!(output.value, 42);
    assert_eq!(output.trace, vec![0, 2]);
    assert_eq!(
        StructuredFunction::recover(&program)
            .unwrap()
            .execute(&[0, 0], 2)
            .unwrap(),
        output
    );
}

#[test]
fn validates_inputs_and_instruction_budgets() {
    let program = programs::named("diamond").unwrap();
    assert!(matches!(
        program.execute(&[], 1),
        Err(ExecutionError::RegisterCount { .. })
    ));
    assert_eq!(program.execute(&[0; 4], 0), Err(ExecutionError::StepLimit));
    let function = StructuredFunction::recover(&program).unwrap();
    assert_eq!(program.execute(&[0; 4], 2), function.execute(&[0; 4], 2));
    assert!(program.execute(&[0; 4], 3).is_ok());
}

#[test]
fn four_thousand_control_flow_programs_preserve_structured_execution() {
    use nirvana::cfg::Flow;
    let choices = [
        Flow::Next,
        Flow::Return,
        Flow::Jump(0),
        Flow::Jump(1),
        Flow::Jump(2),
        Flow::Jump(3),
        Flow::Branch(0),
        Flow::Branch(1),
        Flow::Branch(2),
        Flow::Branch(3),
    ];
    let mut accepted = 0;
    let mut total = 0;
    for &first in &choices {
        for &second in &choices {
            for &third in &choices {
                for entry in 0..4 {
                    let flows = [first, second, third, Flow::Return];
                    let instructions = flows
                        .into_iter()
                        .enumerate()
                        .map(|(address, flow)| {
                            let control = match flow {
                                Flow::Next => Control::Next,
                                Flow::Jump(target) => Control::Jump(target),
                                Flow::Branch(target) => Control::Branch {
                                    condition: Expr::binary(
                                        BinaryOp::And,
                                        Expr::Register(Reg(0)),
                                        Expr::Const(1),
                                    ),
                                    target,
                                },
                                Flow::Return => Control::Return(Expr::Register(Reg(1))),
                                _ => unreachable!(),
                            };
                            instruction(
                                address as u64,
                                vec![
                                    Assignment {
                                        destination: Reg(0).into(),
                                        value: Expr::binary(
                                            BinaryOp::Add,
                                            Expr::Register(Reg(0)),
                                            Expr::Const(address as u64 + 1),
                                        ),
                                    },
                                    Assignment {
                                        destination: Reg(1).into(),
                                        value: Expr::binary(
                                            BinaryOp::Xor,
                                            Expr::Register(Reg(1)),
                                            Expr::Register(Reg(0)),
                                        ),
                                    },
                                ],
                                control,
                            )
                        })
                        .collect();
                    let program = Program::new(entry, 2, instructions).unwrap();
                    if let Ok(function) = StructuredFunction::recover(&program) {
                        accepted += 1;
                        let stats = function.stats();
                        assert_eq!(stats.unique_blocks, program.cfg().reachable_blocks().len());
                        assert!(stats.emitted_block_copies <= 2 * stats.unique_blocks);
                        for input in [[0, 0], [1, 5], [u64::MAX, 1]] {
                            assert_eq!(
                                program.execute(&input, 64),
                                function.execute(&input, 64),
                                "flows={flows:?}, entry={entry}, input={input:?}"
                            );
                        }
                    }
                    total += 1;
                }
            }
        }
    }
    assert_eq!(total, 4000);
    assert!(
        accepted >= 3843,
        "only {accepted} of {total} tiny graphs structured"
    );
    println!(
        "structured {accepted}/{total} generated CFGs; execution checked with three inputs each"
    );
}

#[test]
fn shared_tail_duplication_is_bounded_and_reported() {
    let program = programs::named("shared-tail").unwrap();
    let function = StructuredFunction::recover(&program).unwrap();
    let stats = function.stats();
    assert_eq!(stats.unique_blocks, 5);
    assert_eq!(stats.emitted_block_copies, 5);
    assert_eq!(stats.extra_block_copies, 0);
    assert_eq!(emit_c(&program).unwrap().structure_stats, Some(stats));
    assert_eq!(
        StructuredFunction::recover_with_copy_limit(&program, 1)
            .unwrap()
            .stats(),
        stats
    );
    assert!(matches!(
        StructuredFunction::recover_with_copy_limit(&program, 0),
        Err(StructureError::CopyLimit { limit: 0, .. })
    ));
}

#[test]
fn shared_returns_are_hoisted_without_relaxing_the_copy_limit() {
    let program = programs::named("copy-limit").unwrap();
    let function = StructuredFunction::recover_with_copy_limit(&program, 1).unwrap();
    assert_eq!(function.stats().extra_block_copies, 0);
    assert_eq!(
        function.evidence().compared_copies,
        function.evidence().original_steps
    );
    let output = emit_c(&program).unwrap();
    assert!(output.fallback_reason.is_none());
    assert_eq!(output.structure_stats, Some(function.stats()));
    let expanded = StructuredFunction::recover_with_copy_limit(&program, 3).unwrap();
    assert_eq!(expanded.stats().extra_block_copies, 0);
    for input in 0..16 {
        let input = [input, 0, 0, 0];
        assert_eq!(program.execute(&input, 100), expanded.execute(&input, 100));
        for limit in 0..12 {
            assert_eq!(
                program.run_with_memory(&input, 0, &[], limit),
                function.run_with_memory(&input, 0, &[], limit)
            );
        }
    }
}

#[test]
fn nested_exit_tails_preserve_the_outer_continue_target() {
    let program = programs::named("nonlocal-exit").unwrap();
    let function = StructuredFunction::recover(&program).unwrap();
    for input in 0..16 {
        let input = [input, 0, 9, 10];
        for limit in 0..64 {
            assert_eq!(
                program.execute(&input, limit),
                function.execute(&input, limit)
            );
        }
    }
    let output = emit_c(&program).unwrap();
    assert!(output.fallback_reason.is_none());
    assert!(!output.code.contains("goto bb"));
}

#[test]
fn multi_exit_loop_reaches_the_common_follow_once() {
    for name in [
        "multi-exit",
        "multi-exit-prefix",
        "nested-multi-exit",
        "loop-returns",
    ] {
        let program = programs::named(name).unwrap();
        let function = StructuredFunction::recover(&program).unwrap();
        assert_eq!(function.stats().extra_block_copies, 0, "{name}");
        for input in 0..16 {
            let input = [input, 0, 9, 10];
            let expected = program.execute(&input, 1000);
            assert_eq!(
                expected,
                function.execute(&input, 1000),
                "{name}: {input:?}"
            );
            if name == "multi-exit" {
                assert_eq!(
                    expected
                        .unwrap()
                        .trace
                        .iter()
                        .filter(|&&address| address == 6)
                        .count(),
                    1
                );
            }
        }
    }
}

#[test]
fn larger_generated_graphs_preserve_execution_and_the_copy_bound() {
    let mut random_state = 0x1234_5678_9abc_def0u64;
    let mut next = || {
        random_state ^= random_state << 13;
        random_state ^= random_state >> 7;
        random_state ^= random_state << 17;
        random_state
    };
    let mut accepted = 0;
    for _ in 0..1024 {
        let mut instructions = Vec::new();
        for address in 0..8 {
            let choice = next() % 8;
            let target = next() % 8;
            let forward = if address < 7 {
                address + 1 + target % (7 - address)
            } else {
                7
            };
            let condition = Expr::binary(BinaryOp::And, Expr::Register(Reg(0)), Expr::Const(3));
            let control = if address == 7 {
                Control::Return(Expr::Register(Reg(1)))
            } else {
                match choice {
                    0 => Control::Return(Expr::Register(Reg(1))),
                    1 | 7 => Control::Next,
                    2 => Control::Jump(forward),
                    3 => Control::Branch {
                        condition,
                        target: forward,
                    },
                    4 => Control::Jump(target),
                    5 => Control::Branch { condition, target },
                    6 => Control::Branch {
                        condition,
                        target: address + 1,
                    },
                    _ => unreachable!(),
                }
            };
            instructions.push(instruction(
                address,
                vec![
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::binary(
                            BinaryOp::Add,
                            Expr::Register(Reg(0)),
                            Expr::Const(next() % 5 + 1),
                        ),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: Expr::binary(
                            BinaryOp::Xor,
                            Expr::Register(Reg(1)),
                            Expr::Register(Reg(0)),
                        ),
                    },
                ],
                control,
            ));
        }
        let program = Program::new(next() % 8, 2, instructions).unwrap();
        if let Ok(function) = StructuredFunction::recover(&program) {
            accepted += 1;
            let stats = function.stats();
            assert!(stats.emitted_block_copies <= stats.unique_blocks * 2);
            for input in [[0, 0], [1, 5], [u64::MAX, u64::MAX]] {
                assert_eq!(
                    program.execute(&input, 128),
                    function.execute(&input, 128),
                    "{program:?}, input={input:?}"
                );
            }
        }
    }
    assert!(
        accepted > 200,
        "only {accepted} larger CFGs were structured"
    );
}
