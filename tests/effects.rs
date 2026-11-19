use nirvana::effects::{
    BuildError, CallInstruction, CallTarget, Instruction, Limits, Output, Program, PutsOutcome,
    Status, Suspend, VOLATILE_REGISTERS,
};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, ExecutionError, Expr, IrInstruction, MemoryFault,
    Place, Reg, RunStatus, Width,
};
use nirvana::x86::{RAX, RDI, RSP};

const BASE: u64 = 0x1000;
const PUTS: u64 = 0x9000;
const COUNT: usize = 32;

fn core(address: u64, assignments: Vec<Assignment>, control: Control) -> Instruction {
    Instruction::Core(IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    })
}

fn call(address: u64, target: CallTarget, tail: bool) -> Instruction {
    Instruction::Call(CallInstruction {
        address,
        size: 1,
        target,
        tail,
    })
}

fn program(instructions: Vec<Instruction>) -> Program {
    Program::new(0, COUNT, instructions, PUTS).unwrap()
}

fn one_call(target: CallTarget, tail: bool) -> Program {
    let mut instructions = vec![call(0, target, tail)];
    if !tail {
        instructions.push(core(1, vec![], Control::Return(Expr::Register(Reg(RAX)))));
    }
    program(instructions)
}

fn input() -> [u64; COUNT] {
    let mut registers = [0; COUNT];
    registers[RDI] = BASE;
    registers[RSP] = BASE + 24;
    registers
}

fn memory() -> [u8; 32] {
    let mut memory = [0; 32];
    memory[..4].copy_from_slice(b"abc\0");
    memory
}

fn fault(access: AccessKind, address: u64, width: Width) -> Status {
    Status::Fault(MemoryFault {
        access,
        address,
        width,
    })
}

fn keep_argument(result: u64) -> PutsOutcome {
    let mut outcome = PutsOutcome::success(result);
    outcome.registers[4] = BASE;
    outcome
}

#[test]
fn normal_call_outputs_bytes_clobbers_flags_and_full_return_bits() {
    let program = one_call(CallTarget::Direct(PUTS), false);
    let mut outcome = PutsOutcome::success(0xabcdef0100000007);
    for index in 1..9 {
        outcome.registers[index] = 0xfeed0000 + index as u64;
    }
    outcome.registers[9..].copy_from_slice(&[1, 0, 1, 0, 1]);
    let registers: [u64; COUNT] = std::array::from_fn(|index| {
        if [RDI, RSP].contains(&index) {
            input()[index]
        } else {
            index as u64 + 70
        }
    });
    let report = program
        .run(
            &registers,
            BASE,
            &memory(),
            &[outcome.clone()],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(outcome.registers[0]));
    assert_eq!(report.output, b"abc\n");
    assert_eq!(report.consumed, 1);
    assert_eq!(report.state.trace, [0, 1]);
    assert_eq!(report.state.instruction, Some(1));
    for (index, original) in registers.iter().enumerate() {
        let expected = VOLATILE_REGISTERS
            .iter()
            .position(|&register| register == index)
            .map_or(*original, |position| outcome.registers[position]);
        assert_eq!(report.state.registers[index], expected, "r{index}");
    }
    assert_eq!(&report.state.memory[16..24], &1_u64.to_le_bytes());
    assert_eq!(memory()[16..24], [0; 8]);
}

#[test]
fn scan_is_byte_oriented_and_stops_at_first_nul() {
    let report = one_call(CallTarget::Direct(PUTS), true)
        .run(
            &input(),
            BASE,
            &[0xff, 0xc0, 0, b'x'],
            &[PutsOutcome::success(1)],
            Limits {
                external_reads: 3,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(1));
    assert_eq!(report.output, [0xff, 0xc0, b'\n']);
}

#[test]
fn target_is_read_before_push_and_string_is_read_after_push() {
    let mut registers = input();
    registers[RDI] = BASE + 16;
    let mut ram = memory();
    ram[16..24].copy_from_slice(&PUTS.to_le_bytes());
    let instructions = vec![
        call(0x41, CallTarget::Memory(BASE + 16), false),
        core(0x42, vec![], Control::Return(Expr::Register(Reg(0)))),
    ];
    let program = Program::new(0x41, COUNT, instructions, PUTS).unwrap();
    let report = program
        .run(
            &registers,
            BASE,
            &ram,
            &[PutsOutcome::success(6)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(6));
    assert_eq!(report.output, b"B\n");
    assert_eq!(&report.state.memory[16..24], &0x42_u64.to_le_bytes());
    assert_eq!(report.state.registers[RSP], registers[RSP]);
}

#[test]
fn register_target_uses_rsp_before_stack_decrement() {
    let target = input()[RSP];
    let program = Program::new(
        0,
        COUNT,
        vec![
            call(0, CallTarget::Register(Reg(RSP)), false),
            core(1, vec![], Control::Return(Expr::Register(Reg(0)))),
        ],
        target,
    )
    .unwrap();
    let report = program
        .run(
            &input(),
            BASE,
            &memory(),
            &[PutsOutcome::success(8)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(8));
}

#[test]
fn target_read_fault_precedes_stack_mutation_and_all_call_limits() {
    let report = one_call(CallTarget::Memory(u64::MAX), false)
        .run(
            &input(),
            BASE,
            &memory(),
            &[],
            Limits {
                calls: 0,
                external_reads: 0,
                output_bytes: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, fault(AccessKind::Read, u64::MAX, Width::U64));
    assert_eq!(report.state.registers, input());
    assert_eq!(report.state.memory, memory());
    assert_eq!(report.state.trace, [0]);
    assert_eq!(report.consumed, 0);
}

#[test]
fn push_fault_changes_rsp_but_commits_no_partial_bytes() {
    let mut registers = input();
    registers[RSP] = BASE + 4;
    let report = one_call(CallTarget::Direct(77), false)
        .run(&registers, BASE, &memory(), &[], Limits::default())
        .unwrap();
    assert_eq!(
        report.status,
        fault(AccessKind::Write, BASE - 4, Width::U64)
    );
    assert_eq!(report.state.registers[RSP], BASE - 4);
    assert_eq!(report.state.memory, memory());
    assert!(report.output.is_empty());

    registers[RSP] = 4;
    let report = one_call(CallTarget::Direct(PUTS), false)
        .run(&registers, BASE, &memory(), &[], Limits::default())
        .unwrap();
    assert_eq!(report.state.registers[RSP], u64::MAX - 3);
    assert_eq!(
        report.status,
        fault(AccessKind::Write, u64::MAX - 3, Width::U64)
    );
}

#[test]
fn unknown_target_is_dispatched_after_normal_push_before_scan() {
    let mut registers = input();
    registers[RDI] = u64::MAX;
    let report = one_call(CallTarget::Direct(77), false)
        .run(
            &registers,
            BASE,
            &memory(),
            &[],
            Limits {
                calls: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::UnknownTarget(77));
    assert_eq!(report.state.registers[RSP], BASE + 16);
    assert_eq!(&report.state.memory[16..24], &1_u64.to_le_bytes());
    assert_eq!(report.consumed, 0);
}

#[test]
fn scan_fault_retains_push_without_any_stdout_or_outcome_consumption() {
    let mut registers = input();
    registers[RDI] = BASE + 31;
    let mut ram = memory();
    ram[31] = b'x';
    let report = one_call(CallTarget::Direct(PUTS), false)
        .run(
            &registers,
            BASE,
            &ram,
            &[PutsOutcome::success(0)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, fault(AccessKind::Read, BASE + 32, Width::U8));
    assert!(report.output.is_empty());
    assert_eq!(report.consumed, 0);
    assert_eq!(report.state.registers[RSP], BASE + 16);
    assert_eq!(&report.state.memory[16..24], &1_u64.to_le_bytes());
}

#[test]
fn tail_call_does_not_push_and_callee_return_pops_rsp() {
    let mut registers = input();
    registers[RSP] = BASE;
    let report = one_call(CallTarget::Direct(PUTS), true)
        .run(
            &registers,
            BASE,
            &memory(),
            &[PutsOutcome::success(123)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(123));
    assert_eq!(report.state.registers[RSP], BASE + 8);
    assert_eq!(report.state.memory, memory());
    assert_eq!(report.state.trace, [0]);
    registers[RSP] = u64::MAX - 3;
    let report = one_call(CallTarget::Direct(PUTS), true)
        .run(
            &registers,
            BASE,
            &memory(),
            &[PutsOutcome::success(0)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.state.registers[RSP], 4);
}

#[test]
fn missing_and_invalid_outcomes_are_unconsumed_and_keep_prior_output() {
    let program = program(vec![
        call(0, CallTarget::Direct(PUTS), false),
        call(1, CallTarget::Direct(PUTS), true),
    ]);
    let mut bad_flags = PutsOutcome::success(0);
    bad_flags.registers[13] = 2;
    let bad_prefix = PutsOutcome {
        output: Output::Prefix(5),
        ..PutsOutcome::success(u64::MAX)
    };
    let incomplete_success = PutsOutcome {
        output: Output::Prefix(3),
        ..PutsOutcome::success(0)
    };
    for second in [
        None,
        Some(bad_flags),
        Some(bad_prefix),
        Some(incomplete_success),
    ] {
        let expected = if second.is_some() {
            Status::InvalidOutcome
        } else {
            Status::EnvironmentExhausted
        };
        let mut tape = vec![keep_argument(9)];
        tape.extend(second);
        let report = program
            .run(&input(), BASE, &memory(), &tape, Limits::default())
            .unwrap();
        assert_eq!(report.status, expected);
        assert_eq!(report.output, b"abc\n");
        assert_eq!(report.consumed, 1);
        assert_eq!(report.state.registers[RAX], 9);
        assert_eq!(report.state.registers[RSP], input()[RSP]);
        assert_eq!(report.state.trace, [0, 1]);
    }
}

#[test]
fn negative_low32_return_allows_every_output_prefix_and_preserves_upper_bits() {
    for result in [u64::MAX, 0x1234567880000000, 0x00000000ffffffff] {
        for written in 0..=4 {
            let outcome = PutsOutcome {
                registers: [result, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                output: Output::Prefix(written),
            };
            let report = one_call(CallTarget::Direct(PUTS), true)
                .run(&input(), BASE, &memory(), &[outcome], Limits::default())
                .unwrap();
            assert_eq!(report.status, Status::Returned(result));
            assert_eq!(report.output, b"abc\n"[..written]);
            assert_eq!(report.consumed, 1);
        }
    }
    for result in [0, 7, 0xffffffff00000000] {
        let outcome = PutsOutcome {
            output: Output::Prefix(0),
            ..PutsOutcome::success(result)
        };
        let report = one_call(CallTarget::Direct(PUTS), true)
            .run(&input(), BASE, &memory(), &[outcome], Limits::default())
            .unwrap();
        assert_eq!(report.status, Status::InvalidOutcome);
    }
}

#[test]
fn empty_string_still_reads_nul_and_emits_one_newline() {
    let report = one_call(CallTarget::Direct(PUTS), true)
        .run(
            &input(),
            BASE,
            &[0],
            &[PutsOutcome::success(0)],
            Limits {
                external_reads: 1,
                output_bytes: 1,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(0));
    assert_eq!(report.output, b"\n");
}

#[test]
fn instruction_budget_charges_call_before_any_target_read_or_mutation() {
    let report = one_call(CallTarget::Memory(u64::MAX), false)
        .run(
            &input(),
            BASE,
            &memory(),
            &[],
            Limits {
                instructions: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Suspended(Suspend::Instructions));
    assert!(report.state.trace.is_empty());
    assert_eq!(report.state.instruction, Some(0));
    assert_eq!(report.state.registers, input());
    assert_eq!(report.state.memory, memory());

    let report = one_call(CallTarget::Direct(PUTS), false)
        .run(
            &input(),
            BASE,
            &memory(),
            &[PutsOutcome::success(8)],
            Limits {
                instructions: 1,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Suspended(Suspend::Instructions));
    assert_eq!(report.state.trace, [0]);
    assert_eq!(report.state.instruction, Some(1));
    assert_eq!(report.output, b"abc\n");
    assert_eq!(report.consumed, 1);
    assert_eq!(report.state.registers[RSP], input()[RSP]);
}

#[test]
fn read_budget_includes_terminator_and_precedes_outcome_lookup() {
    for reads in 0..=4 {
        let report = one_call(CallTarget::Direct(PUTS), true)
            .run(
                &input(),
                BASE,
                &memory(),
                &[],
                Limits {
                    external_reads: reads,
                    ..Limits::default()
                },
            )
            .unwrap();
        assert_eq!(
            report.status,
            if reads < 4 {
                Status::Suspended(Suspend::Reads)
            } else {
                Status::EnvironmentExhausted
            }
        );
        assert!(report.output.is_empty());
        assert_eq!(report.consumed, 0);
    }
    let report = one_call(CallTarget::Memory(BASE + 8), true)
        .run(
            &input(),
            BASE,
            &memory(),
            &[],
            Limits {
                external_reads: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::UnknownTarget(0));
}

#[test]
fn call_budget_precedes_scan_and_retains_prior_output() {
    let mut registers = input();
    registers[RDI] = u64::MAX;
    let report = one_call(CallTarget::Direct(PUTS), false)
        .run(
            &registers,
            BASE,
            &memory(),
            &[],
            Limits {
                calls: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Suspended(Suspend::Calls));
    assert_eq!(report.state.registers[RSP], BASE + 16);
    assert_eq!(&report.state.memory[16..24], &1_u64.to_le_bytes());

    let program = program(vec![
        call(0, CallTarget::Direct(PUTS), false),
        call(1, CallTarget::Direct(PUTS), true),
    ]);
    let report = program
        .run(
            &input(),
            BASE,
            &memory(),
            &[keep_argument(9)],
            Limits {
                calls: 1,
                external_reads: 4,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Suspended(Suspend::Calls));
    assert_eq!(report.output, b"abc\n");
    assert_eq!(report.consumed, 1);
}

#[test]
fn output_budget_is_checked_after_validating_outcome_and_commits_atomically() {
    for capacity in 0..=4 {
        let report = one_call(CallTarget::Direct(PUTS), false)
            .run(
                &input(),
                BASE,
                &memory(),
                &[PutsOutcome::success(3)],
                Limits {
                    output_bytes: capacity,
                    ..Limits::default()
                },
            )
            .unwrap();
        if capacity < 4 {
            assert_eq!(report.status, Status::Suspended(Suspend::Output));
            assert_eq!(report.state.registers[RSP], BASE + 16);
            assert!(report.output.is_empty());
            assert_eq!(report.consumed, 0);
        } else {
            assert_eq!(report.status, Status::Returned(3));
            assert_eq!(report.output, b"abc\n");
        }
    }
    let invalid = PutsOutcome {
        output: Output::Prefix(1),
        ..PutsOutcome::success(0)
    };
    let report = one_call(CallTarget::Direct(PUTS), true)
        .run(
            &input(),
            BASE,
            &memory(),
            &[invalid],
            Limits {
                output_bytes: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::InvalidOutcome);

    let program = program(vec![
        call(0, CallTarget::Direct(PUTS), false),
        call(1, CallTarget::Direct(PUTS), true),
    ]);
    let report = program
        .run(
            &input(),
            BASE,
            &memory(),
            &[keep_argument(9), keep_argument(10)],
            Limits {
                output_bytes: 7,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Suspended(Suspend::Output));
    assert_eq!(report.output, b"abc\n");
    assert_eq!(report.consumed, 1);
    assert_eq!(report.state.registers[RAX], 9);
}

#[test]
fn zero_output_failure_can_commit_with_zero_output_budget() {
    let outcome = PutsOutcome {
        output: Output::Prefix(0),
        ..PutsOutcome::success(u64::MAX)
    };
    let report = one_call(CallTarget::Direct(PUTS), true)
        .run(
            &input(),
            BASE,
            &memory(),
            &[outcome],
            Limits {
                output_bytes: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(u64::MAX));
    assert_eq!(report.consumed, 1);
    assert!(report.output.is_empty());
}

fn parity(instructions: Vec<IrInstruction>, ram: &[u8], budget: usize) {
    let original = nirvana::ir::Program::new(0, COUNT, instructions.clone()).unwrap();
    let effects = program(instructions.into_iter().map(Instruction::Core).collect());
    let original = original
        .run_with_memory(&input(), BASE, ram, budget)
        .unwrap();
    let report = effects
        .run(
            &input(),
            BASE,
            ram,
            &[],
            Limits {
                instructions: budget,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.state, original.state);
    assert_eq!(
        report.status,
        match original.status {
            RunStatus::Returned(value) => Status::Returned(value),
            RunStatus::Fault(fault) => Status::Fault(fault),
            RunStatus::Suspended => Status::Suspended(Suspend::Instructions),
        }
    );
    assert!(report.output.is_empty());
    assert_eq!(report.consumed, 0);
}

#[test]
fn core_execution_matches_existing_machine_for_lazy_loads_ordered_stores_and_faults() {
    let instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: vec![
            Assignment {
                destination: Place::Memory {
                    address: Expr::Const(BASE + 1),
                    width: Width::U16,
                },
                value: Expr::Const(0x123456),
            },
            Assignment {
                destination: Reg(0).into(),
                value: Expr::select(
                    Expr::Const(1),
                    Expr::load(Expr::Const(BASE), Width::U32),
                    Expr::load(Expr::Const(u64::MAX), Width::U64),
                ),
            },
            Assignment {
                destination: Reg(1).into(),
                value: Expr::binary(BinaryOp::UMulHigh, Expr::Const(u64::MAX), Expr::Const(2)),
            },
        ],
        control: Control::Return(Expr::binary(
            BinaryOp::Add,
            Expr::Register(Reg(0)),
            Expr::Register(Reg(1)),
        )),
    }];
    for budget in 0..=2 {
        parity(instructions.clone(), &memory(), budget);
    }

    let mut faults = instructions;
    faults[0].assignments.push(Assignment {
        destination: Place::Memory {
            address: Expr::Const(BASE + 31),
            width: Width::U64,
        },
        value: Expr::load(Expr::Const(0), Width::U64),
    });
    parity(faults.clone(), &memory(), 2);
    faults[0].assignments.last_mut().unwrap().destination = Place::Memory {
        address: Expr::Const(BASE + 8),
        width: Width::U64,
    };
    parity(faults, &memory(), 2);
}

#[test]
fn core_loop_suspends_with_exact_trace_instead_of_claiming_completion() {
    let instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: vec![],
        control: Control::Jump(0),
    }];
    for budget in 0..=5 {
        parity(instructions.clone(), &[], budget);
    }
    let program = program(vec![
        call(0, CallTarget::Direct(PUTS), false),
        core(1, vec![], Control::Jump(0)),
    ]);
    let report = program
        .run(
            &input(),
            BASE,
            &memory(),
            &[keep_argument(7), keep_argument(8)],
            Limits {
                instructions: 4,
                ..Limits::default()
            },
        )
        .unwrap();
    assert_eq!(report.status, Status::Suspended(Suspend::Instructions));
    assert_eq!(report.state.trace, [0, 1, 0, 1]);
    assert_eq!(report.output, b"abc\nabc\n");
    assert_eq!(report.consumed, 2);
}

#[test]
fn core_branch_condition_faults_even_when_successors_match() {
    let instructions = vec![
        IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Branch {
                condition: Expr::load(Expr::Const(1), Width::U8),
                target: 1,
            },
        },
        IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(4)),
        },
    ];
    parity(instructions, &memory(), 2);
}

#[test]
fn bad_input_register_count_is_an_invocation_error() {
    assert_eq!(
        one_call(CallTarget::Direct(PUTS), true).run(&[], 0, &[], &[], Limits::default()),
        Err(ExecutionError::RegisterCount {
            expected: COUNT,
            actual: 0
        })
    );
}

#[test]
fn constructor_validates_registers_targets_layout_and_control() {
    for count in [0, 20, 4097] {
        assert!(matches!(
            Program::new(
                0,
                count,
                vec![call(0, CallTarget::Direct(PUTS), true)],
                PUTS
            ),
            Err(BuildError::RegisterCount { .. })
        ));
    }
    for count in [21, 4096] {
        assert_eq!(
            Program::new(
                0,
                count,
                vec![call(0, CallTarget::Direct(PUTS), true)],
                PUTS
            )
            .unwrap()
            .register_count(),
            count
        );
    }
    assert!(matches!(
        Program::new(
            0,
            21,
            vec![call(0, CallTarget::Register(Reg(21)), true)],
            PUTS
        ),
        Err(BuildError::Program(
            nirvana::ir::ProgramError::InvalidRegister { .. }
        ))
    ));
    for bad in [
        vec![core(0, vec![], Control::Return(Expr::Register(Reg(COUNT))))],
        vec![core(0, vec![], Control::Jump(3))],
        vec![call(0, CallTarget::Direct(PUTS), false)],
        vec![
            call(0, CallTarget::Direct(PUTS), true),
            call(0, CallTarget::Direct(PUTS), true),
        ],
        vec![Instruction::Call(CallInstruction {
            address: 0,
            size: 0,
            target: CallTarget::Direct(PUTS),
            tail: true,
        })],
        vec![Instruction::Call(CallInstruction {
            address: u64::MAX,
            size: 1,
            target: CallTarget::Direct(PUTS),
            tail: true,
        })],
    ] {
        assert!(Program::new(0, COUNT, bad, PUTS).is_err());
    }
}

#[test]
fn constructor_bounds_depth_before_clone_or_recursive_drop() {
    fn nested(depth: usize) -> Expr {
        let mut expression = Expr::Const(1);
        for _ in 1..depth {
            expression = Expr::load(expression, Width::U8);
        }
        expression
    }
    assert!(
        Program::new(
            0,
            COUNT,
            vec![core(0, vec![], Control::Return(nested(128)))],
            PUTS
        )
        .is_ok()
    );
    assert!(matches!(
        Program::new(
            0,
            COUNT,
            vec![core(0, vec![], Control::Return(nested(129)))],
            PUTS
        ),
        Err(BuildError::DepthLimit { maximum: 128 })
    ));
    // A recursive clone or destructor on this input would overflow the test thread.
    assert!(matches!(
        Program::new(
            0,
            COUNT,
            vec![core(0, vec![], Control::Return(nested(100_000)))],
            PUTS
        ),
        Err(BuildError::DepthLimit { .. })
    ));
}

#[test]
fn constructor_bounds_instruction_and_total_syntax_counts() {
    for count in [16_384, 16_385] {
        let mut instructions: Vec<_> = (0..count)
            .map(|address| core(address, vec![], Control::Next))
            .collect();
        if let Instruction::Core(last) = instructions.last_mut().unwrap() {
            last.control = Control::Return(Expr::Const(0));
        }
        let result = Program::new(0, COUNT, instructions, PUTS);
        if count == 16_384 {
            assert!(result.is_ok());
        } else {
            assert!(matches!(result, Err(BuildError::InstructionLimit { .. })));
        }
    }
    for assignments in [32_767, 32_768] {
        let assignments = vec![
            Assignment {
                destination: Reg(0).into(),
                value: Expr::Const(0)
            };
            assignments
        ];
        let count = assignments.len();
        let result = Program::new(
            0,
            COUNT,
            vec![core(0, assignments, Control::Return(Expr::Const(0)))],
            PUTS,
        );
        if count == 32_767 {
            assert!(result.is_ok());
        } else {
            assert!(matches!(
                result,
                Err(BuildError::NodeLimit { maximum: 65_536 })
            ));
        }
    }
}

#[test]
fn program_sorts_instructions_and_exposes_cfg_without_executable_call_skeleton() {
    let program = Program::new(
        0,
        COUNT,
        vec![
            core(1, vec![], Control::Return(Expr::Const(1))),
            call(0, CallTarget::Direct(PUTS), false),
        ],
        PUTS,
    )
    .unwrap();
    assert_eq!(program.entry(), 0);
    assert_eq!(program.puts_address(), PUTS);
    assert!(matches!(program.instructions()[0], Instruction::Call(_)));
    assert_eq!(program.cfg().instructions().len(), 2);
    assert_eq!(
        program.cfg().instructions()[0].flow,
        nirvana::cfg::Flow::Next
    );
    let tail = one_call(CallTarget::Direct(PUTS), true);
    assert_eq!(
        tail.cfg().instructions()[0].flow,
        nirvana::cfg::Flow::Return
    );
}
