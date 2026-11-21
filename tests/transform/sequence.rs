//! Replay plans through an independent lowering into the executable IR. The
//! source remains one instruction; plan steps become separate instructions and
//! explicit CFG branches. Compare faults and guest partial state, ignoring only
//! synthetic temporaries and synthetic instruction addresses.

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunReport, RunStatus, Width,
};
use nirvana::sequence::{Evaluation, MAX_EXPRESSION_DEPTH, SequenceError, SequencedExpr, sequence};

const BASE: u64 = 0x1000;

fn binary(operator: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(operator, left, right)
}

fn load(address: u64, width: Width) -> Expr {
    Expr::load(Expr::Const(address), width)
}

fn assignment(destination: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(destination).into(),
        value,
    }
}

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

fn prefix(base: u64, memory_len: usize) -> Vec<Assignment> {
    vec![
        assignment(0, Expr::Const(0xfeed)),
        assignment(2, Expr::Const(0x42)),
        Assignment {
            destination: Place::Memory {
                address: Expr::Const(base + memory_len as u64 - 1),
                width: Width::U8,
            },
            value: Expr::Const(0x99),
        },
    ]
}

fn has_load(expression: &Expr) -> bool {
    match expression {
        Expr::Unary(_, value) => has_load(value),
        Expr::Load { .. } => true,
        Expr::Const(_) | Expr::Register(_) => false,
        Expr::Binary(_, left, right) => has_load(left) || has_load(right),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => has_load(condition) || has_load(taken) || has_load(not_taken),
    }
}

fn check_steps(steps: &[Evaluation], first: usize, end: usize) {
    for step in steps {
        match step {
            Evaluation::Assign { destination, value } => {
                assert!((first..end).contains(&destination.0));
                assert!(!has_load(value));
            }
            Evaluation::Load {
                destination,
                address,
                ..
            } => {
                assert!((first..end).contains(&destination.0));
                assert!(!has_load(address));
            }
            Evaluation::If {
                condition,
                taken,
                not_taken,
            } => {
                assert!(!has_load(condition));
                check_steps(taken, first, end);
                check_steps(not_taken, first, end);
            }
        }
    }
}

struct Lowering {
    next_address: u64,
    instructions: Vec<IrInstruction>,
}

impl Lowering {
    fn address(&mut self) -> u64 {
        let address = self.next_address;
        self.next_address += 1;
        address
    }

    fn steps(&mut self, steps: &[Evaluation], mut continuation: u64) -> u64 {
        for step in steps.iter().rev() {
            continuation = match step {
                Evaluation::Assign { destination, value } => {
                    let address = self.address();
                    self.instructions.push(instruction(
                        address,
                        vec![assignment(destination.0, value.clone())],
                        Control::Jump(continuation),
                    ));
                    address
                }
                Evaluation::Load {
                    destination,
                    address,
                    width,
                    // Original-address metadata is deliberately never replayed.
                    original_address: _,
                } => {
                    let value = Expr::load(address.clone(), *width);
                    let address = self.address();
                    self.instructions.push(instruction(
                        address,
                        vec![assignment(destination.0, value)],
                        Control::Jump(continuation),
                    ));
                    address
                }
                Evaluation::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let taken = self.steps(taken, continuation);
                    let not_taken = self.steps(not_taken, continuation);
                    let address = self.address();
                    let fallthrough = self.address();
                    assert_eq!(fallthrough, address + 1);
                    self.instructions.push(instruction(
                        address,
                        vec![],
                        Control::Branch {
                            condition: condition.clone(),
                            target: taken,
                        },
                    ));
                    self.instructions.push(instruction(
                        fallthrough,
                        vec![],
                        Control::Jump(not_taken),
                    ));
                    address
                }
            };
        }
        continuation
    }
}

fn replay(expression: &Expr, input: &[u64; 4], memory: &[u8]) -> (RunReport, SequencedExpr) {
    let mut assignments = prefix(BASE, memory.len());
    assignments.push(assignment(0, expression.clone()));
    let original = Program::new(
        0,
        input.len(),
        vec![instruction(
            0,
            assignments,
            Control::Return(Expr::Register(Reg(0))),
        )],
    )
    .unwrap()
    .run_with_memory(input, BASE, memory, 1)
    .unwrap();

    let plan = sequence(expression, input.len()).unwrap();
    check_steps(&plan.steps, input.len(), plan.next_register);
    assert!(!has_load(&plan.value));
    let mut lowering = Lowering {
        next_address: 2,
        instructions: vec![instruction(
            1,
            vec![assignment(0, plan.value.clone())],
            Control::Return(Expr::Register(Reg(0))),
        )],
    };
    let entry = lowering.steps(&plan.steps, 1);
    lowering.instructions.push(instruction(
        0,
        prefix(BASE, memory.len()),
        Control::Jump(entry),
    ));
    let mut registers = input.to_vec();
    registers.resize(plan.next_register, 0);
    let replayed = Program::new(0, plan.next_register, lowering.instructions)
        .unwrap()
        .run_with_memory(&registers, BASE, memory, 10_000)
        .unwrap();
    assert_eq!(original.status, replayed.status, "source: {expression:?}");
    assert_eq!(original.state.memory_base, replayed.state.memory_base);
    assert_eq!(original.state.memory, replayed.state.memory);
    assert_eq!(
        original.state.registers,
        replayed.state.registers[..input.len()],
        "source: {expression:?}"
    );
    (original, plan)
}

fn read_fault(address: u64, width: Width) -> RunStatus {
    RunStatus::Fault(MemoryFault {
        access: AccessKind::Read,
        address,
        width,
    })
}

#[test]
fn pure_arithmetic_and_selects_remain_compact() {
    let expression = Expr::select(
        Expr::Register(Reg(3)),
        binary(BinaryOp::Add, Expr::Register(Reg(1)), Expr::Const(9)),
        binary(BinaryOp::Mul, Expr::Register(Reg(2)), Expr::Const(0)),
    );
    for condition in [0, 1, u64::MAX] {
        let (_, plan) = replay(&expression, &[7, BASE, 2, condition], &[0; 32]);
        assert!(plan.steps.is_empty());
        assert_eq!(plan.value, expression);
        assert_eq!(plan.next_register, 4);
    }
}

#[test]
fn two_invalid_loads_fault_on_the_left_operand_before_the_right() {
    for operator in [BinaryOp::Add, BinaryOp::Mul, BinaryOp::UMulHigh] {
        let expression = binary(operator, load(12, Width::U16), load(24, Width::U64));
        let (report, plan) = replay(&expression, &[7, BASE, 2, 0], &[0; 32]);
        assert_eq!(report.status, read_fault(12, Width::U16));
        assert_eq!(report.state.registers, [0xfeed, BASE, 0x42, 0]);
        assert_eq!(report.state.memory[31], 0x99);
        assert_eq!(plan.steps.len(), 2);
        assert_eq!(plan.next_register, 6);
    }
}

#[test]
fn successful_prefix_loads_do_not_commit_a_faulting_expression_destination() {
    let expression = binary(
        BinaryOp::Xor,
        load(BASE, Width::U32),
        binary(BinaryOp::Add, load(12, Width::U16), load(24, Width::U8)),
    );
    let (report, _) = replay(&expression, &[7, BASE, 2, 0], &[0xab; 32]);
    assert_eq!(report.status, read_fault(12, Width::U16));
    assert_eq!(report.state.registers[0], 0xfeed);
    assert_eq!(report.state.memory[..31], [0xab; 31]);
}

#[test]
fn load_addresses_are_sequenced_before_outer_loads_and_keep_original_metadata() {
    let address = binary(
        BinaryOp::Add,
        Expr::load(Expr::Register(Reg(1)), Width::U64),
        Expr::Const(1),
    );
    let expression = Expr::load(address.clone(), Width::U16);
    let mut memory = [0u8; 32];
    memory[..8].copy_from_slice(&(BASE + 15).to_le_bytes());
    memory[16..18].copy_from_slice(&0x1234u16.to_le_bytes());
    let (report, plan) = replay(&expression, &[7, BASE, 2, 0], &memory);
    assert_eq!(report.status, RunStatus::Returned(0x1234));
    assert!(matches!(
        plan.steps.last(),
        Some(Evaluation::Load { original_address, address: pure, .. })
            if *original_address == address && has_load(original_address) && !has_load(pure)
    ));
    let (report, _) = replay(&expression, &[7, 1, 2, 0], &memory);
    assert_eq!(report.status, read_fault(1, Width::U64));
    memory[..8].copy_from_slice(&0u64.to_le_bytes());
    let (report, _) = replay(&expression, &[7, BASE, 2, 0], &memory);
    assert_eq!(report.status, read_fault(1, Width::U16));
}

#[test]
fn zero_stride_product_keeps_a_load_that_still_faults() {
    let expression = binary(
        BinaryOp::Add,
        Expr::Register(Reg(1)),
        binary(BinaryOp::Mul, load(9, Width::U8), Expr::Const(0)),
    );
    let (report, plan) = replay(&expression, &[7, BASE, 2, 0], &[0; 32]);
    assert_eq!(report.status, read_fault(9, Width::U8));
    assert!(matches!(plan.steps.as_slice(), [Evaluation::Load { .. }]));
}

#[test]
fn selects_evaluate_condition_first_and_only_the_selected_arm() {
    let expression = Expr::select(
        Expr::Register(Reg(3)),
        load(BASE, Width::U8),
        load(9, Width::U32),
    );
    for condition in [0, 1, 5, u64::MAX] {
        let (report, plan) = replay(&expression, &[7, BASE, 2, condition], &[0xab; 32]);
        assert_eq!(
            report.status,
            if condition == 0 {
                read_fault(9, Width::U32)
            } else {
                RunStatus::Returned(0xab)
            }
        );
        let [
            Evaluation::If {
                taken, not_taken, ..
            },
        ] = plan.steps.as_slice()
        else {
            panic!("expected a branch plan: {plan:?}");
        };
        let Expr::Register(result) = plan.value else {
            panic!("expected shared result register");
        };
        for arm in [taken, not_taken] {
            assert!(matches!(
                arm.last(),
                Some(Evaluation::Assign { destination, .. }) if *destination == result
            ));
        }
    }
    let expression = Expr::select(
        load(13, Width::U16),
        load(14, Width::U32),
        load(15, Width::U64),
    );
    let (report, _) = replay(&expression, &[7, BASE, 2, 0], &[0; 32]);
    assert_eq!(report.status, read_fault(13, Width::U16));
}

#[test]
fn a_condition_load_with_pure_arms_needs_no_branch_steps() {
    let expression = Expr::select(load(BASE, Width::U8), Expr::Const(7), Expr::Const(11));
    for byte in [0, 1, 255] {
        let (report, plan) = replay(&expression, &[7, BASE, 2, 0], &[byte; 32]);
        assert_eq!(
            report.status,
            RunStatus::Returned(if byte == 0 { 11 } else { 7 })
        );
        assert!(matches!(plan.steps.as_slice(), [Evaluation::Load { .. }]));
        assert!(matches!(plan.value, Expr::Select { .. }));
    }
}

#[test]
fn nested_selects_keep_unselected_faults_out_of_nested_addresses() {
    let expression = binary(
        BinaryOp::Add,
        load(BASE + 8, Width::U32),
        Expr::select(
            load(BASE, Width::U8),
            Expr::select(
                Expr::Register(Reg(3)),
                Expr::load(
                    Expr::select(Expr::Const(0), load(1, Width::U64), Expr::Const(BASE + 16)),
                    Width::U16,
                ),
                load(2, Width::U8),
            ),
            Expr::Const(23),
        ),
    );
    for byte in [0, 1] {
        for condition in [0, 1, u64::MAX] {
            replay(&expression, &[7, BASE, 2, condition], &[byte; 32]);
        }
    }
}

#[test]
fn all_arithmetic_operators_keep_their_unsigned_wrapping_semantics() {
    for operator in [
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::Eq,
        BinaryOp::Ne,
        BinaryOp::Ult,
        BinaryOp::Ule,
        BinaryOp::UMulHigh,
    ] {
        for right in [0u64, 1, 63, 64, 127, u64::MAX] {
            let expression = binary(operator, load(BASE, Width::U64), Expr::Const(right));
            replay(&expression, &[7, BASE, 2, 0], &[0xff; 32]);
        }
    }
}

fn generated(seed: &mut u64, depth: usize) -> Expr {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    let choice = *seed >> 32;
    if depth == 0 {
        return if choice & 1 == 0 {
            Expr::Const(choice)
        } else {
            Expr::Register(Reg((choice as usize) % 4))
        };
    }
    match choice % 6 {
        0 => Expr::load(generated(seed, depth - 1), Width::U8),
        1 => Expr::select(
            generated(seed, depth - 1),
            generated(seed, depth - 1),
            generated(seed, depth - 1),
        ),
        2 => load(BASE + choice % 36, Width::U64),
        value => binary(
            match value {
                3 => BinaryOp::Add,
                4 => BinaryOp::Mul,
                _ => BinaryOp::Xor,
            },
            generated(seed, depth - 1),
            generated(seed, depth - 1),
        ),
    }
}

#[test]
fn generated_mixed_trees_replay_with_exact_faults_and_partial_guest_state() {
    for mut seed in 0..256 {
        let expression = generated(&mut seed, 4);
        for condition in [0, 1, u64::MAX] {
            replay(&expression, &[7, BASE, 2, condition], &[0x5a; 32]);
        }
    }
}

#[test]
fn input_registers_cannot_overlap_the_temporary_range_even_in_unused_arms() {
    for expression in [
        Expr::Register(Reg(4)),
        Expr::load(Expr::Register(Reg(4)), Width::U8),
        Expr::select(Expr::Const(0), Expr::Register(Reg(4)), Expr::Const(9)),
    ] {
        assert_eq!(
            sequence(&expression, 4),
            Err(SequenceError::RegisterCollision {
                register: Reg(4),
                first_temporary: 4,
            })
        );
    }
    assert_eq!(sequence(&Expr::Const(7), 0).unwrap().next_register, 0);
}

#[test]
fn temporary_allocation_reports_overflow_without_wrapping_or_panicking() {
    assert_eq!(
        sequence(&load(BASE, Width::U8), usize::MAX),
        Err(SequenceError::RegisterOverflow)
    );
    assert_eq!(
        sequence(&load(BASE, Width::U8), usize::MAX - 1)
            .unwrap()
            .next_register,
        usize::MAX
    );
    let expression = binary(BinaryOp::Add, load(BASE, Width::U8), load(BASE, Width::U8));
    assert_eq!(
        sequence(&expression, usize::MAX - 1),
        Err(SequenceError::RegisterOverflow)
    );
    assert_eq!(
        sequence(&Expr::Const(7), usize::MAX).unwrap().next_register,
        usize::MAX
    );
}

#[test]
fn returned_register_boundary_keeps_separately_sequenced_plans_disjoint() {
    let first = sequence(&load(BASE, Width::U8), 4).unwrap();
    let second = sequence(
        &Expr::select(
            Expr::Register(Reg(3)),
            load(BASE + 1, Width::U8),
            first.value.clone(),
        ),
        first.next_register,
    )
    .unwrap();
    check_steps(&second.steps, first.next_register, second.next_register);
    assert_eq!(first.next_register, 5);
    assert_eq!(second.next_register, 7);
}

fn balanced(depth: usize) -> Expr {
    if depth == 0 {
        Expr::Const(1)
    } else {
        binary(BinaryOp::Add, balanced(depth - 1), balanced(depth - 1))
    }
}

#[test]
fn depth_node_and_metadata_budgets_fail_with_errors() {
    let mut deep = Expr::Const(0);
    for _ in 1..MAX_EXPRESSION_DEPTH {
        deep = Expr::load(deep, Width::U8);
    }
    let boundary = sequence(&deep, 0).unwrap();
    assert_eq!(boundary.steps.len(), MAX_EXPRESSION_DEPTH - 1);
    deep = Expr::load(deep, Width::U8);
    assert_eq!(sequence(&deep, 0), Err(SequenceError::ExpressionTooDeep));
    assert_eq!(
        sequence(&balanced(16), 0),
        Err(SequenceError::ExpressionTooLarge)
    );
    let mut metadata = balanced(14);
    for _ in 0..9 {
        metadata = Expr::load(metadata, Width::U8);
    }
    assert_eq!(
        sequence(&metadata, 0),
        Err(SequenceError::AddressMetadataTooLarge)
    );
}
