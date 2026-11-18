use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::ssa::{Definition, PhiInput, RegisterValue, Site, SsaFunction, ValueId};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, a, b)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(entry: u64, registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(entry, registers, instructions).unwrap()
}
fn point(
    ssa: &SsaFunction,
    instruction: u64,
    assignment: Option<usize>,
) -> &nirvana::ssa::PointValues {
    ssa.point(Site {
        instruction,
        assignment,
    })
    .unwrap()
}
fn block(ssa: &SsaFunction, start: u64) -> &nirvana::ssa::SsaBlock {
    ssa.blocks.iter().find(|b| b.start == start).unwrap()
}
fn phi(ssa: &SsaFunction, start: u64, reg: usize) -> (ValueId, &[PhiInput]) {
    block(ssa, start)
        .phis
        .iter()
        .find_map(|id| match &ssa.values[id.0] {
            Definition::Phi {
                register, inputs, ..
            } if *register == Reg(reg) => Some((*id, inputs.as_slice())),
            _ => None,
        })
        .unwrap()
}
fn initial(ssa: &SsaFunction, reg: usize) -> ValueId {
    ValueId(
        ssa.values
            .iter()
            .position(|v| *v == Definition::Initial { register: Reg(reg) })
            .unwrap(),
    )
}

#[test]
fn diamond_uses_both_predecessor_definitions() {
    let source = program(
        0,
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 3,
                },
            ),
            ins(1, vec![set(1, c(11))], Control::Jump(4)),
            ins(3, vec![set(1, c(33))], Control::Jump(4)),
            ins(4, vec![], Control::Return(r(1))),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    let (join, inputs) = phi(&ssa, 4, 1);
    assert_eq!(
        inputs,
        &[
            PhiInput {
                predecessor: Some(1),
                value: point(&ssa, 1, Some(0)).definition.unwrap()
            },
            PhiInput {
                predecessor: Some(3),
                value: point(&ssa, 3, Some(0)).definition.unwrap()
            },
        ]
    );
    assert_eq!(
        point(&ssa, 4, None).reads,
        vec![RegisterValue {
            register: Reg(1),
            value: join
        }]
    );
    assert!(block(&ssa, 0).exit_values.is_empty());
    assert_eq!(ssa, SsaFunction::build(&source).unwrap());
}

#[test]
fn loop_carried_phi_is_filled_after_later_block_exit() {
    let source = program(
        0,
        2,
        vec![
            ins(0, vec![set(0, c(0))], Control::Jump(1)),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 3,
                },
            ),
            ins(2, vec![set(0, add(r(0), c(1)))], Control::Jump(1)),
            ins(3, vec![], Control::Return(r(0))),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    let (_, inputs) = phi(&ssa, 1, 0);
    assert_eq!(
        inputs,
        &[
            PhiInput {
                predecessor: Some(0),
                value: point(&ssa, 0, Some(0)).definition.unwrap()
            },
            PhiInput {
                predecessor: Some(2),
                value: point(&ssa, 2, Some(0)).definition.unwrap()
            },
        ]
    );
    let (body_entry, _) = phi(&ssa, 2, 0);
    assert_eq!(point(&ssa, 2, Some(0)).reads[0].value, body_entry);
}

#[test]
fn entry_backedge_preserves_initial_and_actual_predecessor() {
    let source = program(
        10,
        2,
        vec![
            ins(0, vec![set(0, c(99))], Control::Jump(10)),
            ins(
                10,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 20,
                },
            ),
            ins(11, vec![], Control::Return(r(0))),
            ins(20, vec![set(0, add(r(0), c(1)))], Control::Jump(10)),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    assert_eq!(
        ssa.blocks.iter().map(|b| b.start).collect::<Vec<_>>(),
        vec![10, 11, 20]
    );
    let (_, inputs) = phi(&ssa, 10, 0);
    assert_eq!(
        inputs,
        &[
            PhiInput {
                predecessor: None,
                value: initial(&ssa, 0)
            },
            PhiInput {
                predecessor: Some(20),
                value: point(&ssa, 20, Some(0)).definition.unwrap()
            },
        ]
    );
    assert!(
        !ssa.values
            .iter()
            .any(|v| matches!(v, Definition::Assignment { site, .. } if site.instruction == 0))
    );
}

#[test]
fn self_loop_exit_refers_to_its_post_assignment_value() {
    let source = program(
        0,
        1,
        vec![ins(0, vec![set(0, add(r(0), c(1)))], Control::Jump(0))],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    let (entry, inputs) = phi(&ssa, 0, 0);
    let assignment = point(&ssa, 0, Some(0));
    assert_eq!(assignment.reads[0].value, entry);
    assert_eq!(
        inputs,
        &[
            PhiInput {
                predecessor: None,
                value: initial(&ssa, 0)
            },
            PhiInput {
                predecessor: Some(0),
                value: assignment.definition.unwrap()
            },
        ]
    );
}

#[test]
fn repeated_writes_read_old_value_before_each_definition() {
    let source = program(
        0,
        2,
        vec![ins(
            0,
            vec![set(0, add(r(0), r(0))), set(0, r(0)), set(1, r(0))],
            Control::Return(r(1)),
        )],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    let (entry, _) = phi(&ssa, 0, 0);
    let a = point(&ssa, 0, Some(0));
    let b = point(&ssa, 0, Some(1));
    let d = point(&ssa, 0, Some(2));
    assert_eq!(
        a.reads.iter().map(|rv| rv.value).collect::<Vec<_>>(),
        vec![entry, entry]
    );
    assert_eq!(b.reads[0].value, a.definition.unwrap());
    assert_eq!(d.reads[0].value, b.definition.unwrap());
    assert_eq!(point(&ssa, 0, None).reads[0].value, d.definition.unwrap());
    assert_eq!(block(&ssa, 0).points.len(), 4);
    assert!(block(&ssa, 0).exit_values.is_empty());
}

#[test]
fn store_address_load_and_select_leaves_keep_source_order() {
    let source = program(
        0,
        6,
        vec![ins(
            0,
            vec![
                set(4, c(44)),
                Assignment {
                    destination: Place::Memory {
                        address: add(r(3), Expr::load(r(2), Width::U8)),
                        width: Width::U64,
                    },
                    value: Expr::select(r(1), add(r(4), r(4)), Expr::load(r(5), Width::U32)),
                },
                set(0, Expr::load(r(3), Width::U64)),
            ],
            Control::Return(r(0)),
        )],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    let stored = point(&ssa, 0, Some(1));
    assert_eq!(stored.definition, None);
    assert_eq!(
        stored
            .reads
            .iter()
            .map(|rv| rv.register.0)
            .collect::<Vec<_>>(),
        vec![3, 2, 1, 4, 4, 5]
    );
    assert_eq!(
        stored.reads[3].value,
        point(&ssa, 0, Some(0)).definition.unwrap()
    );
    assert_eq!(stored.reads[4].value, stored.reads[3].value);
    assert_eq!(point(&ssa, 0, Some(2)).reads[0].register, Reg(3));
}

#[test]
fn dead_assignments_and_both_select_arms_still_have_input_values() {
    let source = program(
        0,
        4,
        vec![
            ins(0, vec![], Control::Jump(1)),
            ins(
                1,
                vec![set(0, Expr::select(r(1), r(2), r(3)))],
                Control::Return(c(0)),
            ),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    assert_eq!(block(&ssa, 1).phis.len(), 3);
    assert_eq!(point(&ssa, 1, Some(0)).reads.len(), 3);
    assert_eq!(
        block(&ssa, 0)
            .exit_values
            .iter()
            .map(|rv| rv.register.0)
            .collect::<Vec<_>>(),
        vec![1, 2, 3]
    );
}

#[test]
fn duplicate_branch_edges_supply_one_phi_input() {
    let source = program(
        0,
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 1,
                },
            ),
            ins(1, vec![], Control::Return(r(0))),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    assert_eq!(phi(&ssa, 1, 0).1.len(), 1);
    assert_eq!(phi(&ssa, 1, 0).1[0].predecessor, Some(0));
}

#[test]
fn sparse_raw_register_count_only_allocates_active_values() {
    let source = program(
        0,
        4096,
        vec![ins(
            0,
            vec![set(4095, add(r(4095), c(1)))],
            Control::Return(r(4095)),
        )],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    assert_eq!(ssa.register_count, 4096);
    assert_eq!(ssa.values.len(), 3);
    assert_eq!(block(&ssa, 0).phis.len(), 1);
    assert!(ssa.values.iter().all(|v| match v {
        Definition::Initial { register }
        | Definition::Assignment { register, .. }
        | Definition::Phi { register, .. } => *register == Reg(4095),
    }));
}

#[test]
fn irreducible_two_entry_cycle_needs_no_topological_order() {
    let source = program(
        0,
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            ins(1, vec![set(0, add(r(0), c(1)))], Control::Jump(2)),
            ins(
                2,
                vec![set(0, add(r(0), c(2)))],
                Control::Branch {
                    condition: r(1),
                    target: 1,
                },
            ),
            ins(3, vec![], Control::Return(r(0))),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    assert_eq!(
        phi(&ssa, 1, 0)
            .1
            .iter()
            .map(|i| i.predecessor)
            .collect::<Vec<_>>(),
        vec![Some(0), Some(2)]
    );
    assert_eq!(
        phi(&ssa, 2, 0)
            .1
            .iter()
            .map(|i| i.predecessor)
            .collect::<Vec<_>>(),
        vec![Some(0), Some(1)]
    );
}

#[test]
fn constant_only_program_has_no_register_values() {
    let source = program(0, 0, vec![ins(0, vec![], Control::Return(c(7)))]);
    let ssa = SsaFunction::build(&source).unwrap();
    assert!(ssa.values.is_empty());
    assert_eq!(block(&ssa, 0).points.len(), 1);
    assert!(point(&ssa, 0, None).reads.is_empty());
}

#[test]
fn oversized_raw_register_space_declines() {
    let source = program(0, 4097, vec![ins(0, vec![], Control::Return(c(0)))]);
    assert!(SsaFunction::build(&source).is_none());
}

fn sum(registers: std::ops::Range<usize>) -> Expr {
    if registers.len() == 1 {
        return r(registers.start);
    }
    let mid = registers.start + registers.len() / 2;
    add(sum(registers.start..mid), sum(mid..registers.end))
}
#[test]
fn liveness_matrix_product_declines_before_allocation() {
    let mut instructions: Vec<_> = (0..512u64)
        .map(|a| ins(a, vec![], Control::Jump(a + 1)))
        .collect();
    instructions.push(ins(512, vec![], Control::Return(sum(0..512))));
    let source = program(0, 512, instructions);
    assert!(SsaFunction::build(&source).is_none());
}

#[test]
fn registers_used_only_by_unreachable_instructions_are_absent() {
    let source = program(
        10,
        4096,
        vec![
            ins(0, vec![set(4095, r(4094))], Control::Jump(10)),
            ins(10, vec![], Control::Return(r(0))),
        ],
    );
    let ssa = SsaFunction::build(&source).unwrap();
    assert_eq!(ssa.blocks.len(), 1);
    assert_eq!(ssa.values.len(), 2);
    assert_eq!(ssa.values[0], Definition::Initial { register: Reg(0) });
    assert_eq!(point(&ssa, 10, None).reads[0].value, phi(&ssa, 10, 0).0);
}

#[test]
fn too_many_phi_definitions_declines_with_bounded_liveness_state() {
    let mut instructions: Vec<_> = (0..257u64)
        .map(|a| ins(a, vec![], Control::Jump(a + 1)))
        .collect();
    instructions.push(ins(257, vec![], Control::Return(sum(0..256))));
    let source = program(0, 256, instructions);
    assert!(SsaFunction::build(&source).is_none());
}

#[test]
fn liveness_revisit_budget_declines_even_when_final_graph_would_fit() {
    // The worklist order opposes this cycle, so newly live registers advance
    // gradually. The complete SSA would have 62,049 values and 61,920 inputs,
    // below their limits, but repeatedly visiting the liveness state is capped.
    let instructions = (0..128u64)
        .map(|a| {
            let base = (a as usize % 120) * 4;
            ins(
                a,
                vec![set(
                    480,
                    add(add(r(base), r(base + 1)), add(r(base + 2), r(base + 3))),
                )],
                Control::Jump(if a == 0 { 127 } else { a - 1 }),
            )
        })
        .collect();
    let source = program(0, 481, instructions);
    assert!(SsaFunction::build(&source).is_none());
}
