//! Candidates are constructed here without invoking the SSA builder.
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::ssa::{
    self, Definition, PhiInput, PointValues, RegisterValue, Site, SsaBlock, SsaError, SsaFunction,
    ValueId,
};

fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn reg(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn rv(register: usize, value: usize) -> RegisterValue {
    RegisterValue {
        register: Reg(register),
        value: ValueId(value),
    }
}
fn site(instruction: u64, assignment: Option<usize>) -> Site {
    Site {
        instruction,
        assignment,
    }
}
fn point(
    instruction: u64,
    assignment: Option<usize>,
    definition: Option<usize>,
    reads: &[(usize, usize)],
) -> PointValues {
    PointValues {
        site: site(instruction, assignment),
        definition: definition.map(ValueId),
        reads: reads.iter().map(|&(r, v)| rv(r, v)).collect(),
    }
}
fn initial(register: usize) -> Definition {
    Definition::Initial {
        register: Reg(register),
    }
}
fn assignment(instruction: u64, index: usize, register: usize) -> Definition {
    Definition::Assignment {
        site: site(instruction, Some(index)),
        register: Reg(register),
    }
}
fn phi(block: u64, register: usize, inputs: &[(Option<u64>, usize)]) -> Definition {
    Definition::Phi {
        block,
        register: Reg(register),
        inputs: inputs
            .iter()
            .map(|&(predecessor, value)| PhiInput {
                predecessor,
                value: ValueId(value),
            })
            .collect(),
    }
}
fn block(
    start: u64,
    phis: &[usize],
    points: Vec<PointValues>,
    exits: &[(usize, usize)],
) -> SsaBlock {
    SsaBlock {
        start,
        phis: phis.iter().copied().map(ValueId).collect(),
        points,
        exit_values: exits.iter().map(|&(r, v)| rv(r, v)).collect(),
    }
}
fn diamond() -> (Program, SsaFunction) {
    let source = Program::new(
        0,
        3,
        vec![
            ins(
                0,
                vec![set(1, Expr::Const(3))],
                Control::Branch {
                    condition: reg(0),
                    target: 2,
                },
            ),
            ins(1, vec![set(2, reg(1))], Control::Jump(3)),
            ins(2, vec![set(2, Expr::Const(9))], Control::Jump(3)),
            ins(
                3,
                vec![],
                Control::Return(Expr::binary(BinaryOp::Add, reg(2), reg(1))),
            ),
        ],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 3,
        values: vec![
            initial(0),
            phi(0, 0, &[(None, 0)]),
            assignment(0, 0, 1),
            phi(1, 1, &[(Some(0), 2)]),
            assignment(1, 0, 2),
            phi(2, 1, &[(Some(0), 2)]),
            assignment(2, 0, 2),
            phi(3, 1, &[(Some(1), 3), (Some(2), 5)]),
            phi(3, 2, &[(Some(1), 4), (Some(2), 6)]),
        ],
        blocks: vec![
            block(
                0,
                &[1],
                vec![
                    point(0, Some(0), Some(2), &[]),
                    point(0, None, None, &[(0, 1)]),
                ],
                &[(1, 2)],
            ),
            block(
                1,
                &[3],
                vec![point(1, Some(0), Some(4), &[(1, 3)])],
                &[(1, 3), (2, 4)],
            ),
            block(
                2,
                &[5],
                vec![point(2, Some(0), Some(6), &[])],
                &[(1, 5), (2, 6)],
            ),
            block(
                3,
                &[7, 8],
                vec![point(3, None, None, &[(2, 8), (1, 7)])],
                &[],
            ),
        ],
    };
    (source, candidate)
}
fn entry_loop() -> (Program, SsaFunction) {
    let source = Program::new(
        0,
        2,
        vec![
            ins(
                0,
                vec![
                    set(0, Expr::binary(BinaryOp::Add, reg(0), Expr::Const(1))),
                    set(1, Expr::binary(BinaryOp::Add, reg(1), reg(0))),
                ],
                Control::Branch {
                    condition: reg(1),
                    target: 0,
                },
            ),
            ins(1, vec![], Control::Return(reg(0))),
        ],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 2,
        values: vec![
            initial(0),
            initial(1),
            phi(0, 0, &[(None, 0), (Some(0), 4)]),
            phi(0, 1, &[(None, 1), (Some(0), 5)]),
            assignment(0, 0, 0),
            assignment(0, 1, 1),
            phi(1, 0, &[(Some(0), 4)]),
        ],
        blocks: vec![
            block(
                0,
                &[2, 3],
                vec![
                    point(0, Some(0), Some(4), &[(0, 2)]),
                    point(0, Some(1), Some(5), &[(1, 3), (0, 4)]),
                    point(0, None, None, &[(1, 5)]),
                ],
                &[(0, 4), (1, 5)],
            ),
            block(1, &[6], vec![point(1, None, None, &[(0, 6)])], &[]),
        ],
    };
    (source, candidate)
}
fn inputs(candidate: &mut SsaFunction, index: usize) -> &mut Vec<PhiInput> {
    let Definition::Phi { inputs, .. } = &mut candidate.values[index] else {
        panic!("test phi")
    };
    inputs
}
fn reject(source: &Program, candidate: &SsaFunction) {
    assert!(
        std::panic::catch_unwind(|| ssa::validate(source, candidate))
            .expect("validator panicked")
            .is_err()
    );
}
#[test]
fn validates_manual_diamond_and_entry_self_loop() {
    for (source, candidate) in [diamond(), entry_loop()] {
        let evidence = ssa::validate(&source, &candidate).unwrap();
        assert_eq!(evidence.blocks, candidate.blocks.len());
        assert_eq!(evidence.definitions, candidate.values.len());
        assert_eq!(
            evidence.register_reads,
            candidate
                .blocks
                .iter()
                .flat_map(|b| &b.points)
                .map(|p| p.reads.len())
                .sum()
        );
    }
}
#[test]
fn identities_and_block_listing_need_no_canonical_numbering() {
    let (source, mut candidate) = diamond();
    let count = candidate.values.len();
    candidate.values.reverse();
    for node in &mut candidate.values {
        if let Definition::Phi { inputs, .. } = node {
            for input in inputs {
                input.value.0 = count - 1 - input.value.0;
            }
        }
    }
    for block in &mut candidate.blocks {
        block.phis.reverse();
        for phi in &mut block.phis {
            phi.0 = count - 1 - phi.0;
        }
        for point in &mut block.points {
            if let Some(value) = &mut point.definition {
                value.0 = count - 1 - value.0;
            }
            for read in &mut point.reads {
                read.value.0 = count - 1 - read.value.0;
            }
        }
        for exit in &mut block.exit_values {
            exit.value.0 = count - 1 - exit.value.0;
        }
    }
    candidate.blocks.reverse();
    ssa::validate(&source, &candidate).unwrap();
}
#[test]
fn rejects_missing_duplicate_and_wrong_predecessor_edges() {
    let (source, candidate) = diamond();
    let mut bad = candidate.clone();
    inputs(&mut bad, 8).pop();
    reject(&source, &bad);
    let mut bad = candidate.clone();
    inputs(&mut bad, 8)[1].predecessor = Some(1);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    inputs(&mut bad, 8)[1].predecessor = Some(0);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    inputs(&mut bad, 8)[1].value = ValueId(4);
    reject(&source, &bad);
    let mut bad = candidate;
    inputs(&mut bad, 8).push(PhiInput {
        predecessor: Some(2),
        value: ValueId(6),
    });
    reject(&source, &bad);
}
#[test]
fn rejects_missing_or_forged_virtual_entry_and_loop_edge_values() {
    let (source, candidate) = entry_loop();
    let mut bad = candidate.clone();
    inputs(&mut bad, 2).remove(0);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    inputs(&mut bad, 2)[0].value = ValueId(4);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    inputs(&mut bad, 2)[0].value = ValueId(1);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    inputs(&mut bad, 2)[1].value = ValueId(2);
    reject(&source, &bad);
    let mut bad = candidate;
    inputs(&mut bad, 2)[1].value = ValueId(5);
    reject(&source, &bad);
}
#[test]
fn rejects_future_wrong_register_and_swapped_ordered_reads() {
    let (source, candidate) = entry_loop();
    let mut bad = candidate.clone();
    bad.blocks[0].points[0].reads[0].value = ValueId(4);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].points[1].reads.swap(0, 1);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].points[1].reads[1].register = Reg(1);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].points[0].reads.push(rv(0, 2));
    reject(&source, &bad);
    let mut bad = candidate;
    bad.blocks[0].points[1].reads.pop();
    reject(&source, &bad);
}
#[test]
fn rejects_changed_sites_origins_owners_and_orphan_definitions() {
    let (source, candidate) = diamond();
    let mut bad = candidate.clone();
    bad.blocks[0].points[0].site.instruction = 1;
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.values[2] = assignment(1, 0, 1);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.values[2] = assignment(0, 0, 2);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    let Definition::Phi { block, .. } = &mut bad.values[7] else {
        unreachable!()
    };
    *block = 2;
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.values.push(assignment(0, 0, 1));
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.values.push(initial(0));
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].phis.push(ValueId(1));
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[3].points[0].definition = Some(ValueId(8));
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].points.pop();
    reject(&source, &bad);
    let mut bad = candidate;
    bad.blocks[3]
        .points
        .push(point(3, None, None, &[(2, 8), (1, 7)]));
    reject(&source, &bad);
}
#[test]
fn rejects_missing_forwarded_phi_or_exit_and_unsorted_duplicate_exits() {
    let (source, candidate) = diamond();
    let mut bad = candidate.clone();
    bad.blocks[1].phis.clear();
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[2].exit_values.remove(0);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[1].exit_values.swap(0, 1);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[1].exit_values.push(rv(2, 4));
    reject(&source, &bad);
    let mut bad = candidate;
    bad.blocks[1].exit_values[1].value = ValueId(6);
    reject(&source, &bad);
}
#[test]
fn store_address_then_rhs_and_all_select_arms_are_syntactically_checked() {
    let source = Program::new(
        0,
        3,
        vec![ins(
            0,
            vec![Assignment {
                destination: Place::Memory {
                    address: Expr::binary(BinaryOp::Add, reg(0), reg(1)),
                    width: Width::U8,
                },
                value: Expr::select(
                    reg(1),
                    Expr::load(reg(2), Width::U8),
                    Expr::binary(BinaryOp::Sub, reg(0), reg(2)),
                ),
            }],
            Control::Return(Expr::Const(0)),
        )],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 3,
        values: vec![
            initial(0),
            initial(1),
            initial(2),
            phi(0, 0, &[(None, 0)]),
            phi(0, 1, &[(None, 1)]),
            phi(0, 2, &[(None, 2)]),
        ],
        blocks: vec![block(
            0,
            &[3, 4, 5],
            vec![
                point(
                    0,
                    Some(0),
                    None,
                    &[(0, 3), (1, 4), (1, 4), (2, 5), (0, 3), (2, 5)],
                ),
                point(0, None, None, &[]),
            ],
            &[],
        )],
    };
    ssa::validate(&source, &candidate).unwrap();
    let mut bad = candidate.clone();
    bad.blocks[0].points[0].reads.swap(0, 2);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].points[0].reads.truncate(4);
    reject(&source, &bad);
    let mut bad = candidate;
    bad.blocks[0].points[0].definition = Some(ValueId(3));
    reject(&source, &bad);
}
#[test]
fn coincident_branch_arms_require_one_predecessor_input() {
    let source = Program::new(
        0,
        1,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 1,
                },
            ),
            ins(1, vec![], Control::Return(reg(0))),
        ],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 1,
        values: vec![
            initial(0),
            phi(0, 0, &[(None, 0)]),
            phi(1, 0, &[(Some(0), 1)]),
        ],
        blocks: vec![
            block(0, &[1], vec![point(0, None, None, &[(0, 1)])], &[(0, 1)]),
            block(1, &[2], vec![point(1, None, None, &[(0, 2)])], &[]),
        ],
    };
    ssa::validate(&source, &candidate).unwrap();
    let mut bad = candidate;
    inputs(&mut bad, 2).push(PhiInput {
        predecessor: Some(0),
        value: ValueId(1),
    });
    reject(&source, &bad);
}
#[test]
fn accepts_irreducible_two_entry_scc() {
    let source = Program::new(
        0,
        1,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Jump(3)),
            ins(2, vec![], Control::Jump(3)),
            ins(
                3,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 1,
                },
            ),
            ins(
                4,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 2,
                },
            ),
            ins(5, vec![], Control::Return(reg(0))),
        ],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 1,
        values: vec![
            initial(0),
            phi(0, 0, &[(None, 0)]),
            phi(1, 0, &[(Some(0), 1), (Some(3), 4)]),
            phi(2, 0, &[(Some(0), 1), (Some(4), 5)]),
            phi(3, 0, &[(Some(1), 2), (Some(2), 3)]),
            phi(4, 0, &[(Some(3), 4)]),
            phi(5, 0, &[(Some(4), 5)]),
        ],
        blocks: vec![
            block(0, &[1], vec![point(0, None, None, &[(0, 1)])], &[(0, 1)]),
            block(1, &[2], vec![], &[(0, 2)]),
            block(2, &[3], vec![], &[(0, 3)]),
            block(3, &[4], vec![point(3, None, None, &[(0, 4)])], &[(0, 4)]),
            block(4, &[5], vec![point(4, None, None, &[(0, 5)])], &[(0, 5)]),
            block(5, &[6], vec![point(5, None, None, &[(0, 6)])], &[]),
        ],
    };
    ssa::validate(&source, &candidate).unwrap();
    let mut bad = candidate;
    inputs(&mut bad, 2)[1].value = ValueId(3);
    reject(&source, &bad);
}
#[test]
fn unreachable_predecessor_is_excluded_and_cannot_be_forged() {
    let source = Program::new(
        0,
        1,
        vec![
            ins(0, vec![], Control::Jump(2)),
            ins(1, vec![], Control::Jump(2)),
            ins(2, vec![], Control::Return(reg(0))),
        ],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 1,
        values: vec![
            initial(0),
            phi(0, 0, &[(None, 0)]),
            phi(2, 0, &[(Some(0), 1)]),
        ],
        blocks: vec![
            block(0, &[1], vec![], &[(0, 1)]),
            block(2, &[2], vec![point(2, None, None, &[(0, 2)])], &[]),
        ],
    };
    ssa::validate(&source, &candidate).unwrap();
    let mut bad = candidate.clone();
    inputs(&mut bad, 2)[0].predecessor = Some(1);
    reject(&source, &bad);
    let mut bad = candidate;
    bad.blocks[0].start = 1;
    reject(&source, &bad);
}
#[test]
fn malicious_indices_shapes_and_resource_excesses_fail_without_panics() {
    let (source, candidate) = diamond();
    for poisoned in [candidate.values.len(), usize::MAX] {
        let mut bad = candidate.clone();
        bad.blocks[0].points[0].definition = Some(ValueId(poisoned));
        reject(&source, &bad);
        let mut bad = candidate.clone();
        bad.blocks[0].phis[0] = ValueId(poisoned);
        reject(&source, &bad);
        let mut bad = candidate.clone();
        inputs(&mut bad, 1)[0].value = ValueId(poisoned);
        reject(&source, &bad);
        let mut bad = candidate.clone();
        bad.blocks[0].points[1].reads[0].value = ValueId(poisoned);
        reject(&source, &bad);
        let mut bad = candidate.clone();
        bad.blocks[0].exit_values[0].value = ValueId(poisoned);
        reject(&source, &bad);
    }
    let mut bad = candidate.clone();
    bad.register_count = usize::MAX;
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.entry = 1;
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].points[1].reads[0].register = Reg(usize::MAX);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.values[0] = initial(usize::MAX);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].exit_values[0].register = Reg(usize::MAX);
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[1].start = 0;
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.blocks[0].start = u64::MAX;
    reject(&source, &bad);
    let mut bad = candidate.clone();
    bad.values = vec![initial(0); ssa::MAX_VALUES + 1];
    assert!(matches!(
        ssa::validate(&source, &bad),
        Err(SsaError::Unavailable(_))
    ));
    let mut bad = candidate.clone();
    inputs(&mut bad, 1).resize(
        ssa::MAX_PHI_INPUTS + 1,
        PhiInput {
            predecessor: None,
            value: ValueId(0),
        },
    );
    assert!(matches!(
        ssa::validate(&source, &bad),
        Err(SsaError::Unavailable(_))
    ));
    let mut bad = candidate;
    bad.blocks[0].points[1].reads = vec![rv(0, 1); ssa::MAX_NODES + 1];
    assert!(matches!(
        ssa::validate(&source, &bad),
        Err(SsaError::Unavailable(_))
    ));
}
#[test]
fn original_sparse_register_space_and_expression_depth_are_preflighted() {
    let huge = Program::new(
        0,
        usize::MAX,
        vec![ins(0, vec![], Control::Return(Expr::Const(0)))],
    )
    .unwrap();
    let candidate = SsaFunction {
        entry: 0,
        register_count: 0,
        values: vec![],
        blocks: vec![],
    };
    assert!(matches!(
        ssa::validate(&huge, &candidate),
        Err(SsaError::Unavailable(_))
    ));
    let mut expression = Expr::Const(0);
    for _ in 0..ssa::MAX_DEPTH {
        expression = Expr::binary(BinaryOp::Add, expression, Expr::Const(0));
    }
    let deep = Program::new(0, 0, vec![ins(0, vec![], Control::Return(expression))]).unwrap();
    assert!(matches!(
        ssa::validate(&deep, &candidate),
        Err(SsaError::Unavailable(_))
    ));
}
