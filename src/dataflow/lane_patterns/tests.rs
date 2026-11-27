use super::*;
use crate::model::ir::{BlockExit, Control};

fn fixture(offsets: &[u64], varying_xor: bool, peeled: bool) -> Program {
    let r = |n| Expr::Register(Reg(n));
    let k = Expr::Const;
    let op = Expr::binary;
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let mut instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: vec![set(4, op(BinaryOp::Add, r(0), k(1)))],
        control: Control::Jump(10),
    }];
    for (lane, &offset) in offsets.iter().enumerate() {
        let pc = 10 + lane as u64 * 10;
        let index = if peeled && lane == 0 {
            r(0)
        } else {
            op(BinaryOp::And, r(5), k(3))
        };
        let other = op(BinaryOp::Xor, r(3), if varying_xor { r(5) } else { r(4) });
        let update = if lane & 1 == 0 {
            op(BinaryOp::Add, other, r(2))
        } else {
            op(BinaryOp::Add, r(2), other)
        };
        instructions.push(IrInstruction {
            address: pc,
            size: 1,
            assignments: vec![
                set(5, op(BinaryOp::Add, r(0), k(offset))),
                set(
                    3,
                    Expr::load(
                        op(BinaryOp::Add, r(1), op(BinaryOp::Mul, index, k(8))),
                        Width::U64,
                    ),
                ),
                set(2, update),
            ],
            control: Control::Next,
        });
        instructions.push(IrInstruction {
            address: pc + 1,
            size: 1,
            assignments: vec![Assignment {
                destination: Place::Memory {
                    address: op(BinaryOp::Add, r(1), k(16)),
                    width: Width::U64,
                },
                value: r(2),
            }],
            control: if lane + 1 == offsets.len() {
                Control::Return(r(2))
            } else {
                Control::Jump(pc + 10)
            },
        });
    }
    Program::new(0, 6, instructions).unwrap()
}
fn has_lane(term: &PatternExpr) -> bool {
    match term {
        PatternExpr::Lane => true,
        PatternExpr::Unary(_, v) => has_lane(v),
        PatternExpr::Binary(_, a, b) => has_lane(a) || has_lane(b),
        PatternExpr::Select(a, b, c) => has_lane(a) || has_lane(b) || has_lane(c),
        _ => false,
    }
}

#[test]
fn advisory_caps_align_the_peeled_lane_without_changing_source_kernels() {
    let acyclic = fixture(&[0, 1, 2, 3], false, true);
    let mut code = acyclic.instructions().to_vec();
    let last = code.last_mut().unwrap();
    last.assignments.push(Assignment {
        destination: Reg(0).into(),
        value: Expr::binary(
            BinaryOp::And,
            Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
            Expr::Const(3),
        ),
    });
    last.control = Control::Jump(10);
    let source = Program::new(0, 6, code).unwrap();
    let ordinary = discover(&source).unwrap();
    assert_eq!(ordinary.groups()[0].offsets, [1, 2, 3]);
    let hinted = ordinary
        .with_advisory_entry_caps(10, &[(Reg(0), 2)])
        .unwrap();
    assert_eq!(hinted.advisory_header(), Some(10));
    assert!(hinted.belongs_to(&source));
    assert_eq!(hinted.kernels(), ordinary.kernels());
    assert_eq!(hinted.groups()[0].offsets, [0, 1, 2, 3]);
    assert_eq!(hinted.groups()[0].step, 1);
    let raw = ordinary
        .register_expression(ordinary.kernels()[0].load, Reg(0))
        .unwrap();
    let masked = PatternExpr::Binary(
        BinaryOp::And,
        Box::new(PatternExpr::Binary(
            BinaryOp::Add,
            Box::new(raw.clone()),
            Box::new(PatternExpr::Constant(0)),
        )),
        Box::new(PatternExpr::Constant(3)),
    );
    assert!(!ordinary.proposal_match(&raw, &masked));
    assert!(hinted.proposal_match(&raw, &masked));
    assert_eq!(
        hinted.register_expression(hinted.kernels()[0].load, Reg(0)),
        Some(raw)
    );
    for caps in [[(Reg(0), 3)], [(Reg(2), 2)]] {
        assert_eq!(
            ordinary
                .with_advisory_entry_caps(10, &caps)
                .unwrap()
                .groups()[0]
                .offsets,
            [1, 2, 3]
        );
    }
    assert!(matches!(
        ordinary.with_advisory_entry_caps(11, &[(Reg(0), 2)]),
        Err(Error::SourceUnavailable)
    ));
    assert!(matches!(
        ordinary.with_advisory_entry_caps(10, &[(Reg(6), 2)]),
        Err(Error::SourceUnavailable)
    ));
    assert!(matches!(
        ordinary.with_advisory_entry_caps(10, &[(Reg(0), 65)]),
        Err(Error::SourceUnavailable)
    ));
}

#[test]
fn read_identities_follow_copies_and_keep_separate_load_snapshots() {
    let source = Program::new(
        0,
        4,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::load(Expr::Register(Reg(3)), Width::U64),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: Expr::Register(Reg(0)),
                    },
                ],
                control: Control::Next,
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::load(Expr::Register(Reg(3)), Width::U64),
                }],
                control: Control::Return(Expr::binary(
                    BinaryOp::Xor,
                    Expr::Register(Reg(0)),
                    Expr::Register(Reg(1)),
                )),
            },
        ],
    )
    .unwrap();
    let found = discover(&source).unwrap();
    let captured = found
        .read_identity(
            Site {
                instruction: 0,
                assignment: Some(1),
            },
            Reg(0),
        )
        .unwrap();
    assert_eq!(
        found.read_identity(
            Site {
                instruction: 1,
                assignment: None
            },
            Reg(1)
        ),
        Some(captured)
    );
    assert_ne!(
        found.read_identity(
            Site {
                instruction: 1,
                assignment: None
            },
            Reg(0)
        ),
        Some(captured)
    );
}

#[test]
fn discovers_varying_indices_while_preserving_the_invariant_xor_operand() {
    let source = fixture(&[0, 1, 2, 3], false, true);
    let found = discover(&source).unwrap();
    assert!(found.belongs_to(&source));
    assert_eq!(found.kernels().len(), 4);
    assert_eq!(found.groups().len(), 1, "{:#?}", found.kernels());
    let group = &found.groups()[0];
    assert_eq!(group.offsets, [1, 2, 3]);
    assert_eq!(group.step, 1);
    assert_eq!(
        group
            .kernels
            .iter()
            .map(|k| k.store.instruction)
            .collect::<Vec<_>>(),
        [21, 31, 41]
    );
    assert!(has_lane(&group.load_address));
    assert!(!has_lane(&group.update_expression));
    assert!(!has_lane(&group.store_address));
    let source = fixture(&[1, 2, 3], true, false);
    let found = discover(&source).unwrap();
    assert!(has_lane(&found.groups()[0].update_expression));
}

#[test]
fn bindings_require_a_live_current_value_and_keep_load_events_opaque() {
    let source = fixture(&[1, 2, 3], false, false);
    let discovery = discover(&source).unwrap();
    for kernel in discovery.kernels() {
        let point = discovery.ssa().point(kernel.load).unwrap();
        let pointer = point.reads.iter().find(|r| r.register == Reg(1)).unwrap();
        assert_eq!(
            discovery.available_register(kernel.load, pointer.value),
            Some(Reg(1))
        );
        assert!(discovery.register_expression(kernel.load, Reg(5)).is_some());
        assert!(
            discovery
                .register_expression(kernel.update, Reg(3))
                .is_none()
        );
    }
    let initial = discovery
        .ssa()
        .values
        .iter()
        .position(|v| matches!(v, Definition::Initial { register: Reg(5) }))
        .unwrap();
    assert_eq!(
        discovery.available_register(discovery.kernels()[0].load, ValueId(initial)),
        None
    );
    assert_eq!(
        discovery.available_register(
            Site {
                instruction: u64::MAX,
                assignment: None
            },
            ValueId(initial)
        ),
        None
    );
    assert_eq!(
        discovery.available_register(discovery.kernels()[0].load, ValueId(usize::MAX)),
        None
    );
}

#[test]
fn unrelated_literals_widths_and_incomplete_families_keep_distinct_patterns() {
    assert!(
        discover(&fixture(&[1, 2], false, false))
            .unwrap()
            .groups()
            .is_empty()
    );
    assert!(
        discover(&fixture(&[1, 2, 4], false, false))
            .unwrap()
            .groups()
            .is_empty()
    );
    let source = fixture(&[2, 4, 6], false, false);
    let found = discover(&source).unwrap();
    assert_eq!(found.groups()[0].step, 2);
    assert!(
        !discover(&fixture(&[1, 2, 3], false, false))
            .unwrap()
            .belongs_to(&source)
    );
    let mut instructions = source.instructions().to_vec();
    if let Expr::Load { width, .. } = &mut instructions[5].assignments[1].value {
        *width = Width::U32;
    } else {
        panic!("load fixture");
    }
    let different = Program::new(0, 6, instructions).unwrap();
    assert!(discover(&different).unwrap().groups().is_empty());
}

fn evaluate(
    term: &PatternExpr,
    graph: &SsaFunction,
    input: &[u64],
    accumulator: u64,
    loaded: u64,
    lane: u64,
) -> u64 {
    let eval = |term| evaluate(term, graph, input, accumulator, loaded, lane);
    match term {
        PatternExpr::Constant(value) => *value,
        PatternExpr::Accumulator => accumulator,
        PatternExpr::Loaded => loaded,
        PatternExpr::Lane => lane,
        PatternExpr::Value(value) => match graph.values[value.0] {
            Definition::Initial { register } => input[register.0],
            _ => panic!("acyclic fixture retains initial identities only"),
        },
        PatternExpr::Unary(op, value) => op.evaluate(eval(value)),
        PatternExpr::Binary(op, a, b) => op.evaluate(eval(a), eval(b)),
        PatternExpr::Select(c, a, b) => {
            if eval(c) == 0 {
                eval(b)
            } else {
                eval(a)
            }
        }
    }
}

#[test]
fn inferred_templates_match_actual_sequential_kernels_with_aliasing_memory() {
    let source = fixture(&[1, 2, 3], false, false);
    let found = discover(&source).unwrap();
    let group = &found.groups()[0];
    for seed in 0..128u64 {
        let mut registers = vec![
            seed & 3,
            4224,
            seed.wrapping_mul(0x9e3779b97f4a7c15),
            0,
            0,
            0,
        ];
        let mut memory: Vec<_> = (0..512).map(|n| (n * 29 + 7) as u8).collect();
        let prefix = source
            .run_block_with_memory(0, &registers, 4096, &memory)
            .unwrap();
        registers = prefix.state.registers;
        for (kernel, &offset) in group.kernels.iter().zip(&group.offsets) {
            let address = evaluate(
                &group.load_address,
                found.ssa(),
                &registers,
                registers[2],
                0,
                offset,
            );
            let location = (address - 4096) as usize;
            let loaded = u64::from_le_bytes(memory[location..location + 8].try_into().unwrap());
            let predicted = evaluate(
                &group.update_expression,
                found.ssa(),
                &registers,
                registers[2],
                loaded,
                offset,
            );
            let report = source
                .run_block_with_memory(kernel.load.instruction, &registers, 4096, &memory)
                .unwrap();
            assert_eq!(
                report.state.registers[2], predicted,
                "seed={seed} offset={offset}"
            );
            assert!(matches!(
                report.exit,
                BlockExit::Next(_) | BlockExit::Returned(_)
            ));
            registers = report.state.registers;
            memory = report.state.memory;
        }
    }
}

#[test]
fn resource_limits_decline_atomically_and_nested_memory_expressions_remain_unsupported() {
    let source = fixture(&[1, 2, 3], false, false);
    let mut instructions = source.instructions().to_vec();
    for instruction in &mut instructions {
        for assignment in &mut instruction.assignments {
            if assignment.destination == Place::Register(Reg(3)) {
                assignment.value =
                    Expr::binary(BinaryOp::Add, assignment.value.clone(), Expr::Const(0));
            }
        }
    }
    let nested = Program::new(0, 6, instructions).unwrap();
    assert!(discover(&nested).unwrap().kernels().is_empty());
    let source = Program::new(
        0,
        MAX_REGISTERS + 1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    assert!(matches!(discover(&source), Err(Error::Limit)));
    let mut budget = Budget {
        work: 0,
        terms: 0,
        exhausted: false,
    };
    assert!(group::discover(&[], &mut budget, &BTreeMap::new()).is_empty());
    assert_eq!(budget.node(), None);
    assert!(budget.exhausted);
}

#[test]
fn copy_cycles_collapse_invariants_but_keep_distinct_phi_inputs_separate() {
    let original = fixture(&[1, 2, 3], false, false);
    let mut instructions = original.instructions().to_vec();
    let last = instructions.last_mut().unwrap();
    last.control = Control::Next;
    instructions.push(IrInstruction {
        address: 32,
        size: 1,
        assignments: vec![Assignment {
            destination: Reg(0).into(),
            value: Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
        }],
        control: Control::Branch {
            condition: Expr::Register(Reg(7)),
            target: 0,
        },
    });
    instructions.push(IrInstruction {
        address: 33,
        size: 1,
        assignments: vec![],
        control: Control::Return(Expr::Register(Reg(2))),
    });
    let cyclic = Program::new(0, 8, instructions).unwrap();
    let found = discover(&cyclic).unwrap();
    assert_eq!(found.groups().len(), 1);
    assert!(!has_lane(&found.groups()[0].update_expression));

    let step = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    let source = Program::new(
        0,
        2,
        vec![
            step(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::Register(Reg(0)),
                    target: 3,
                },
            ),
            step(
                1,
                vec![Assignment {
                    destination: Reg(1).into(),
                    value: Expr::Const(1),
                }],
                Control::Jump(4),
            ),
            step(
                3,
                vec![Assignment {
                    destination: Reg(1).into(),
                    value: Expr::Const(2),
                }],
                Control::Jump(4),
            ),
            step(4, vec![], Control::Return(Expr::Register(Reg(1)))),
        ],
    )
    .unwrap();
    let graph = SsaFunction::build(&source).unwrap();
    let instructions = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let points = graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect();
    let aliases = resolve::aliases(&graph, &instructions, &points, &mut Budget::new()).unwrap();
    let phi = graph
        .values
        .iter()
        .position(|value| {
            matches!(
                value,
                Definition::Phi {
                    block: 4,
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap();
    assert_eq!(aliases[phi], ValueId(phi));
}
