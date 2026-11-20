use std::collections::BTreeSet;

use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg};
use nirvana::ssa::{Definition, Site, SsaFunction};
use nirvana::{ssa_destroy, ssa_locals, ssa_storage};

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
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

fn allocated(source: &Program) -> (SsaFunction, ssa_locals::Plan, ssa_locals::Plan) {
    let graph = SsaFunction::build(source).unwrap();
    let groups = ssa_locals::analyze(source, &graph, &BTreeSet::new()).unwrap();
    let compact = ssa_storage::reuse(source, &graph, &groups).unwrap();
    assert!(compact.local_count <= groups.local_count);
    ssa_locals::validate(source, &graph, &compact).unwrap();
    (graph, groups, compact)
}

fn at(graph: &SsaFunction, instruction: u64, assignment: usize) -> usize {
    graph
        .point(Site {
            instruction,
            assignment: Some(assignment),
        })
        .unwrap()
        .definition
        .unwrap()
        .0
}

#[test]
fn many_unrelated_writes_reuse_storage_without_affinity_or_dead_code_removal() {
    let source = Program::new(
        0,
        1,
        (0..64)
            .map(|n| {
                ins(
                    n,
                    vec![set(0, Expr::Const(n * 37))],
                    if n == 63 {
                        Control::Return(r(0))
                    } else {
                        Control::Next
                    },
                )
            })
            .collect(),
    )
    .unwrap();
    let (graph, groups, compact) = allocated(&source);
    assert!(groups.local_count > 64);
    assert_eq!(compact.local_count, 2);
    let lowered = ssa_destroy::lower_with_plan(&source, &graph, compact).unwrap();
    assert_eq!(lowered.program().instructions().len(), 64);
    for budget in 0..=65 {
        assert_eq!(
            source
                .run_with_memory(&[0xbadcafe], 0x1000, &[0; 8], budget)
                .unwrap(),
            lowered
                .run_with_memory(&[0xbadcafe], 0x1000, &[0; 8], budget)
                .unwrap()
        );
    }
}

#[test]
fn simultaneous_operands_and_dead_writes_keep_distinct_storage() {
    let source = Program::new(
        0,
        3,
        vec![ins(
            0,
            vec![
                set(0, Expr::Const(7)),
                set(1, Expr::Const(7)),
                set(2, Expr::Const(99)),
            ],
            Control::Return(Expr::binary(BinaryOp::Add, r(0), r(1))),
        )],
    )
    .unwrap();
    let (graph, _, compact) = allocated(&source);
    let colors: Vec<_> = (0..3).map(|i| compact.by_value[at(&graph, 0, i)]).collect();
    assert_eq!(colors.iter().collect::<BTreeSet<_>>().len(), 3);
    for (value, definition) in graph.values.iter().enumerate() {
        if matches!(definition, Definition::Initial { .. }) {
            assert_eq!(
                compact
                    .by_value
                    .iter()
                    .filter(|&&c| c == compact.by_value[value])
                    .count(),
                1
            );
        }
    }
    let mut bad = compact;
    bad.by_value[at(&graph, 0, 2)] = bad.by_value[at(&graph, 0, 0)];
    assert!(ssa_locals::validate(&source, &graph, &bad).is_err());
}

#[test]
fn loop_backedges_and_phi_copies_preserve_every_budget_and_fault_state() {
    let mut prefix = vec![
        set(0, Expr::Const(3)),
        set(1, Expr::Const(11)),
        set(2, Expr::Const(19)),
    ];
    prefix.extend((0..16).map(|n| set(3, Expr::Const(n))));
    let source = Program::new(
        0,
        5,
        vec![
            ins(0, prefix, Control::Next),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 3,
                },
            ),
            ins(
                2,
                vec![Assignment {
                    destination: nirvana::ir::Place::Memory {
                        address: r(4),
                        width: nirvana::ir::Width::U64,
                    },
                    value: r(1),
                }],
                Control::Return(r(2)),
            ),
            ins(
                3,
                vec![
                    set(3, r(1)),
                    set(1, r(2)),
                    set(2, r(3)),
                    set(0, Expr::binary(BinaryOp::Sub, r(0), Expr::Const(1))),
                ],
                Control::Jump(1),
            ),
        ],
    )
    .unwrap();
    let (graph, groups, compact) = allocated(&source);
    assert!(compact.local_count < groups.local_count);
    let lowered = ssa_destroy::lower_with_plan(&source, &graph, compact.clone()).unwrap();
    for input in [[0, 0, 0, 0, 0x1000], [u64::MAX; 5]] {
        for budget in 0..32 {
            assert_eq!(
                source
                    .run_with_memory(&input, 0x1000, &[0; 24], budget)
                    .unwrap(),
                lowered
                    .run_with_memory(&input, 0x1000, &[0; 24], budget)
                    .unwrap()
            );
        }
    }
    let mut permuted = graph;
    permuted.blocks.reverse();
    for block in &mut permuted.blocks {
        block.phis.reverse();
    }
    for definition in &mut permuted.values {
        if let Definition::Phi { inputs, .. } = definition {
            inputs.reverse();
        }
    }
    assert_eq!(
        ssa_storage::reuse(&source, &permuted, &groups).unwrap(),
        compact
    );
}

#[test]
fn empty_and_malformed_mappings_are_checked_before_allocation() {
    let source = Program::new(0, 0, vec![ins(0, vec![], Control::Return(Expr::Const(7)))]).unwrap();
    let (graph, groups, compact) = allocated(&source);
    assert_eq!(compact.local_count, 0);
    let mut malformed = groups;
    malformed.local_count = usize::MAX;
    assert!(ssa_storage::reuse(&source, &graph, &malformed).is_err());
}
