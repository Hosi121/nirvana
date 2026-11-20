use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg};
use nirvana::ssa::{
    Definition, PhiInput, PointValues, RegisterValue, Site, SsaBlock, SsaError, SsaFunction,
    ValueId,
};
use nirvana::ssa_locals::{self, Plan};
use std::collections::{BTreeMap, BTreeSet};

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, a, b)
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
fn source(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}
fn site(instruction: u64, assignment: usize) -> Site {
    Site {
        instruction,
        assignment: Some(assignment),
    }
}
fn definition(graph: &SsaFunction, instruction: u64, assignment: usize) -> usize {
    graph
        .point(site(instruction, assignment))
        .unwrap()
        .definition
        .unwrap()
        .0
}
fn phi(graph: &SsaFunction, block: u64, register: usize) -> usize {
    graph.values.iter().position(|v| matches!(v, Definition::Phi { block: b, register: r, .. } if *b == block && r.0 == register)).unwrap()
}
fn identity(graph: &SsaFunction) -> Plan {
    Plan {
        by_value: (0..graph.values.len()).collect(),
        local_count: graph.values.len(),
    }
}
fn analyze(source: &Program, graph: &SsaFunction) -> Plan {
    let plan = ssa_locals::analyze(source, graph, &BTreeSet::new()).unwrap();
    ssa_locals::validate(source, graph, &plan).unwrap();
    plan
}
fn merge(candidate: &Plan, a: usize, b: usize) -> Plan {
    let mut by_value = candidate.by_value.clone();
    let old = by_value[b];
    let new = by_value[a];
    for local in &mut by_value {
        if *local == old {
            *local = new;
        }
    }
    let mut dense = BTreeMap::new();
    for local in &mut by_value {
        let next = dense.len();
        *local = *dense.entry(*local).or_insert(next);
    }
    Plan {
        by_value,
        local_count: dense.len(),
    }
}
fn diamond() -> Program {
    source(
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            ins(1, vec![set(1, c(11))], Control::Jump(3)),
            ins(2, vec![set(1, c(22))], Control::Jump(3)),
            ins(3, vec![], Control::Return(r(1))),
        ],
    )
}
#[test]
fn real_copy_affinity_reduces_locals_and_exclusions_prevent_it() {
    let source = source(
        3,
        vec![ins(
            0,
            vec![set(0, c(9)), set(1, r(0)), set(2, r(1))],
            Control::Return(r(2)),
        )],
    );
    let graph = SsaFunction::build(&source).unwrap();
    let plan = analyze(&source, &graph);
    assert_eq!(plan.local_count, graph.values.len() - 2);
    let copies: Vec<_> = (0..3)
        .map(|a| plan.by_value[definition(&graph, 0, a)])
        .collect();
    assert_eq!(copies, [copies[0]; 3]);
    let excluded = BTreeSet::from([site(0, 1)]);
    let blocked = ssa_locals::analyze(&source, &graph, &excluded).unwrap();
    assert_eq!(blocked.local_count, plan.local_count + 1);
    assert_ne!(
        blocked.by_value[definition(&graph, 0, 0)],
        blocked.by_value[definition(&graph, 0, 1)]
    );
    let excluded = BTreeSet::from([site(0, 1), site(0, 2)]);
    assert_eq!(
        ssa_locals::analyze(&source, &graph, &excluded)
            .unwrap()
            .local_count,
        graph.values.len()
    );
}
#[test]
fn only_real_register_copies_and_phis_create_affinities() {
    for assignments in [
        vec![set(0, c(7)), set(1, c(7))],
        vec![set(0, c(7)), set(1, add(r(0), c(0)))],
    ] {
        let source = source(2, vec![ins(0, assignments, Control::Return(r(1)))]);
        let graph = SsaFunction::build(&source).unwrap();
        assert_eq!(analyze(&source, &graph), identity(&graph));
        // The checker accepts another safe allocation without using producer
        // affinity rules or requiring the producer's canonical local numbering.
        let alternative = merge(
            &identity(&graph),
            definition(&graph, 0, 0),
            definition(&graph, 0, 1),
        );
        ssa_locals::validate(&source, &graph, &alternative).unwrap();
    }
}
#[test]
fn equal_copy_operands_still_conflict_while_simultaneously_live() {
    let source = source(
        2,
        vec![ins(
            0,
            vec![set(0, c(7)), set(1, r(0))],
            Control::Return(add(r(0), r(1))),
        )],
    );
    let graph = SsaFunction::build(&source).unwrap();
    let a = definition(&graph, 0, 0);
    let b = definition(&graph, 0, 1);
    let plan = analyze(&source, &graph);
    assert_ne!(plan.by_value[a], plan.by_value[b]);
    assert!(ssa_locals::validate(&source, &graph, &merge(&identity(&graph), a, b)).is_err());
}
#[test]
fn diamond_phi_coalesces_both_exclusive_predecessor_values() {
    let source = diamond();
    let graph = SsaFunction::build(&source).unwrap();
    let plan = analyze(&source, &graph);
    let result = phi(&graph, 3, 1);
    assert_eq!(
        plan.by_value[result],
        plan.by_value[definition(&graph, 1, 0)]
    );
    assert_eq!(
        plan.by_value[result],
        plan.by_value[definition(&graph, 2, 0)]
    );
    assert!(plan.local_count < graph.values.len());
    let mut permuted = graph.clone();
    permuted.blocks.reverse();
    for b in &mut permuted.blocks {
        b.phis.reverse();
    }
    for d in &mut permuted.values {
        if let Definition::Phi { inputs, .. } = d {
            inputs.reverse();
        }
    }
    assert_eq!(analyze(&source, &permuted), plan);
}
#[test]
fn initial_values_stay_private_even_when_entry_phi_has_no_conflict() {
    let source = source(2, vec![ins(0, vec![set(1, r(0))], Control::Return(r(1)))]);
    let graph = SsaFunction::build(&source).unwrap();
    let plan = analyze(&source, &graph);
    for (i, d) in graph.values.iter().enumerate() {
        if matches!(d, Definition::Initial { .. }) {
            assert_eq!(
                plan.by_value
                    .iter()
                    .filter(|&&local| local == plan.by_value[i])
                    .count(),
                1
            );
            for other in 0..graph.values.len() {
                if other != i {
                    assert!(
                        ssa_locals::validate(&source, &graph, &merge(&identity(&graph), i, other))
                            .is_err()
                    );
                }
            }
        }
    }
    // Dense but differently numbered safe locals remain acceptable.
    let mut reverse = identity(&graph);
    reverse.by_value.reverse();
    ssa_locals::validate(&source, &graph, &reverse).unwrap();
}
#[test]
fn dead_assignment_is_a_write_and_cannot_alias_an_after_live_value() {
    let source = source(
        2,
        vec![ins(
            0,
            vec![set(0, c(7)), set(1, c(99))],
            Control::Return(r(0)),
        )],
    );
    let graph = SsaFunction::build(&source).unwrap();
    let old = definition(&graph, 0, 0);
    let dead = definition(&graph, 0, 1);
    let live = nirvana::value_liveness::analyze(&source, &graph).unwrap();
    assert!(live.values[dead].uses.is_empty());
    let bad = merge(&identity(&graph), old, dead);
    assert_eq!(
        ssa_locals::validate(&source, &graph, &bad),
        Err(SsaError::Malformed("local definition clobbers live value"))
    );
    assert_ne!(
        analyze(&source, &graph).by_value[old],
        analyze(&source, &graph).by_value[dead]
    );
}
#[test]
fn a_dead_copy_destination_cannot_clobber_the_live_source() {
    let source = source(
        2,
        vec![ins(
            0,
            vec![set(0, c(7)), set(1, r(0))],
            Control::Return(r(0)),
        )],
    );
    let graph = SsaFunction::build(&source).unwrap();
    let a = definition(&graph, 0, 0);
    let b = definition(&graph, 0, 1);
    let plan = analyze(&source, &graph);
    assert_ne!(plan.by_value[a], plan.by_value[b]);
    assert!(ssa_locals::validate(&source, &graph, &merge(&identity(&graph), a, b)).is_err());
}
#[test]
fn simultaneous_dead_phis_conflict_with_each_other_and_live_phis() {
    let source = source(3, vec![ins(0, vec![], Control::Return(r(2)))]);
    // Extra dead phis are legal SSA and still issue incoming edge writes.
    let graph = SsaFunction {
        entry: 0,
        register_count: 3,
        values: (0..3)
            .map(|register| Definition::Initial {
                register: Reg(register),
            })
            .chain((0..3).map(|register| Definition::Phi {
                block: 0,
                register: Reg(register),
                inputs: vec![PhiInput {
                    predecessor: None,
                    value: ValueId(register),
                }],
            }))
            .collect(),
        blocks: vec![SsaBlock {
            start: 0,
            phis: vec![ValueId(3), ValueId(4), ValueId(5)],
            points: vec![PointValues {
                site: Site {
                    instruction: 0,
                    assignment: None,
                },
                definition: None,
                reads: vec![RegisterValue {
                    register: Reg(2),
                    value: ValueId(5),
                }],
            }],
            exit_values: vec![],
        }],
    };
    nirvana::ssa::validate(&source, &graph).unwrap();
    let live = nirvana::value_liveness::analyze(&source, &graph).unwrap();
    assert!(live.values[3].uses.is_empty() && live.values[4].uses.is_empty());
    assert_eq!(live.blocks[0].live_in, [ValueId(5)]);
    for pair in [(3, 4), (3, 5), (4, 5)] {
        assert!(
            ssa_locals::validate(&source, &graph, &merge(&identity(&graph), pair.0, pair.1))
                .is_err()
        );
    }
    assert_eq!(analyze(&source, &graph), identity(&graph));
}
#[test]
fn entry_loop_and_multiple_backedges_have_safe_deterministic_groups() {
    let sources = [
        source(
            2,
            vec![
                ins(
                    0,
                    vec![set(0, add(r(0), c(1))), set(1, add(r(1), r(0)))],
                    Control::Branch {
                        condition: r(1),
                        target: 0,
                    },
                ),
                ins(1, vec![], Control::Return(r(0))),
            ],
        ),
        source(
            2,
            vec![
                ins(0, vec![set(1, c(0))], Control::Jump(2)),
                ins(1, vec![], Control::Return(r(1))),
                ins(
                    2,
                    vec![],
                    Control::Branch {
                        condition: r(0),
                        target: 4,
                    },
                ),
                ins(
                    3,
                    vec![set(0, add(r(0), c(1))), set(1, add(r(1), r(0)))],
                    Control::Jump(2),
                ),
                ins(
                    4,
                    vec![],
                    Control::Branch {
                        condition: r(1),
                        target: 1,
                    },
                ),
                ins(5, vec![set(0, add(r(0), c(1)))], Control::Jump(2)),
            ],
        ),
    ];
    for source in sources {
        let graph = SsaFunction::build(&source).unwrap();
        let plan = analyze(&source, &graph);
        assert!(plan.local_count < graph.values.len());
        // Adversarially try every pair: either rejected or independently safe.
        for a in 0..graph.values.len() {
            for b in a + 1..graph.values.len() {
                let candidate = merge(&identity(&graph), a, b);
                if ssa_locals::validate(&source, &graph, &candidate).is_ok() {
                    assert!(!matches!(graph.values[a], Definition::Initial { .. }));
                    assert!(!matches!(graph.values[b], Definition::Initial { .. }));
                }
            }
        }
    }
}
#[test]
fn empty_ssa_has_no_locals() {
    let source = source(0, vec![ins(0, vec![], Control::Return(c(7)))]);
    let graph = SsaFunction::build(&source).unwrap();
    assert_eq!(
        analyze(&source, &graph),
        Plan {
            by_value: vec![],
            local_count: 0
        }
    );
}
#[test]
fn malformed_dense_maps_and_ssa_or_source_mismatches_are_rejected_without_panics() {
    let source = diamond();
    let graph = SsaFunction::build(&source).unwrap();
    let n = graph.values.len();
    let candidates = [
        Plan {
            by_value: vec![],
            local_count: 0,
        },
        Plan {
            by_value: vec![0; n],
            local_count: 0,
        },
        Plan {
            by_value: vec![usize::MAX; n],
            local_count: 1,
        },
        Plan {
            by_value: vec![1; n],
            local_count: 2,
        },
        Plan {
            by_value: vec![0; n],
            local_count: usize::MAX,
        },
    ];
    for plan in candidates {
        assert!(
            std::panic::catch_unwind(|| ssa_locals::validate(&source, &graph, &plan))
                .unwrap()
                .is_err()
        );
    }
    let mut bad = graph.clone();
    bad.blocks[0].points[0].reads[0].value = ValueId(usize::MAX);
    assert!(ssa_locals::analyze(&source, &bad, &BTreeSet::new()).is_err());
    assert!(ssa_locals::validate(&source, &bad, &identity(&graph)).is_err());
    let other = self::source(2, vec![ins(0, vec![], Control::Return(r(1)))]);
    assert!(ssa_locals::analyze(&other, &graph, &BTreeSet::new()).is_err());
}
fn sum(start: usize, end: usize) -> Expr {
    if end == start + 1 {
        return r(start);
    }
    let middle = (start + end) / 2;
    add(sum(start, middle), sum(middle, end))
}
#[test]
fn source_ssa_and_liveness_limits_decline_atomically() {
    let source = source(0, vec![ins(0, vec![], Control::Return(c(7)))]);
    let mut graph = SsaFunction::build(&source).unwrap();
    graph.values.resize(
        nirvana::ssa::MAX_VALUES + 1,
        Definition::Initial { register: Reg(0) },
    );
    assert!(matches!(
        ssa_locals::analyze(&source, &graph, &BTreeSet::new()),
        Err(SsaError::Unavailable(_))
    ));
    assert!(matches!(
        ssa_locals::validate(
            &source,
            &graph,
            &Plan {
                by_value: vec![],
                local_count: 0
            }
        ),
        Err(SsaError::Unavailable(_))
    ));
    let oversized = self::source(
        nirvana::ssa::MAX_REGISTERS + 1,
        vec![ins(0, vec![], Control::Return(c(7)))],
    );
    assert!(matches!(
        ssa_locals::analyze(&oversized, &graph, &BTreeSet::new()),
        Err(SsaError::Unavailable(_))
    ));
    let large = self::source(
        1001,
        vec![ins(
            0,
            (0..550).map(|i| set(1000, c(i))).collect(),
            Control::Return(sum(0, 1000)),
        )],
    );
    let graph = SsaFunction::build(&large).unwrap();
    assert_eq!(
        ssa_locals::analyze(&large, &graph, &BTreeSet::new()),
        Err(SsaError::Unavailable("liveness memberships"))
    );
    assert_eq!(
        ssa_locals::validate(&large, &graph, &identity(&graph)),
        Err(SsaError::Unavailable("liveness memberships"))
    );
}
