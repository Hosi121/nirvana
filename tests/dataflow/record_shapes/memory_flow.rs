//! Store provenance supplies type compatibility, independently of value aliases.
use super::*;

fn memory_edges(analysis: &Analysis, to: ValueId) -> Vec<&record_shapes::Constraint> {
    analysis
        .constraints
        .iter()
        .filter(|c| c.kind == ConstraintKind::Memory && c.to == to)
        .collect()
}

#[test]
fn full_word_reload_uses_the_stored_ssa_snapshot_without_a_stack_abi() {
    let source = one(
        6,
        vec![
            set(5, load(1, 0, Width::U32)),
            store(r(0), Width::U64, r(1)),
            set(1, r(2)),
            store(at(0, 8), Width::U8, c(0)),
            set(3, load(0, 0, Width::U64)),
            set(4, load(3, 16, Width::U64)),
            set(5, load(1, 24, Width::U16)),
        ],
    );
    let types = TypeAnalysis::analyze(&source).unwrap();
    let graph = types.graph();
    let original = initial(graph, 1);
    let other = initial(graph, 2);
    let reloaded = value(graph, 0, 4);
    let before_types = types.to_json().unwrap();
    let before_c = emit::emit_c(&source).unwrap().code;
    let inputs = [
        [0x1000, 0x1020, 0x1040, 91, 92, 93],
        [0x1000, 0x1000, 0x1040, 91, 92, 93],
        [0x105f, 0x1020, 0x1040, 91, 92, 93],
        [0x1000, u64::MAX, 0x1040, 91, 92, 93],
    ];
    let execute = || {
        inputs
            .iter()
            .flat_map(|input| {
                [0, 1, 2].map(|budget| {
                    source
                        .run_with_memory(input, 0x1000, &[0x55; 96], budget)
                        .unwrap()
                })
            })
            .collect::<Vec<_>>()
    };
    let before = execute();
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, original);
    assert_eq!(node.id, record(&analysis, reloaded).id);
    assert_ne!(node.id, record(&analysis, other).id);
    assert!(field(node, 0, Width::U32).reads);
    assert!(field(node, 16, Width::U64).reads);
    let edges = memory_edges(&analysis, reloaded);
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].from, original);
    assert_eq!(
        edges[0].site,
        Some(Site {
            instruction: 0,
            assignment: Some(1),
        })
    );
    assert_eq!(analysis.memory_flow.as_ref().unwrap().complete_loads, 1);
    assert_ne!(types.aliases()[original.0], types.aliases()[reloaded.0]);
    assert_eq!(
        TypeAnalysis::analyze(&source).unwrap().to_json().unwrap(),
        before_types
    );
    assert_eq!(emit::emit_c(&source).unwrap().code, before_c);
    assert_eq!(execute(), before);
}

#[test]
fn partial_stores_may_alias_clobbers_truncation_and_nested_loads_keep_shapes_separate() {
    for mode in 0..6 {
        let mut assignments = vec![set(4, load(1, 0, Width::U8)), store(r(0), Width::U64, r(1))];
        match mode {
            0..=2 => assignments.push(store(r(0), [Width::U8, Width::U16, Width::U32][mode], c(0))),
            3 => assignments.push(store(r(2), Width::U8, c(0))),
            _ => {}
        }
        let index = assignments.len();
        let loaded = match mode {
            4 => load(0, 0, Width::U32),
            5 => Expr::load(load(0, 0, Width::U64), Width::U64),
            _ => load(0, 0, Width::U64),
        };
        assignments.extend([set(3, loaded), set(4, load(3, 8, Width::U8))]);
        let source = one(5, assignments);
        let graph = graph(&source);
        let reloaded = value(&graph, 0, index);
        let analysis = record_shapes::analyze(&source, None).unwrap();
        assert_ne!(
            record(&analysis, initial(&graph, 1)).id,
            record(&analysis, reloaded).id,
            "mode {mode}"
        );
        assert!(memory_edges(&analysis, reloaded).is_empty(), "mode {mode}");
    }
}

#[test]
fn a_complete_overwrite_forgets_the_old_pointer_origin() {
    let source = one(
        5,
        vec![
            set(4, load(1, 0, Width::U8)),
            set(4, load(2, 8, Width::U16)),
            store(r(0), Width::U64, r(1)),
            store(r(0), Width::U64, r(2)),
            set(3, load(0, 0, Width::U64)),
            set(4, load(3, 16, Width::U32)),
        ],
    );
    let graph = graph(&source);
    let reloaded = value(&graph, 0, 4);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    assert_eq!(
        record(&analysis, initial(&graph, 2)).id,
        record(&analysis, reloaded).id
    );
    assert_ne!(
        record(&analysis, initial(&graph, 1)).id,
        record(&analysis, reloaded).id
    );
    let edges = memory_edges(&analysis, reloaded);
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].from, initial(&graph, 2));
}

#[test]
fn all_memory_phi_alternatives_need_whole_stores_including_the_entry_path() {
    for initial_path in [false, true] {
        let source = Program::new(
            0,
            6,
            vec![
                ins(
                    0,
                    vec![
                        set(5, load(1, 0, Width::U8)),
                        set(5, load(2, 8, Width::U16)),
                    ],
                    Control::Branch {
                        condition: r(4),
                        target: 2,
                    },
                ),
                ins(
                    1,
                    if initial_path {
                        vec![]
                    } else {
                        vec![store(r(0), Width::U64, r(1))]
                    },
                    Control::Jump(3),
                ),
                ins(2, vec![store(r(0), Width::U64, r(2))], Control::Jump(3)),
                ins(
                    3,
                    vec![
                        set(3, load(0, 0, Width::U64)),
                        set(5, load(3, 16, Width::U32)),
                    ],
                    Control::Return(r(5)),
                ),
            ],
        )
        .unwrap();
        let graph = graph(&source);
        let reloaded = value(&graph, 3, 0);
        let analysis = record_shapes::analyze(&source, None).unwrap();
        let a = record(&analysis, initial(&graph, 1));
        let b = record(&analysis, initial(&graph, 2));
        let loaded = record(&analysis, reloaded);
        if initial_path {
            assert_ne!(a.id, loaded.id);
            assert_ne!(b.id, loaded.id);
            assert!(memory_edges(&analysis, reloaded).is_empty());
        } else {
            assert_eq!(a.id, loaded.id);
            assert_eq!(b.id, loaded.id);
            assert_eq!(memory_edges(&analysis, reloaded).len(), 2);
        }
        assert_eq!(
            analysis.memory_flow.as_ref().unwrap().complete_loads,
            usize::from(!initial_path)
        );
    }
}

#[test]
fn predecessor_address_translation_connects_the_selected_slots_and_store_values() {
    let source = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![
                    set(7, load(2, 0, Width::U8)),
                    set(7, load(3, 8, Width::U16)),
                ],
                Control::Branch {
                    condition: r(4),
                    target: 2,
                },
            ),
            ins(
                1,
                vec![store(r(0), Width::U64, r(2)), set(5, r(0))],
                Control::Jump(3),
            ),
            ins(
                2,
                vec![store(r(1), Width::U64, r(3)), set(5, r(1))],
                Control::Jump(3),
            ),
            ins(
                3,
                vec![
                    set(6, load(5, 0, Width::U64)),
                    set(7, load(6, 16, Width::U32)),
                ],
                Control::Return(r(7)),
            ),
        ],
    )
    .unwrap();
    let types = TypeAnalysis::analyze(&source).unwrap();
    let graph = types.graph();
    let reloaded = value(graph, 3, 0);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, reloaded);
    assert_eq!(node.id, record(&analysis, initial(graph, 2)).id);
    assert_eq!(node.id, record(&analysis, initial(graph, 3)).id);
    assert_eq!(memory_edges(&analysis, reloaded).len(), 2);
    assert_ne!(
        types.aliases()[initial(graph, 2).0],
        types.aliases()[initial(graph, 3).0]
    );
}

#[test]
fn stored_nullable_select_keeps_its_pointer_source_and_null_alternative() {
    let source = one(
        5,
        vec![
            set(4, load(1, 0, Width::U32)),
            store(r(0), Width::U64, Expr::select(r(2), r(1), c(0))),
            set(3, load(0, 0, Width::U64)),
            set(4, load(3, 8, Width::U16)),
        ],
    );
    let graph = graph(&source);
    let reloaded = value(&graph, 0, 2);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, reloaded);
    assert_eq!(node.id, record(&analysis, initial(&graph, 1)).id);
    assert!(node.null_alternatives.contains(&reloaded));
    assert_eq!(memory_edges(&analysis, reloaded).len(), 1);
}

#[test]
fn an_optional_memory_limit_keeps_existing_shapes_without_partial_memory_connections() {
    fn tree(code: &mut Vec<IrInstruction>, pc: u64, depth: u32, join: u64, rhs: &Expr) {
        if depth == 0 {
            code.push(ins(
                pc,
                vec![store(r(0), Width::U64, rhs.clone())],
                Control::Jump(join),
            ));
        } else {
            let right = pc + (1 << depth);
            code.push(ins(
                pc,
                vec![],
                Control::Branch {
                    condition: binary(B::And, r(4), c(1 << (depth - 1))),
                    target: right,
                },
            ));
            tree(code, pc + 1, depth - 1, join, rhs);
            tree(code, right, depth - 1, join, rhs);
        }
    }
    for (loads, selects) in [(513, 0), (512, 64)] {
        let mut code = vec![ins(
            0,
            vec![
                set(3, load(1, 0, Width::U32)),
                set(5, r(1)),
                set(6, load(5, 4, Width::U8)),
            ],
            Control::Next,
        )];
        let mut rhs = r(1);
        for _ in 0..selects {
            rhs = Expr::select(r(4), rhs, c(0));
        }
        tree(&mut code, 1, 7, 256, &rhs);
        let mut assignments = Vec::new();
        for _ in 0..loads {
            assignments.extend([
                set(2, load(0, 0, Width::U64)),
                set(3, load(2, 16, Width::U32)),
            ]);
        }
        code.push(ins(256, assignments, Control::Return(r(3))));
        let source = Program::new(0, 7, code).unwrap();
        let graph = graph(&source);
        let analysis = record_shapes::analyze(&source, None).unwrap();
        let reason = analysis.memory_flow.as_ref().unwrap_err();
        if selects == 0 {
            assert!(reason.contains("transfer limit"), "{reason}");
        } else {
            assert!(reason.contains("candidate declined"), "{reason}");
        }
        assert!(
            analysis
                .constraints
                .iter()
                .all(|c| c.kind != ConstraintKind::Memory)
        );
        assert!(
            analysis
                .records
                .iter()
                .all(|r| r.null_alternatives.is_empty())
        );
        assert_eq!(
            record(&analysis, initial(&graph, 1)).id,
            record(&analysis, value(&graph, 0, 1)).id
        );
        assert_ne!(
            record(&analysis, initial(&graph, 1)).id,
            record(&analysis, value(&graph, 256, 0)).id
        );
        assert!(
            analysis
                .to_json()
                .unwrap()
                .contains("\"memory_flow\":{\"status\":\"unavailable\"")
        );
    }
}

#[test]
fn alias_canonical_addresses_keep_the_original_copy_and_phi_evidence() {
    let source = Program::new(
        0,
        3,
        vec![
            ins(
                0,
                vec![set(1, r(0)), set(2, load(0, 0, Width::U32))],
                Control::Jump(1),
            ),
            ins(
                1,
                vec![set(2, load(1, 8, Width::U32))],
                Control::Return(r(2)),
            ),
        ],
    )
    .unwrap();
    let types = TypeAnalysis::analyze(&source).unwrap();
    let graph = types.graph();
    let input = initial(graph, 0);
    let copied = value(graph, 0, 0);
    assert_eq!(types.aliases()[input.0], types.aliases()[copied.0]);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, input);
    assert_eq!(node.id, record(&analysis, copied).id);
    assert!(field(node, 0, Width::U32).reads);
    assert!(field(node, 8, Width::U32).reads);
    assert!(
        analysis
            .constraints
            .iter()
            .any(|c| c.kind == ConstraintKind::Copy && c.to == copied)
    );
}

#[test]
fn loop_backedges_keep_the_entry_store_and_later_whole_store_alternatives() {
    let source = Program::new(
        0,
        7,
        vec![
            ins(
                0,
                vec![
                    set(6, load(1, 0, Width::U8)),
                    set(6, load(3, 8, Width::U16)),
                    store(r(0), Width::U64, r(1)),
                    set(5, r(4)),
                ],
                Control::Next,
            ),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: binary(B::Eq, r(5), c(0)),
                    target: 3,
                },
            ),
            ins(
                2,
                vec![
                    store(r(0), Width::U64, r(3)),
                    set(5, binary(B::Sub, r(5), c(1))),
                ],
                Control::Jump(1),
            ),
            ins(
                3,
                vec![
                    set(2, load(0, 0, Width::U64)),
                    set(6, load(2, 16, Width::U32)),
                ],
                Control::Return(r(6)),
            ),
        ],
    )
    .unwrap();
    let graph = graph(&source);
    let reloaded = value(&graph, 3, 0);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, reloaded);
    assert_eq!(node.id, record(&analysis, initial(&graph, 1)).id);
    assert_eq!(node.id, record(&analysis, initial(&graph, 3)).id);
    assert_eq!(memory_edges(&analysis, reloaded).len(), 2);
}
