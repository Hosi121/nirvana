//! Independent source-IR cases: shape compatibility never proves value equality.

use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::record_shapes::{self, Analysis, ConstraintKind, Field, Record};
use nirvana::ssa::{Definition, Site, SsaFunction, ValueId};
use nirvana::{emit, type_infer::TypeAnalysis};

use crate::support::ir::c;
use crate::support::ir::r;
fn binary(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn at(base: usize, offset: i64) -> Expr {
    binary(B::Add, r(base), c(offset as u64))
}
fn load(base: usize, offset: i64, width: Width) -> Expr {
    Expr::load(at(base, offset), width)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
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
fn one(registers: usize, assignments: Vec<Assignment>) -> Program {
    Program::new(
        0,
        registers,
        vec![ins(0, assignments, Control::Return(r(0)))],
    )
    .unwrap()
}
fn graph(source: &Program) -> SsaFunction {
    SsaFunction::build(source).unwrap()
}
fn value(graph: &SsaFunction, pc: u64, assignment: usize) -> ValueId {
    graph
        .point(Site {
            instruction: pc,
            assignment: Some(assignment),
        })
        .unwrap()
        .definition
        .unwrap()
}
fn initial(graph: &SsaFunction, register: usize) -> ValueId {
    ValueId(
        graph
            .values
            .iter()
            .position(
                |d| matches!(d, Definition::Initial { register: Reg(index) } if *index == register),
            )
            .unwrap(),
    )
}
fn record(analysis: &Analysis, value: ValueId) -> &Record {
    let found: Vec<_> = analysis
        .records
        .iter()
        .filter(|record| record.values.contains(&value))
        .collect();
    assert_eq!(found.len(), 1, "candidate containing {value:?}");
    found[0]
}
fn field(record: &Record, offset: u64, width: Width) -> &Field {
    let found: Vec<_> = record
        .fields
        .iter()
        .filter(|field| field.offset == offset && field.width == width)
        .collect();
    assert_eq!(found.len(), 1, "field {offset}:{width:?} in {record:?}");
    found[0]
}

fn linked_list() -> Program {
    Program::new(
        0,
        2,
        vec![
            ins(0, vec![], Control::Jump(1)),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: binary(B::Eq, r(0), c(0)),
                    target: 3,
                },
            ),
            ins(
                2,
                vec![
                    set(1, load(0, 0, Width::U64)),
                    set(1, load(0, 16, Width::U32)),
                    set(0, load(0, 8, Width::U64)),
                ],
                Control::Jump(1),
            ),
            ins(3, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap()
}

#[test]
fn linked_list_phi_has_a_recursive_field_and_source_evidence() {
    let source = linked_list();
    let graph = graph(&source);
    let loaded_next = value(&graph, 2, 2);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, loaded_next);
    assert!(node.values.contains(&initial(&graph, 0)));
    assert!(field(node, 0, Width::U64).reads);
    assert!(field(node, 16, Width::U32).reads);
    let next = field(node, 8, Width::U64);
    assert!(next.reads);
    assert!(next.loaded_values.contains(&loaded_next));
    assert!(next.pointer_targets.contains(&node.id));
    assert!(analysis.constraints.iter().any(|constraint| {
        constraint.kind == ConstraintKind::Phi
            && (constraint.from == loaded_next || constraint.to == loaded_next)
    }));
    assert!(node.null_tests.contains(&Site {
        instruction: 1,
        assignment: None,
    }));
}

#[test]
fn bst_select_unifies_value_alternatives_without_its_condition() {
    let source = Program::new(
        0,
        4,
        vec![
            ins(0, vec![set(1, load(3, 32, Width::U8))], Control::Jump(1)),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: binary(B::Eq, r(0), c(0)),
                    target: 3,
                },
            ),
            ins(
                2,
                vec![
                    set(1, load(0, 0, Width::U64)),
                    set(1, load(0, 8, Width::U64)),
                    set(2, load(0, 16, Width::U64)),
                    set(0, Expr::select(r(3), r(1), r(2))),
                ],
                Control::Jump(1),
            ),
            ins(3, vec![], Control::Return(r(0))),
        ],
    )
    .unwrap();
    let graph = graph(&source);
    let left = value(&graph, 2, 1);
    let right = value(&graph, 2, 2);
    let selected = value(&graph, 2, 3);
    let condition = initial(&graph, 3);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let node = record(&analysis, selected);
    assert!(node.values.contains(&initial(&graph, 0)));
    assert!(node.values.contains(&left));
    assert!(node.values.contains(&right));
    assert!(!node.values.contains(&condition));
    assert_ne!(node.id, record(&analysis, condition).id);
    assert!(field(node, 0, Width::U64).reads);
    for (offset, loaded) in [(8, left), (16, right)] {
        let child = field(node, offset, Width::U64);
        assert!(child.loaded_values.contains(&loaded));
        assert!(child.pointer_targets.contains(&node.id));
        assert!(analysis.constraints.iter().any(|constraint| {
            constraint.kind == ConstraintKind::Select
                && constraint.from == loaded
                && constraint.to == selected
                && constraint.site
                    == Some(Site {
                        instruction: 2,
                        assignment: Some(3),
                    })
        }));
    }
}

#[test]
fn shared_proven_zero_does_not_bridge_unrelated_nullable_shapes() {
    let source = one(
        7,
        vec![
            set(2, c(0)),
            set(3, Expr::select(r(4), r(0), r(2))),
            set(5, Expr::select(r(4), r(1), r(2))),
            set(6, load(3, 8, Width::U64)),
            set(6, load(5, 24, Width::U32)),
        ],
    );
    let graph = graph(&source);
    let zero = value(&graph, 0, 0);
    let selected_a = value(&graph, 0, 1);
    let selected_b = value(&graph, 0, 2);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let a = record(&analysis, selected_a);
    let b = record(&analysis, selected_b);
    assert_ne!(a.id, b.id);
    assert!(a.values.contains(&initial(&graph, 0)));
    assert!(b.values.contains(&initial(&graph, 1)));
    // These members have a NULL alternative; this list does not assert zero.
    assert!(a.null_alternatives.contains(&selected_a));
    assert!(b.null_alternatives.contains(&selected_b));
    assert!(!analysis.records.iter().any(|r| r.values.contains(&zero)));
    assert!(field(a, 8, Width::U64).pointer_targets.is_empty());
    assert!(field(b, 24, Width::U32).pointer_targets.is_empty());
}

#[test]
fn an_index_only_loaded_field_is_not_a_pointer_target() {
    let source = one(
        4,
        vec![
            set(1, load(0, 8, Width::U64)),
            set(
                2,
                Expr::load(binary(B::Add, r(3), binary(B::Mul, r(1), c(4))), Width::U32),
            ),
        ],
    );
    let graph = graph(&source);
    let index = value(&graph, 0, 0);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let root = record(&analysis, initial(&graph, 0));
    let scalar = field(root, 8, Width::U64);
    assert!(scalar.loaded_values.contains(&index));
    assert!(scalar.pointer_targets.is_empty());
    assert!(!analysis.records.iter().any(|r| r.bases.contains(&index)));
}

#[test]
fn overlapping_widths_and_out_of_range_offset_evidence_are_retained() {
    let source = one(
        2,
        vec![
            set(1, load(0, 0, Width::U64)),
            set(1, load(0, 0, Width::U32)),
            set(1, load(0, 6, Width::U16)),
            store(at(0, 0), Width::U32, r(1)),
            set(1, load(0, -1, Width::U8)),
            set(1, load(0, 4097, Width::U8)),
        ],
    );
    let graph = graph(&source);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let root = record(&analysis, initial(&graph, 0));
    assert!(field(root, 0, Width::U64).reads);
    let word = field(root, 0, Width::U32);
    assert!(word.reads && word.writes);
    assert!(field(root, 6, Width::U16).reads);
    let wide = root
        .fields
        .iter()
        .position(|f| f.offset == 0 && f.width == Width::U64)
        .unwrap();
    let narrow = root
        .fields
        .iter()
        .position(|f| f.offset == 0 && f.width == Width::U32)
        .unwrap();
    assert!(
        root.overlaps.contains(&(wide, narrow)) || root.overlaps.contains(&(narrow, wide)),
        "{root:?}"
    );
    assert!(root.excluded_offsets >= 2);
    assert!(root.fields.iter().all(|field| field.offset <= 4096));
    assert!(analysis.to_c().unwrap().contains("struct record_"));
}

#[test]
fn exact_o0_stack_reload_connects_shapes_but_unknown_clobber_is_omitted() {
    for unknown_clobber in [false, true] {
        let mut assignments = vec![
            set(2, load(0, 0, Width::U32)),
            store(at(4, -8), Width::U64, r(0)),
        ];
        if unknown_clobber {
            assignments.push(store(r(3), Width::U8, c(0)));
        }
        let reload_assignment = assignments.len();
        assignments.extend([
            set(1, load(4, -8, Width::U64)),
            set(2, load(1, 8, Width::U64)),
        ]);
        let source = one(5, assignments);
        let graph = graph(&source);
        let original = initial(&graph, 0);
        let reloaded = value(&graph, 0, reload_assignment);
        let analysis = record_shapes::analyze(&source, Some(Reg(4))).unwrap();
        let before = record(&analysis, original);
        let after = record(&analysis, reloaded);
        let relation = analysis.constraints.iter().find(|constraint| {
            constraint.kind == ConstraintKind::Stack
                && constraint.from == original
                && constraint.to == reloaded
                && constraint.site
                    == Some(Site {
                        instruction: 0,
                        assignment: Some(1), // the exact reaching source store
                    })
        });
        if unknown_clobber {
            assert_ne!(before.id, after.id);
            assert!(relation.is_none());
            assert!(analysis.skipped_stack_flows > 0);
        } else {
            assert_eq!(before.id, after.id);
            assert!(relation.is_some());
            assert!(field(before, 0, Width::U32).reads);
            assert!(field(before, 8, Width::U64).reads);
        }
    }
}

#[test]
fn a_nested_stack_load_is_not_the_assignment_root_result() {
    let source = one(
        5,
        vec![
            store(at(4, -8), Width::U64, r(0)),
            set(1, Expr::load(load(4, -8, Width::U64), Width::U64)),
            set(2, load(0, 16, Width::U32)),
            set(2, load(1, 24, Width::U32)),
        ],
    );
    let graph = graph(&source);
    let nested_result = value(&graph, 0, 1);
    let analysis = record_shapes::analyze(&source, Some(Reg(4))).unwrap();
    assert_ne!(
        record(&analysis, initial(&graph, 0)).id,
        record(&analysis, nested_result).id
    );
    assert!(!analysis.constraints.iter().any(|constraint| {
        constraint.kind == ConstraintKind::Stack && constraint.to == nested_result
    }));
}

#[test]
fn analysis_preserves_ir_value_aliases_c_and_execution_and_declines_bounds_atomically() {
    let source = linked_list();
    let instructions = source.instructions().to_vec();
    let legacy = TypeAnalysis::analyze(&source).unwrap();
    let old_json = legacy.to_json().unwrap();
    let old_aliases = legacy.aliases().to_vec();
    let old_c = emit::emit_c(&source).unwrap().code;
    let next = value(legacy.graph(), 2, 2);
    assert_ne!(
        old_aliases[initial(legacy.graph(), 0).0],
        old_aliases[next.0],
        "a recursive shape must not require exact-value aliases"
    );
    let mut memory = [0u8; 48];
    memory[0..8].copy_from_slice(&42u64.to_le_bytes());
    memory[8..16].copy_from_slice(&4120u64.to_le_bytes());
    memory[16..20].copy_from_slice(&1u32.to_le_bytes());
    memory[24..32].copy_from_slice(&9u64.to_le_bytes());
    memory[40..44].copy_from_slice(&2u32.to_le_bytes());
    let inputs = [0, 4096, 4097, 4143, u64::MAX];
    let before: Vec<_> = inputs
        .iter()
        .flat_map(|pointer| {
            [0, 1, 16].map(|budget| {
                source
                    .run_with_memory(&[*pointer, 0], 4096, &memory, budget)
                    .unwrap()
            })
        })
        .collect();
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let json = analysis.to_json().unwrap();
    assert!(json.contains("nirvana-record-shapes-v1"));
    assert!(analysis.to_c().unwrap().contains("struct record_"));
    let oversized = Program::new(0, 4097, instructions.clone()).unwrap();
    assert!(record_shapes::analyze(&oversized, None).is_err());
    assert_eq!(oversized.instructions(), instructions);
    assert_eq!(
        record_shapes::analyze(&source, None)
            .unwrap()
            .to_json()
            .unwrap(),
        json
    );
    let after: Vec<_> = inputs
        .iter()
        .flat_map(|pointer| {
            [0, 1, 16].map(|budget| {
                source
                    .run_with_memory(&[*pointer, 0], 4096, &memory, budget)
                    .unwrap()
            })
        })
        .collect();
    assert_eq!(before, after);
    assert_eq!(source.instructions(), instructions);
    let legacy_after = TypeAnalysis::analyze(&source).unwrap();
    assert_eq!(legacy_after.aliases(), old_aliases);
    assert_eq!(legacy_after.to_json().unwrap(), old_json);
    assert_eq!(emit::emit_c(&source).unwrap().code, old_c);
}

#[test]
fn unused_phi_does_not_merge_distinct_observed_pointer_shapes() {
    let source = Program::new(
        0,
        5,
        vec![
            ins(
                0,
                vec![
                    set(2, load(0, 0, Width::U32)),
                    set(2, load(1, 16, Width::U64)),
                ],
                Control::Branch {
                    condition: r(3),
                    target: 2,
                },
            ),
            ins(1, vec![set(4, r(0))], Control::Jump(3)),
            ins(2, vec![set(4, r(1))], Control::Jump(3)),
            ins(3, vec![], Control::Return(c(0))),
        ],
    )
    .unwrap();
    let graph = graph(&source);
    let analysis = record_shapes::analyze(&source, None).unwrap();
    let a = record(&analysis, initial(&graph, 0));
    let b = record(&analysis, initial(&graph, 1));
    assert_ne!(
        a.id, b.id,
        "an unobserved register phi should not bridge record types"
    );
    assert!(field(a, 0, Width::U32).reads);
    assert!(field(b, 16, Width::U64).reads);
}

#[path = "record_shapes/memory_flow.rs"]
mod memory_flow;
