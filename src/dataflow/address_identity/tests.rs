use super::*;
use crate::dataflow::type_infer::test_layouts as layouts;
use crate::model::ir::{Assignment, IrInstruction, Reg};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, a, b)
}
fn mul(a: Expr, n: u64) -> Expr {
    Expr::binary(BinaryOp::Mul, a, c(n))
}
fn shl(a: Expr, n: u64) -> Expr {
    Expr::binary(BinaryOp::Shl, a, c(n))
}
fn load(address: Expr, width: Width) -> Expr {
    Expr::load(address, width)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Register(Reg(n)),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn program(assignments: Vec<Assignment>, control: Expr) -> Program {
    Program::new(
        0,
        8,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(control),
        }],
    )
    .unwrap()
}
fn graph(source: &Program) -> (SsaFunction, Vec<ValueId>) {
    let graph = SsaFunction::build(source).unwrap();
    let ids = (0..graph.values.len()).map(ValueId).collect();
    (graph, ids)
}
fn accesses(source: &Program) -> (SsaFunction, Vec<MemoryAccess>) {
    let (graph, ids) = graph(source);
    let result = collect(source, &graph, &ids).unwrap();
    (graph, result)
}
fn definition(graph: &SsaFunction, assignment: usize) -> ValueId {
    graph
        .point(Site {
            instruction: 0,
            assignment: Some(assignment),
        })
        .unwrap()
        .definition
        .unwrap()
}
fn base(address: AddressShape) -> ValueId {
    let AddressShape::Base { base, .. } = address else {
        panic!("not a base: {address:?}")
    };
    base
}

#[test]
fn scalar_fields_preserve_widths_results_and_overlap() {
    let source = program(
        vec![
            set(2, load(r(0), Width::U32)),
            set(3, load(add(r(0), c(8)), Width::U64)),
            store(r(0), Width::U64, c(1)),
            set(4, load(r(0), Width::U32)),
        ],
        c(0),
    );
    let (graph, found) = accesses(&source);
    assert_eq!(found.len(), 4);
    assert_eq!(found[0].result, Some(definition(&graph, 0)));
    assert_eq!(found[1].result, Some(definition(&graph, 1)));
    assert_eq!(found[2].result, None);
    let grouped = layouts(&found).unwrap();
    assert_eq!(grouped.len(), 1);
    let group = &grouped[0];
    assert_eq!(group.fields.len(), 3);
    assert_eq!(group.fields[0].offset, 0);
    assert_eq!(group.fields[1].offset, 8);
    assert_eq!(
        group.fields[0].loaded_values,
        vec![definition(&graph, 0), definition(&graph, 3)]
    );
    assert!(group.fields[0].reads && !group.fields[0].writes);
    assert!(group.fields[2].writes && !group.fields[2].reads);
    assert_eq!(group.overlaps, vec![(0, 2)]);
    assert!(!group.ambiguous_intervals);
}
#[test]
fn loaded_pointer_is_an_atom_and_explicit_scaled_indices_group() {
    let source = program(
        vec![
            set(2, load(r(0), Width::U64)),
            set(3, load(add(r(2), mul(r(1), 4)), Width::U32)),
            store(add(r(2), shl(r(4), 2)), Width::U32, c(9)),
        ],
        c(0),
    );
    let (graph, found) = accesses(&source);
    let pointer = definition(&graph, 0);
    assert_eq!(base(found[1].address), pointer);
    let grouped = layouts(&found).unwrap();
    let arrays = &grouped.iter().find(|g| g.base == pointer).unwrap().arrays;
    assert_eq!(arrays.len(), 1);
    assert_eq!(arrays[0].stride, 4);
    assert_eq!(arrays[0].indices.len(), 2);
    assert_eq!(arrays[0].loaded_values, vec![definition(&graph, 1)]);
    assert!(arrays[0].reads && arrays[0].writes);
}
#[test]
fn wrapping_offsets_negative_factors_and_shift_mask_are_exact() {
    let source = program(
        vec![
            set(2, load(Expr::binary(BinaryOp::Sub, r(0), c(8)), Width::U8)),
            set(
                2,
                load(
                    add(r(0), Expr::binary(BinaryOp::Sub, c(0), mul(r(1), 4))),
                    Width::U8,
                ),
            ),
            set(2, load(add(r(0), shl(r(1), 65)), Width::U8)),
            set(2, load(add(c(u64::MAX), c(4)), Width::U8)),
            set(2, load(add(r(0), mul(r(1), 0)), Width::U8)),
        ],
        c(0),
    );
    let (_, found) = accesses(&source);
    assert!(
        matches!(found[0].address, AddressShape::Base { offset, index: None, .. } if offset == u64::MAX - 7)
    );
    assert!(
        matches!(found[1].address, AddressShape::Base { index: Some(ScaledIndex { stride, .. }), .. } if stride == 0u64.wrapping_sub(4))
    );
    assert!(matches!(
        found[2].address,
        AddressShape::Base {
            index: Some(ScaledIndex { stride: 2, .. }),
            ..
        }
    ));
    assert_eq!(found[3].address, AddressShape::Absolute(3));
    assert!(matches!(
        found[4].address,
        AddressShape::Base { index: None, .. }
    ));
}
#[test]
fn coefficient_one_sum_is_ambiguous_even_after_identity_scaling() {
    let source = program(
        vec![
            set(2, load(add(r(0), r(1)), Width::U8)),
            set(2, load(add(r(0), mul(r(1), 1)), Width::U8)),
            set(2, load(add(r(0), shl(r(1), 64)), Width::U8)),
            set(2, load(mul(r(1), 4), Width::U8)),
        ],
        c(0),
    );
    let (_, found) = accesses(&source);
    assert!(found.iter().all(|a| a.address == AddressShape::Unknown));
    assert!(layouts(&found).unwrap().is_empty());
}
#[test]
fn pure_lea_temporaries_expand_but_changed_source_versions_do_not_merge() {
    let source = program(
        vec![
            set(2, add(r(0), c(8))),
            set(3, add(r(2), mul(r(1), 4))),
            set(4, load(r(3), Width::U32)),
            set(0, load(c(4096), Width::U64)),
            set(4, load(add(r(0), c(8)), Width::U32)),
        ],
        c(0),
    );
    let (graph, found) = accesses(&source);
    assert!(matches!(
        found[0].address,
        AddressShape::Base {
            offset: 8,
            index: Some(ScaledIndex { stride: 4, .. }),
            ..
        }
    ));
    assert_ne!(base(found[0].address), base(found[2].address));
    assert_eq!(base(found[2].address), definition(&graph, 3));
}
#[test]
fn aliases_are_trusted_only_after_bounds_and_ssa_validation() {
    let source = program(
        vec![
            set(2, r(0)),
            set(3, load(r(0), Width::U32)),
            set(4, load(r(2), Width::U32)),
        ],
        c(0),
    );
    let (graph, mut ids) = graph(&source);
    let first = graph
        .point(Site {
            instruction: 0,
            assignment: Some(0),
        })
        .unwrap()
        .reads[0]
        .value;
    ids[definition(&graph, 0).0] = first;
    let found = collect(&source, &graph, &ids).unwrap();
    assert_eq!(found[0].address, found[1].address);
    assert!(collect(&source, &graph, &ids[..ids.len() - 1]).is_none());
    ids[0] = ValueId(graph.values.len());
    assert!(collect(&source, &graph, &ids).is_none());
    let mut invalid = graph.clone();
    invalid.blocks[0].points[0].reads.clear();
    assert!(
        collect(
            &source,
            &invalid,
            &(0..graph.values.len()).map(ValueId).collect::<Vec<_>>()
        )
        .is_none()
    );
}
#[test]
fn identical_pointer_loads_remain_distinct_values() {
    let source = program(
        vec![
            set(2, load(r(0), Width::U64)),
            set(3, load(r(0), Width::U64)),
            set(4, load(r(2), Width::U8)),
            set(5, load(r(3), Width::U8)),
        ],
        c(0),
    );
    let (graph, found) = accesses(&source);
    assert_eq!(base(found[2].address), definition(&graph, 0));
    assert_eq!(base(found[3].address), definition(&graph, 1));
    assert_ne!(found[2].address, found[3].address);
}
#[test]
fn nested_loads_lazy_arms_store_addresses_and_control_keep_routes() {
    let source = program(
        vec![store(
            load(r(0), Width::U64),
            Width::U8,
            Expr::select(
                load(r(1), Width::U8),
                load(r(2), Width::U16),
                add(load(r(3), Width::U32), c(1)),
            ),
        )],
        load(load(r(4), Width::U64), Width::U8),
    );
    let (_, found) = accesses(&source);
    assert_eq!(found.len(), 7);
    assert_eq!(
        (found[0].operand, found[0].path.as_slice()),
        (Operand::Destination, &[PathEdge::Address][..])
    );
    assert_eq!(found[1].path, vec![PathEdge::Condition]);
    assert_eq!(found[2].path, vec![PathEdge::Taken]);
    assert_eq!(found[3].path, vec![PathEdge::NotTaken, PathEdge::Left]);
    assert_eq!(found[4].kind, AccessKind::Write);
    assert_eq!(found[4].address, AddressShape::Unknown);
    assert_eq!(found[5].operand, Operand::Control);
    assert_eq!(found[5].path, vec![PathEdge::Address]);
    assert_eq!(found[6].address, AddressShape::Unknown);
    assert!(found.iter().all(|a| a.result.is_none()));
    assert_eq!(found[0].site.assignment, Some(0));
    assert_eq!(found[6].site.assignment, None);
}
#[test]
fn unmodified_root_load_is_the_only_load_with_result_id() {
    let source = program(
        vec![
            set(2, add(load(r(0), Width::U32), c(0))),
            set(3, load(load(r(1), Width::U64), Width::U32)),
        ],
        c(0),
    );
    let (graph, found) = accesses(&source);
    assert_eq!(found[0].result, None);
    assert_eq!(found[1].result, None);
    assert_eq!(found[2].result, Some(definition(&graph, 1)));
}
#[test]
fn interval_endpoint_overflow_is_visible_and_negative_offsets_overlap() {
    let source = program(
        vec![
            set(2, load(add(r(0), c(i64::MAX as u64)), Width::U64)),
            set(3, load(add(r(0), c(u64::MAX - 3)), Width::U64)),
            set(4, load(r(0), Width::U32)),
        ],
        c(0),
    );
    let (_, found) = accesses(&source);
    let groups = layouts(&found).unwrap();
    assert!(groups[0].ambiguous_intervals);
    assert_eq!(groups[0].overlaps, vec![(1, 2)]);
}
#[test]
fn unsupported_address_still_preserves_load_evidence() {
    let source = program(
        vec![
            set(
                2,
                load(Expr::binary(BinaryOp::And, r(0), c(255)), Width::U8),
            ),
            set(3, load(Expr::select(c(1), r(0), r(1)), Width::U8)),
        ],
        c(0),
    );
    let (_, found) = accesses(&source);
    assert_eq!(found.len(), 2);
    assert!(found.iter().all(|a| a.address == AddressShape::Unknown));
}
#[test]
fn access_and_term_caps_decline_without_partial_results() {
    let source = program(
        (0..MAX_ACCESSES / 2 + 1)
            .map(|_| store(c(0), Width::U8, load(c(0), Width::U8)))
            .collect(),
        c(0),
    );
    let (graph, ids) = graph(&source);
    assert!(collect(&source, &graph, &ids).is_none());
    let mut form = Affine::default();
    let mut budget = Budget(MAX_WORK);
    for n in 0..MAX_TERMS {
        form = form
            .add(Affine::atom(ValueId(n)), false, &mut budget)
            .unwrap();
    }
    assert!(
        form.add(Affine::atom(ValueId(MAX_TERMS)), false, &mut budget)
            .is_err()
    );
    let access = MemoryAccess {
        site: Site {
            instruction: 0,
            assignment: None,
        },
        operand: Operand::Control,
        path: vec![],
        kind: AccessKind::Read,
        width: Width::U8,
        address: AddressShape::Absolute(0),
        result: None,
    };
    assert!(layouts(&vec![access; MAX_ACCESSES + 1]).is_none());
}
#[test]
fn layout_work_and_overlap_limits_decline_atomically() {
    fn evidence(base: usize, offset: u64, width: Width) -> MemoryAccess {
        MemoryAccess {
            site: Site {
                instruction: 0,
                assignment: None,
            },
            operand: Operand::Control,
            path: vec![],
            kind: AccessKind::Read,
            width,
            address: AddressShape::Base {
                base: ValueId(base),
                offset,
                index: None,
            },
            result: None,
        }
    }
    // More than eight million pair comparisons, despite no intersections.
    let sparse: Vec<_> = (0..4096).map(|n| evidence(0, n * 8, Width::U8)).collect();
    assert!(layouts(&sparse).is_none());
    // Many bounded groups keep pair work small but exceed total overlap
    // output capacity. No incomplete prefix of groups may escape.
    let mut dense = Vec::new();
    for base in 0..12 {
        for offset in 0..128 {
            for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
                dense.push(evidence(base, offset, width));
            }
        }
    }
    assert!(layouts(&dense).is_none());
    assert!(Affine::atom(ValueId(0)).scale(4, &mut Budget(0)).is_err());
}
#[test]
fn affine_cancellation_and_literal_products_follow_modular_arithmetic() {
    let source = program(
        vec![
            set(
                2,
                load(
                    Expr::binary(
                        BinaryOp::Sub,
                        add(r(0), mul(r(1), u64::MAX)),
                        mul(r(1), u64::MAX),
                    ),
                    Width::U8,
                ),
            ),
            set(2, load(add(r(0), mul(r(1), 1u64 << 63)), Width::U8)),
            set(2, load(mul(c(u64::MAX), 2), Width::U8)),
            set(2, load(shl(c(3), 65), Width::U8)),
        ],
        c(0),
    );
    let (_, found) = accesses(&source);
    assert!(matches!(
        found[0].address,
        AddressShape::Base {
            offset: 0,
            index: None,
            ..
        }
    ));
    assert!(
        matches!(found[1].address, AddressShape::Base { index: Some(ScaledIndex { stride, .. }), .. } if stride == 1u64 << 63)
    );
    assert_eq!(found[2].address, AddressShape::Absolute(u64::MAX - 1));
    assert_eq!(found[3].address, AddressShape::Absolute(6));
}
fn and(a: Expr, mask: u64) -> Expr {
    Expr::binary(BinaryOp::And, a, c(mask))
}

#[test]
fn mask_elision_requires_the_entire_atom_bit_hull() {
    let source = program(
        vec![
            set(2, load(and(r(0), 255), Width::U8)),
            set(2, load(and(r(0), 247), Width::U8)),
            set(2, load(and(r(0), 256), Width::U8)),
            set(2, load(and(add(r(0), c(1)), 255), Width::U8)),
        ],
        c(0),
    );
    let (graph, ids) = graph(&source);
    let input = graph
        .point(Site {
            instruction: 0,
            assignment: Some(0),
        })
        .unwrap()
        .reads[0]
        .value;
    let mut bits = vec![64; graph.values.len()];
    bits[input.0] = 8;
    let found = collect_with_bounds(&source, &graph, &ids, &bits).unwrap();
    assert!(
        matches!(found[0].address, AddressShape::Base { base, offset: 0, index: None } if base == input)
    );
    assert!(
        found[1..]
            .iter()
            .all(|a| a.address == AddressShape::Unknown)
    );
    bits[input.0] = 64;
    assert!(
        collect_with_bounds(&source, &graph, &ids, &bits)
            .unwrap()
            .iter()
            .all(|a| a.address == AddressShape::Unknown)
    );
    bits[input.0] = 0;
    assert!(matches!(
        collect_with_bounds(&source, &graph, &ids, &bits).unwrap()[2].address,
        AddressShape::Base { .. }
    ));
    bits[input.0] = 65;
    assert!(collect_with_bounds(&source, &graph, &ids, &bits).is_none());
    assert!(collect_with_bounds(&source, &graph, &ids, &bits[..bits.len() - 1]).is_none());
}
#[test]
fn loaded_u32_proof_links_masked_index_to_loaded_pointer_layout() {
    let source = program(
        vec![
            set(2, load(add(r(0), c(8)), Width::U64)),
            set(3, load(r(1), Width::U32)),
            set(
                4,
                load(add(r(2), mul(and(r(3), u32::MAX as u64), 4)), Width::U32),
            ),
        ],
        c(0),
    );
    let (graph, ids) = graph(&source);
    let pointer = definition(&graph, 0);
    let index = definition(&graph, 1);
    let mut bits = vec![64; graph.values.len()];
    bits[index.0] = 32;
    let found = collect_with_bounds(&source, &graph, &ids, &bits).unwrap();
    assert_eq!(
        found[2].address,
        AddressShape::Base {
            base: pointer,
            offset: 0,
            index: Some(ScaledIndex {
                value: index,
                stride: 4
            })
        }
    );
    assert_eq!(
        layouts(&found)
            .unwrap()
            .iter()
            .find(|l| l.base == pointer)
            .unwrap()
            .arrays[0]
            .stride,
        4
    );
    bits[index.0] = 64;
    assert_eq!(
        collect_with_bounds(&source, &graph, &ids, &bits).unwrap()[2].address,
        AddressShape::Unknown
    );
}
#[test]
fn mask_identity_and_definition_expansion_are_pure_and_canonical() {
    let source = program(
        vec![
            set(2, and(r(0), 255)),
            set(3, load(r(2), Width::U8)),
            set(4, load(and(add(r(0), mul(r(1), 4)), u64::MAX), Width::U8)),
            set(5, load(and(load(r(0), Width::U64), u64::MAX), Width::U8)),
        ],
        c(0),
    );
    let (graph, ids) = graph(&source);
    let input = graph
        .point(Site {
            instruction: 0,
            assignment: Some(0),
        })
        .unwrap()
        .reads[0]
        .value;
    let mut bits = vec![64; graph.values.len()];
    bits[input.0] = 8;
    let found = collect_with_bounds(&source, &graph, &ids, &bits).unwrap();
    assert_eq!(base(found[0].address), input);
    assert!(matches!(
        found[1].address,
        AddressShape::Base {
            index: Some(ScaledIndex { stride: 4, .. }),
            ..
        }
    ));
    assert_eq!(found[3].address, AddressShape::Unknown);
    let copies = program(
        vec![set(2, r(0)), set(3, load(and(r(2), 255), Width::U8))],
        c(0),
    );
    let (graph, mut ids) = self::graph(&copies);
    let root = graph
        .point(Site {
            instruction: 0,
            assignment: Some(0),
        })
        .unwrap()
        .reads[0]
        .value;
    let copy = definition(&graph, 0);
    ids[copy.0] = root;
    let mut bits = vec![64; graph.values.len()];
    bits[copy.0] = 8;
    assert_eq!(
        collect_with_bounds(&copies, &graph, &ids, &bits).unwrap()[0].address,
        AddressShape::Unknown
    );
}
