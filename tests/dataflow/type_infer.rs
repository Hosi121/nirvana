use crate::support::ir::c;
use crate::support::ir::r;
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::ssa::{Definition, Site};
use nirvana::type_infer::{self, AddressShape, TypeAnalysis};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
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
fn one(assignments: Vec<Assignment>, control: Control) -> Program {
    Program::new(0, 16, vec![ins(0, assignments, control)]).unwrap()
}
fn value(analysis: &TypeAnalysis, pc: u64, assignment: usize) -> usize {
    analysis
        .graph()
        .point(Site {
            instruction: pc,
            assignment: Some(assignment),
        })
        .unwrap()
        .definition
        .unwrap()
        .0
}
#[test]
fn record_fields_link_to_loaded_pointer_array_and_index_width() {
    let source = one(
        vec![
            set(1, Expr::load(r(0), Width::U32)),
            set(2, Expr::load(b(B::Add, r(0), c(8)), Width::U64)),
            set(
                3,
                Expr::load(b(B::Add, r(2), b(B::Mul, r(1), c(4))), Width::U32),
            ),
        ],
        Control::Return(r(3)),
    );
    let original = source.instructions().to_vec();
    let analysis = TypeAnalysis::analyze(&source).unwrap();
    let index = value(&analysis, 0, 0);
    let pointer = value(&analysis, 0, 1);
    let element = value(&analysis, 0, 2);
    assert_eq!(analysis.values()[index].maximum_bits, 32);
    assert_eq!(analysis.values()[element].maximum_bits, 32);
    assert!(analysis.values()[pointer].flow_uses.address_base);
    assert!(analysis.values()[index].flow_uses.address_index);
    let record = analysis
        .layouts()
        .iter()
        .find(|l| l.fields.iter().any(|f| f.offset == 8))
        .unwrap();
    assert!(
        record
            .fields
            .iter()
            .any(|f| f.offset == 0 && f.width == Width::U32)
    );
    assert!(record.fields.iter().any(|f| f.offset == 8
        && f.width == Width::U64
        && f.loaded_values.iter().any(|v| v.0 == pointer)));
    assert!(analysis.layouts().iter().any(|l| {
        l.base == analysis.aliases()[pointer]
            && l.arrays
                .iter()
                .any(|a| a.stride == 4 && a.width == Width::U32)
    }));
    assert_eq!(source.instructions(), original);
}
#[test]
fn overlapping_widths_keep_both_candidates_and_distinct_pointer_reloads() {
    let source = one(
        vec![
            set(1, Expr::load(r(0), Width::U64)),
            set(2, Expr::load(r(0), Width::U32)),
            set(3, Expr::load(r(0), Width::U64)),
            set(4, Expr::load(r(1), Width::U8)),
            set(5, Expr::load(r(3), Width::U16)),
        ],
        Control::Return(r(5)),
    );
    let a = TypeAnalysis::analyze(&source).unwrap();
    assert_ne!(a.aliases()[value(&a, 0, 0)], a.aliases()[value(&a, 0, 2)]);
    let l = a
        .layouts()
        .iter()
        .find(|l| {
            l.fields.iter().any(|f| f.width == Width::U64)
                && l.fields.iter().any(|f| f.width == Width::U32)
        })
        .unwrap();
    assert!(!l.overlaps.is_empty());
    assert!(l.fields.len() >= 2);
}
fn signed(left: Expr, right: Expr) -> Expr {
    let result = b(B::Sub, left.clone(), right.clone());
    let sign = b(B::Shr, result.clone(), c(63));
    let overflow = b(
        B::Ne,
        b(
            B::And,
            b(
                B::And,
                b(B::Xor, left.clone(), right),
                b(B::Xor, left, result),
            ),
            c(1 << 63),
        ),
        c(0),
    );
    b(B::Xor, sign, overflow)
}
#[test]
fn signed_and_unsigned_uses_coexist_without_forcing_a_declared_type() {
    let source = one(
        vec![set(2, signed(r(0), r(1))), set(3, b(B::Ult, r(0), r(1)))],
        Control::Return(b(B::Or, r(2), r(3))),
    );
    let a = TypeAnalysis::analyze(&source).unwrap();
    let id = a
        .graph()
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { register: Reg(0) }))
        .unwrap();
    assert!(a.values()[id].flow_uses.signed_compare);
    assert!(a.values()[id].flow_uses.unsigned_compare);
    assert_eq!(a.values()[id].maximum_bits, 64);
}
#[test]
fn copy_and_phi_preserve_possible_address_roles_and_loop_bounds() {
    let p = Program::new(
        0,
        16,
        vec![
            ins(
                0,
                vec![
                    set(1, Expr::load(r(7), Width::U32)),
                    set(2, r(0)),
                    set(3, c(0)),
                ],
                Control::Jump(1),
            ),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: b(B::Eq, r(1), c(0)),
                    target: 3,
                },
            ),
            ins(
                2,
                vec![
                    set(4, Expr::load(r(2), Width::U8)),
                    set(3, b(B::Add, r(3), c(1))),
                    set(1, b(B::Sub, r(1), c(1))),
                ],
                Control::Jump(1),
            ),
            ins(3, vec![], Control::Return(r(3))),
        ],
    )
    .unwrap();
    let a = TypeAnalysis::analyze(&p).unwrap();
    let initial = a
        .graph()
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { register: Reg(0) }))
        .unwrap();
    assert!(a.values()[initial].flow_uses.address_base);
    let phi = a
        .graph()
        .values
        .iter()
        .position(|d| {
            matches!(
                d,
                Definition::Phi {
                    block: 1,
                    register: Reg(2),
                    ..
                }
            )
        })
        .unwrap();
    assert_eq!(a.aliases()[phi], a.aliases()[initial]);
    let counter = a
        .graph()
        .values
        .iter()
        .position(|d| {
            matches!(
                d,
                Definition::Phi {
                    block: 1,
                    register: Reg(3),
                    ..
                }
            )
        })
        .unwrap();
    assert_eq!(a.values()[counter].maximum_bits, 64);
    let bounds: Vec<_> = a.values().iter().map(|v| v.maximum_bits).collect();
    assert!(type_infer::validate_bounds(&p, a.graph(), &bounds));
}
#[test]
fn bounds_match_actual_prefix_values_for_all_integer_operators() {
    let mut assignments = vec![
        set(2, Expr::load(r(7), Width::U8)),
        set(3, Expr::load(b(B::Add, r(7), c(4)), Width::U32)),
    ];
    for op in [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::Eq,
        B::Ne,
        B::Ult,
        B::Ule,
        B::UMulHigh,
    ] {
        assignments.push(set(4, b(op, r(2), r(3))));
    }
    assignments.extend([
        set(5, b(B::Shr, r(3), c(65))),
        set(6, b(B::Shl, r(2), c(64))),
        set(8, b(B::UMulHigh, r(2), r(3))),
    ]);
    let p = one(assignments.clone(), Control::Return(r(4)));
    let a = TypeAnalysis::analyze(&p).unwrap();
    for x in [0u64, 1, 255, u64::MAX] {
        for y in [0u64, 1, 64, 65, u64::MAX] {
            let mut memory = [0; 32];
            memory[..8].copy_from_slice(&x.to_le_bytes());
            memory[4..12].copy_from_slice(&y.to_le_bytes());
            let mut input = [0; 16];
            input[7] = 4096;
            for (i, assignment) in assignments.iter().enumerate() {
                let Place::Register(dest) = assignment.destination else {
                    panic!()
                };
                let prefix = one(
                    assignments[..=i].to_vec(),
                    Control::Return(Expr::Register(dest)),
                );
                let result = prefix
                    .execute_with_memory(&input, 4096, &memory, 1)
                    .unwrap()
                    .value;
                let bits = a.values()[value(&a, 0, i)].maximum_bits;
                assert!(
                    bits == 64 || result < (1u64 << bits),
                    "assignment={i},bits={bits},result={result:#x}"
                );
            }
        }
    }
    assert_eq!(
        a.values()[value(&a, 0, assignments.len() - 1)].maximum_bits,
        0
    );
}
#[test]
fn bound_checker_rejects_false_initial_phi_and_load_claims() {
    let p = one(
        vec![set(2, Expr::load(r(0), Width::U32))],
        Control::Return(r(2)),
    );
    let a = TypeAnalysis::analyze(&p).unwrap();
    let correct: Vec<_> = a.values().iter().map(|v| v.maximum_bits).collect();
    for (i, d) in a.graph().values.iter().enumerate() {
        if matches!(
            d,
            Definition::Initial { .. } | Definition::Phi { .. } | Definition::Assignment { .. }
        ) && correct[i] > 0
        {
            let mut wrong = correct.clone();
            wrong[i] = 0;
            assert!(!type_infer::validate_bounds(&p, a.graph(), &wrong));
        }
    }
    let mut wrong = correct.clone();
    wrong[0] = 65;
    assert!(!type_infer::validate_bounds(&p, a.graph(), &wrong));
}
#[test]
fn unknown_addresses_keep_access_evidence_and_resource_failure_is_atomic() {
    let p = one(
        vec![set(2, Expr::load(b(B::Add, r(0), r(1)), Width::U32))],
        Control::Return(r(2)),
    );
    let a = TypeAnalysis::analyze(&p).unwrap();
    assert_eq!(a.accesses().len(), 1);
    assert_eq!(a.accesses()[0].address, AddressShape::Unknown);
    let p = Program::new(0, 4097, p.instructions().to_vec()).unwrap();
    assert!(TypeAnalysis::analyze(&p).is_none());
}
#[test]
fn read_write_alias_evidence_does_not_modify_faults_or_memory() {
    let p = one(
        vec![
            set(1, Expr::load(r(0), Width::U32)),
            Assignment {
                destination: Place::Memory {
                    address: b(B::Add, r(0), c(2)),
                    width: Width::U16,
                },
                value: r(1),
            },
        ],
        Control::Return(r(1)),
    );
    let original = p.instructions().to_vec();
    let mut inputs = [0; 16];
    for pointer in [4096, 4097, 4100, 4103, u64::MAX] {
        inputs[0] = pointer;
        let before = p.run_with_memory(&inputs, 4096, &[17; 8], 8).unwrap();
        let a = TypeAnalysis::analyze(&p).unwrap();
        assert!(a.layouts().iter().any(|l| !l.overlaps.is_empty()));
        let after = p.run_with_memory(&inputs, 4096, &[17; 8], 8).unwrap();
        assert_eq!(before.status, after.status);
        assert_eq!(before.state.memory, after.state.memory);
        assert_eq!(p.instructions(), original);
    }
}

#[test]
fn loop_address_representative_keeps_the_input_phi_instead_of_a_later_copy() {
    let p = Program::new(
        0,
        16,
        vec![
            ins(0, vec![set(2, r(0))], Control::Jump(1)),
            ins(
                1,
                vec![set(1, Expr::load(r(2), Width::U8))],
                Control::Branch {
                    condition: b(B::Eq, r(1), c(0)),
                    target: 3,
                },
            ),
            ins(
                2,
                vec![
                    set(3, r(2)),
                    Assignment {
                        destination: Place::Memory {
                            address: b(B::Add, r(3), c(4)),
                            width: Width::U8,
                        },
                        value: r(1),
                    },
                    set(2, Expr::load(b(B::Add, r(2), c(8)), Width::U64)),
                ],
                Control::Jump(1),
            ),
            ins(3, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap();
    let a = TypeAnalysis::analyze(&p).unwrap();
    let phi = a
        .graph()
        .values
        .iter()
        .position(|d| {
            matches!(
                d,
                Definition::Phi {
                    block: 1,
                    register: Reg(2),
                    ..
                }
            )
        })
        .unwrap();
    let root = a.aliases()[phi];
    assert!(matches!(
        a.graph().values[root.0],
        Definition::Phi {
            block: 1,
            register: Reg(2),
            ..
        }
    ));
    let header = a
        .accesses()
        .iter()
        .find(|x| x.site.instruction == 1)
        .unwrap();
    assert!(matches!(header.address,AddressShape::Base{base,..}if base==root));
}

#[test]
fn forwarded_pointer_keeps_its_load_definition_as_the_alias_representative() {
    let p = Program::new(
        0,
        16,
        vec![
            ins(
                0,
                vec![
                    set(1, Expr::load(b(B::Add, r(0), c(8)), Width::U64)),
                    set(2, Expr::load(r(1), Width::U8)),
                ],
                Control::Jump(1),
            ),
            ins(
                1,
                vec![set(3, Expr::load(r(1), Width::U16))],
                Control::Return(r(3)),
            ),
        ],
    )
    .unwrap();
    let a = TypeAnalysis::analyze(&p).unwrap();
    let loaded = value(&a, 0, 0);
    assert_eq!(a.aliases()[loaded], nirvana::ssa::ValueId(loaded));
    assert!(a.layouts().iter().any(|l| l.base.0 == loaded
        && l.fields.iter().any(|f| f.width == Width::U8)
        && l.fields.iter().any(|f| f.width == Width::U16)));
}
