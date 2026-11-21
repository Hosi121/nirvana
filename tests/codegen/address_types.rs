use nirvana::address_types::register_hints;
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use std::collections::BTreeMap;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn add(left: Expr, right: Expr) -> Expr {
    b(B::Add, left, right)
}
fn load(address: Expr, width: Width) -> Expr {
    Expr::load(address, width)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
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
fn one(assignments: Vec<Assignment>, control: Expr) -> Program {
    Program::new(0, 16, vec![ins(0, assignments, Control::Return(control))]).unwrap()
}
fn expected(pairs: &[(usize, Width)]) -> BTreeMap<usize, Width> {
    pairs.iter().copied().collect()
}

#[test]
fn loaded_pointer_to_indexed_read_has_width_hint_and_keeps_source() {
    let program = one(
        vec![
            set(2, load(r(0), Width::U64)),
            set(3, load(add(r(2), b(B::Mul, r(1), c(4))), Width::U32)),
        ],
        r(3),
    );
    let original = program.instructions().to_vec();
    assert_eq!(
        register_hints(&program),
        expected(&[(0, Width::U64), (2, Width::U32)])
    );
    assert_eq!(program.instructions(), original);
}

#[test]
fn each_access_width_can_describe_guest_addresses() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let program = one(
            vec![
                store(r(0), width, c(42)),
                set(1, load(add(r(0), c(16)), width)),
            ],
            r(1),
        );
        assert_eq!(register_hints(&program), expected(&[(0, width)]));
    }
}

#[test]
fn mixed_element_widths_and_overlapping_layouts_decline() {
    for (offset, width) in [(8, Width::U16), (2, Width::U32)] {
        let program = one(
            vec![
                set(1, load(r(0), Width::U32)),
                set(2, load(add(r(0), c(offset)), width)),
            ],
            c(0),
        );
        assert!(register_hints(&program).is_empty());
    }
    let program = one(
        vec![set(1, load(add(r(0), c(i64::MAX as u64)), Width::U32))],
        c(0),
    );
    assert!(register_hints(&program).is_empty());
}

#[test]
fn raw_register_scalar_lifetime_prevents_pointer_hint() {
    let program = one(
        vec![
            set(2, load(c(4096), Width::U64)),
            set(3, load(r(2), Width::U32)),
            set(2, c(7)),
            set(4, add(r(2), c(1))),
        ],
        r(4),
    );
    assert!(register_hints(&program).is_empty());
}

#[test]
fn unread_initial_and_unused_scalar_definition_do_not_veto_later_pointer() {
    let program = one(
        vec![
            set(2, c(7)),
            set(2, load(c(4096), Width::U64)),
            set(3, load(r(2), Width::U32)),
            set(2, c(123)),
        ],
        r(3),
    );
    assert_eq!(register_hints(&program), expected(&[(2, Width::U32)]));
}

#[test]
fn all_read_lifetimes_must_have_the_same_width() {
    for second in [Width::U16, Width::U32] {
        let program = one(
            vec![
                set(2, load(c(4096), Width::U64)),
                set(3, load(r(2), Width::U32)),
                set(2, load(c(4104), Width::U64)),
                set(3, load(r(2), second)),
            ],
            r(3),
        );
        assert_eq!(
            register_hints(&program),
            if second == Width::U32 {
                expected(&[(2, second)])
            } else {
                BTreeMap::new()
            }
        );
    }
}

#[test]
fn aliases_and_copies_share_exact_evidence() {
    let program = one(
        vec![set(2, r(0)), set(3, r(2)), set(4, load(r(3), Width::U16))],
        r(4),
    );
    assert_eq!(
        register_hints(&program),
        expected(&[(0, Width::U16), (2, Width::U16), (3, Width::U16)])
    );
    let program = one(
        vec![
            set(2, r(0)),
            set(3, load(r(0), Width::U16)),
            set(4, add(r(2), c(1))),
        ],
        r(4),
    );
    assert!(register_hints(&program).is_empty());
}

#[test]
fn pure_address_construction_passes_but_scalar_or_dead_construction_does_not() {
    let program = one(
        vec![
            set(2, add(r(0), c(8))),
            set(3, add(r(2), b(B::Mul, r(1), c(4)))),
            set(4, load(r(3), Width::U32)),
        ],
        r(4),
    );
    assert_eq!(register_hints(&program), expected(&[(0, Width::U32)]));
    for control in [r(2), c(0)] {
        let program = one(
            vec![set(1, load(r(0), Width::U32)), set(2, add(r(0), c(8)))],
            control,
        );
        assert!(register_hints(&program).is_empty());
    }
}

#[test]
fn index_bitwise_shift_comparison_and_return_roles_decline() {
    for value in [
        b(B::And, r(0), c(255)),
        b(B::Shr, r(0), c(4)),
        b(B::Eq, r(0), c(0)),
        b(B::Ult, r(0), c(42)),
        b(B::Mul, r(0), r(1)),
    ] {
        let program = one(vec![set(2, load(r(0), Width::U32)), set(3, value)], r(3));
        assert!(register_hints(&program).is_empty());
    }
    let program = one(
        vec![
            set(2, load(r(0), Width::U32)),
            set(3, load(add(r(1), b(B::Mul, r(0), c(4))), Width::U32)),
        ],
        r(3),
    );
    assert_eq!(register_hints(&program), expected(&[(1, Width::U32)]));
    let program = one(vec![set(2, load(r(0), Width::U32))], r(0));
    assert!(register_hints(&program).is_empty());
}

#[test]
fn unknown_address_use_vetoes_other_exact_evidence() {
    for address in [add(r(0), r(1)), b(B::Mul, r(0), c(4))] {
        let program = one(
            vec![
                set(2, load(r(0), Width::U32)),
                set(3, load(address, Width::U32)),
            ],
            r(3),
        );
        assert!(register_hints(&program).is_empty());
    }
    let program = one(vec![set(2, load(add(r(0), r(1)), Width::U32))], r(2));
    assert!(register_hints(&program).is_empty());
}

#[test]
fn nested_load_addresses_and_store_operands_have_separate_roles() {
    let program = one(
        vec![store(c(4096), Width::U32, load(r(0), Width::U32))],
        load(r(1), Width::U16),
    );
    assert_eq!(
        register_hints(&program),
        expected(&[(0, Width::U32), (1, Width::U16)])
    );
    let program = one(
        vec![set(
            2,
            load(
                add(load(r(0), Width::U64), b(B::Mul, r(1), c(4))),
                Width::U32,
            ),
        )],
        r(2),
    );
    assert_eq!(register_hints(&program), expected(&[(0, Width::U64)]));
    let program = one(vec![store(load(r(0), Width::U64), Width::U32, c(0))], c(0));
    assert_eq!(register_hints(&program), expected(&[(0, Width::U64)]));
}

#[test]
fn trivial_loop_phi_can_preserve_copy_alias() {
    let program = Program::new(
        0,
        16,
        vec![
            ins(0, vec![set(2, r(0)), set(1, c(0))], Control::Jump(1)),
            ins(
                1,
                vec![set(3, load(r(2), Width::U32))],
                Control::Branch {
                    condition: b(B::Eq, r(1), c(3)),
                    target: 3,
                },
            ),
            ins(2, vec![set(1, add(r(1), c(1)))], Control::Jump(1)),
            ins(3, vec![], Control::Return(r(3))),
        ],
    )
    .unwrap();
    assert_eq!(
        register_hints(&program),
        expected(&[(0, Width::U32), (2, Width::U32)])
    );
}

#[test]
fn nontrivial_phi_and_register_grouping_do_not_invent_a_common_root() {
    let program = Program::new(
        0,
        16,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            ins(1, vec![set(0, load(c(4096), Width::U64))], Control::Jump(3)),
            ins(2, vec![set(0, load(c(4104), Width::U64))], Control::Jump(3)),
            ins(
                3,
                vec![set(2, load(r(0), Width::U32))],
                Control::Return(r(2)),
            ),
        ],
    )
    .unwrap();
    assert!(register_hints(&program).is_empty());
}

#[test]
fn no_reads_no_layout_and_unavailable_analysis_have_no_hints() {
    for program in [
        one(vec![], c(0)),
        one(vec![set(0, c(4096))], c(0)),
        one(vec![], r(0)),
        Program::new(0, 4097, vec![ins(0, vec![], Control::Return(c(0)))]).unwrap(),
    ] {
        assert!(register_hints(&program).is_empty());
    }
}
