use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::stack_role::StackRoles;
use nirvana::structure::{Node, StructuredFunction};
use nirvana::value_role::ValueRole;

use crate::support::native;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn address(offset: i64) -> Expr {
    b(BinaryOp::Add, r(0), c(offset as u64))
}
fn load(offset: i64) -> Expr {
    Expr::load(address(offset), Width::U64)
}
fn set(id: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(id).into(),
        value,
    }
}
fn store(offset: i64, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: address(offset),
            width: Width::U64,
        },
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
fn sum(extra: Vec<Assignment>) -> Program {
    let mut body = extra;
    body.extend([
        set(3, load(-16)),
        set(4, b(BinaryOp::Add, r(3), r(1))),
        store(-16, r(4)),
        set(5, b(BinaryOp::Add, r(1), c(1))),
        store(-8, r(5)),
    ]);
    Program::new(
        0,
        9,
        vec![
            ins(
                0,
                vec![store(-8, c(0)), store(-16, c(0)), store(-24, r(6))],
                Control::Next,
            ),
            ins(
                1,
                vec![set(1, load(-8)), set(2, load(-24))],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(1), r(2)),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Return(load(-16))),
            ins(3, body, Control::Jump(1)),
        ],
    )
    .unwrap()
}
fn analyze(program: &Program) -> (StackRoles, Vec<Node>) {
    let tree = StructuredFunction::recover(program).unwrap();
    let nodes = tree.body().to_vec();
    (StackRoles::analyze(program, Reg(0), &nodes).unwrap(), nodes)
}

#[test]
fn stack_reload_sum_roles_and_inputs_remain_unchanged() {
    let program = sum(vec![]);
    let before = program.instructions().to_vec();
    let tree = StructuredFunction::recover(&program).unwrap();
    let nodes = tree.body().to_vec();
    let roles = StackRoles::analyze(&program, Reg(0), &nodes).unwrap();
    for id in [1, 5] {
        assert_eq!(roles.register_role(Reg(id)), Some(ValueRole::Counter));
    }
    for id in [3, 4] {
        assert_eq!(roles.register_role(Reg(id)), Some(ValueRole::Accumulator));
    }
    assert_eq!(roles.register_role(Reg(2)), Some(ValueRole::Limit));
    assert_eq!(roles.offset_role(-8), Some(ValueRole::Counter));
    assert_eq!(roles.offset_role(-16), Some(ValueRole::Accumulator));
    assert_eq!(roles.offset_role(-24), Some(ValueRole::Limit));
    let counter_web = roles.register_web(Reg(1)).unwrap();
    assert_eq!(roles.register_web(Reg(5)), Some(counter_web));
    assert_ne!(roles.register_web(Reg(3)), Some(counter_web));
    assert_eq!(roles.web_location(counter_web).unwrap().offset, -8);
    assert_eq!(roles.web_location(usize::MAX), None);
    assert_eq!(program.instructions(), before);
    assert_eq!(nodes, tree.body());
}

#[test]
fn unambiguous_copies_receive_candidates_but_reused_registers_do_not() {
    let program = sum(vec![set(7, r(1)), set(8, c(3)), set(8, c(4))]);
    let (roles, _) = analyze(&program);
    assert_eq!(roles.register_role(Reg(7)), Some(ValueRole::Counter));
    assert_eq!(roles.register_role(Reg(8)), None);
}

#[test]
fn unknown_alias_and_partial_overlap_prevent_spurious_provenance() {
    let unknown = Assignment {
        destination: Place::Memory {
            address: r(7),
            width: Width::U8,
        },
        value: c(1),
    };
    let partial = Assignment {
        destination: Place::Memory {
            address: address(-15),
            width: Width::U8,
        },
        value: c(1),
    };
    for write in [unknown, partial] {
        let program = sum(vec![write]);
        let (roles, _) = analyze(&program);
        assert_eq!(roles.register_role(Reg(3)), None);
        assert_eq!(roles.offset_role(-16), None);
    }
}

#[test]
fn different_lifetimes_at_one_offset_do_not_force_a_common_name() {
    let program = Program::new(
        0,
        9,
        vec![
            ins(0, vec![store(-8, c(0))], Control::Next),
            ins(
                1,
                vec![set(1, load(-8))],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(1), r(6)),
                    target: 3,
                },
            ),
            ins(2, vec![store(-8, c(0))], Control::Jump(4)),
            ins(
                3,
                vec![set(2, b(BinaryOp::Add, r(1), c(1))), store(-8, r(2))],
                Control::Jump(1),
            ),
            ins(
                4,
                vec![set(3, load(-8))],
                Control::Branch {
                    condition: r(7),
                    target: 6,
                },
            ),
            ins(5, vec![], Control::Return(r(3))),
            ins(
                6,
                vec![set(4, b(BinaryOp::Xor, r(3), r(8))), store(-8, r(4))],
                Control::Jump(4),
            ),
        ],
    )
    .unwrap();
    let (roles, _) = analyze(&program);
    assert_eq!(roles.register_role(Reg(1)), Some(ValueRole::Counter));
    assert_eq!(roles.register_role(Reg(3)), Some(ValueRole::Accumulator));
    assert_eq!(roles.offset_role(-8), None);
}

#[test]
fn unannotated_control_loads_stay_opaque() {
    let program = sum(vec![]);
    let nodes = vec![Node::Loop(vec![
        Node::If {
            condition: b(BinaryOp::Ult, load(-8), load(-24)),
            taken: vec![],
            not_taken: vec![Node::Break],
        },
        Node::Step {
            address: 3,
            assignments: program.instructions()[3].assignments.clone(),
        },
        Node::Continue,
    ])];
    let roles = StackRoles::analyze(&program, Reg(0), &nodes).unwrap();
    assert_ne!(roles.register_role(Reg(1)), Some(ValueRole::Counter));
    assert_ne!(roles.offset_role(-24), Some(ValueRole::Limit));
}

#[test]
fn mismatched_step_annotations_and_oversized_trees_fail_conservatively() {
    let program = sum(vec![]);
    let nodes = vec![Node::Loop(vec![
        Node::Step {
            address: 99,
            assignments: vec![set(8, load(-8))],
        },
        Node::Continue,
    ])];
    let roles = StackRoles::analyze(&program, Reg(0), &nodes).unwrap();
    assert_eq!(roles.register_role(Reg(8)), None);
    assert!(StackRoles::analyze(&program, Reg(99), &[]).is_none());
    assert!(StackRoles::analyze(&program, Reg(0), &vec![Node::Break; 24_001]).is_none());
    let mut deep = Node::Continue;
    for _ in 0..66 {
        deep = Node::Loop(vec![deep]);
    }
    assert!(StackRoles::analyze(&program, Reg(0), &[deep]).is_none());
}

#[test]
fn compiled_o0_sum_exposes_spilled_roles_without_rewriting_executable_inputs() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("sum.o");
    native::object(
        &native::fixture_root().join("cases/sum.c"),
        &object,
        "-O0",
        "fixture",
    );
    let lifted = nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
    let webs = nirvana::web::split(reduced.program()).unwrap();
    let program = webs.program();
    let before = program.instructions().to_vec();
    let tree = StructuredFunction::recover(program).unwrap();
    let nodes = tree.body().to_vec();
    let roles = StackRoles::analyze(program, Reg(nirvana::x86::RSP), &nodes).unwrap();
    let observed: Vec<_> = (0..program.register_count())
        .filter_map(|id| roles.register_role(Reg(id)))
        .collect();
    for expected in [ValueRole::Counter, ValueRole::Accumulator, ValueRole::Limit] {
        assert!(
            observed.contains(&expected),
            "missing {expected:?}: {roles:?}"
        );
    }
    assert_eq!(program.instructions(), before);
    assert_eq!(tree.body(), nodes);
    let output = nirvana::readable::emit_readable_c_with_options(
        &lifted.program,
        nirvana::readable::ReadableOptions {
            stack_register: Some(Reg(nirvana::x86::RSP)),
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: true,
        },
    )
    .unwrap();
    assert!(output.local_plan.verified_storage_pools > 0);
    assert_eq!(output.local_plan.storage_verification_fallbacks, 0);
    let limits: Vec<_> = output
        .locals
        .iter()
        .filter(|local| local.role == Some(ValueRole::Limit))
        .collect();
    assert_eq!(limits.len(), 1, "spilled limit should share one C local");
    let stack = output.stack_roles.as_ref().unwrap();
    assert!(
        limits[0]
            .registers
            .iter()
            .filter(|&&reg| stack.register_role(reg) == Some(ValueRole::Limit))
            .count()
            >= 2,
        "at least two separately lifted reloads must share that local"
    );
}

#[test]
fn direct_memory_rhs_and_lazy_faulting_values_remain_naming_only() {
    let mut instructions = sum(vec![]).instructions().to_vec();
    instructions[3].assignments = vec![
        set(3, load(-16)),
        store(-16, b(BinaryOp::Add, r(3), r(1))),
        store(-8, b(BinaryOp::Add, load(-8), c(1))),
    ];
    let program = Program::new(0, 9, instructions).unwrap();
    let (roles, _) = analyze(&program);
    assert_eq!(roles.register_role(Reg(1)), Some(ValueRole::Counter));
    assert_eq!(roles.register_role(Reg(3)), Some(ValueRole::Accumulator));
    assert_eq!(roles.offset_role(-8), Some(ValueRole::Counter));

    let program = sum(vec![
        set(
            8,
            Expr::select(r(7), Expr::load(c(u64::MAX), Width::U64), load(-8)),
        ),
        store(-16, r(8)),
    ]);
    let before = program.instructions().to_vec();
    let (roles, nodes) = analyze(&program);
    assert_eq!(roles.register_role(Reg(8)), None);
    assert_eq!(program.instructions(), before);
    assert_eq!(StructuredFunction::recover(&program).unwrap().body(), nodes);
}
