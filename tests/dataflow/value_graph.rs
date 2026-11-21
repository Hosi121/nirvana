use crate::support::ir::c;
use crate::support::ir::r;
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::value_graph::{Point, ValueGraph, ValueNode};
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn point(n: usize) -> Point {
    Point {
        instruction: 0,
        assignment: n,
    }
}
fn one(assignments: Vec<Assignment>) -> Program {
    Program::new(
        0,
        8,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(r(0)),
        }],
    )
    .unwrap()
}
#[test]
fn copies_intern_pure_syntax_and_overwrites_preserve_snapshots() {
    let expr = Expr::binary(B::Add, r(0), c(3));
    let p = one(vec![
        set(1, r(0)),
        set(2, expr),
        set(0, c(4)),
        set(3, Expr::binary(B::Add, r(1), c(3))),
        set(4, Expr::binary(B::Add, r(0), c(3))),
        set(5, r(2)),
    ]);
    let graph = ValueGraph::build(&p).unwrap();
    let b = graph.block(0).unwrap();
    assert_eq!(b.value_before(Reg(0), point(0)), b.rhs(point(0)));
    assert_eq!(b.rhs(point(1)), b.rhs(point(3)));
    assert_ne!(b.rhs(point(1)), b.rhs(point(4)));
    assert_eq!(b.rhs(point(1)), b.rhs(point(5)));
    assert_eq!(b.definition_before(Reg(0), point(2)), None);
    assert_eq!(
        b.definition_before(Reg(0), point(3)).unwrap().point,
        point(2)
    );
    assert!(b.value_before(Reg(9), point(0)).is_none());
    assert!(b.value_before(Reg(0), point(99)).is_none());
}
#[test]
fn every_load_syntax_is_unique_but_captured_copies_are_equal() {
    let load = Expr::load(r(0), Width::U64);
    let p = one(vec![
        set(1, load.clone()),
        set(2, load.clone()),
        set(3, r(1)),
        set(4, Expr::select(c(0), load.clone(), r(1))),
        set(5, Expr::select(c(0), load, r(1))),
    ]);
    let g = ValueGraph::build(&p).unwrap();
    let b = g.block(0).unwrap();
    assert_ne!(b.rhs(point(0)), b.rhs(point(1)));
    assert_eq!(b.rhs(point(0)), b.rhs(point(2)));
    assert_ne!(b.rhs(point(3)), b.rhs(point(4)));
    assert!(matches!(
        b.node(b.rhs(point(0)).unwrap()),
        Some(ValueNode::CapturedLoad(_))
    ));
}
#[test]
fn before_definition_and_loop_entry_start_with_arbitrary_values() {
    let p = Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(1, c(77))],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(2, r(1)), set(1, c(77))],
                control: Control::Branch {
                    condition: r(0),
                    target: 1,
                },
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(2)),
            },
        ],
    )
    .unwrap();
    let g = ValueGraph::build(&p).unwrap();
    let b = g.block(1).unwrap();
    let p = Point {
        instruction: 1,
        assignment: 0,
    };
    assert!(b.definition_before(Reg(1), p).is_none());
    assert_eq!(b.node(b.rhs(p).unwrap()), Some(ValueNode::Initial(Reg(1))));
}
#[test]
fn resource_excess_returns_no_partial_graph() {
    let p = Program::new(
        0,
        4097,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(c(0)),
        }],
    )
    .unwrap();
    assert!(ValueGraph::build(&p).is_none());
    let p = one((0..16385).map(|_| set(1, c(1))).collect());
    assert!(ValueGraph::build(&p).is_none());
    let mut deep = r(0);
    for _ in 0..129 {
        deep = Expr::binary(B::Add, deep, c(1));
    }
    assert!(ValueGraph::build(&one(vec![set(1, deep)])).is_none());
}
#[test]
fn pure_dag_values_agree_with_ir_execution_after_each_write() {
    use nirvana::value_graph::{BlockValues, ValueId};
    fn eval(block: &BlockValues, id: ValueId, input: &[u64]) -> u64 {
        match block.node(id).unwrap() {
            ValueNode::Initial(reg) => input[reg.0],
            ValueNode::Constant(n) => n,
            ValueNode::Unary(op, value) => {
                crate::support::ir::unary_value(op, eval(block, value, input))
            }
            ValueNode::Select(c, t, n) => {
                eval(block, if eval(block, c, input) != 0 { t } else { n }, input)
            }
            ValueNode::Binary(op, a, b) => {
                let a = eval(block, a, input);
                let b = eval(block, b, input);
                match op {
                    B::Add => a.wrapping_add(b),
                    B::Sub => a.wrapping_sub(b),
                    B::Mul => a.wrapping_mul(b),
                    B::And => a & b,
                    B::Or => a | b,
                    B::Xor => a ^ b,
                    B::Shl => a.wrapping_shl((b & 63) as u32),
                    B::Shr => a.wrapping_shr((b & 63) as u32),
                    B::Eq => (a == b) as u64,
                    B::Ne => (a != b) as u64,
                    B::Ult => (a < b) as u64,
                    B::Ule => (a <= b) as u64,
                    B::UMulHigh => ((a as u128 * b as u128) >> 64) as u64,
                    B::SMulHigh => ((i128::from(a as i64) * i128::from(b as i64)) >> 64) as u64,
                    B::AShr => ((a as i64) >> (b & 63)) as u64,
                    B::UDiv | B::URem | B::SDiv | B::SRem => {
                        crate::support::ir::division_value(op, a, b)
                    }
                }
            }
            ValueNode::CapturedLoad(_) => panic!("pure oracle"),
        }
    }
    let mut assignments = vec![set(1, r(0)), set(0, c(9))];
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
        B::SMulHigh,
        B::AShr,
        B::UDiv,
        B::URem,
        B::SDiv,
        B::SRem,
    ] {
        assignments.push(set(2, Expr::binary(op, r(1), r(4))));
        assignments.push(set(3, Expr::select(r(5), r(2), r(0))));
        assignments.push(set(1, Expr::binary(B::Add, r(1), c(7))));
    }
    let graph = ValueGraph::build(&one(assignments.clone())).unwrap();
    let block = graph.block(0).unwrap();
    for (x, y, cond) in [
        (0, 0, 0),
        (u64::MAX, 64, 1),
        (1, 65, 0),
        (0x8765432112345678, 0xfedcba9876543210, 1),
    ] {
        let mut input = [0; 8];
        input[0] = x;
        input[4] = y;
        input[5] = cond;
        for (i, assignment) in assignments.iter().enumerate() {
            let Place::Register(destination) = assignment.destination else {
                panic!()
            };
            let prefix = one(assignments[..=i].to_vec());
            let execution = prefix.execute(&input, 1).unwrap();
            assert_eq!(
                eval(block, block.rhs(point(i)).unwrap(), &input),
                execution.registers[destination.0]
            );
        }
    }
}
#[test]
fn stores_between_loads_do_not_equate_captured_values() {
    use nirvana::ir::Place;
    let p = one(vec![
        set(1, Expr::load(r(0), Width::U64)),
        Assignment {
            destination: Place::Memory {
                address: r(0),
                width: Width::U64,
            },
            value: c(42),
        },
        set(2, Expr::load(r(0), Width::U64)),
        set(3, r(1)),
    ]);
    let graph = ValueGraph::build(&p).unwrap();
    let block = graph.block(0).unwrap();
    assert_ne!(block.rhs(point(0)), block.rhs(point(2)));
    assert_eq!(block.rhs(point(0)), block.rhs(point(3)));
    let mut input = [0; 8];
    input[0] = 0x1000;
    let run = p
        .execute_with_memory(&input, 0x1000, &17u64.to_le_bytes(), 1)
        .unwrap();
    assert_eq!(
        (run.registers[1], run.registers[2], run.registers[3]),
        (17, 42, 17)
    );
}

#[test]
fn control_points_use_final_register_versions_and_keep_load_occurrences_distinct() {
    let load = Expr::load(r(0), Width::U64);
    let mut instructions = one(vec![set(1, load.clone()), set(0, c(17)), set(2, r(0))])
        .instructions()
        .to_vec();
    instructions[0].control = Control::Return(Expr::binary(B::Add, r(2), load));
    let p = Program::new(0, 8, instructions).unwrap();
    let legacy = ValueGraph::build(&p).unwrap();
    let extended = ValueGraph::build_with_control(&p).unwrap();
    let a = legacy.block(0).unwrap();
    let b = extended.block(0).unwrap();
    assert_eq!(a.points(), b.points());
    assert!(a.control().is_none());
    let control = b.control().unwrap();
    assert_eq!(control.point, point(3));
    assert_eq!(b.order(point(3)), Some(3));
    assert_eq!(b.all_points().count(), 4);
    assert_eq!(b.value_before(Reg(0), point(3)), b.rhs(point(1)));
    assert_eq!(b.value_before(Reg(2), point(3)), b.rhs(point(1)));
    let Some(ValueNode::Binary(B::Add, left, read)) = b.node(control.value) else {
        panic!()
    };
    assert_eq!(Some(left), b.rhs(point(1)));
    assert_ne!(Some(read), b.rhs(point(0)));
    assert!(matches!(b.node(read), Some(ValueNode::CapturedLoad(_))));
    assert_eq!(b.origin(read), Some(point(3)));
    assert_eq!(b.origin(left), Some(point(1)));
    assert_eq!(
        b.nodes().take(a.nodes().count()).collect::<Vec<_>>(),
        a.nodes().collect::<Vec<_>>()
    );
}
