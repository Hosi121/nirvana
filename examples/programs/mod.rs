use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg};

pub const NAMES: &[&str] = &[
    "diamond",
    "nested",
    "early-return",
    "sum",
    "nested-loops",
    "irreducible",
    "shared-tail",
    "multi-exit",
    "multi-exit-prefix",
    "nested-multi-exit",
    "loop-returns",
    "nonlocal-exit",
    "copy-limit",
    "arithmetic",
];

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn assign(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn branch(condition: Expr, target: u64) -> Control {
    Control::Branch { condition, target }
}

pub fn named(name: &str) -> Option<Program> {
    use BinaryOp::*;
    use Control::{Jump, Next, Return};
    let instructions = match name {
        "diamond" => vec![
            (vec![], branch(b(Ult, r(0), c(10)), 2)),
            (vec![assign(1, b(Add, r(0), c(20)))], Jump(3)),
            (vec![assign(1, b(Mul, r(0), c(3)))], Next),
            (vec![], Return(r(1))),
        ],
        "nested" => vec![
            (vec![], branch(b(Ult, r(0), c(10)), 4)),
            (vec![], branch(b(And, r(0), c(1)), 3)),
            (vec![assign(1, b(Add, r(0), c(1)))], Jump(5)),
            (vec![assign(1, b(Add, r(0), c(2)))], Jump(5)),
            (vec![assign(1, b(Mul, r(0), c(3)))], Jump(5)),
            (vec![], Return(r(1))),
        ],
        "early-return" => vec![
            (vec![], branch(b(Eq, r(0), c(0)), 2)),
            (vec![], Return(b(Add, r(0), c(1)))),
            (vec![], Return(c(42))),
        ],
        "sum" => vec![
            (
                vec![
                    assign(1, b(And, r(0), c(7))),
                    assign(2, c(0)),
                    assign(3, c(0)),
                ],
                Next,
            ),
            (vec![], branch(b(Ult, r(2), r(1)), 3)),
            (vec![], Return(r(3))),
            (
                vec![assign(3, b(Add, r(3), r(2))), assign(2, b(Add, r(2), c(1)))],
                Jump(1),
            ),
        ],
        "nested-loops" => vec![
            (
                vec![
                    assign(0, b(And, r(0), c(3))),
                    assign(1, c(0)),
                    assign(3, c(0)),
                ],
                Next,
            ),
            (vec![], branch(b(Ult, r(1), r(0)), 3)),
            (vec![], Return(r(3))),
            (vec![assign(2, c(0))], Next),
            (vec![], branch(b(Ult, r(2), c(3)), 6)),
            (vec![assign(1, b(Add, r(1), c(1)))], Jump(1)),
            (
                vec![
                    assign(3, b(Add, r(3), b(Add, r(1), r(2)))),
                    assign(2, b(Add, r(2), c(1))),
                ],
                Jump(4),
            ),
        ],
        "irreducible" => vec![
            (vec![assign(1, c(0))], branch(b(And, r(0), c(1)), 2)),
            (vec![assign(0, b(Sub, r(0), c(1)))], Jump(2)),
            (
                vec![assign(1, b(Add, r(1), c(1)))],
                branch(b(Ult, r(1), c(5)), 1),
            ),
            (vec![], Return(b(Xor, r(0), r(1)))),
        ],
        "shared-tail" => vec![
            (vec![], branch(b(And, r(0), c(1)), 3)),
            (vec![], branch(b(And, r(0), c(2)), 4)),
            (vec![assign(2, c(111))], Return(r(2))),
            (vec![assign(2, c(222))], Jump(4)),
            (vec![], Return(b(Add, r(2), r(0)))),
        ],
        "multi-exit" => vec![
            (vec![assign(1, c(0))], Next),
            (vec![], branch(b(And, r(0), c(1)), 5)),
            (
                vec![assign(1, b(Add, r(1), c(1)))],
                branch(b(Ult, r(1), c(3)), 1),
            ),
            (vec![assign(2, c(100))], Jump(6)),
            (vec![], Return(c(0))),
            (vec![assign(2, c(200))], Jump(6)),
            (vec![], Return(b(Add, r(2), r(1)))),
        ],
        "multi-exit-prefix" => vec![
            (vec![assign(1, b(Add, r(1), c(1)))], branch(c(1), 1)),
            (vec![], branch(b(And, r(0), c(1)), 5)),
            (vec![], branch(b(Ult, r(1), c(3)), 0)),
            (vec![assign(2, c(100))], Jump(6)),
            (vec![], Return(c(0))),
            (vec![assign(2, c(200))], Jump(6)),
            (vec![], Return(b(Add, r(2), r(1)))),
        ],
        "nested-multi-exit" => vec![
            (
                vec![
                    assign(0, b(And, r(0), c(3))),
                    assign(1, c(0)),
                    assign(3, c(0)),
                ],
                Next,
            ),
            (vec![], branch(b(Ult, r(1), r(0)), 3)),
            (vec![], Return(r(3))),
            (vec![assign(2, c(0))], Next),
            (vec![], branch(b(Ult, r(2), c(3)), 6)),
            (vec![assign(1, b(Add, r(1), c(1)))], Jump(1)),
            (
                vec![assign(3, b(Add, r(3), r(2))), assign(2, b(Add, r(2), c(1)))],
                branch(b(Eq, r(2), c(2)), 8),
            ),
            (vec![], Jump(4)),
            (vec![assign(3, b(Add, r(3), c(10)))], Jump(5)),
        ],
        "loop-returns" => vec![
            (vec![assign(1, c(0))], Next),
            (vec![], branch(b(Eq, r(0), c(0)), 5)),
            (
                vec![assign(1, b(Add, r(1), c(1)))],
                branch(b(Ult, r(1), c(3)), 1),
            ),
            (vec![], Return(b(Add, r(1), c(7)))),
            (vec![], Return(c(0))),
            (vec![], Return(c(42))),
        ],
        "nonlocal-exit" => vec![
            (
                vec![
                    assign(0, b(And, r(0), c(3))),
                    assign(1, c(0)),
                    assign(3, c(0)),
                ],
                Next,
            ),
            (vec![], branch(b(Ult, r(1), r(0)), 3)),
            (vec![], Return(r(3))),
            (vec![assign(2, c(0))], Next),
            (vec![], branch(b(Ult, r(2), c(3)), 6)),
            (vec![assign(1, b(Add, r(1), c(1)))], Jump(1)),
            (
                vec![assign(3, b(Add, r(3), r(2))), assign(2, b(Add, r(2), c(1)))],
                branch(b(Eq, r(2), c(2)), 2),
            ),
            (vec![], Jump(4)),
        ],
        "copy-limit" => vec![
            (vec![], branch(b(And, r(0), c(1)), 5)),
            (vec![], branch(b(And, r(0), c(2)), 6)),
            (vec![], branch(b(And, r(0), c(4)), 7)),
            (vec![], Return(c(111))),
            (vec![], Return(c(0))),
            (vec![assign(2, c(10))], Jump(8)),
            (vec![assign(2, c(20))], Jump(8)),
            (vec![assign(2, c(30))], Jump(8)),
            (vec![], Return(b(Add, r(2), r(0)))),
        ],
        "arithmetic" => vec![(
            vec![
                assign(2, b(Add, r(0), r(1))),
                assign(3, b(Sub, r(0), r(1))),
                assign(2, b(Mul, r(2), r(3))),
                assign(3, b(Or, r(0), r(1))),
                assign(2, b(Xor, r(2), r(3))),
                assign(3, b(And, r(0), r(1))),
                assign(2, b(Shl, r(2), r(1))),
                assign(3, b(Shr, r(3), r(1))),
                assign(
                    2,
                    b(Add, r(2), b(Add, b(Eq, r(0), r(1)), b(Ne, r(0), r(1)))),
                ),
                assign(
                    3,
                    b(Add, r(3), b(Add, b(Ult, r(0), r(1)), b(Ule, r(0), r(1)))),
                ),
            ],
            Return(b(Xor, r(2), r(3))),
        )],
        _ => return None,
    };
    let instructions = instructions
        .into_iter()
        .enumerate()
        .map(|(address, (assignments, control))| IrInstruction {
            address: address as u64,
            size: 1,
            assignments,
            control,
        })
        .collect();
    Some(Program::new(0, 4, instructions).expect("valid example IR"))
}
