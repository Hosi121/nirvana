use nirvana::ir::{BinaryOp as B, Control, ExecutionError, Expr, IrInstruction, Program, Width};
use nirvana::simplify::{node_count, simplify};

const OPERATORS: [B; 19] = [
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
];
const BOUNDARIES: [u64; 23] = [
    0,
    1,
    2,
    3,
    7,
    8,
    9,
    10,
    31,
    32,
    63,
    64,
    65,
    127,
    128,
    255,
    256,
    u32::MAX as u64,
    1 << 32,
    (1 << 63) - 1,
    1 << 63,
    u64::MAX - 1,
    u64::MAX,
];

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn program(expression: Expr) -> Program {
    Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression),
        }],
    )
    .unwrap()
}

fn check(expression: &Expr, inputs: &[[u64; 3]]) {
    let simplified = simplify(expression);
    assert!(
        node_count(&simplified) <= node_count(expression),
        "{expression:?} -> {simplified:?}"
    );
    assert_eq!(
        simplify(&simplified),
        simplified,
        "not idempotent: {expression:?}"
    );
    let original = program(expression.clone());
    let changed = program(simplified);
    let memory: Vec<u8> = (0..32).map(|i| (i * 17) as u8).collect();
    for registers in inputs {
        for (base, memory) in [
            (0x1000, memory.as_slice()),
            (0, &[][..]),
            (u64::MAX - 7, &memory[..8]),
        ] {
            for limit in [0, 1] {
                assert_eq!(
                    original.run_with_memory(registers, base, memory, limit),
                    changed.run_with_memory(registers, base, memory, limit),
                    "expression={expression:?}, registers={registers:?}, base={base:#x}, limit={limit}"
                );
            }
        }
    }
}

fn boundary_inputs() -> Vec<[u64; 3]> {
    BOUNDARIES
        .iter()
        .enumerate()
        .map(|(index, &value)| {
            [
                value,
                BOUNDARIES[(index * 7 + 3) % BOUNDARIES.len()],
                0x1000 + index as u64,
            ]
        })
        .collect()
}

#[test]
fn all_binary_operators_fold_constants_with_u64_semantics() {
    for op in OPERATORS {
        for left in BOUNDARIES {
            for right in BOUNDARIES {
                let expression = b(op, c(left), c(right));
                let simplified = simplify(&expression);
                assert!(matches!(simplified, Expr::Const(_)));
                assert_eq!(
                    program(expression).execute(&[0; 3], 1),
                    program(simplified).execute(&[0; 3], 1)
                );
            }
        }
    }
}

#[test]
fn restores_cmp_formulas_and_inverts_boolean_comparisons() {
    let equal = b(B::Eq, r(0), r(1));
    let less = b(B::Ult, r(0), r(1));
    let cases = [
        (b(B::Eq, b(B::Sub, r(0), r(1)), c(0)), equal.clone()),
        (b(B::Ne, c(0), b(B::Sub, r(0), r(1))), b(B::Ne, r(0), r(1))),
        (b(B::Or, less.clone(), equal.clone()), b(B::Ule, r(0), r(1))),
        (
            b(B::Or, b(B::Eq, r(1), r(0)), less.clone()),
            b(B::Ule, r(0), r(1)),
        ),
        (b(B::Eq, less.clone(), c(0)), b(B::Ule, r(1), r(0))),
        (b(B::Ne, c(1), less.clone()), b(B::Ule, r(1), r(0))),
        (b(B::Xor, less, c(1)), b(B::Ule, r(1), r(0))),
        (b(B::Eq, equal, c(0)), b(B::Ne, r(0), r(1))),
    ];
    for (expression, expected) in cases {
        assert_eq!(simplify(&expression), expected);
        check(&expression, &boundary_inputs());
    }
    // The actual carry/zero expansion produced by an unsigned CMP in the lifter.
    let machine_cmp = b(
        B::Or,
        b(
            B::Or,
            b(B::Ult, r(0), c(9)),
            b(B::And, c(0), b(B::Eq, r(0), c(9))),
        ),
        b(B::Eq, b(B::Sub, b(B::Sub, r(0), c(9)), c(0)), c(0)),
    );
    assert_eq!(simplify(&machine_cmp), b(B::Ule, r(0), c(9)));
    check(&machine_cmp, &boundary_inputs());
}

#[test]
fn identities_and_coefficient_combining_do_not_assume_no_overflow() {
    let cases = [
        (b(B::Xor, r(0), r(0)), c(0)),
        (b(B::Sub, r(0), r(0)), c(0)),
        (
            b(B::Add, r(0), b(B::Mul, c(2), r(0))),
            b(B::Mul, r(0), c(3)),
        ),
        (b(B::Add, b(B::Mul, r(0), c(u64::MAX)), r(0)), c(0)),
        (b(B::Add, b(B::Add, r(0), c(u64::MAX)), c(1)), r(0)),
        (b(B::Sub, b(B::Sub, r(0), c(u64::MAX)), c(1)), r(0)),
        (
            b(B::And, b(B::And, r(0), c(255)), c(15)),
            b(B::And, r(0), c(15)),
        ),
        (b(B::Shl, r(0), c(64)), r(0)),
        (b(B::Shr, r(0), c(65)), b(B::Shr, r(0), c(1))),
        (
            b(B::Shl, r(0), b(B::And, r(1), c(127))),
            b(B::Shl, r(0), r(1)),
        ),
    ];
    for (expression, expected) in cases {
        assert_eq!(simplify(&expression), expected);
        check(&expression, &boundary_inputs());
    }
}

fn loads(expression: &Expr, output: &mut Vec<(Expr, Width)>) {
    match expression {
        Expr::Unary(_, value) => loads(value, output),
        Expr::Load { address, width } => {
            loads(address, output);
            output.push(((**address).clone(), *width));
        }
        Expr::Binary(_, left, right) => {
            loads(left, output);
            loads(right, output);
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            loads(condition, output);
            loads(taken, output);
            loads(not_taken, output);
        }
        _ => {}
    }
}

#[test]
fn faulting_operands_are_never_discarded_duplicated_or_reordered() {
    let first = Expr::load(c(0x2000), Width::U8);
    let second = Expr::load(c(0x3000), Width::U16);
    let mut cases = vec![
        b(B::Mul, first.clone(), c(0)),
        b(B::Mul, c(0), first.clone()),
        b(B::And, first.clone(), c(0)),
        b(B::Or, c(u64::MAX), first.clone()),
        b(B::Xor, first.clone(), first.clone()),
        b(B::Sub, first.clone(), first.clone()),
        b(B::Eq, first.clone(), first.clone()),
        b(B::Ult, first.clone(), c(0)),
        b(B::Ule, c(0), first.clone()),
        b(B::UMulHigh, first.clone(), c(0)),
        b(B::Add, first.clone(), b(B::Mul, first.clone(), c(2))),
        b(B::Eq, b(B::Ult, first.clone(), second.clone()), c(0)),
        b(
            B::Or,
            b(B::Ult, first.clone(), second.clone()),
            b(B::Eq, first.clone(), second.clone()),
        ),
        b(B::Eq, b(B::Sub, first.clone(), second.clone()), c(0)),
        b(B::Ne, c(0), b(B::Sub, second.clone(), first.clone())),
        b(B::Add, b(B::Add, first.clone(), c(u64::MAX)), c(1)),
    ];
    cases.push(Expr::load(Expr::load(c(0x4000), Width::U32), Width::U64));
    for expression in cases {
        let changed = simplify(&expression);
        let mut before = vec![];
        let mut after = vec![];
        loads(&expression, &mut before);
        loads(&changed, &mut after);
        assert_eq!(before, after, "{expression:?} -> {changed:?}");
        check(&expression, &boundary_inputs());
        assert!(matches!(
            program(changed).execute(&[0; 3], 1),
            Err(ExecutionError::MemoryAccess { .. })
        ));
    }
}

#[test]
fn lazy_select_preserves_condition_faults_and_skips_unselected_faults() {
    let bad = Expr::load(c(0x2000), Width::U64);
    let good = Expr::load(c(0x1000), Width::U8);
    let cases = [
        Expr::select(c(1), c(42), bad.clone()),
        Expr::select(c(0), bad.clone(), c(42)),
        Expr::select(bad.clone(), c(1), c(1)),
        Expr::select(r(0), good.clone(), bad.clone()),
        Expr::select(b(B::Eq, good.clone(), c(0)), bad.clone(), c(0)),
        Expr::select(b(B::Ne, good, c(0)), c(1), bad.clone()),
        Expr::select(r(0), bad.clone(), bad.clone()),
        Expr::select(bad.clone(), c(1), c(0)),
        Expr::select(bad, c(0), c(1)),
    ];
    for expression in cases {
        check(&expression, &boundary_inputs());
    }
    assert_eq!(
        simplify(&Expr::select(c(1), c(42), Expr::load(c(0), Width::U64))),
        c(42)
    );
}

fn next(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn generated(seed: &mut u64, depth: usize) -> Expr {
    if depth == 0 {
        return match next(seed) % 3 {
            0 => r((next(seed) % 3) as usize),
            1 => c(BOUNDARIES[(next(seed) as usize) % BOUNDARIES.len()]),
            _ => c(next(seed)),
        };
    }
    match next(seed) % 8 {
        0 => {
            let condition = generated(seed, depth - 1);
            let taken = generated(seed, depth - 1);
            let not_taken = generated(seed, depth - 1);
            Expr::select(condition, taken, not_taken)
        }
        1 => {
            let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
            let width = widths[(next(seed) % 4) as usize];
            let address = match next(seed) % 4 {
                0 => c(0x1000 + next(seed) % 32),
                1 => r(2),
                2 => c(u64::MAX - next(seed) % 8),
                _ => generated(seed, depth - 1),
            };
            Expr::load(address, width)
        }
        2 => {
            let value = generated(seed, depth - 1);
            let op = [B::Xor, B::Sub, B::Eq, B::Ne, B::And, B::Or][(next(seed) % 6) as usize];
            b(op, value.clone(), value)
        }
        3 => {
            let value = generated(seed, depth - 1);
            b(B::Add, value.clone(), b(B::Mul, value, c(2)))
        }
        _ => {
            let op = OPERATORS[(next(seed) % 13) as usize];
            let left = generated(seed, depth - 1);
            let right = generated(seed, depth - 1);
            b(op, left, right)
        }
    }
}

fn with_extensions(expression: &Expr, seed: &mut u64) -> Expr {
    let expression = match expression {
        Expr::Unary(op, value) => Expr::unary(*op, with_extensions(value, seed)),
        Expr::Binary(op, a, b) => {
            Expr::binary(*op, with_extensions(a, seed), with_extensions(b, seed))
        }
        Expr::Load { address, width } => Expr::load(with_extensions(address, seed), *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            with_extensions(condition, seed),
            with_extensions(taken, seed),
            with_extensions(not_taken, seed),
        ),
        value => value.clone(),
    };
    if next(seed) & 3 == 0 {
        let width = [Width::U8, Width::U16, Width::U32, Width::U64][(next(seed) & 3) as usize];
        Expr::unary(nirvana::ir::UnaryOp::SignExtend(width), expression)
    } else {
        expression
    }
}

fn with_divisions(expression: &Expr, seed: &mut u64) -> Expr {
    let expression = match expression {
        Expr::Unary(op, v) => Expr::unary(*op, with_divisions(v, seed)),
        Expr::Binary(op, a, z) => b(*op, with_divisions(a, seed), with_divisions(z, seed)),
        Expr::Load { address, width } => Expr::load(with_divisions(address, seed), *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            with_divisions(condition, seed),
            with_divisions(taken, seed),
            with_divisions(not_taken, seed),
        ),
        e => e.clone(),
    };
    if next(seed) & 3 != 0 {
        return expression;
    }
    let op = [B::UDiv, B::URem, B::SDiv, B::SRem][(next(seed) & 3) as usize];
    let denominator = match next(seed) % 7 {
        0 => c(0),
        1 => c(1),
        2 => c(u64::MAX),
        3 => c(1 << 63),
        4 => r(1),
        5 => Expr::load(r(2), Width::U64),
        _ => c(next(seed)),
    };
    b(op, expression, denominator)
}

#[test]
fn seeded_expression_trees_match_the_original_ir_interpreter() {
    let mut seed = 0x792c_48a9_1234_cdef;
    let mut extension_seed = 0x9f71_b382_65ca_4de0;
    let mut division_seed = 0x5639_4338_87d2_eec1;
    let inputs = boundary_inputs();
    let mut before = 0;
    let mut after = 0;
    for _ in 0..1024 {
        let expression = generated(&mut seed, 4);
        before += node_count(&expression);
        after += node_count(&simplify(&expression));
        check(&expression, &inputs);
        check(&with_extensions(&expression, &mut extension_seed), &inputs);
        check(&with_divisions(&expression, &mut division_seed), &inputs);
    }
    assert!(after < before);
    println!(
        "3072 seeded trees: original, nested extensions and total division; original nodes {before} -> {after}; 23 boundary register vectors, three memory layouts, two instruction limits"
    );
}
