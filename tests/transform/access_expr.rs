use nirvana::access_expr::{self, IndexedAddress, recognize, validate};
use nirvana::ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, Width};

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn indexed(base: Expr, index: Expr, stride: u64) -> Expr {
    b(B::Add, base, b(B::Mul, index, c(stride)))
}
fn program(expression: &Expr) -> Program {
    Program::new(
        0,
        8,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression.clone()),
        }],
    )
    .unwrap()
}

// Independent observation of actual reads, respecting lazy evaluation. Static
// syntax reads below additionally check the arms which this input did not take.
fn observe(expression: &Expr, input: &[u64], reads: &mut Vec<usize>) -> u64 {
    match expression {
        Expr::Unary(op, value) => {
            crate::support::ir::unary_value(*op, observe(value, input, reads))
        }
        Expr::Const(value) => *value,
        Expr::Register(Reg(id)) => {
            reads.push(*id);
            input[*id]
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            if observe(condition, input, reads) != 0 {
                observe(taken, input, reads)
            } else {
                observe(not_taken, input, reads)
            }
        }
        Expr::Binary(op, left, right) => {
            let left = observe(left, input, reads);
            let right = observe(right, input, reads);
            match op {
                B::Add => left.wrapping_add(right),
                B::Sub => left.wrapping_sub(right),
                B::Mul => left.wrapping_mul(right),
                B::And => left & right,
                B::Or => left | right,
                B::Xor => left ^ right,
                B::Shl => left.wrapping_shl((right & 63) as u32),
                B::Shr => left.wrapping_shr((right & 63) as u32),
                B::Eq => u64::from(left == right),
                B::Ne => u64::from(left != right),
                B::Ult => u64::from(left < right),
                B::Ule => u64::from(left <= right),
                B::UMulHigh => ((u128::from(left) * u128::from(right)) >> 64) as u64,
                B::SMulHigh => ((i128::from(left as i64) * i128::from(right as i64)) >> 64) as u64,
                B::AShr => ((left as i64) >> (right & 63)) as u64,
            }
        }
        Expr::Load { .. } => panic!("test oracle expects pure expressions"),
    }
}

fn syntax_reads(expression: &Expr, reads: &mut Vec<usize>) {
    match expression {
        Expr::Unary(_, value) => syntax_reads(value, reads),
        Expr::Register(Reg(id)) => reads.push(*id),
        Expr::Const(_) => {}
        Expr::Binary(_, left, right) => {
            syntax_reads(left, reads);
            syntax_reads(right, reads);
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            syntax_reads(condition, reads);
            syntax_reads(taken, reads);
            syntax_reads(not_taken, reads);
        }
        Expr::Load { .. } => panic!("test oracle expects pure expressions"),
    }
}

fn compare(expression: &Expr, inputs: &[[u64; 8]]) {
    let view = recognize(expression).expect("generated indexed expression should match");
    assert!(validate(expression, &view));
    assert!(!validate(
        expression,
        &IndexedAddress {
            stride: view.stride.wrapping_add(1),
            ..view
        }
    ));
    assert!(!validate(
        expression,
        &IndexedAddress {
            offset: view.offset.wrapping_add(1),
            ..view
        }
    ));
    let mut before = Vec::new();
    let mut after = Vec::new();
    syntax_reads(expression, &mut before);
    syntax_reads(view.base, &mut after);
    syntax_reads(view.index, &mut after);
    before.sort_unstable();
    after.sort_unstable();
    assert_eq!(
        before, after,
        "including duplicate reads and every lazy arm"
    );

    let original = program(expression);
    let base = program(view.base);
    let index = program(view.index);
    for input in inputs {
        let expected = original.execute(input, 1).unwrap().value;
        let actual = base
            .execute(input, 1)
            .unwrap()
            .value
            .wrapping_add(
                index
                    .execute(input, 1)
                    .unwrap()
                    .value
                    .wrapping_mul(view.stride),
            )
            .wrapping_add(view.offset);
        assert_eq!(expected, actual);
        let mut before = Vec::new();
        let mut after = Vec::new();
        assert_eq!(observe(expression, input, &mut before), expected);
        let base = observe(view.base, input, &mut after);
        let index = observe(view.index, input, &mut after);
        assert_eq!(
            base.wrapping_add(index.wrapping_mul(view.stride))
                .wrapping_add(view.offset),
            expected
        );
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after, "executed register read multiplicities");
    }
}

const BOUNDARIES: [u64; 10] = [
    0,
    1,
    2,
    63,
    64,
    255,
    u32::MAX as u64,
    1 << 63,
    u64::MAX - 1,
    u64::MAX,
];

fn boundary_inputs() -> Vec<[u64; 8]> {
    let mut inputs = Vec::new();
    for (i, value) in BOUNDARIES.into_iter().enumerate() {
        inputs.push(std::array::from_fn(|j| {
            BOUNDARIES[(i + j) % BOUNDARIES.len()]
        }));
        inputs.push([value; 8]);
    }
    inputs
}

#[test]
fn commuted_terms_literal_scales_offsets_and_borrowed_operands_are_exact() {
    let inputs = boundary_inputs();
    for stride in [2, 3, 4, 8, 127, 1 << 63, u64::MAX] {
        for expression in [
            indexed(r(0), r(1), stride),
            b(B::Add, b(B::Mul, c(stride), r(1)), r(0)),
            b(B::Add, c(u64::MAX), indexed(r(0), r(1), stride)),
            b(B::Sub, indexed(r(0), r(1), stride), c(7)),
            b(
                B::Add,
                b(B::Sub, b(B::Add, c(u64::MAX), r(0)), c(3)),
                b(B::Add, b(B::Mul, r(1), c(stride)), c(11)),
            ),
        ] {
            compare(&expression, &inputs);
        }
    }
    let expression = b(B::Sub, indexed(r(0), b(B::Add, r(1), c(3)), 8), c(5));
    let Expr::Binary(_, sum, _) = &expression else {
        unreachable!()
    };
    let Expr::Binary(_, base, product) = &**sum else {
        unreachable!()
    };
    let Expr::Binary(_, index, _) = &**product else {
        unreachable!()
    };
    let view = recognize(&expression).unwrap();
    assert!(std::ptr::eq(view.base, &**base));
    assert!(std::ptr::eq(view.index, &**index));
    assert_eq!((view.stride, view.offset), (8, 0_u64.wrapping_sub(5)));
    assert_eq!(
        view.index,
        &b(B::Add, r(1), c(3)),
        "offset remains inside borrowed index"
    );
    compare(&expression, &inputs);
    let huge_id = indexed(r(usize::MAX), r(usize::MAX - 1), 8);
    assert!(
        recognize(&huge_id).is_some(),
        "no register-ID-sized allocation"
    );
}

#[test]
fn shift_mask_and_nested_scale_products_obey_modulo64() {
    let inputs = boundary_inputs();
    for count in [1, 2, 63, 65, 127, u64::MAX] {
        let expression = b(B::Add, r(0), b(B::Shl, r(1), c(count)));
        assert_eq!(
            recognize(&expression).unwrap().stride,
            1_u64 << (count & 63)
        );
        compare(&expression, &inputs);
    }
    for count in [0, 64, 128] {
        assert!(recognize(&b(B::Add, r(0), b(B::Shl, r(1), c(count)))).is_none());
    }
    let expression = indexed(r(0), b(B::Mul, c(u64::MAX), r(1)), 2);
    assert_eq!(recognize(&expression).unwrap().stride, u64::MAX - 1);
    compare(&expression, &inputs);
    for expression in [
        indexed(r(0), r(1), 0),
        indexed(r(0), r(1), 1),
        indexed(r(0), b(B::Mul, r(1), c(u64::MAX)), u64::MAX),
        indexed(r(0), b(B::Shl, r(1), c(63)), 2),
    ] {
        assert!(
            recognize(&expression).is_none(),
            "zero/one effective scale declines"
        );
    }
}

#[test]
fn duplicate_reads_are_preserved_and_ambiguous_or_cancelled_terms_decline() {
    let inputs = boundary_inputs();
    compare(&indexed(r(0), r(0), 8), &inputs);
    compare(
        &indexed(b(B::Sub, r(0), r(0)), b(B::Xor, r(1), r(1)), 8),
        &inputs,
    );
    for expression in [
        b(B::Add, b(B::Add, r(0), r(0)), b(B::Mul, r(1), c(8))),
        b(B::Add, indexed(r(0), r(1), 8), b(B::Mul, r(1), c(8))),
        b(B::Add, indexed(r(0), r(1), 8), b(B::Sub, r(2), r(2))),
        b(B::Add, indexed(r(0), r(1), 8), b(B::Mul, r(2), c(0))),
        b(B::Add, b(B::Mul, r(0), c(4)), b(B::Mul, r(1), c(8))),
        b(B::Add, r(0), r(1)),
        b(B::Sub, r(0), b(B::Mul, r(1), c(8))),
        indexed(c(4096), r(1), 8),
        indexed(r(0), c(2), 8),
    ] {
        assert!(
            recognize(&expression).is_none(),
            "conservative ambiguity policy: {expression:?}"
        );
    }
}

#[test]
fn validator_rejects_cloned_wrong_overlapping_and_missing_read_views() {
    let expression = indexed(r(0), r(0), 8);
    let view = recognize(&expression).unwrap();
    let cloned_base = view.base.clone();
    let cloned_index = view.index.clone();
    let cloned_address = expression.clone();
    for forged in [
        IndexedAddress {
            base: &cloned_base,
            ..view
        },
        IndexedAddress {
            index: &cloned_index,
            ..view
        },
        IndexedAddress {
            base: view.index,
            index: view.base,
            ..view
        },
        IndexedAddress {
            base: view.index,
            ..view
        },
        IndexedAddress {
            base: &expression,
            ..view
        },
        IndexedAddress { stride: 4, ..view },
        IndexedAddress { stride: 0, ..view },
        IndexedAddress { stride: 1, ..view },
        IndexedAddress { offset: 1, ..view },
    ] {
        assert!(!validate(&expression, &forged));
    }
    assert!(!validate(&cloned_address, &view));
    for extra in [b(B::Sub, r(2), r(2)), b(B::Mul, r(2), c(0)), r(0)] {
        let expression = b(B::Add, indexed(r(0), r(1), 8), extra);
        let Expr::Binary(_, original, _) = &expression else {
            unreachable!()
        };
        let view = recognize(original).unwrap();
        assert!(
            !validate(&expression, &view),
            "unknown reads cannot cancel out of the certificate"
        );
    }
    let expression = b(B::Sub, r(0), r(1));
    let Expr::Binary(_, base, index) = &expression else {
        unreachable!()
    };
    assert!(
        !validate(
            &expression,
            &IndexedAddress {
                base,
                index,
                stride: u64::MAX,
                offset: 0
            }
        ),
        "a negated term has no explicit literal scale"
    );
}

#[test]
fn all_loads_including_untaken_lazy_arms_decline_before_matching() {
    let hidden = Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8));
    for expression in [
        indexed(Expr::load(r(2), Width::U64), r(1), 8),
        indexed(r(0), Expr::load(r(2), Width::U64), 8),
        indexed(hidden.clone(), r(1), 8),
        indexed(r(0), hidden.clone(), 8),
        indexed(
            Expr::select(Expr::load(r(2), Width::U8), r(0), r(0)),
            r(1),
            8,
        ),
        b(B::Add, indexed(r(0), r(1), 8), hidden),
    ] {
        assert!(recognize(&expression).is_none());
        assert!(!validate(
            &expression,
            &IndexedAddress {
                base: &expression,
                index: &expression,
                stride: 8,
                offset: 0
            }
        ));
    }
    let expression = b(
        B::Add,
        indexed(r(0), r(1), 8),
        Expr::select(c(1), c(0), Expr::load(r(2), Width::U64)),
    );
    let Expr::Binary(_, original, _) = &expression else {
        unreachable!()
    };
    assert!(
        !validate(&expression, &recognize(original).unwrap()),
        "valid pointers do not bypass whole-tree purity"
    );
}

fn balanced(leaves: usize) -> Expr {
    if leaves == 1 {
        return c(0);
    }
    b(B::Xor, balanced(leaves / 2), balanced(leaves - leaves / 2))
}

// Avoid making an intentionally very deep test fixture's destructor recursive.
fn drop_iteratively(expression: Expr) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            Expr::Unary(_, value) => pending.push(*value),
            Expr::Binary(_, left, right) => pending.extend([*left, *right]),
            Expr::Load { address, .. } => pending.push(*address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([*condition, *taken, *not_taken]),
            _ => {}
        }
    }
}

#[test]
fn whole_tree_depth_and_node_limits_precede_matching_or_external_operand_inspection() {
    let mut deep = r(0);
    for _ in 0..10_000 {
        deep = b(B::Xor, deep, c(0));
    }
    let ordinary = indexed(r(0), r(1), 8);
    let ordinary_view = recognize(&ordinary).unwrap();
    assert!(!validate(
        &ordinary,
        &IndexedAddress {
            base: &deep,
            ..ordinary_view
        }
    ));
    let expression = indexed(deep, r(1), 8);
    assert!(recognize(&expression).is_none());
    assert!(!validate(&expression, &ordinary_view));
    drop_iteratively(expression);

    let expression = indexed(b(B::Xor, balanced(access_expr::MAX_NODES), r(0)), r(1), 8);
    assert!(recognize(&expression).is_none());
    assert!(!validate(&expression, &ordinary_view));
    let mut at_limit = r(0);
    for _ in 0..access_expr::MAX_DEPTH - 2 {
        at_limit = b(B::Xor, at_limit, c(0));
    }
    assert!(recognize(&indexed(at_limit, r(1), 8)).is_some());
}

struct Generator(u64);
impl Generator {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn expression(&mut self, depth: usize) -> Expr {
        if depth == 0 {
            return if self.next() & 1 == 0 {
                r(self.next() as usize % 8)
            } else {
                c(self.next())
            };
        }
        if self.next().is_multiple_of(8) {
            return Expr::select(r(2), self.expression(depth - 1), self.expression(depth - 1));
        }
        let ops = [
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
        ];
        let op = ops[self.next() as usize % ops.len()];
        b(op, self.expression(depth - 1), self.expression(depth - 1))
    }
}

#[test]
fn generated_pure_operands_match_ir_execution_and_preserve_all_read_multiplicities() {
    let mut generator = Generator(0x8b9f_08de_4397_a601);
    let mut checks = 0;
    for case in 0..512 {
        // Opaque top-level operators keep each generated operand intact; Select
        // exercises both lazy branches across zero/nonzero condition inputs.
        let base = Expr::select(
            r(2),
            generator.expression(2),
            b(B::Sub, r(0), generator.expression(2)),
        );
        let index = b(B::Xor, r(1), generator.expression(2));
        let stride = [2, 3, 8, 16, 127, u64::MAX, 1 << 63][case % 7];
        let product = if case & 1 == 0 {
            b(B::Mul, c(stride), index)
        } else {
            b(B::Mul, index, c(stride))
        };
        let offset = generator.next();
        let expression = match case % 4 {
            0 => b(B::Add, b(B::Add, c(offset), base), product),
            1 => b(B::Sub, b(B::Add, product, base), c(offset)),
            2 => b(B::Add, base, b(B::Add, c(offset), product)),
            _ => b(B::Add, b(B::Sub, product, c(offset)), base),
        };
        let mut inputs = boundary_inputs();
        for _ in 0..12 {
            let mut input = std::array::from_fn(|_| generator.next());
            input[2] = generator.next() & 1;
            inputs.push(input);
        }
        compare(&expression, &inputs);
        checks += inputs.len();
    }
    assert_eq!(checks, 16_384);
}
