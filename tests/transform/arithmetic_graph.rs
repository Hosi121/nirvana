use crate::support::ir::c;
use crate::support::ir::r;
use crate::support::native;
use nirvana::{
    arithmetic_graph::{ArithmeticFacts, numerator, validate_quotient, validate_remainder},
    ir::*,
    value_graph::Point,
};
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
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
fn single(assignments: Vec<Assignment>) -> Program {
    Program::new(
        0,
        8,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(r(3)),
        }],
    )
    .unwrap()
}
fn magic(d: u64, s: u32) -> u64 {
    u64::try_from((1u128 << (64 + s)).div_ceil(d as u128)).unwrap()
}
fn packet(d: u64, s: u32) -> Vec<Assignment> {
    vec![
        set(1, b(BinaryOp::UMulHigh, c(magic(d, s)), r(0))),
        set(2, b(BinaryOp::Shr, r(1), c(s as u64))),
        set(
            3,
            b(
                BinaryOp::Sub,
                r(0),
                b(
                    BinaryOp::Add,
                    b(BinaryOp::And, r(1), c(u64::MAX << s)),
                    r(2),
                ),
            ),
        ),
    ]
}
fn check(p: &Program, q: usize, rem: usize) -> ArithmeticFacts {
    let facts = ArithmeticFacts::analyze(p).unwrap();
    assert_eq!(facts.quotients().len(), q, "{:#?}", p.instructions());
    assert_eq!(facts.remainders().len(), rem, "{:#?}", p.instructions());
    for proof in facts.quotients() {
        assert!(validate_quotient(p, proof));
    }
    for proof in facts.remainders() {
        assert!(validate_remainder(p, proof));
    }
    facts
}
fn samples(d: u64) -> Vec<u64> {
    let mut xs = vec![0, 1, d - 1, d, d + 1, u64::MAX, u64::MAX - 1];
    let mut seed = 0x349ccf6c1234abcd_u64;
    for _ in 0..256 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        xs.push(seed);
    }
    xs
}
#[test]
fn division_and_remainder_without_a_store_keeper_match_ir_arithmetic() {
    for (d, s) in [(3, 1), (5, 2), (9, 3), (17, 4), (33, 5)] {
        let p = single(packet(d, s));
        let facts = check(&p, 1, 1);
        let q = facts.quotients()[0];
        assert_eq!(
            (
                q.divisor,
                q.point,
                q.high_definition,
                q.quotient,
                q.high_register
            ),
            (d, point(1), point(0), Reg(2), Reg(1))
        );
        let Expr::Binary(BinaryOp::UMulHigh, _, actual) = &p.instructions()[0].assignments[0].value
        else {
            panic!()
        };
        assert!(std::ptr::eq(numerator(&p, &q).unwrap(), &**actual));
        for x in samples(d) {
            let mut input = [0; 8];
            input[0] = x;
            assert_eq!(p.execute(&input, 8).unwrap().value, x % d);
            let mut instructions = p.instructions().to_vec();
            instructions[0].control = Control::Return(r(2));
            let qprogram = Program::new(0, 8, instructions).unwrap();
            assert_eq!(qprogram.execute(&input, 8).unwrap().value, x / d);
        }
    }
}
#[test]
fn materialized_products_and_historical_q_h_x_survive_overwrites_and_copies() {
    for (d, s) in [(3, 1), (5, 2), (9, 3)] {
        let mut a = packet(d, s);
        a.pop();
        a.extend([
            set(4, r(0)),
            set(5, r(2)),
            set(6, r(1)),
            set(0, c(99)),
            set(1, c(101)),
            set(2, c(103)),
            set(
                7,
                b(
                    BinaryOp::Add,
                    b(BinaryOp::And, r(6), c(u64::MAX << s)),
                    r(5),
                ),
            ),
            set(5, c(107)),
            set(6, c(109)),
            set(3, b(BinaryOp::Sub, r(4), r(7))),
        ]);
        let p = single(a);
        check(&p, 1, 1);
        for x in samples(d) {
            let mut input = [0; 8];
            input[0] = x;
            assert_eq!(p.execute(&input, 8).unwrap().value, x % d);
        }
    }
}
#[test]
fn numerator_capture_may_name_a_prior_load_but_never_replays_a_source_load() {
    let mut a = vec![set(0, Expr::load(r(7), Width::U64)), set(4, r(0))];
    a.extend(packet(5, 2));
    a.insert(4, set(0, c(99)));
    let Expr::Binary(BinaryOp::Sub, lhs, _) = &mut a[5].value else {
        panic!()
    };
    **lhs = r(4);
    let p = single(a);
    check(&p, 1, 1);
    for x in samples(5) {
        let mut input = [0; 8];
        input[7] = 0x1000;
        assert_eq!(
            p.execute_with_memory(&input, 0x1000, &x.to_le_bytes(), 8)
                .unwrap()
                .value,
            x % 5
        );
    }
    for bad in [
        Expr::load(r(7), Width::U64),
        Expr::select(c(0), Expr::load(r(7), Width::U64), r(0)),
    ] {
        let mut a = packet(5, 2);
        a[0].value = b(BinaryOp::UMulHigh, c(magic(5, 2)), bad);
        check(&single(a), 0, 0);
    }
    let mut a = packet(5, 2);
    a[2].value = b(
        BinaryOp::Sub,
        Expr::select(c(0), Expr::load(r(7), Width::U64), r(0)),
        b(BinaryOp::Mul, r(2), c(5)),
    );
    check(&single(a), 1, 0);
    // Two equal-looking loads are distinct captures.
    let mut a = vec![set(0, Expr::load(r(7), Width::U64))];
    a.extend(packet(5, 2));
    a.insert(3, set(0, Expr::load(r(7), Width::U64)));
    check(&single(a), 1, 0);
}
#[test]
fn checked_nonnegative_coefficient_algebra_and_operand_orders() {
    let mut a = packet(3, 1);
    a[0].value = b(BinaryOp::UMulHigh, r(0), c(magic(3, 1)));
    a[2].value = b(
        BinaryOp::Sub,
        r(0),
        b(
            BinaryOp::Sub,
            b(
                BinaryOp::Add,
                b(BinaryOp::Shl, r(2), c(2)),
                b(BinaryOp::Mul, c(2), r(2)),
            ),
            b(BinaryOp::Mul, r(2), c(3)),
        ),
    );
    check(&single(a), 1, 1);
    for product in [
        b(BinaryOp::Mul, r(2), c(4)),
        b(BinaryOp::Mul, r(2), c(u64::MAX)),
        b(BinaryOp::Sub, c(0), r(2)),
        b(BinaryOp::Shl, r(2), c(64)),
        b(BinaryOp::Add, b(BinaryOp::Mul, r(2), c(u64::MAX)), r(2)),
    ] {
        let mut a = packet(3, 1);
        a[2].value = b(BinaryOp::Sub, r(0), product);
        check(&single(a), 1, 0);
    }
}
#[test]
fn wrong_masks_divisors_versions_and_nonliteral_sources_decline() {
    for badmask in [u64::MAX, u64::MAX << 2, 0] {
        let mut a = packet(3, 1);
        a[2].value = b(
            BinaryOp::Sub,
            r(0),
            b(BinaryOp::Add, b(BinaryOp::And, r(1), c(badmask)), r(2)),
        );
        check(&single(a), 1, 0);
    }
    for write in [set(0, c(99)), set(1, c(99)), set(2, c(99))] {
        let mut a = packet(3, 1);
        a.insert(2, write);
        check(&single(a), 1, 0);
    }
    let mut a = packet(3, 1);
    a[0].value = b(BinaryOp::UMulHigh, c(magic(3, 1)), r(4));
    check(&single(a), 1, 0);
    for shift in [64, 65, u64::MAX] {
        let mut a = packet(3, 1);
        a[1].value = b(BinaryOp::Shr, r(1), c(shift));
        check(&single(a), 0, 0);
    }
    let mut a = packet(3, 1);
    a.insert(1, set(1, r(1)));
    check(&single(a), 0, 0);
    let mut a = packet(3, 1);
    a.swap(0, 1);
    check(&single(a), 0, 0);
}
#[test]
fn every_public_fact_and_certificate_field_is_source_checked() {
    let p = single(packet(5, 2));
    let facts = check(&p, 1, 1);
    let good = facts.quotients()[0];
    let mut bad = Vec::new();
    macro_rules! poison {
        ($field:ident,$v:expr) => {{
            let mut q = good;
            q.$field = $v;
            bad.push(q);
        }};
    }
    poison!(block_start, 9);
    poison!(point, point(2));
    poison!(high_definition, point(1));
    poison!(quotient, Reg(1));
    poison!(high_register, Reg(0));
    poison!(divisor, 3);
    let mut q = good;
    q.certificate.multiplier ^= 1;
    bad.push(q);
    let mut q = good;
    q.certificate.shift += 1;
    bad.push(q);
    let mut q = good;
    q.certificate.excess ^= 1;
    bad.push(q);
    let mut q = good;
    q.certificate.upper_bound ^= 1;
    bad.push(q);
    for q in bad {
        assert!(!validate_quotient(&p, &q));
        assert!(numerator(&p, &q).is_none());
    }
    let good = facts.remainders()[0];
    let mut bad = Vec::new();
    macro_rules! poison_rem {
        ($field:ident,$v:expr) => {{
            let mut q = good;
            q.$field = $v;
            bad.push(q);
        }};
    }
    poison_rem!(block_start, 9);
    poison_rem!(point, point(1));
    poison_rem!(quotient_definition, point(0));
    poison_rem!(divisor, 3);
    for q in bad {
        assert!(!validate_remainder(&p, &q));
    }
    for index in [0, 1, 2] {
        let mut a = packet(5, 2);
        a[index].value = c(0);
        let other = single(a);
        assert!(!validate_remainder(&other, &good));
        if index != 2 {
            assert!(!validate_quotient(&other, &facts.quotients()[0]));
        }
    }
}
#[test]
fn block_and_loop_boundaries_do_not_import_facts() {
    let a = packet(3, 1);
    for split in [1, 2] {
        let p = Program::new(
            0,
            8,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: a[..split].to_vec(),
                    control: Control::Jump(1),
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: a[split..].to_vec(),
                    control: Control::Branch {
                        condition: r(6),
                        target: 1,
                    },
                },
                IrInstruction {
                    address: 2,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(r(3)),
                },
            ],
        )
        .unwrap();
        check(&p, usize::from(split == 2), 0);
    }
    // A complete packet within a loop block is valid for that iteration.
    let p = Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: a,
                control: Control::Branch {
                    condition: r(6),
                    target: 1,
                },
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(3)),
            },
        ],
    )
    .unwrap();
    check(&p, 1, 1);
}
#[test]
fn bounds_decline_whole_analysis_including_earlier_valid_facts() {
    let p = Program::new(
        0,
        4097,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: packet(3, 1),
            control: Control::Return(r(3)),
        }],
    )
    .unwrap();
    assert!(ArithmeticFacts::analyze(&p).is_none());
    let mut a = packet(3, 1);
    a.extend((0..16384).map(|_| set(4, c(0))));
    assert!(ArithmeticFacts::analyze(&single(a)).is_none());
    let mut deep = r(0);
    for _ in 0..129 {
        deep = b(BinaryOp::Add, deep, c(1));
    }
    let mut a = packet(3, 1);
    a.push(set(4, deep));
    assert!(ArithmeticFacts::analyze(&single(a)).is_none());
    // Source syntax is shallow but its materialized value DAG exceeds depth.
    let mut a = packet(3, 1);
    a.pop();
    a.push(set(4, r(2)));
    for _ in 0..129 {
        a.push(set(4, b(BinaryOp::Add, r(4), c(0))));
    }
    a.push(set(3, b(BinaryOp::Sub, r(0), b(BinaryOp::Mul, r(4), c(3)))));
    assert!(ArithmeticFacts::analyze(&single(a)).is_none());
}
#[test]
fn actual_gcc_o2_division_and_remainder_packets_are_recognized() {
    let scratch = native::Scratch::new();
    for d in [3, 5, 9] {
        let src = scratch.0.join(format!("div{d}.c"));
        let obj = scratch.0.join(format!("div{d}.o"));
        std::fs::write(&src,format!("#include <stdint.h>\nuint64_t fixture(uint64_t*p){{uint64_t x=p[0],q=x/{d},r=x%{d};p[1]=q;p[2]=r;return q^r;}}\n")).unwrap();
        native::object(&src, &obj, "-O2", "fixture");
        let lifted = nirvana::frontend::lift_elf(&std::fs::read(obj).unwrap(), "fixture").unwrap();
        let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
        let web = nirvana::web::split(reduced.program()).unwrap();
        let input = web.program();
        let widths = nirvana::value_width::ValueWidths::analyze(input);
        let width = |reg| {
            if reduced.parameters().contains(&reg) {
                Width::U64
            } else {
                widths.width(reg)
            }
        };
        let mut instructions = input.instructions().to_vec();
        for ins in &mut instructions {
            for a in &mut ins.assignments {
                a.value = nirvana::presentation::normalize(&a.value, width);
            }
        }
        let program = Program::new(
            input.cfg().block(input.cfg().entry()).start,
            input.register_count(),
            instructions,
        )
        .unwrap();
        let facts = check(&program, 1, 1);
        assert_eq!(facts.quotients()[0].divisor, d);
        assert_eq!(facts.remainders()[0].divisor, d);
        // Compare the actual lifted sequential IR with integer / and % across
        // full-width boundaries; parameter register IDs are preserved by web.
        for x in samples(d) {
            let mut registers = vec![0; program.register_count()];
            for reg in reduced.parameters() {
                registers[reg.0] = 0x1000;
            }
            let mut memory = vec![0u8; 24];
            memory[..8].copy_from_slice(&x.to_le_bytes());
            let run = program
                .execute_with_memory(&registers, 0x1000, &memory, 128)
                .unwrap();
            assert_eq!(run.value, (x / d) ^ (x % d));
        }
    }
}
