use nirvana::{
    division_expr,
    ir::*,
    remainder_graph::{GraphRemainders, validate},
};
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: r(7),
            width: Width::U64,
        },
        value,
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
        store(r(2)),
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
fn check(p: &Program, count: usize) {
    let plan = GraphRemainders::analyze(p).unwrap();
    assert_eq!(plan.evidence().len(), count, "{:#?}", p.instructions());
    for proof in plan.evidence() {
        assert!(validate(p, proof));
    }
}
#[test]
fn three_five_nine_and_seventeen_restore_and_bind_actual_lhs() {
    for (d, s) in [(3, 1), (5, 2), (9, 3), (17, 4), (33, 5)] {
        let p = single(packet(d, s));
        check(&p, 1);
        let plan = GraphRemainders::analyze(&p).unwrap();
        let proof = plan.evidence()[0];
        assert_eq!(
            (proof.divisor, proof.maximum_remainder, proof.quotient),
            (d, d - 1, Reg(2))
        );
        let source = &p.instructions()[0].assignments[3].value;
        let view = plan.view(&p, 0, 3, &source.clone()).unwrap();
        let Expr::Binary(BinaryOp::Sub, lhs, _) = source else {
            panic!()
        };
        assert!(std::ptr::eq(view.value, &**lhs));
        assert!(plan.view(&p, 0, 3, &r(0)).is_none());
        assert!(plan.view(&p, 0, 2, source).is_none());
        // Evaluate original wrapping IR against integer remainder on boundaries
        // and an independent deterministic full-width sample.
        let mut seed = 0x349ccf6c1234abcd_u64;
        let mut xs = vec![0, 1, d - 1, d, d + 1, u64::MAX, u64::MAX - 1];
        for _ in 0..128 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            xs.push(seed);
        }
        for x in xs {
            let mut input = [0; 8];
            input[0] = x;
            input[7] = 0x1000;
            let run = p.execute_with_memory(&input, 0x1000, &[0; 8], 8).unwrap();
            assert_eq!(run.value, x % d);
        }
    }
}
#[test]
fn captured_load_and_raw_copy_aliases_preserve_old_value() {
    let mut a = vec![set(0, Expr::load(r(7), Width::U64)), set(4, r(0))];
    a.extend(packet(5, 2));
    // Old numerator lives in r4 after r0 is overwritten. The view must borrow
    // that actual source operand, rather than introducing an r0 read.
    a.insert(5, set(0, c(99)));
    a[6].value = b(
        BinaryOp::Sub,
        r(4),
        b(
            BinaryOp::Add,
            b(BinaryOp::And, r(1), c(u64::MAX << 2)),
            r(2),
        ),
    );
    check(&single(a), 1);
}
#[test]
fn reject_invalidating_writes_masks_shifts_and_mixed_values() {
    for write in [set(0, c(99)), set(1, c(99)), set(2, c(99)), set(2, r(2))] {
        let mut a = packet(3, 1);
        a.insert(3, write);
        check(&single(a), 0);
    }
    for badmask in [u64::MAX, u64::MAX << 2, 0] {
        let mut a = packet(3, 1);
        a[3].value = b(
            BinaryOp::Sub,
            r(0),
            b(BinaryOp::Add, b(BinaryOp::And, r(1), c(badmask)), r(2)),
        );
        check(&single(a), 0);
    }
    for shift in [0, 2, 64, 65, u64::MAX] {
        let mut a = packet(3, 1);
        a[1].value = b(BinaryOp::Shr, r(1), c(shift));
        check(&single(a), 0);
    }
    let mut a = packet(3, 1);
    a[0].value = b(BinaryOp::UMulHigh, c(magic(3, 1)), r(4));
    check(&single(a), 0);
    let mut a = packet(3, 1);
    a.swap(0, 1);
    check(&single(a), 0);
}
#[test]
fn keeper_must_be_exact_preceding_store_in_current_q_definition() {
    let mut a = packet(3, 1);
    a.remove(2);
    check(&single(a), 0);
    let mut a = packet(3, 1);
    a.swap(2, 3);
    check(&single(a), 0);
    let mut a = packet(3, 1);
    a[2] = store(b(BinaryOp::Add, r(2), c(0)));
    check(&single(a), 0);
    let mut a = packet(3, 1);
    a[2] = set(4, r(2));
    check(&single(a), 0);
    let mut a = packet(3, 1);
    a.insert(3, set(2, b(BinaryOp::Shr, r(1), c(1))));
    check(&single(a), 0);
}
#[test]
fn reject_every_source_load_even_dead_lazy_arm() {
    for bad in [
        Expr::load(r(7), Width::U64),
        Expr::select(c(0), Expr::load(r(7), Width::U64), r(0)),
    ] {
        let mut a = packet(3, 1);
        a[0].value = b(BinaryOp::UMulHigh, c(magic(3, 1)), bad.clone());
        a[3].value = b(
            BinaryOp::Sub,
            bad,
            b(
                BinaryOp::Add,
                b(BinaryOp::And, r(1), c(u64::MAX << 1)),
                r(2),
            ),
        );
        check(&single(a), 0);
    }
}
#[test]
fn generic_checked_coefficient_rules_and_overflow_decline() {
    let mut a = packet(3, 1);
    a[3].value = b(
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
    check(&single(a), 1);
    let mut a = packet(3, 1);
    a[3].value = b(BinaryOp::Sub, r(0), b(BinaryOp::Mul, r(2), c(u64::MAX)));
    check(&single(a), 0);
}
#[test]
fn evidence_and_source_poisoning_are_independently_rejected() {
    let p = single(packet(5, 2));
    let plan = GraphRemainders::analyze(&p).unwrap();
    let good = plan.evidence()[0];
    let mut variants = Vec::new();
    macro_rules! poison {
        ($field:ident,$value:expr) => {{
            let mut p = good;
            p.$field = $value;
            variants.push(p);
        }};
    }
    poison!(block_start, 9);
    poison!(instruction, 9);
    poison!(assignment, 0);
    poison!(definition_assignment, 0);
    poison!(definition_instruction, 9);
    poison!(quotient, Reg(1));
    poison!(divisor, 3);
    poison!(maximum_remainder, 0);
    let mut bad = good;
    bad.certificate.multiplier ^= 1;
    variants.push(bad);
    let mut bad = good;
    bad.certificate.shift += 1;
    variants.push(bad);
    let mut bad = good;
    bad.certificate.excess ^= 1;
    variants.push(bad);
    let mut bad = good;
    bad.certificate.upper_bound ^= 1;
    variants.push(bad);
    let mut bad = good;
    bad.keeper.assignment = 3;
    variants.push(bad);
    for bad in variants {
        assert!(!validate(&p, &bad), "{bad:?}");
    }
    let other = single(packet(9, 3));
    assert!(!validate(&other, &good));
    assert!(
        plan.view(&other, 0, 3, &other.instructions()[0].assignments[3].value)
            .is_none()
    );
}
#[test]
fn block_edges_do_not_import_historical_values() {
    let a = packet(3, 1);
    let p = Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: a[..3].to_vec(),
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![a[3].clone()],
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
    check(&p, 0);
}
#[test]
fn actual_gcc_o2_materialized_high_packets_are_recognized() {
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
        let plan = GraphRemainders::analyze(&program).unwrap();
        assert_eq!(
            plan.evidence().len(),
            1,
            "d={d}: {:#?}",
            program.instructions()
        );
        assert_eq!(plan.evidence()[0].divisor, d);
        assert!(validate(&program, &plan.evidence()[0]));
        // The certificate is generic rather than a divisor or magic table.
        let cert = plan.evidence()[0].certificate;
        assert!(
            division_expr::recognize(&b(
                BinaryOp::Shr,
                b(BinaryOp::UMulHigh, c(cert.multiplier), r(0)),
                c(cert.shift as u64)
            ))
            .is_some()
        );
    }
}
#[test]
fn materialized_product_and_high_alias_reads_are_not_erased() {
    let mut a = packet(3, 1);
    a.insert(3, set(4, b(BinaryOp::And, r(1), c(u64::MAX << 1))));
    a[4].value = b(BinaryOp::Sub, r(0), b(BinaryOp::Add, r(4), r(2)));
    check(&single(a), 0);
    let mut a = packet(3, 1);
    a.insert(3, set(4, r(1)));
    a[4].value = b(
        BinaryOp::Sub,
        r(0),
        b(
            BinaryOp::Add,
            b(BinaryOp::And, r(4), c(u64::MAX << 1)),
            r(2),
        ),
    );
    check(&single(a), 0);
}
#[test]
fn sparse_ids_and_oversized_graphs_decline_whole_plan() {
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
    assert!(GraphRemainders::analyze(&p).is_none());
    let mut a = packet(3, 1);
    a.extend((0..16384).map(|_| set(4, c(0))));
    assert!(GraphRemainders::analyze(&single(a)).is_none());
}
