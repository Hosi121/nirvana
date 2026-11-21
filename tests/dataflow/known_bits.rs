use crate::support::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp, Width,
};
use nirvana::known_bits::{self, BitPlan, KnownBits as K};
use nirvana::ssa::{Definition, Site};
const OPS: [B; 19] = [
    B::Add,
    B::Sub,
    B::Mul,
    B::And,
    B::Or,
    B::Xor,
    B::Shl,
    B::Shr,
    B::AShr,
    B::Eq,
    B::Ne,
    B::Ult,
    B::Ule,
    B::UMulHigh,
    B::SMulHigh,
    B::UDiv,
    B::URem,
    B::SDiv,
    B::SRem,
];
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
fn program(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, instructions).unwrap()
}
fn compare(source: &Program, candidate: &Program) {
    for x in [0, 1, 2, 7, 15, 128, 255, 256, 1 << 31, 1 << 63, u64::MAX] {
        for pointer in [4096, 4097, 4104, 4112, 4120, 4127, u64::MAX] {
            let mut input = [0x9371_cafe_7890_fedc; 8];
            input[0] = x;
            input[7] = pointer;
            for memory in [vec![0; 32], (0..32).map(|n| (n * 29 + 7) as u8).collect()] {
                for limit in [0, 1, 2, 3, 4, 8, 16, 32] {
                    assert_eq!(
                        source.run_with_memory(&input, 4096, &memory, limit),
                        candidate.run_with_memory(&input, 4096, &memory, limit),
                        "{x}/{pointer}/{limit}"
                    );
                }
            }
        }
    }
}

#[test]
fn every_operator_soundly_covers_all_four_bit_input_fact_sets() {
    let mut facts = Vec::new();
    for pattern in 0..81u32 {
        let mut n = pattern;
        let mut z = !15u64;
        let mut o = 0;
        for bit in 0..4 {
            match n % 3 {
                0 => {}
                1 => z |= 1 << bit,
                2 => o |= 1 << bit,
                _ => unreachable!(),
            }
            n /= 3;
        }
        let fact = K::new(z, o).unwrap();
        let values = (0..16u64).filter(|v| fact.contains(*v)).collect::<Vec<_>>();
        assert!(!values.is_empty());
        facts.push((fact, values));
    }
    let mut observations = 0;
    let mut useful = 0;
    for (a, av) in &facts {
        for (z, zv) in &facts {
            for op in OPS {
                let result = K::binary(op, *a, *z);
                assert_eq!(result.zero() & result.one(), 0);
                if result != K::UNKNOWN {
                    useful += 1;
                }
                for &x in av {
                    for &y in zv {
                        assert!(
                            result.contains(op.evaluate(x, y)),
                            "{op:?}/{a:?}/{z:?}/{x}/{y}: {result:?}"
                        );
                        observations += 1;
                    }
                }
            }
        }
    }
    assert_eq!(observations, 1_245_184);
    assert!(useful > 100_000);
    assert!(K::new(1, 1).is_none());
    println!("{observations} exhaustive four-bit transfer observations; {useful} nontrivial facts");
}

#[test]
fn sparse_full_word_facts_cover_sign_wrap_division_zero_and_dynamic_shift_boundaries() {
    let mut seed = 0x8937_cddf_1234_6689u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut observations = 0;
    for _ in 0..256 {
        let ua = (1 << (next() % 64)) | (1 << (next() % 64)) | (1 << (next() % 64));
        let oa = next() & !ua;
        let a = K::new(!(ua | oa), oa).unwrap();
        let ub = (1 << (next() % 64)) | (1 << (next() % 64)) | (1 << (next() % 64));
        let ob = next() & !ub;
        let z = K::new(!(ub | ob), ob).unwrap();
        for op in OPS {
            for right in [
                z,
                K::constant(0),
                K::constant(1),
                K::constant(64),
                K::constant(1 << 63),
                K::constant(u64::MAX),
            ] {
                let output = K::binary(op, a, right);
                assert_eq!(output.zero() & output.one(), 0);
                for x in [a.minimum(), a.maximum(), oa | (next() & ua)] {
                    for y in [
                        right.minimum(),
                        right.maximum(),
                        right.one() | (next() & !(right.zero() | right.one())),
                    ] {
                        assert!(
                            output.contains(op.evaluate(x, y)),
                            "{op:?}/{a:?}/{right:?}/{x}/{y}: {output:?}"
                        );
                        observations += 1;
                    }
                }
            }
        }
        for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
            let ops = [UnaryOp::SignExtend(width)].into_iter().chain(
                [0, 1, 7, 8, 31, 32, 60, 63, 64, 65, 255]
                    .into_iter()
                    .map(|start| UnaryOp::Extract { start, width }),
            );
            for op in ops {
                let output = K::unary(op, a);
                for x in [a.minimum(), a.maximum(), oa | (next() & ua)] {
                    assert!(output.contains(crate::support::ir::unary_value(op, x)));
                    observations += 1;
                }
            }
        }
    }
    let multiple = K::new(15, 0).unwrap();
    assert_eq!(
        K::binary(B::SRem, multiple, K::constant(16)).number(),
        Some(0)
    );
    assert_eq!(K::binary(B::SDiv, K::UNKNOWN, K::constant(0)).one(), 1);
    println!("{observations} sparse 64-bit transfer observations");
}

#[test]
fn phi_alternatives_keep_common_bits_and_fold_only_proved_constants() {
    let source = program(vec![
        ins(
            0,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 2,
            },
        ),
        ins(1, vec![set(1, c(0x11))], Control::Jump(3)),
        ins(2, vec![set(1, c(0x13))], Control::Jump(3)),
        ins(
            3,
            vec![set(2, b(B::And, r(1), c(0x11)))],
            Control::Return(r(2)),
        ),
    ]);
    let plan = BitPlan::analyze(&source).unwrap();
    let types = nirvana::type_infer::TypeAnalysis::analyze(&source).unwrap();
    assert_eq!(
        known_bits::analyze_values(&source, types.graph()).unwrap(),
        plan.values()
    );
    let phi = plan
        .graph()
        .values
        .iter()
        .position(|v| {
            matches!(
                v,
                Definition::Phi {
                    block: 3,
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap();
    let fact = plan.values()[phi];
    assert_eq!(fact.one(), 0x11);
    assert_eq!(fact.zero(), !0x13);
    let (candidate, evidence) = plan.propose(&source).unwrap();
    assert!(evidence.replacements >= 2);
    assert_eq!(candidate.instructions()[3].assignments[0].value, c(0x11));
    assert_eq!(
        candidate.instructions()[3].control,
        Control::Return(c(0x11))
    );
    compare(&source, &candidate);
    let mut bad = plan.values().to_vec();
    bad[phi] = K::constant(0x11);
    assert!(known_bits::validate_facts(&source, plan.graph(), &bad).is_err());
}

#[test]
fn masked_loop_invariants_are_closed_but_entry_values_remain_arbitrary() {
    let source = program(vec![
        ins(
            0,
            vec![
                set(1, b(B::Or, b(B::And, r(0), c(15)), c(16))),
                set(2, b(B::And, r(0), c(3))),
            ],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![],
            Control::Branch {
                condition: r(2),
                target: 3,
            },
        ),
        ins(2, vec![], Control::Return(b(B::And, r(1), c(16)))),
        ins(
            3,
            vec![
                set(1, b(B::Or, b(B::And, b(B::Add, r(1), c(1)), c(15)), c(16))),
                set(2, b(B::Sub, r(2), c(1))),
            ],
            Control::Jump(1),
        ),
    ]);
    let plan = BitPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    assert_eq!(candidate.instructions()[2].control, Control::Return(c(16)));
    compare(&source, &candidate);
    for (index, definition) in plan.graph().values.iter().enumerate() {
        if matches!(definition, Definition::Initial { .. }) {
            assert_eq!(plan.values()[index], K::UNKNOWN);
        }
    }
    let entry = program(vec![
        ins(
            0,
            vec![set(1, b(B::And, r(1), c(15)))],
            Control::Branch {
                condition: r(0),
                target: 0,
            },
        ),
        ins(1, vec![], Control::Return(r(1))),
    ]);
    let plan = BitPlan::analyze(&entry).unwrap();
    let phi = plan
        .graph()
        .values
        .iter()
        .position(|v| {
            matches!(
                v,
                Definition::Phi {
                    block: 0,
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap();
    assert_eq!(plan.values()[phi], K::UNKNOWN);
    let mut forged = plan.values().to_vec();
    forged[phi] = K::new(!15, 0).unwrap();
    assert!(known_bits::validate_facts(&entry, plan.graph(), &forged).is_err());
}

#[test]
fn load_bounds_keep_reads_lazy_arms_stores_and_fault_order_at_original_sites() {
    let store = |address, value| Assignment {
        destination: Place::Memory {
            address,
            width: Width::U64,
        },
        value,
    };
    let source = program(vec![ins(
        0,
        vec![
            set(1, Expr::load(r(7), Width::U8)),
            set(2, b(B::And, r(1), c(0xff00))),
            store(c(4096), c(77)),
            store(
                b(B::Add, r(7), c(16)),
                Expr::select(
                    b(B::Eq, r(2), c(0)),
                    Expr::load(b(B::Add, r(7), c(8)), Width::U64),
                    Expr::load(c(u64::MAX), Width::U64),
                ),
            ),
        ],
        Control::Return(r(2)),
    )]);
    let plan = BitPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    assert_eq!(candidate.instructions()[0].assignments[1].value, c(0));
    assert_eq!(
        candidate.instructions()[0].assignments[0],
        source.instructions()[0].assignments[0]
    );
    assert!(format!("{:?}", candidate.instructions()).contains("18446744073709551615"));
    compare(&source, &candidate);
    let mut changed = candidate.instructions().to_vec();
    changed[0].assignments.remove(0);
    let changed = program(changed);
    assert!(known_bits::validate(&source, plan.graph(), plan.values(), &changed).is_err());
    let mut graph = plan.graph().clone();
    let point = graph
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.points)
        .find(|p| {
            p.site
                == Site {
                    instruction: 0,
                    assignment: Some(1),
                }
        })
        .unwrap();
    point.reads[0].register = Reg(3);
    assert!(known_bits::validate_facts(&source, &graph, plan.values()).is_err());
}
