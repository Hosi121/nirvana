use nirvana::{ir, signed_expr};
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, RunStatus, Width};
use signed_expr::{SignedKind, recognize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::process::Command;

const SIGN: u64 = 1 << 63;
const VALUES: [u64; 12] = [
    0,
    1,
    2,
    127,
    255,
    65535,
    (1 << 31),
    SIGN - 1,
    SIGN,
    SIGN + 1,
    0x0123_4567_89ab_cdef,
    u64::MAX,
];
fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}

fn flags(left: Expr, right: Expr, result: Expr, width: u32, variant: u8) -> Expr {
    let sign = b(B::Shr, result.clone(), c(u64::from(width - 1)));
    let signs = if variant & 4 != 0 {
        b(B::Xor, right, left.clone())
    } else {
        b(B::Xor, left.clone(), right)
    };
    let changed = if variant & 4 != 0 {
        b(B::Xor, result, left)
    } else {
        b(B::Xor, left, result)
    };
    let pair = if variant & 2 != 0 {
        b(B::And, changed, signs)
    } else {
        b(B::And, signs, changed)
    };
    let bits = if variant & 8 != 0 {
        b(B::And, c(1 << (width - 1)), pair)
    } else {
        b(B::And, pair, c(1 << (width - 1)))
    };
    let overflow = if variant & 8 != 0 {
        b(B::Ne, c(0), bits)
    } else {
        b(B::Ne, bits, c(0))
    };
    if variant & 1 != 0 {
        b(B::Xor, overflow, sign)
    } else {
        b(B::Xor, sign, overflow)
    }
}
fn relation(left: Expr, right: Expr, kind: SignedKind, variant: u8) -> Expr {
    let result = b(B::Sub, left.clone(), right.clone());
    let less = flags(left.clone(), right.clone(), result.clone(), 64, variant);
    if kind == SignedKind::Slt64 {
        return less;
    }
    let equal = if variant & 2 != 0 {
        b(B::Eq, result, c(0))
    } else if variant & 4 != 0 {
        b(B::Eq, right, left)
    } else {
        b(B::Eq, left, right)
    };
    if variant & 1 != 0 {
        b(B::Or, less, equal)
    } else {
        b(B::Or, equal, less)
    }
}
fn evaluate(expression: &Expr, inputs: &[u64]) -> u64 {
    Program::new(
        0,
        inputs.len(),
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression.clone()),
        }],
    )
    .unwrap()
    .execute(inputs, 1)
    .unwrap()
    .value
}
fn oracle(kind: SignedKind, left: u64, right: u64) -> u64 {
    // Rust's cast preserves the low 64-bit representation. This test oracle
    // does not impose a signed conversion on the generated C helper.
    match kind {
        SignedKind::Slt64 => u64::from((left as i64) < (right as i64)),
        SignedKind::Sle64 => u64::from((left as i64) <= (right as i64)),
    }
}
fn dependencies(expression: &Expr) -> BTreeSet<usize> {
    let mut result = BTreeSet::new();
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            Expr::Register(reg) => {
                result.insert(reg.0);
            }
            Expr::Binary(_, a, z) => pending.extend([&**a, &**z]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    result
}

#[test]
fn exact_flags_match_signed_oracles_for_zero_sign_and_wrap_boundaries() {
    for kind in [SignedKind::Slt64, SignedKind::Sle64] {
        for variant in 0..16 {
            let expression = relation(r(0), r(1), kind, variant);
            let before = expression.clone();
            let view = recognize(&expression).unwrap();
            assert_eq!(view.kind, kind);
            assert_eq!(view.left, &r(0));
            assert_eq!(view.right, &r(1));
            let mut retained = dependencies(view.left);
            retained.extend(dependencies(view.right));
            assert_eq!(dependencies(&expression), retained);
            for a in VALUES {
                for z in VALUES {
                    assert_eq!(
                        evaluate(&expression, &[a, z]),
                        oracle(kind, a, z),
                        "{kind:?}, variant={variant}, {a:#x},{z:#x}"
                    );
                }
            }
            assert_eq!(expression, before);
        }
    }
}

#[test]
fn complex_operands_are_borrowed_raw_and_keep_every_dependency() {
    let left = Expr::select(r(2), b(B::Add, r(0), c(7)), b(B::Xor, r(0), c(u64::MAX)));
    let right = b(B::UMulHigh, r(1), c(0x8123_4567_89ab_cdef));
    let expression = relation(left.clone(), right.clone(), SignedKind::Slt64, 0);
    let Expr::Binary(_, sign, _) = &expression else {
        unreachable!()
    };
    let Expr::Binary(_, difference, _) = &**sign else {
        unreachable!()
    };
    let Expr::Binary(_, original_left, original_right) = &**difference else {
        unreachable!()
    };
    let view = recognize(&expression).unwrap();
    assert!(std::ptr::eq(view.left, &**original_left));
    assert!(std::ptr::eq(view.right, &**original_right));
    let mut retained = dependencies(view.left);
    retained.extend(dependencies(view.right));
    assert_eq!(retained, BTreeSet::from([0, 1, 2]));
    assert_eq!(dependencies(&expression), retained);
    for a in VALUES {
        for z in VALUES {
            for choose in [0, 1, u64::MAX] {
                let inputs = [a, z, choose];
                assert_eq!(
                    evaluate(&expression, &inputs),
                    oracle(
                        view.kind,
                        evaluate(&left, &inputs),
                        evaluate(&right, &inputs)
                    )
                );
            }
        }
    }
    assert!(recognize(&relation(r(usize::MAX), c(0), SignedKind::Slt64, 0)).is_some());
}

#[test]
fn unsigned_narrow_addition_unknown_result_and_raw_mismatches_decline() {
    let a = r(0);
    let z = r(1);
    let difference = b(B::Sub, a.clone(), z.clone());
    for expression in [
        b(B::Ult, a.clone(), z.clone()),
        b(B::Ule, a.clone(), z.clone()),
        flags(a.clone(), z.clone(), r(2), 64, 0),
        flags(a.clone(), z.clone(), b(B::Add, a.clone(), z.clone()), 64, 0),
        flags(
            a.clone(),
            z.clone(),
            b(B::Sub, difference.clone(), r(2)),
            64,
            0,
        ),
        flags(a.clone(), z.clone(), difference.clone(), 32, 0),
        flags(a.clone(), z.clone(), difference.clone(), 16, 0),
        flags(a.clone(), z.clone(), difference.clone(), 8, 0),
        b(
            B::Or,
            b(B::Eq, a.clone(), r(2)),
            relation(a.clone(), z.clone(), SignedKind::Slt64, 0),
        ),
    ] {
        assert!(recognize(&expression).is_none(), "{expression:?}");
    }
    let Expr::Binary(_, _, overflow) = flags(a.clone(), z.clone(), difference.clone(), 64, 0)
    else {
        unreachable!()
    };
    for sign in [
        b(
            B::Shr,
            b(B::Sub, b(B::Add, a.clone(), c(0)), z.clone()),
            c(63),
        ),
        b(B::Shr, b(B::Sub, r(10), z.clone()), c(63)),
        b(B::Shr, difference.clone(), c(127)),
    ] {
        assert!(recognize(&b(B::Xor, sign, (*overflow).clone())).is_none());
    }
    let Expr::Binary(_, sign, overflow) = flags(a, z, difference, 64, 0) else {
        unreachable!()
    };
    let Expr::Binary(_, mask, zero) = *overflow else {
        unreachable!()
    };
    assert!(
        recognize(&b(
            B::Xor,
            (*sign).clone(),
            b(B::Eq, (*mask).clone(), (*zero).clone())
        ))
        .is_none()
    );
    assert!(
        recognize(&b(
            B::Xor,
            (*sign).clone(),
            b(B::Ne, b(B::And, (*mask).clone(), c(SIGN - 1)), c(0))
        ))
        .is_none()
    );
    let base = relation(r(0), r(1), SignedKind::Slt64, 0);
    assert!(
        recognize(&b(B::Xor, base, c(1))).is_none(),
        "truth wrappers remain outside the borrowed match"
    );
}

#[test]
fn loads_and_lazy_load_dependencies_never_factor_or_disappear() {
    for value in [
        Expr::load(r(2), Width::U64),
        Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8)),
        b(B::Mul, c(0), Expr::load(r(2), Width::U64)),
    ] {
        assert!(recognize(&relation(value.clone(), r(1), SignedKind::Slt64, 0)).is_none());
        assert!(recognize(&relation(r(0), value, SignedKind::Sle64, 0)).is_none());
    }
}

#[test]
fn whole_expression_size_and_depth_are_bounded_before_matching() {
    let mut deep = r(0);
    for _ in 0..=signed_expr::MAX_DEPTH {
        deep = b(B::Add, deep, c(0));
    }
    assert!(recognize(&relation(deep, r(1), SignedKind::Slt64, 0)).is_none());
    fn balanced(leaves: usize) -> Expr {
        if leaves == 1 {
            return c(0);
        }
        b(B::Add, balanced(leaves / 2), balanced(leaves - leaves / 2))
    }
    assert!(
        recognize(&relation(
            balanced(signed_expr::MAX_NODES),
            r(1),
            SignedKind::Sle64,
            0
        ))
        .is_none()
    );
    let malformed = b(
        B::Or,
        relation(r(0), r(1), SignedKind::Slt64, 0),
        balanced(signed_expr::MAX_NODES),
    );
    assert!(recognize(&malformed).is_none());
    const {
        assert!(signed_expr::MAX_WORK >= signed_expr::MAX_NODES);
    }
}

#[test]
fn helpers_match_independent_signed_comparisons_at_o0_o2_and_ubsan() {
    let scratch = native::Scratch::new();
    let mut source =
        String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    for kind in [SignedKind::Slt64, SignedKind::Sle64] {
        source.push_str(kind.c_helper());
        assert!(kind.c_helper().contains(kind.helper_name()));
    }
    source.push_str(r#"
int main(void) {
    uint64_t a,b;
    while(scanf("%" SCNu64 " %" SCNu64,&a,&b)==2) {
        uint64_t bits[2]={a,b};
        const int64_t *signed_bits=(const int64_t *)(const void *)bits;
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               nirvana_slt64(a,b),nirvana_sle64(a,b),
               (uint64_t)(signed_bits[0]<signed_bits[1]),(uint64_t)(signed_bits[0]<=signed_bits[1]));
    }
}
"#);
    let path = scratch.0.join("helpers.c");
    std::fs::write(&path, source).unwrap();
    let mut input = String::new();
    let mut expected = Vec::new();
    for a in VALUES {
        for z in VALUES {
            writeln!(input, "{a} {z}").unwrap();
            let lt = oracle(SignedKind::Slt64, a, z);
            let le = oracle(SignedKind::Sle64, a, z);
            expected.push(vec![lt, le, lt, le]);
        }
    }
    for opt in ["-O0", "-O2"] {
        for sanitize in [false, true] {
            let binary = scratch.0.join(format!("helpers{opt}{sanitize}"));
            let mut command = Command::new("cc");
            command.args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fno-lto",
                opt,
            ]);
            if sanitize {
                command.args(["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]);
            }
            let output = command.arg(&path).arg("-o").arg(&binary).output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, 4),
                expected,
                "{opt}, UBSan={sanitize}"
            );
        }
    }
}

#[test]
fn actual_signed_fixtures_keep_native_ir_results_and_only_explicit_raw_candidates() {
    let scratch = native::Scratch::new();
    let mut input = String::new();
    let mut inputs = Vec::new();
    for a in VALUES {
        for z in VALUES {
            let state = [a, z, 0xaaaa_aaaa_aaaa_aaaa, 0xbbbb_bbbb_bbbb_bbbb];
            writeln!(input, "{} {} {} {}", state[0], state[1], state[2], state[3]).unwrap();
            inputs.push(state);
        }
    }
    for name in ["signed-compare", "signed-branch"] {
        for opt in ["-O0", "-O2"] {
            let object = scratch.0.join(format!("{name}{opt}.o"));
            native::object(
                &native::fixture_root().join(format!("recovery/{name}.c")),
                &object,
                opt,
                "fixture",
            );
            let harness = scratch.0.join(format!("harness{opt}.o"));
            native::object(
                &native::fixture_root().join("harness.c"),
                &harness,
                opt,
                "fixture",
            );
            let binary = scratch.0.join(format!("{name}{opt}"));
            native::link(&[&object, &harness], &binary);
            let native = native::run(&binary, &input);
            assert_eq!(native.len(), inputs.len());
            let lifted =
                nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
            let original = lifted.program.instructions().to_vec();
            for (state, row) in inputs.iter().zip(native) {
                let mut registers = vec![0; lifted.program.register_count()];
                registers[nirvana::x86::RDI] = 8192;
                registers[nirvana::x86::RSP] = 65536;
                let mut memory: Vec<u8> = (0usize..65536)
                    .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                    .collect();
                for (i, value) in state.iter().enumerate() {
                    memory[4096 + i * 8..4096 + i * 8 + 8].copy_from_slice(&value.to_le_bytes());
                }
                let report = lifted
                    .program
                    .run_with_memory(&registers, 4096, &memory, 100000)
                    .unwrap();
                let RunStatus::Returned(value) = report.status else {
                    panic!("valid signed fixture did not return");
                };
                let mut ir = vec![value];
                ir.extend((0..4).map(|i| {
                    u64::from_le_bytes(
                        report.state.memory[4096 + i * 8..4096 + i * 8 + 8]
                            .try_into()
                            .unwrap(),
                    )
                }));
                assert_eq!(row, ir, "{name}{opt}, {state:?}");
                let lt = oracle(SignedKind::Slt64, state[0], state[1]);
                let le = oracle(SignedKind::Sle64, state[0], state[1]);
                let expected = if name == "signed-compare" {
                    let gt = 1 - le;
                    let ge = 1 - lt;
                    vec![
                        lt | (le << 1) | (gt << 2) | (ge << 3),
                        state[0],
                        state[1],
                        lt | (le << 1),
                        gt | (ge << 1),
                    ]
                } else {
                    vec![lt | (le << 1), state[0], state[1], lt, le]
                };
                assert_eq!(row, expected);
            }
            let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
            let webs = nirvana::web::split(reduced.program()).unwrap();
            nirvana::web_verify::validate(reduced.program(), webs.program()).unwrap();
            let widths = nirvana::value_width::ValueWidths::analyze(webs.program());
            let width = |reg| {
                if reduced.parameters().contains(&reg) {
                    Width::U64
                } else {
                    widths.width(reg)
                }
            };
            let mut counts = BTreeMap::new();
            fn visit(expression: &Expr, counts: &mut BTreeMap<SignedKind, usize>) {
                if let Some(view) = recognize(expression) {
                    let mut retained = dependencies(view.left);
                    retained.extend(dependencies(view.right));
                    assert_eq!(dependencies(expression), retained);
                    *counts.entry(view.kind).or_default() += 1;
                    return;
                }
                match expression {
                    Expr::Binary(_, a, z) => {
                        visit(a, counts);
                        visit(z, counts);
                    }
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        for x in [condition, taken, not_taken] {
                            visit(x, counts);
                        }
                    }
                    Expr::Load { address, .. } => visit(address, counts),
                    _ => {}
                }
            }
            for instruction in webs.program().instructions() {
                for assignment in &instruction.assignments {
                    visit(
                        &nirvana::presentation::normalize(&assignment.value, width),
                        &mut counts,
                    );
                }
                match &instruction.control {
                    Control::Branch { condition, .. } | Control::Return(condition) => visit(
                        &nirvana::presentation::normalize(condition, width),
                        &mut counts,
                    ),
                    _ => {}
                }
            }
            let total: usize = counts.values().sum();
            assert_eq!(
                total,
                match (name, opt) {
                    ("signed-compare", "-O0") => 4,
                    ("signed-compare", "-O2") => 1,
                    ("signed-branch", "-O0") => 2,
                    ("signed-branch", "-O2") => 1,
                    _ => 0,
                },
                "{name}{opt}: {counts:?}"
            );
            assert_eq!(lifted.program.instructions(), original);
            println!("{name}{opt}: {counts:?}");
        }
    }
}
