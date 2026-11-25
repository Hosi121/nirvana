//! Full-u64 audits of masks returned by the actual checking kernel.
use super::kernel;
use crate::dataflow::known_bits::KnownBits as K;
use crate::model::ir::{BinaryOp as B, Expr, Reg, UnaryOp as U, Width};
use crate::verification::verify::{self, Solver, Verdict};
use std::path::Path;

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn input(index: usize, fact: K) -> Expr {
    b(
        B::Or,
        b(B::And, r(index), c(!(fact.zero() | fact.one()))),
        c(fact.one()),
    )
}
fn violation(value: Expr, fact: K) -> Expr {
    b(
        B::Or,
        b(B::And, value.clone(), c(fact.zero())),
        b(B::Xor, b(B::And, value, c(fact.one())), c(fact.one())),
    )
}
fn check(directory: &Path, solver: &Solver, name: &str, value: Expr, fact: K) -> Verdict {
    let query = verify::pure_query(&violation(value, fact), &c(0)).unwrap();
    std::fs::write(
        directory.join(format!("{name}.smt2")),
        format!("{}(check-sat)\n", query.smt2()),
    )
    .unwrap();
    let result = solver.check_query(&query);
    std::fs::write(
        directory.join(format!("{name}.out")),
        format!("{result:?}\n"),
    )
    .unwrap();
    result
}

#[test]
#[ignore = "requires Z3 and empty NIRVANA_BITS_CHECK_OUT managed directory"]
fn actual_checking_masks_have_full_word_proofs_and_replayed_mutants() {
    let out = std::path::PathBuf::from(
        std::env::var_os("NIRVANA_BITS_CHECK_OUT").expect("set NIRVANA_BITS_CHECK_OUT"),
    );
    std::fs::create_dir_all(&out).unwrap();
    assert!(std::fs::read_dir(&out).unwrap().next().is_none());
    let solver = Solver::new(std::env::var("NIRVANA_Z3").expect("set NIRVANA_Z3"));
    let mut ops = vec![
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
    let mut unary = Vec::new();
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        unary.push(U::SignExtend(width));
        for start in [0, 1, 7, 8, 31, 32, 60, 63, 64, 255] {
            ops.push(B::Insert { start, width });
            unary.push(U::Extract { start, width });
        }
    }
    let cases = [
        (K::new(!255, 0).unwrap(), K::constant(3)),
        (K::new(15, 0).unwrap(), K::constant(16)),
        (K::new(!511, 256).unwrap(), K::new(!7, 1).unwrap()),
        (K::new(0, u64::MAX ^ 255).unwrap(), K::constant(1)),
        (K::UNKNOWN, K::constant(0)),
        (K::new(!255, 128).unwrap(), K::constant(64)),
    ];
    let mut proved = 0;
    let mut unknown_masks = 0;
    let mut failures = Vec::new();
    for (case, (left, right)) in cases.into_iter().enumerate() {
        for (index, &op) in ops.iter().enumerate() {
            let fact = kernel::binary(op, left, right);
            if fact == K::UNKNOWN {
                unknown_masks += 1;
                continue;
            }
            let name = format!("binary-{case}-{index}");
            let result = check(
                &out,
                &solver,
                &name,
                b(op, input(0, left), input(1, right)),
                fact,
            );
            if result == Verdict::EquivalentUnderModel {
                proved += 1;
            } else {
                failures.push(format!("{name}/{op:?}/{fact:?}: {result:?}"));
            }
        }
    }
    for (case, value) in [
        K::UNKNOWN,
        K::new(!255, 0).unwrap(),
        K::new(0, u64::MAX ^ 127).unwrap(),
    ]
    .into_iter()
    .enumerate()
    {
        for (index, &op) in unary.iter().enumerate() {
            let fact = kernel::unary(op, value);
            if fact == K::UNKNOWN {
                unknown_masks += 1;
                continue;
            }
            let name = format!("unary-{case}-{index}");
            let result = check(&out, &solver, &name, Expr::unary(op, input(0, value)), fact);
            if result == Verdict::EquivalentUnderModel {
                proved += 1;
            } else {
                failures.push(format!("{name}/{op:?}/{fact:?}: {result:?}"));
            }
        }
    }
    let mutants = [
        (
            "lost-carry",
            b(B::Add, input(0, K::new(!255, 0).unwrap()), c(1)),
            K::new(1 << 8, 0).unwrap(),
        ),
        ("unmasked-shift", b(B::Shl, r(0), c(64)), K::constant(0)),
        (
            "signed-zero-divisor",
            b(B::SDiv, r(0), c(0)),
            K::constant(0),
        ),
        (
            "unsigned-zero-remainder",
            b(B::URem, r(0), c(0)),
            K::constant(0),
        ),
        (
            "signed-min-overflow",
            b(B::SDiv, c(1 << 63), c(u64::MAX)),
            K::constant(0),
        ),
        (
            "clipped-insert",
            b(
                B::Insert {
                    start: 63,
                    width: Width::U64,
                },
                r(0),
                r(1),
            ),
            K::new(1 << 62, 0).unwrap(),
        ),
        ("high-product", b(B::UMulHigh, r(0), c(2)), K::constant(0)),
        (
            "arithmetic-fill",
            b(B::AShr, input(0, K::new(0, 1 << 63).unwrap()), c(63)),
            K::constant(0),
        ),
    ];
    let mut replayed = 0;
    for (name, value, fact) in mutants {
        let result = check(&out, &solver, name, value, fact);
        if let Verdict::Counterexample(witness) = result {
            assert_ne!(witness.before, 0, "IR-replayed violation {name}");
            replayed += 1;
        } else {
            failures.push(format!("missing replayed mutant {name}: {result:?}"));
        }
    }
    std::fs::write(
        out.join("summary.json"),
        format!("{{\"full_u64_unsat\":{proved},\"unknown_masks\":{unknown_masks},\"ir_replayed_sat\":{replayed},\"failures\":{}}}\n", failures.len()),
    )
    .unwrap();
    assert!(proved >= 70);
    assert_eq!(replayed, 8);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    println!(
        "{proved} checking-kernel full-u64 UNSAT; {unknown_masks} unknown masks; {replayed} IR-replayed SAT controls"
    );
}

#[cfg(test)]
#[path = "smt_prefix.rs"]
mod prefix;

#[cfg(test)]
#[path = "smt_cubes.rs"]
mod cubes;
