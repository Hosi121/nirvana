//! New proof obligations under the existing pure-u64-v1 bit-vector model.
//!
//! The source of truth is the unsigned modular IR contract. Input bounds are
//! encoded as And masks in Expr, with no solver assumptions. These checks cover
//! the declared transfer cases and indexed rewrites only; they do not prove
//! the CFG fixed point, origin analysis, memory effects, C emission, or types.
//! Full-U64 width bounds are counted but skipped because their masks are
//! tautological. SAT and Unknown never count as positive results. The default
//! Solver timeout remains two seconds; the strict proof matrix below is an explicitly limited fragment.

use nirvana::indexed::{IndexedAddress, recover_indexed};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg, Width};
use nirvana::value_width::ValueWidths;
use nirvana::verify::{Solver, UnknownReason, Verdict};

const BITS: [u32; 10] = [0, 1, 7, 8, 15, 16, 31, 32, 63, 64];

fn solver() -> Solver {
    Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
}

use crate::support::ir::r;

use crate::support::ir::c;

fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

fn mask(bits: u32) -> u64 {
    if bits == 0 {
        0
    } else {
        u64::MAX >> (64 - bits)
    }
}

fn bounded(register: usize, bits: u32) -> Expr {
    b(BinaryOp::And, r(register), c(mask(bits)))
}

fn inferred_width(expression: &Expr) -> Width {
    let program = Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(2).into(),
                value: expression.clone(),
            }],
            control: Control::Return(r(2)),
        }],
    )
    .unwrap();
    ValueWidths::analyze(&program).width(Reg(2))
}

fn equivalent(solver: &Solver, name: &str, before: &Expr, after: &Expr) {
    assert_eq!(
        solver.check(before, after),
        Verdict::EquivalentUnderModel,
        "positive obligation {name}"
    );
}

fn mutant(solver: &Solver, name: &str, before: &Expr, after: &Expr) {
    let verdict = solver.check(before, after);
    // Solver::check emits Counterexample only after replaying the model in the
    // executable IR and confirming before != after; malformed models fail.
    let Verdict::Counterexample(witness) = verdict else {
        panic!("mutant {name} requires an IR-replayed SAT witness: {verdict:?}");
    };
    assert_ne!(witness.before, witness.after);
    println!("mutant {name}: IR-replayed SAT witness {witness:?}");
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn unsigned_width_transfer_bounds_hold_and_unsafe_narrowing_has_a_witness() {
    use BinaryOp::*;
    let solver = solver();
    let mut cases = Vec::new();
    // Every operator is represented. The declared multiplier fragment has one
    // constant operand: x*3 and high(x*2^63). Symbolic-by-symbolic multiplication
    // is excluded: an initial masked 7-bit product query returned Unknown with
    // the unchanged two-second budget. That is no verdict on excluded cases.
    // Constant shifts include 64 to exercise the IR's count masking.
    for bits in BITS {
        for op in [And, Or, Xor, Add, Sub, Mul, Eq, Ne, Ult, Ule, UMulHigh] {
            let right = match op {
                Mul => c(3),
                UMulHigh => c(1 << 63),
                _ => bounded(1, bits),
            };
            cases.push((format!("{op:?}/{bits}"), b(op, bounded(0, bits), right)));
        }
        for (op, count) in [(Shl, 1), (Shr, 1), (Shl, 64), (Shr, 63)] {
            cases.push((
                format!("{op:?}/{bits}/count-{count}"),
                b(op, bounded(0, bits), c(count)),
            ));
        }
    }
    assert_eq!(cases.len(), 150);
    let mut proved = 0;
    let mut full_u64 = 0;
    for (name, expression) in cases {
        let width = inferred_width(&expression);
        if width == Width::U64 {
            full_u64 += 1;
            continue;
        }
        equivalent(
            &solver,
            &format!("{name}, inferred={width:?}"),
            &expression,
            &b(And, expression.clone(), c(width.mask())),
        );
        proved += 1;
    }
    // This guards against a vacuous analyzer returning U64 for every case.
    assert!(
        (50..=150).contains(&proved),
        "only {proved} nontrivial bounds"
    );
    let sixteen_bit_input = bounded(0, 16);
    assert_eq!(inferred_width(&sixteen_bit_input), Width::U16);
    mutant(
        &solver,
        "unsafe-U8-mask-for-U16-input",
        &sixteen_bit_input,
        &b(And, sixteen_bit_input.clone(), c(Width::U8.mask())),
    );
    println!(
        "width bounds: {proved} UNSAT/EquivalentUnderModel; {full_u64} full-U64 tautologies skipped; 1 SAT mutant; {} solver.check queries",
        proved + 1
    );
}

fn indexed_expression(address: &IndexedAddress) -> Expr {
    b(
        BinaryOp::Add,
        b(
            BinaryOp::Add,
            r(address.register.0),
            c(address.offset as u64),
        ),
        b(BinaryOp::Mul, address.index.clone(), c(address.stride)),
    )
}

// Reg2 is a current-point copy with the supplied honest origin. Substitute it
// on BOTH sides, including if it occurs in the index. Reg0 is the entry value;
// Reg1 is unrestricted and may equal Reg0 (no non-aliasing assumption).
fn honest_origin(expression: &Expr, offset: i64) -> Expr {
    match expression {
        Expr::Register(Reg(2)) => b(BinaryOp::Add, r(0), c(offset as u64)),
        Expr::Binary(op, left, right) => b(
            *op,
            honest_origin(left, offset),
            honest_origin(right, offset),
        ),
        Expr::Const(_) | Expr::Register(_) => expression.clone(),
        _ => panic!("proof cases must be load-free and select-free"),
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn indexed_recovery_preserves_modular_addresses_and_mutants_have_witnesses() {
    use BinaryOp::*;
    let solver = solver();
    let mut cases = Vec::new();
    for offset in [-17, i64::MIN, i64::MAX] {
        for stride in [1, 8, u64::MAX] {
            cases.push((
                format!("copy-offset-{offset}/stride-{stride}"),
                offset,
                b(
                    Sub,
                    b(Add, c(7), b(Add, r(2), b(Mul, r(1), c(stride)))),
                    c(31),
                ),
            ));
        }
    }
    for count in [0, 3, 63, 64, 65, u64::MAX] {
        cases.push((
            format!("shift-count-{count}"),
            -17,
            b(Sub, b(Add, r(2), b(Shl, r(1), c(count))), c(5)),
        ));
    }
    cases.extend([
        (
            "negative-stride".into(),
            -17,
            b(Sub, b(Add, r(2), c(31)), b(Mul, r(1), c(8))),
        ),
        (
            "opaque-current-index".into(),
            -17,
            b(Add, r(2), b(Xor, r(1), c(7))),
        ),
        (
            "index-aliases-entry-base".into(),
            -17,
            b(Add, r(2), b(Mul, r(0), c(8))),
        ),
    ]);
    assert_eq!(cases.len(), 18);
    for (name, offset, original) in &cases {
        let recovered = recover_indexed(original, |expr| match expr {
            Expr::Register(Reg(0)) => Some((Reg(0), 0)),
            Expr::Register(Reg(2)) => Some((Reg(0), *offset)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("declared indexed case must recover: {name}"));
        equivalent(
            &solver,
            name,
            &honest_origin(original, *offset),
            &honest_origin(&indexed_expression(&recovered), *offset),
        );
    }
    let original = b(Add, r(2), b(Mul, r(1), c(8)));
    let recovered =
        recover_indexed(&original, |expr| (expr == &r(2)).then_some((Reg(0), -17))).unwrap();
    let before = honest_origin(&original, -17);
    let mut wrong_stride = recovered.clone();
    wrong_stride.stride = 9;
    mutant(
        &solver,
        "wrong-index-stride",
        &before,
        &indexed_expression(&wrong_stride),
    );
    let mut wrong_offset = recovered;
    wrong_offset.offset = wrong_offset.offset.wrapping_add(1);
    mutant(
        &solver,
        "wrong-base-offset",
        &before,
        &indexed_expression(&wrong_offset),
    );
    println!(
        "indexed recovery: 18 UNSAT/EquivalentUnderModel; 2 SAT mutants; 20 solver.check queries"
    );
}

// Keep the initially inconclusive symbolic multiplier as a distinct probe.
// A successful harness run here does not count Unknown as a proof: the checked
// rewrite must retain the entire original expression on either resource cutoff.
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn symbolic_product_width_probe_retains_the_original_on_resource_cutoff() {
    let before = b(BinaryOp::Mul, bounded(0, 7), bounded(1, 7));
    let width = inferred_width(&before);
    let candidate = b(BinaryOp::And, before.clone(), c(width.mask()));
    let checked = solver().checked_rewrite(&before, &candidate);
    match &checked.verdict {
        Verdict::EquivalentUnderModel => assert_eq!(checked.expression, candidate),
        Verdict::Unknown(UnknownReason::SolverUnknown | UnknownReason::SolverTimeout) => {
            assert_eq!(checked.expression, before)
        }
        other => panic!("unexpected symbolic multiplication outcome: {other:?}"),
    }
    println!(
        "symbolic 7x7 product width probe: {:?}; Unknown is not a positive obligation",
        checked.verdict
    );
}
