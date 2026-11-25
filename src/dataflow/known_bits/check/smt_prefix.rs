//! All-mask mathematical audit of the prefix carry/borrow equations.
//!
//! These expressions are independently written formulas, not a verified
//! translation of Rust. The finite bridge below checks correspondence on real
//! kernel masks; the separate actual-kernel SMT audit remains necessary.
use super::{B, Expr, K, Path, Reg, Solver, Verdict, b, c, check, kernel, r, verify};
use std::time::{Duration, Instant};

fn conjunction(conditions: impl IntoIterator<Item = Expr>) -> Expr {
    conditions
        .into_iter()
        .fold(c(1), |old, next| b(B::And, old, next))
}

pub(super) fn membership() -> Expr {
    // ZA, OA, ZB, OB, a, b are independent full-width symbolic registers.
    conjunction([
        b(B::Eq, b(B::And, r(0), r(1)), c(0)),
        b(B::Eq, b(B::And, r(2), r(3)), c(0)),
        b(B::Eq, b(B::And, r(4), r(0)), c(0)),
        b(B::Eq, b(B::And, r(4), r(1)), r(1)),
        b(B::Eq, b(B::And, r(5), r(2)), c(0)),
        b(B::Eq, b(B::And, r(5), r(3)), r(3)),
    ])
}

fn known_inputs(bit: u32) -> Expr {
    let both = b(B::And, b(B::Or, r(0), r(1)), b(B::Or, r(2), r(3)));
    b(B::Ne, b(B::And, both, c(1u64 << bit)), c(0))
}

fn incoming(op: B, bit: u32) -> (Expr, Expr) {
    let place = 1u64 << bit;
    let prefix = place - 1;
    let amin = b(B::And, r(1), c(prefix));
    let amax = b(B::And, b(B::Xor, r(0), c(u64::MAX)), c(prefix));
    let bmin = b(B::And, r(3), c(prefix));
    let bmax = b(B::And, b(B::Xor, r(2), c(u64::MAX)), c(prefix));
    match op {
        // Prefix sums cannot overflow u64: each operand is at most 2^63-1.
        B::Add => (
            b(B::Ule, c(place), b(B::Add, amin, bmin)),
            b(B::Ult, b(B::Add, amax, bmax), c(place)),
        ),
        B::Sub => (b(B::Ult, amax, bmin), b(B::Ule, bmax, amin)),
        _ => unreachable!(),
    }
}

fn equation(op: B, bit: u32, force_false: bool) -> Expr {
    let place = 1u64 << bit;
    let (incoming_true, incoming_false) = incoming(op, bit);
    let parity = b(B::And, b(B::Xor, r(1), r(3)), c(place));
    let (premise, prediction) = if force_false {
        // Make the bad prediction on a definitely true carry/borrow. Current
        // input bits remain known, and every membership premise is retained.
        (incoming_true, parity)
    } else {
        (
            b(B::Or, incoming_true.clone(), incoming_false),
            b(B::Xor, parity, Expr::select(incoming_true, c(place), c(0))),
        )
    };
    let discrepancy = b(B::And, b(B::Xor, b(op, r(4), r(5)), prediction), c(place));
    Expr::select(
        conjunction([membership(), known_inputs(bit), premise]),
        discrepancy,
        c(0),
    )
}

fn bounded_check(
    directory: &Path,
    solver: &Solver,
    name: &str,
    value: Expr,
    started: Instant,
) -> Verdict {
    let remaining = Duration::from_secs(295).saturating_sub(started.elapsed());
    if remaining < Duration::from_millis(500) {
        // Preserve the unexecuted query and an explicit Unknown if the whole
        // audit reaches its bound. No missing query can count as a proof.
        let query = verify::pure_query(&super::violation(value, K::constant(0)), &c(0)).unwrap();
        std::fs::write(
            directory.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let result = Verdict::Unknown(verify::UnknownReason::ResourceLimit);
        std::fs::write(
            directory.join(format!("{name}.out")),
            format!("{result:?}\n"),
        )
        .unwrap();
        return result;
    }
    // SAT invokes the solver again to retrieve a replayable model. Reserve
    // both possible subprocess calls, including their timeout grace periods.
    let timeout = ((remaining - Duration::from_millis(400)) / 2).min(Duration::from_secs(2));
    check(
        directory,
        &solver.limited_to(timeout),
        name,
        value,
        K::constant(0),
    )
}

fn concrete_prediction(op: B, left: K, right: K, bit: u32) -> Option<bool> {
    let place = 1u64 << bit;
    if ((left.zero() | left.one()) & (right.zero() | right.one()) & place) == 0 {
        return None;
    }
    let prefix = u128::from(place - 1);
    let (amin, amax) = (
        u128::from(left.one()) & prefix,
        u128::from(!left.zero()) & prefix,
    );
    let (bmin, bmax) = (
        u128::from(right.one()) & prefix,
        u128::from(!right.zero()) & prefix,
    );
    let (yes, no) = match op {
        B::Add => (
            amin + bmin >= u128::from(place),
            amax + bmax < u128::from(place),
        ),
        B::Sub => (amax < bmin, amin >= bmax),
        _ => unreachable!(),
    };
    if !yes && !no {
        None
    } else {
        Some((((left.one() ^ right.one()) & place) != 0) ^ yes)
    }
}

fn finite_bridge() -> usize {
    let mut masks = vec![
        K::UNKNOWN,
        K::constant(0),
        K::constant(1),
        K::constant(u64::MAX),
        K::constant(1 << 63),
        K::constant((1 << 63) - 1),
        K::new(!255, 0).unwrap(),
        K::new(255, 0).unwrap(),
        K::new(0xaaaa_aaaa_aaaa_aaaa, 0x1111_1111_1111_1111).unwrap(),
    ];
    for bit in [0, 1, 7, 31, 63] {
        let place = 1u64 << bit;
        masks.extend([
            K::new(!place, 0).unwrap(),
            K::new(place, 0).unwrap(),
            K::new(0, place).unwrap(),
        ]);
    }
    let mut comparisons = 0;
    for &left in &masks {
        for &right in &masks {
            for op in [B::Add, B::Sub] {
                let actual = kernel::binary(op, left, right);
                for bit in 0..64 {
                    let place = 1u64 << bit;
                    let actual_bit = if actual.zero() & place != 0 {
                        Some(false)
                    } else if actual.one() & place != 0 {
                        Some(true)
                    } else {
                        None
                    };
                    assert_eq!(
                        actual_bit,
                        concrete_prediction(op, left, right, bit),
                        "finite formula/kernel bridge: {op:?}, bit {bit}, {left:?}, {right:?}"
                    );
                    comparisons += 1;
                }
                for a in [left.minimum(), left.maximum()] {
                    for bb in [right.minimum(), right.maximum()] {
                        assert!(actual.contains(op.evaluate(a, bb)));
                    }
                }
            }
        }
    }
    comparisons
}

fn inspect_control(op: B, witness: &verify::Counterexample) -> Result<(), String> {
    let mut values = [None; 6];
    for &(Reg(index), word) in &witness.registers {
        if index >= values.len() || values[index].replace(word).is_some() {
            return Err("unexpected or duplicated witness register".into());
        }
    }
    let [Some(za), Some(oa), Some(zb), Some(ob), Some(a), Some(bb)] = values else {
        return Err("witness must contain all six symbolic registers".into());
    };
    let left = K::new(za, oa).ok_or("invalid left witness mask")?;
    let right = K::new(zb, ob).ok_or("invalid right witness mask")?;
    if !left.contains(a) || !right.contains(bb) {
        return Err("witness violates cube membership".into());
    }
    let place = 1u64 << 63;
    let correct = op.evaluate(a, bb);
    let wrong = (oa ^ ob) & place;
    let actual_mask = kernel::binary(op, left, right);
    if witness.before == 0 || witness.after != 0 || (correct ^ wrong) & place == 0 {
        return Err("forced-false carry/borrow did not replay a discrepancy".into());
    }
    if !actual_mask.contains(correct)
        || concrete_prediction(op, left, right, 63) != Some(correct & place != 0)
        || (actual_mask.zero() | actual_mask.one()) & place == 0
    {
        return Err("actual kernel did not retain the correct witness result bit".into());
    }
    Ok(())
}

#[test]
fn finite_prefix_equations_match_actual_kernel_masks() {
    assert_eq!(finite_bridge(), 73_728);
}

#[test]
fn symbolic_prefix_equations_have_nonvacuous_concrete_premises() {
    use crate::model::ir::Machine;

    let zero = K::constant(0);
    let one = K::constant(1);
    let byte = K::new(!255, 0).unwrap();
    let cases = [
        (B::Add, 63, K::constant(u64::MAX), one, u64::MAX, 1, true),
        (B::Sub, 63, zero, one, 0, 1, true),
        (B::Add, 0, zero, zero, 0, 0, false),
        (B::Sub, 0, zero, zero, 0, 0, false),
        (B::Add, 63, zero, zero, 0, 0, false),
        (B::Sub, 63, zero, zero, 0, 0, false),
        (B::Add, 8, byte, zero, 255, 0, false),
        (B::Sub, 8, byte, zero, 255, 0, false),
        (B::Add, 8, K::constant(255), one, 255, 1, true),
        (B::Sub, 8, zero, one, 0, 1, true),
    ];
    let mut covered = [[false; 2]; 2];
    for (op, bit, left, right, a, bb, expected_incoming) in cases {
        let machine = Machine::new(
            6,
            &[left.zero(), left.one(), right.zero(), right.one(), a, bb],
            0,
        )
        .unwrap();
        let (yes, no) = incoming(op, bit);
        assert_eq!(membership().evaluate(&machine).unwrap(), 1);
        assert_eq!(known_inputs(bit).evaluate(&machine).unwrap(), 1);
        assert_eq!(
            yes.evaluate(&machine).unwrap(),
            u64::from(expected_incoming)
        );
        assert_eq!(
            no.evaluate(&machine).unwrap(),
            u64::from(!expected_incoming)
        );
        let premise = conjunction([membership(), known_inputs(bit), b(B::Or, yes, no)]);
        assert_eq!(premise.evaluate(&machine).unwrap(), 1);
        assert_eq!(
            equation(op, bit, false).evaluate(&machine).unwrap(),
            0,
            "symbolic equation: {op:?}, bit {bit}, {left:?}, {right:?}"
        );
        if expected_incoming {
            assert_eq!(
                equation(op, bit, true).evaluate(&machine).unwrap(),
                1u64 << bit,
                "forced-false symbolic equation must expose {op:?} incoming bit {bit}"
            );
        }
        assert!(kernel::binary(op, left, right).contains(op.evaluate(a, bb)));
        covered[usize::from(op == B::Sub)][usize::from(expected_incoming)] = true;
    }
    assert_eq!(covered, [[true; 2]; 2]);
}

#[test]
#[ignore = "requires Z3 and empty NIRVANA_BITS_PREFIX_OUT managed directory"]
fn all_mask_prefix_equations_have_unsat_proofs_and_replayed_controls() {
    let out = std::path::PathBuf::from(
        std::env::var_os("NIRVANA_BITS_PREFIX_OUT").expect("set NIRVANA_BITS_PREFIX_OUT"),
    );
    std::fs::create_dir_all(&out).unwrap();
    assert!(std::fs::read_dir(&out).unwrap().next().is_none());
    let solver = Solver::new(std::env::var("NIRVANA_Z3").expect("set NIRVANA_Z3"))
        .with_timeout(Duration::from_secs(2));
    let bridge_comparisons = finite_bridge();
    let started = Instant::now();
    let (mut proved, mut positive_sat, mut unknown, mut replayed) = (0, 0, 0, 0);
    let mut failures = Vec::new();
    for (label, op) in [("add", B::Add), ("sub", B::Sub)] {
        for bit in 0..64 {
            let name = format!("prefix-{label}-{bit:02}");
            let result = bounded_check(&out, &solver, &name, equation(op, bit, false), started);
            match result {
                Verdict::EquivalentUnderModel => proved += 1,
                Verdict::Counterexample(_) => positive_sat += 1,
                Verdict::Unknown(_) => unknown += 1,
            }
            if result != Verdict::EquivalentUnderModel {
                failures.push(format!("{name}: {result:?}"));
            }
        }
    }
    for (label, op) in [("lost-carry", B::Add), ("lost-borrow", B::Sub)] {
        let result = bounded_check(&out, &solver, label, equation(op, 63, true), started);
        match &result {
            Verdict::Counterexample(witness) => match inspect_control(op, witness) {
                Ok(()) => replayed += 1,
                Err(error) => failures.push(format!("{label}: {error}; {result:?}")),
            },
            Verdict::Unknown(_) => {
                unknown += 1;
                failures.push(format!("{label}: {result:?}"));
            }
            Verdict::EquivalentUnderModel => {
                failures.push(format!("missing SAT control {label}: {result:?}"))
            }
        }
    }
    std::fs::write(out.join("failures.txt"), failures.join("\n")).unwrap();
    std::fs::write(out.join("summary.json"), format!(
        "{{\"scope\":\"all-mask prefix equations; not a verified Rust translation\",\"positive_queries\":128,\"all_mask_unsat\":{proved},\"positive_sat\":{positive_sat},\"unknown\":{unknown},\"ir_replayed_sat\":{replayed},\"finite_bridge_bit_comparisons\":{bridge_comparisons},\"per_solver_timeout_ms\":2000,\"audit_budget_seconds\":295,\"elapsed_ms\":{},\"failures\":{}}}\n",
        started.elapsed().as_millis(), failures.len())).unwrap();
    println!(
        "{proved}/128 all-mask equation UNSAT; {unknown} Unknown; {replayed}/2 IR-replayed SAT controls; {bridge_comparisons} finite kernel/formula bit comparisons"
    );
    assert_eq!(proved, 128, "{}", failures.join("\n"));
    assert_eq!(replayed, 2, "{}", failures.join("\n"));
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
