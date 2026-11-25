//! Universal mathematical bit-cube rules, not a verified Rust translation.
//! Fixed-count projection covers the concrete word at its actual masked count.
//! Count-class membership and low-six equivalence justify that choice; taking
//! intersections of compatible-count masks only weakens these facts. This is
//! not a model check of the Rust enumeration loop or of every IR operator.
use super::prefix::membership;
use super::{B, Expr, K, Path, Reg, Solver, U, Verdict, Width, b, c, check, kernel, r, verify};
use crate::dataflow::ssa_facts::Domain;
use crate::model::ir::Machine;
use std::time::{Duration, Instant};

#[derive(Clone, Copy)]
enum Kind {
    Binary(B),
    Unary(U),
    FixedShift(B),
    SelectTrue,
    SelectFalse,
    Join,
    CountClass,
    MaskedShift,
}
struct Rule {
    name: String,
    kind: Kind,
    guard: Expr,
    raw: Expr,
    masks: Option<(Expr, Expr)>,
}
fn not(value: Expr) -> Expr {
    b(B::Xor, value, c(u64::MAX))
}
fn both(left: Expr, right: Expr) -> Expr {
    b(B::And, left, right)
}
fn mask_violation(value: Expr, zero: Expr, one: Expr) -> Expr {
    b(
        B::Or,
        both(value.clone(), zero),
        b(B::Xor, both(value, one.clone()), one),
    )
}
impl Rule {
    fn mask(name: String, kind: Kind, output: Expr, zero: Expr, one: Expr) -> Self {
        Self {
            name,
            kind,
            guard: c(1),
            raw: mask_violation(output, zero.clone(), one.clone()),
            masks: Some((zero, one)),
        }
    }
    fn property(name: &str, kind: Kind, guard: Expr, raw: Expr) -> Self {
        Self {
            name: name.into(),
            kind,
            guard,
            raw,
            masks: None,
        }
    }
    fn query(&self) -> Expr {
        Expr::select(
            both(membership(), self.guard.clone()),
            self.raw.clone(),
            c(0),
        )
    }
}

fn boolean_masks(yes: Expr, no: Expr) -> (Expr, Expr) {
    (
        Expr::select(no, c(u64::MAX), c(!1)),
        Expr::select(yes, c(1), c(0)),
    )
}
fn rules() -> Vec<Rule> {
    let mut rules = Vec::new();
    for op in [B::And, B::Or, B::Xor] {
        let (zero, one) = match op {
            B::And => (b(B::Or, r(0), r(2)), both(r(1), r(3))),
            B::Or => (both(r(0), r(2)), b(B::Or, r(1), r(3))),
            B::Xor => (
                b(B::Or, both(r(0), r(2)), both(r(1), r(3))),
                b(B::Or, both(r(0), r(3)), both(r(1), r(2))),
            ),
            _ => unreachable!(),
        };
        rules.push(Rule::mask(
            format!("logic-{op:?}"),
            Kind::Binary(op),
            b(op, r(4), r(5)),
            zero,
            one,
        ));
    }
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let mut unary = vec![U::SignExtend(width)];
        for start in [0, 1, 7, 8, 31, 32, 60, 63, 64, 255] {
            unary.push(U::Extract { start, width });
            let op = B::Insert { start, width };
            rules.push(Rule::mask(
                format!("insert-{}-{start}", width.bits()),
                Kind::Binary(op),
                b(op, r(4), r(5)),
                not(b(op, not(r(0)), not(r(2)))),
                b(op, r(1), r(3)),
            ));
        }
        for (index, op) in unary.into_iter().enumerate() {
            rules.push(Rule::mask(
                format!("unary-{}-{index}", width.bits()),
                Kind::Unary(op),
                Expr::unary(op, r(4)),
                not(Expr::unary(op, not(r(0)))),
                Expr::unary(op, r(1)),
            ));
        }
    }
    for op in [B::Shl, B::Shr, B::AShr] {
        rules.push(Rule::mask(
            format!("fixed-count-{op:?}"),
            Kind::FixedShift(op),
            b(op, r(4), r(5)),
            not(b(op, not(r(0)), r(5))),
            b(op, r(1), r(5)),
        ));
        rules.push(Rule::property(
            &format!("masked-count-{op:?}"),
            Kind::MaskedShift,
            c(1),
            b(B::Xor, b(op, r(4), r(5)), b(op, r(4), both(r(5), c(63)))),
        ));
    }
    let conflict = b(B::Ne, b(B::Or, both(r(1), r(2)), both(r(0), r(3))), c(0));
    for op in [B::Eq, B::Ne, B::Ult, B::Ule] {
        let (yes, no) = match op {
            B::Eq => (c(0), conflict.clone()),
            B::Ne => (conflict.clone(), c(0)),
            B::Ult => (b(B::Ult, not(r(0)), r(3)), b(B::Ule, not(r(2)), r(1))),
            B::Ule => (b(B::Ule, not(r(0)), r(3)), b(B::Ult, not(r(2)), r(1))),
            _ => unreachable!(),
        };
        let (zero, one) = boolean_masks(yes, no);
        rules.push(Rule::mask(
            format!("boolean-{op:?}"),
            Kind::Binary(op),
            b(op, r(4), r(5)),
            zero,
            one,
        ));
    }
    rules.push(Rule::property(
        "select-known-true",
        Kind::SelectTrue,
        b(B::Ne, r(3), c(0)),
        b(B::Eq, r(5), c(0)),
    ));
    rules.push(Rule::property(
        "select-known-false",
        Kind::SelectFalse,
        both(b(B::Eq, r(2), c(u64::MAX)), b(B::Eq, r(3), c(0))),
        b(B::Ne, r(5), c(0)),
    ));
    let (zero, one) = (both(r(0), r(2)), both(r(1), r(3)));
    let mut join = Rule::mask(
        "join-union-containment".into(),
        Kind::Join,
        r(4),
        zero.clone(),
        one.clone(),
    );
    join.raw = b(B::Or, join.raw, mask_violation(r(5), zero, one));
    rules.push(join);
    let n = both(r(5), c(63));
    let count_class = both(
        b(B::Ult, n.clone(), c(64)),
        both(
            b(B::Eq, both(both(n.clone(), r(2)), c(63)), c(0)),
            b(B::Eq, both(both(n, r(3)), c(63)), both(r(3), c(63))),
        ),
    );
    rules.push(Rule::property(
        "compatible-count-class",
        Kind::CountClass,
        c(1),
        b(B::Eq, count_class, c(0)),
    ));
    assert_eq!(rules.len(), 101);
    rules
}

fn controls() -> Vec<Rule> {
    let wrong_and = Rule::mask(
        "wrong-and-one-union".into(),
        Kind::Binary(B::And),
        b(B::And, r(4), r(5)),
        b(B::Or, r(0), r(2)),
        b(B::Or, r(1), r(3)),
    );
    let wrong_sign = Rule::mask(
        "wrong-sign-extension-upper-zero".into(),
        Kind::Unary(U::SignExtend(Width::U8)),
        Expr::unary(U::SignExtend(Width::U8), r(4)),
        c(!255),
        c(0),
    );
    let mut wrong_shift = Rule::mask(
        "wrong-unmasked-shift-at-64".into(),
        Kind::Binary(B::Shl),
        b(B::Shl, r(4), r(5)),
        c(u64::MAX),
        c(0),
    );
    wrong_shift.guard = b(B::Eq, r(5), c(64));
    vec![wrong_and, wrong_sign, wrong_shift]
}

fn bounded_check(directory: &Path, solver: &Solver, rule: &Rule, started: Instant) -> Verdict {
    let remaining = Duration::from_secs(245).saturating_sub(started.elapsed());
    let value = rule.query();
    if remaining < Duration::from_millis(500) {
        let query = verify::pure_query(&super::violation(value, K::constant(0)), &c(0)).unwrap();
        std::fs::write(
            directory.join(format!("{}.smt2", rule.name)),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let result = Verdict::Unknown(verify::UnknownReason::ResourceLimit);
        std::fs::write(
            directory.join(format!("{}.out", rule.name)),
            format!("{result:?}\n"),
        )
        .unwrap();
        return result;
    }
    let timeout = ((remaining - Duration::from_millis(400)) / 2).min(Duration::from_secs(2));
    check(
        directory,
        &solver.limited_to(timeout),
        &rule.name,
        value,
        K::constant(0),
    )
}

fn machine(left: K, right: K, a: u64, bb: u64) -> Machine {
    Machine::new(
        6,
        &[left.zero(), left.one(), right.zero(), right.one(), a, bb],
        0,
    )
    .unwrap()
}
fn actual_mask(kind: Kind, left: K, right: K, bb: u64) -> Option<K> {
    use super::super::CheckingDomain as D;
    match kind {
        Kind::Binary(op) => Some(kernel::binary(op, left, right)),
        Kind::Unary(op) => Some(kernel::unary(op, left)),
        Kind::FixedShift(op) => Some(kernel::binary(op, left, K::constant(bb))),
        Kind::Join => match D::Facts(left).join(D::Facts(right)) {
            D::Facts(value) => Some(value),
            _ => unreachable!(),
        },
        _ => None,
    }
}

#[test]
fn generated_cube_equations_have_nonempty_premises_and_actual_kernel_bridges() {
    use super::super::CheckingDomain as D;
    let masks = [
        K::UNKNOWN,
        K::constant(0),
        K::constant(1),
        K::constant(64),
        K::constant(u64::MAX),
        K::new(!255, 0).unwrap(),
        K::new(0, 1 << 63).unwrap(),
        K::constant(128),
        K::new(63, 64).unwrap(),
        K::new(0xaaaa_aaaa_aaaa_aaaa, 0x1111_1111_1111_1111).unwrap(),
    ];
    for rule in rules() {
        let query = rule.query();
        let mut nonempty = 0;
        for left in masks {
            for right in masks {
                for a in [left.minimum(), left.maximum()] {
                    for bb in [right.minimum(), right.maximum()] {
                        let machine = machine(left, right, a, bb);
                        assert_eq!(membership().evaluate(&machine).unwrap(), 1);
                        assert_eq!(
                            query.evaluate(&machine).unwrap(),
                            0,
                            "{}: {left:?} {right:?}, {a:#x} {bb:#x}",
                            rule.name
                        );
                        if rule.guard.evaluate(&machine).unwrap() == 0 {
                            continue;
                        }
                        nonempty += 1;
                        assert_eq!(
                            rule.raw.evaluate(&machine).unwrap(),
                            0,
                            "active premise: {}",
                            rule.name
                        );
                        if let Some((zero, one)) = &rule.masks {
                            let claim = K::new(
                                zero.evaluate(&machine).unwrap(),
                                one.evaluate(&machine).unwrap(),
                            )
                            .unwrap();
                            let actual = actual_mask(rule.kind, left, right, bb).unwrap();
                            assert_eq!(
                                claim.zero() & !actual.zero(),
                                0,
                                "zero correspondence: {}",
                                rule.name
                            );
                            assert_eq!(
                                claim.one() & !actual.one(),
                                0,
                                "one correspondence: {}",
                                rule.name
                            );
                            if let Kind::FixedShift(op) = rule.kind {
                                let joined = kernel::binary(op, left, right);
                                assert_eq!(joined.zero() & !claim.zero(), 0);
                                assert_eq!(joined.one() & !claim.one(), 0);
                            }
                        }
                        if matches!(rule.kind, Kind::SelectTrue | Kind::SelectFalse) {
                            let actual = D::select(
                                D::Facts(right),
                                D::Facts(K::constant(11)),
                                D::Facts(K::constant(22)),
                            );
                            let wanted = if matches!(rule.kind, Kind::SelectTrue) {
                                11
                            } else {
                                22
                            };
                            assert_eq!(actual.number(), Some(wanted));
                        }
                    }
                }
            }
        }
        assert!(nonempty > 0, "vacuous concrete premises: {}", rule.name);
    }
    // Demonstrate all three generated bad claims are nonvacuous in the IR,
    // even before asking a solver to find independent witnesses.
    let controls = controls();
    for (rule, (left, right, a, bb)) in controls.iter().zip([
        (K::constant(1), K::constant(0), 1, 0),
        (K::constant(128), K::constant(0), 128, 0),
        (K::constant(1), K::constant(64), 1, 64),
    ]) {
        let machine = machine(left, right, a, bb);
        assert_eq!(membership().evaluate(&machine).unwrap(), 1);
        assert_eq!(rule.guard.evaluate(&machine).unwrap(), 1);
        assert_ne!(rule.query().evaluate(&machine).unwrap(), 0, "{}", rule.name);
    }
}

fn inspect_control(rule: &Rule, witness: &verify::Counterexample) -> Result<(), String> {
    let mut values = [None; 6];
    for &(Reg(index), value) in &witness.registers {
        if index >= values.len() || values[index].replace(value).is_some() {
            return Err("unexpected witness registers".into());
        }
    }
    let [Some(za), Some(oa), Some(zb), Some(ob), Some(a), Some(bb)] = values else {
        return Err("missing symbolic registers".into());
    };
    let left = K::new(za, oa).ok_or("invalid left mask")?;
    let right = K::new(zb, ob).ok_or("invalid right mask")?;
    let machine = machine(left, right, a, bb);
    if !left.contains(a)
        || !right.contains(bb)
        || membership().evaluate(&machine).unwrap() != 1
        || rule.guard.evaluate(&machine).unwrap() != 1
        || rule.query().evaluate(&machine).unwrap() == 0
        || witness.before == 0
        || witness.after != 0
    {
        return Err("control lost membership, active guard, or IR-replayed violation".into());
    }
    let output = match rule.kind {
        Kind::Binary(op) => op.evaluate(a, bb),
        Kind::Unary(op) => op.evaluate(a),
        _ => unreachable!(),
    };
    if !actual_mask(rule.kind, left, right, bb)
        .unwrap()
        .contains(output)
    {
        return Err("actual kernel rejected concrete control result".into());
    }
    Ok(())
}

#[test]
#[ignore = "requires Z3 and empty NIRVANA_BITS_CUBE_OUT managed directory"]
fn universal_cube_equations_have_unsat_proofs_and_replayed_controls() {
    let out = std::path::PathBuf::from(
        std::env::var_os("NIRVANA_BITS_CUBE_OUT").expect("set NIRVANA_BITS_CUBE_OUT"),
    );
    std::fs::create_dir_all(&out).unwrap();
    assert!(std::fs::read_dir(&out).unwrap().next().is_none());
    let solver = Solver::new(std::env::var("NIRVANA_Z3").expect("set NIRVANA_Z3"))
        .with_timeout(Duration::from_secs(2));
    let started = Instant::now();
    let (mut proved, mut positive_sat, mut unknown, mut replayed) = (0, 0, 0, 0);
    let mut failures = Vec::new();
    for rule in rules() {
        let result = bounded_check(&out, &solver, &rule, started);
        match &result {
            Verdict::EquivalentUnderModel => proved += 1,
            Verdict::Counterexample(_) => positive_sat += 1,
            Verdict::Unknown(_) => unknown += 1,
        }
        if result != Verdict::EquivalentUnderModel {
            failures.push(format!("{}: {result:?}", rule.name));
        }
    }
    for rule in controls() {
        let result = bounded_check(&out, &solver, &rule, started);
        match &result {
            Verdict::Counterexample(witness) => match inspect_control(&rule, witness) {
                Ok(()) => replayed += 1,
                Err(error) => failures.push(format!("{}: {error}; {result:?}", rule.name)),
            },
            Verdict::Unknown(_) => {
                unknown += 1;
                failures.push(format!("{}: {result:?}", rule.name));
            }
            Verdict::EquivalentUnderModel => {
                failures.push(format!("missing SAT control {}: {result:?}", rule.name))
            }
        }
    }
    std::fs::write(out.join("failures.txt"), failures.join("\n")).unwrap();
    std::fs::write(out.join("summary.json"), format!(
        "{{\"scope\":\"universal bit-cube equations; not a verified Rust translation; no Mul/Div/Rem universal claim\",\"positive_queries\":101,\"all_mask_unsat\":{proved},\"positive_sat\":{positive_sat},\"unknown\":{unknown},\"ir_replayed_sat\":{replayed},\"per_solver_timeout_ms\":2000,\"audit_budget_seconds\":245,\"elapsed_ms\":{},\"failures\":{}}}\n", started.elapsed().as_millis(), failures.len())).unwrap();
    println!(
        "{proved}/101 universal cube equation UNSAT; {unknown} Unknown; {replayed}/3 IR-replayed SAT controls"
    );
    assert_eq!(proved, 101, "{}", failures.join("\n"));
    assert_eq!(replayed, 3, "{}", failures.join("\n"));
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
