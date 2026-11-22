use super::*;
use crate::model::ir::{BinaryOp as B, Control, IrInstruction, Place};

fn source() -> Program {
    let c = Expr::Const;
    let r = |n| Expr::Register(Reg(n));
    let at = |n| Expr::binary(B::Add, r(7), c(n));
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let store = |n, width, value| Assignment {
        destination: Place::Memory {
            address: at(n),
            width,
        },
        value,
    };
    let load = |n, width| Expr::load(at(n), width);
    let row = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        0,
        8,
        vec![
            row(
                0,
                vec![
                    set(0, load(0, Width::U64)),
                    store(32, Width::U64, r(0)),
                    set(0, c(0)),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            row(1, vec![set(2, load(32, Width::U64))], Control::Jump(3)),
            row(2, vec![set(2, load(32, Width::U64))], Control::Jump(3)),
            row(
                3,
                vec![
                    store(
                        48,
                        Width::U16,
                        Expr::unary(
                            UnaryOp::Extract {
                                start: 8,
                                width: Width::U16,
                            },
                            r(2),
                        ),
                    ),
                    set(2, c(0)),
                    set(3, load(49, Width::U8)),
                ],
                Control::Return(r(3)),
            ),
        ],
    )
    .unwrap()
}

#[test]
fn resaved_phi_roots_share_one_snapshot_without_changing_any_observed_prefix() {
    let source = source();
    let base = MemoryValuePlan::analyze(&source).unwrap();
    assert_eq!(base.captures.len(), 2);
    let plan = base.canonicalize(&source).unwrap();
    assert_eq!(plan.captures.len(), 1);
    assert_eq!(plan.merged_snapshots(), 1);
    let candidate = plan.lower(&source).unwrap();
    validate(&source, &plan, &candidate).unwrap();
    let repeated = plan.canonicalize(&source).unwrap();
    assert_eq!(
        repeated.lower(&source).unwrap().instructions(),
        candidate.instructions()
    );
    assert!(repeated.basis.as_ref().unwrap().basis.is_none());
    let mut count = 0;
    for word in [0u64, 1, 0x8877665544332211, u64::MAX] {
        let mut memory = [0xa5; 64];
        memory[..8].copy_from_slice(&word.to_le_bytes());
        for branch in [0, 1] {
            for pointer in [4096, 4097, 4112, 4127, u64::MAX] {
                let input = [word, branch, 0, 0, 0, 0, 0, pointer];
                let mut extended = input.to_vec();
                extended.resize(candidate.register_count(), 0xdeadbeefcafebabe);
                for limit in 0..=6 {
                    let expected = source
                        .run_with_memory(&input, 4096, &memory, limit)
                        .unwrap();
                    let mut actual = candidate
                        .run_with_memory(&extended, 4096, &memory, limit)
                        .unwrap();
                    actual.state.registers.truncate(source.register_count());
                    assert_eq!(actual, expected);
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 280);
}

#[test]
fn derived_roots_reject_wrong_bits_unchecked_facts_nested_witnesses_and_changed_source() {
    let source = source();
    let base = MemoryValuePlan::analyze(&source).unwrap();
    let good = base.canonicalize(&source).unwrap();
    let context = Context::new(&source).unwrap();
    for mutation in 0..3 {
        let mut plan = good.clone();
        match mutation {
            0 => {
                plan.proofs.last_mut().unwrap().key.start = 8;
                plan.facts = value_facts::solve(&context, &plan.proofs).unwrap();
            }
            1 => {
                let base = plan.basis.as_mut().unwrap();
                let phi = context
                    .graph
                    .values
                    .iter()
                    .position(|d| {
                        matches!(
                            d,
                            Definition::Phi {
                                block: 3,
                                register: Reg(2),
                                ..
                            }
                        )
                    })
                    .unwrap();
                base.facts[phi].as_mut().unwrap().start = 8;
            }
            _ => plan.basis.as_mut().unwrap().basis = Some(Box::new(base.clone())),
        }
        let (candidate, count) = rewrite::construct(&source, &plan, &context).unwrap();
        plan.evidence.replaced_reads = count;
        assert!(
            verify::check(&source, &plan, &candidate, &context).is_err(),
            "mutation {mutation}"
        );
        if mutation == 0 {
            let mut memory = [0; 64];
            memory[..8].copy_from_slice(&0x8877665544332211u64.to_le_bytes());
            let input = [0, 0, 0, 0, 0, 0, 0, 4096];
            let mut extended = input.to_vec();
            extended.resize(candidate.register_count(), u64::MAX);
            let expected = source.run_with_memory(&input, 4096, &memory, 8).unwrap();
            let actual = candidate
                .run_with_memory(&extended, 4096, &memory, 8)
                .unwrap();
            assert_ne!(
                actual.status, expected.status,
                "the rejected offset must replay a real counterexample"
            );
        }
    }
    let mut rows = source.instructions().to_vec();
    rows[2].assignments[0].value = Expr::load(Expr::Register(Reg(7)), Width::U64);
    let changed = Program::new(0, 8, rows).unwrap();
    assert!(good.canonicalize(&changed).is_none());
    assert!(good.inspect(&changed).is_err());
}

#[test]
fn composition_keeps_zero_extension_bounds_and_cycles_conservative() {
    let source = source();
    let mut base = MemoryValuePlan::analyze(&source).unwrap();
    let original = Key {
        value: SavedValue::Register(ValueId(0)),
        start: 0,
        width: Width::U16,
    };
    let narrow = Key {
        value: SavedValue::Register(ValueId(1)),
        start: 8,
        width: Width::U8,
    };
    base.facts[0] = Some(narrow);
    let widened = Key {
        width: Width::U16,
        ..narrow
    };
    assert_eq!(
        canonical(&base, original, &mut Budget::new()),
        Some(original)
    );
    assert!(!check_alias(&base, original, widened, &mut Budget::new()).unwrap());
    let a = Key {
        width: Width::U64,
        ..original
    };
    let b = Key {
        value: SavedValue::Register(ValueId(1)),
        ..a
    };
    base.facts[0] = Some(b);
    base.facts[1] = Some(a);
    assert_eq!(canonical(&base, a, &mut Budget::new()), Some(a));
}
