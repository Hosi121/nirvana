use super::*;
use crate::model::ir::{BinaryOp as B, Control, IrInstruction, Place};

fn source(offset: u64, initialized: bool) -> Program {
    let r = |n| Expr::Register(Reg(n));
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let ins = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![
                    Assignment {
                        destination: Place::Memory {
                            address: r(7),
                            width: Width::U64,
                        },
                        value: r(0),
                    },
                    set(0, Expr::Const(0)),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            ins(
                1,
                vec![set(2, Expr::load(r(7), Width::U8))],
                Control::Jump(3),
            ),
            ins(
                2,
                if initialized {
                    vec![set(
                        2,
                        Expr::load(Expr::binary(B::Add, r(7), Expr::Const(offset)), Width::U8),
                    )]
                } else {
                    vec![]
                },
                Control::Jump(3),
            ),
            ins(3, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap()
}

#[test]
fn independent_checker_rejects_a_forged_phi_and_replays_its_wrong_return() {
    for initialized in [false, true] {
        let source = source(1, initialized);
        let context = Context::new(&source).unwrap();
        let (proofs, captures) = analyze::collect(&context, RecoveryPolicy::Source, true).unwrap();
        let mut facts = solve(&context, &proofs).unwrap();
        let key = proofs.iter().find(|p| p.site.instruction == 1).unwrap().key;
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
        assert_eq!(facts[phi], None);
        facts[phi] = Some(key);
        assert!(matches!(
            validate(&context, &proofs, &facts),
            Err(SsaError::Malformed("saved slice phi input"))
        ));
        let mut plan = MemoryValuePlan {
            source_registers: source.register_count(),
            evidence: MemoryValueEvidence {
                ssa: context.evidence,
                proved_loads: proofs.len(),
                snapshot_values: captures.len(),
                replaced_reads: 0,
            },
            proofs,
            captures,
            facts,
        };
        let (candidate, count) = rewrite::construct(&source, &plan, &context).unwrap();
        plan.evidence.replaced_reads = count;
        assert!(super::super::verify::check(&source, &plan, &candidate, &context).is_err());
        let mut input = vec![0; 8];
        input[0] = 0x3412;
        input[1] = 1;
        input[2] = 0x56;
        input[7] = 4096;
        let expected = source
            .execute_with_memory(&input, 4096, &[0; 32], 4)
            .unwrap();
        input.resize(candidate.register_count(), u64::MAX);
        let actual = candidate
            .execute_with_memory(&input, 4096, &[0; 32], 4)
            .unwrap();
        assert_ne!(expected.value, actual.value);
    }
}

#[test]
fn seed_claims_and_arbitrary_initial_values_have_independent_checks() {
    let source = source(0, true);
    let context = Context::new(&source).unwrap();
    let plan = MemoryValuePlan::analyze(&source).unwrap();
    let mut facts = vec![None; plan.facts.len()];
    let seed = context
        .point(plan.proofs[0].site)
        .unwrap()
        .definition
        .unwrap()
        .0;
    let mut key = plan.facts[seed].unwrap();
    key.start += 8;
    facts[seed] = Some(key);
    assert!(matches!(
        validate(&context, &plan.proofs, &facts),
        Err(SsaError::Malformed("saved slice changed seed"))
    ));
    let mut facts = plan.facts.clone();
    let initial = context
        .graph
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { register: Reg(2) }))
        .unwrap();
    facts[initial] = Some(plan.proofs[0].key);
    assert!(matches!(
        validate(&context, &plan.proofs, &facts),
        Err(SsaError::Malformed("saved slice arbitrary initial value"))
    ));
}
