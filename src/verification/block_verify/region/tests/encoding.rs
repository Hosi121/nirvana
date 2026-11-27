//! Compare the new exit projection with the original all-path representation.
use super::*;
use crate::model::ir::BinaryOp;
use crate::verification::verify::Solver;
use std::time::Duration;

fn fixture(seed: usize) -> Program {
    let r = |n| Expr::Register(Reg(n));
    let k = Expr::Const;
    let add = |a, b| Expr::binary(BinaryOp::Add, a, b);
    let width = [Width::U8, Width::U16, Width::U32, Width::U64][seed % 4];
    let load = |address| Expr::load(address, width);
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let step = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        0,
        4,
        vec![
            step(0, vec![set(2, add(r(0), k(seed as u64)))], Control::Next),
            step(
                1,
                vec![Assignment {
                    destination: Place::Memory {
                        address: r(0),
                        width,
                    },
                    value: Expr::select(r(1), load(r(3)), r(2)),
                }],
                Control::Next,
            ),
            step(
                2,
                vec![],
                Control::Branch {
                    condition: if seed & 4 == 0 { load(r(3)) } else { r(1) },
                    target: if seed & 8 == 0 { 4 } else { 3 },
                },
            ),
            step(3, vec![set(1, load(r(0)))], Control::Jump(5)),
            step(
                4,
                vec![set(1, Expr::select(r(2), load(add(r(3), k(1))), k(37)))],
                Control::Next,
            ),
            step(
                5,
                vec![set(2, add(r(1), r(2)))],
                Control::Return(if seed & 16 == 0 {
                    r(2)
                } else {
                    load(add(r(0), k(8)))
                }),
            ),
        ],
    )
    .unwrap()
}

fn miter(source: &Program, candidate: Encoder) -> Query {
    let registers: Vec<_> = (0..source.register_count()).map(Reg).collect();
    build_query_encoded(
        source,
        source,
        &registers,
        Observations::uniform(&registers).unwrap(),
        encode::reference_dag,
        candidate,
    )
    .unwrap()
}

#[test]
fn normal_projection_retains_effect_queries_and_reduces_fault_value_phis() {
    let source = fixture(5);
    let registers: Vec<_> = (0..source.register_count()).map(Reg).collect();
    let old = build_query_encoded(
        &source,
        &source,
        &registers,
        Observations::uniform(&registers).unwrap(),
        encode::reference_dag,
        encode::reference_dag,
    )
    .unwrap();
    let new = query(&source, &source, &registers, &registers).unwrap();
    assert!(new.smt2().len() < old.smt2().len());
    assert!(new.smt2().contains("memory_witness"));
    assert!(new.smt2().contains("(xor "));
}

#[test]
#[ignore = "requires NIRVANA_Z3; universal old/new encoding and mutation checks"]
fn reference_and_projected_exit_encodings_agree_for_arbitrary_words_and_ram() {
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(5));
    for seed in 0..32 {
        let source = fixture(seed);
        let query = miter(&source, encode::dag);
        assert_eq!(
            query.check(&solver),
            Verdict::EquivalentUnderModel,
            "seed={seed}"
        );
    }
    fn wrong_fault(
        builder: &mut Builder,
        program: &Program,
        order: &[u64],
        shared: &Registers,
        prefix: &str,
    ) -> Result<(State, String, Vec<String>), Error> {
        let (mut state, complete, names) = encode::dag(builder, program, order, shared, prefix)?;
        state.fault_width = word(0);
        Ok((state, complete, names))
    }
    fn wrong_memory(
        builder: &mut Builder,
        program: &Program,
        order: &[u64],
        shared: &Registers,
        prefix: &str,
    ) -> Result<(State, String, Vec<String>), Error> {
        let (mut state, complete, names) = encode::dag(builder, program, order, shared, prefix)?;
        state.memory = "initial_memory".into();
        Ok((state, complete, names))
    }
    fn wrong_value(
        builder: &mut Builder,
        program: &Program,
        order: &[u64],
        shared: &Registers,
        prefix: &str,
    ) -> Result<(State, String, Vec<String>), Error> {
        let (mut state, complete, names) = encode::dag(builder, program, order, shared, prefix)?;
        state.registers[2] = word(0);
        Ok((state, complete, names))
    }
    for candidate in [wrong_fault as Encoder, wrong_memory, wrong_value] {
        let q = miter(&fixture(0), candidate);
        assert_eq!(solver.run_smt(q.smt2(), &[]).unwrap().trim(), "sat");
        assert_eq!(
            q.check(&solver),
            Verdict::Unknown(UnknownReason::InvalidCounterexample)
        );
    }
    println!(
        "EXIT-PROJECTION old_new_unsat=32 encoding_mutants_sat=3 invalid_rust_replays_rejected=3 all_words=true all_ram=true"
    );
}

#[test]
#[ignore = "requires NIRVANA_Z3; pure value normalization and first-fault replay"]
fn canonical_values_preserve_ordered_loads_and_noncommutative_operations() {
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(5));
    let returned = |value| {
        Program::new(
            0,
            2,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(value),
            }],
        )
        .unwrap()
    };
    let operations = [
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::Eq,
        BinaryOp::Ne,
        BinaryOp::Ult,
        BinaryOp::Ule,
        BinaryOp::UMulHigh,
        BinaryOp::SMulHigh,
        BinaryOp::AShr,
        BinaryOp::UDiv,
        BinaryOp::URem,
        BinaryOp::SDiv,
        BinaryOp::SRem,
        BinaryOp::Insert {
            start: 8,
            width: Width::U32,
        },
        BinaryOp::Insert {
            start: 64,
            width: Width::U64,
        },
    ];
    for op in operations {
        let source = returned(Expr::binary(
            op,
            Expr::Register(Reg(1)),
            Expr::Register(Reg(0)),
        ));
        assert_eq!(
            miter(&source, encode::dag).check(&solver),
            Verdict::EquivalentUnderModel,
            "operation={op:?}"
        );
    }
    let load = |reg| Expr::load(Expr::Register(Reg(reg)), Width::U64);
    let source = returned(Expr::binary(BinaryOp::Add, load(1), load(0)));
    assert_eq!(
        miter(&source, encode::dag).check(&solver),
        Verdict::EquivalentUnderModel
    );
    // Commuting evaluation of the operands changes which load faults first.
    let reordered = returned(Expr::binary(BinaryOp::Add, load(0), load(1)));
    let Verdict::Counterexample(witness) = query(&source, &reordered, &[Reg(0), Reg(1)], &[])
        .unwrap()
        .check(&solver)
    else {
        panic!("reordered loads need a replayed fault counterexample");
    };
    assert_ne!(witness.before.status, witness.after.status);
    println!("VALUE-NORMALIZATION old_new_unsat=22 reordered_load_faults_replayed=1");
}
