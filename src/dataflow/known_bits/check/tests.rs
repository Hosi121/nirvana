use super::*;
use crate::dataflow::known_bits::{self, BitPlan};
use crate::dataflow::ssa::{Definition, ValueId};
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place, Reg};

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn store(address: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address,
            width: Width::U8,
        },
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
fn program(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}
fn returning(expression: Expr) -> Program {
    program(2, vec![ins(0, vec![], Control::Return(expression))])
}

/// A test-only bad producer and its self-check agree that arbitrary XOR is
/// zero. No production injection hook is used; honest SSA leaves stay Unknown.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BadProducer(CheckingDomain);
impl Domain for BadProducer {
    fn bottom() -> Self {
        Self(CheckingDomain::bottom())
    }
    fn unknown() -> Self {
        Self(CheckingDomain::unknown())
    }
    fn constant(n: u64) -> Self {
        Self(CheckingDomain::constant(n))
    }
    fn number(self) -> Option<u64> {
        self.0.number()
    }
    fn join(self, other: Self) -> Self {
        Self(self.0.join(other.0))
    }
    fn finish(self) -> Self {
        Self(self.0.finish())
    }
    fn valid(self) -> bool {
        self.0.valid()
    }
    fn follows_from(self, derived: Self) -> bool {
        self.0.follows_from(derived.0)
    }
    fn unary(op: UnaryOp, value: Self) -> Self {
        Self(CheckingDomain::unary(op, value.0))
    }
    fn binary(op: BinaryOp, a: Self, z: Self) -> Self {
        if op == BinaryOp::Xor {
            Self::constant(0)
        } else {
            Self(CheckingDomain::binary(op, a.0, z.0))
        }
    }
    fn select(c: Self, t: Self, n: Self) -> Self {
        Self(CheckingDomain::select(c.0, t.0, n.0))
    }
    fn load(width: Width) -> Self {
        Self(CheckingDomain::load(width))
    }
    fn binary_cost(op: BinaryOp, a: Self, z: Self) -> usize {
        CheckingDomain::binary_cost(op, a.0, z.0)
    }
}

fn bad_candidate(source: &Program) -> (SsaFunction, Vec<KnownBits>, Program) {
    let graph = SsaFunction::build(source).unwrap();
    let values = vec![KnownBits::UNKNOWN; graph.values.len()];
    let bad = vec![BadProducer::unknown(); graph.values.len()];
    let loads = LoadInputs::default();
    // With no claimed SSA constants, a facts-only independent check succeeds.
    validate_facts(source, &graph, &values, &loads).unwrap();
    let (candidate, _) = ssa_facts::propose_with_loads(source, &graph, &bad, &loads)
        .expect("bad producer must create the inline mutation");
    ssa_facts::validate_with_loads(source, &graph, &bad, &loads, &candidate)
        .expect("the same bad producer accepts its mutation");
    assert!(validate(source, &graph, &values, &loads, &candidate).is_err());
    assert!(known_bits::validate(source, &graph, &values, &candidate).is_err());
    (graph, values, candidate)
}

#[test]
fn independent_numeric_check_rejects_inline_return_branch_and_store_address_mutations() {
    let source = returning(b(BinaryOp::Xor, r(0), r(1)));
    let (_, _, candidate) = bad_candidate(&source);
    assert_eq!(source.execute(&[1, 2], 1).unwrap().value, 3);
    assert_eq!(candidate.execute(&[1, 2], 1).unwrap().value, 0);

    let source = program(
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Xor, r(0), r(1)),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Return(c(7))),
            ins(2, vec![], Control::Return(c(9))),
        ],
    );
    let (_, _, candidate) = bad_candidate(&source);
    assert_eq!(source.execute(&[1, 2], 2).unwrap().value, 9);
    assert_eq!(candidate.execute(&[1, 2], 2).unwrap().value, 7);

    let source = program(
        2,
        vec![ins(
            0,
            vec![store(b(BinaryOp::Xor, r(0), r(1)), c(3))],
            Control::Return(c(4)),
        )],
    );
    let (_, _, candidate) = bad_candidate(&source);
    assert_ne!(
        source.run_with_memory(&[4096, 0], 4096, &[0; 8], 1),
        candidate.run_with_memory(&[4096, 0], 4096, &[0; 8], 1)
    );
}

#[test]
fn partial_unknown_memory_bytes_participate_without_discarding_checked_reads() {
    let source = program(
        4,
        vec![ins(
            0,
            vec![store(r(0), c(3)), set(1, Expr::load(r(0), Width::U16))],
            Control::Return(b(BinaryOp::Eq, b(BinaryOp::And, r(1), c(255)), c(3))),
        )],
    );
    let plan = BitPlan::analyze(&source).unwrap();
    let loads = LoadInputs::analyze(&source, plan.graph());
    assert_eq!(loads.len(), 1);
    assert_eq!(
        loads.bindings().count(),
        0,
        "the old bindings view omits partially unknown bytes"
    );
    known_bits::validate_facts(&source, plan.graph(), plan.values()).unwrap();
    let (candidate, evidence) = plan.propose(&source).unwrap();
    assert_eq!(evidence.memory_loads, 1);
    assert!(matches!(
        candidate.instructions()[0].assignments[1].value,
        Expr::Load {
            width: Width::U16,
            ..
        }
    ));
    assert_eq!(candidate.instructions()[0].control, Control::Return(c(1)));
    for pointer in [4096, 4097, u64::MAX] {
        for bytes in [0, 1, 2, 8] {
            for budget in 0..=2 {
                let ram = vec![0x71; bytes];
                assert_eq!(
                    source.run_with_memory(&[pointer, 0, 0, 0], 4096, &ram, budget),
                    candidate.run_with_memory(&[pointer, 0, 0, 0], 4096, &ram, budget)
                );
            }
        }
    }
    // The high byte remains unconstrained: only the masked byte was proved.
    let mut wrong = source.instructions().to_vec();
    wrong[0].control = Control::Return(c(3));
    let source_word = program(
        4,
        vec![ins(
            0,
            source.instructions()[0].assignments.clone(),
            Control::Return(r(1)),
        )],
    );
    let word_plan = BitPlan::analyze(&source_word).unwrap();
    let wrong = program(4, wrong);
    assert!(
        known_bits::validate(&source_word, word_plan.graph(), word_plan.values(), &wrong).is_err()
    );
}

#[test]
fn may_alias_overwrite_keeps_all_byte_sources_and_prevents_a_false_constant() {
    let source = program(
        4,
        vec![ins(
            0,
            vec![
                store(r(0), c(3)),
                store(r(3), c(4)),
                set(1, Expr::load(r(0), Width::U16)),
            ],
            Control::Return(b(BinaryOp::Eq, b(BinaryOp::And, r(1), c(255)), c(3))),
        )],
    );
    let plan = BitPlan::analyze(&source).unwrap();
    known_bits::validate_facts(&source, plan.graph(), plan.values()).unwrap();
    let mut wrong = source.instructions().to_vec();
    wrong[0].control = Control::Return(c(1));
    let wrong = program(4, wrong);
    assert!(known_bits::validate(&source, plan.graph(), plan.values(), &wrong).is_err());
    let actual = source
        .execute_with_memory(&[4096, 0, 0, 4096], 4096, &[0x71; 8], 1)
        .unwrap();
    assert_eq!(actual.value, 0);
}

#[test]
fn phi_alternatives_and_arbitrary_entry_cannot_publish_self_supporting_bits() {
    let source = program(
        3,
        vec![
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
                vec![set(2, b(BinaryOp::And, r(1), c(0x11)))],
                Control::Return(r(2)),
            ),
        ],
    );
    let plan = BitPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    assert_eq!(
        candidate.instructions()[3].control,
        Control::Return(c(0x11))
    );
    let phi = plan
        .graph()
        .values
        .iter()
        .position(|d| {
            matches!(
                d,
                Definition::Phi {
                    block: 3,
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap();
    let mut wrong = plan.values().to_vec();
    wrong[phi] = KnownBits::constant(0x11);
    assert!(known_bits::validate_facts(&source, plan.graph(), &wrong).is_err());
    let mut broken = plan.graph().clone();
    if let Definition::Phi { inputs, .. } = &mut broken.values[phi] {
        inputs.pop();
    }
    assert!(known_bits::validate_facts(&source, &broken, plan.values()).is_err());

    let source = program(
        2,
        vec![
            ins(
                0,
                vec![set(0, b(BinaryOp::And, r(0), c(15)))],
                Control::Branch {
                    condition: r(1),
                    target: 0,
                },
            ),
            ins(1, vec![], Control::Return(r(0))),
        ],
    );
    let plan = BitPlan::analyze(&source).unwrap();
    let mut wrong = plan.values().to_vec();
    let initial = plan
        .graph()
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { .. }))
        .unwrap();
    wrong[initial] = KnownBits::constant(0);
    assert!(known_bits::validate_facts(&source, plan.graph(), &wrong).is_err());
}

#[test]
fn source_binding_dimensions_and_purity_remain_the_shared_structural_boundary() {
    let source = program(2, vec![ins(0, vec![set(0, c(3))], Control::Return(r(0)))]);
    let plan = BitPlan::analyze(&source).unwrap();
    let different = program(2, vec![ins(0, vec![set(0, c(4))], Control::Return(r(0)))]);
    assert!(known_bits::validate_facts(&different, plan.graph(), plan.values()).is_err());
    assert!(plan.propose(&different).is_none());
    assert!(known_bits::validate_facts(&source, plan.graph(), &[]).is_err());
    let mut wrong = plan.graph().clone();
    wrong.blocks[0].points.last_mut().unwrap().reads[0].value = ValueId(usize::MAX);
    assert!(known_bits::validate_facts(&source, &wrong, plan.values()).is_err());

    let source = returning(b(BinaryOp::Mul, Expr::load(c(u64::MAX), Width::U8), c(0)));
    let graph = SsaFunction::build(&source).unwrap();
    let values = vec![KnownBits::UNKNOWN; graph.values.len()];
    let wrong = returning(c(0));
    assert!(known_bits::validate(&source, &graph, &values, &wrong).is_err());
    assert_ne!(
        source.run_with_memory(&[0, 0], 4096, &[0; 8], 1),
        wrong.run_with_memory(&[0, 0], 4096, &[0; 8], 1)
    );
    // The shared matcher also retains its conservative rule for syntactic
    // loads in lazy arms, including this never-executed arm.
    let source = returning(Expr::select(c(0), Expr::load(c(u64::MAX), Width::U8), c(7)));
    let graph = SsaFunction::build(&source).unwrap();
    let values = vec![KnownBits::UNKNOWN; graph.values.len()];
    assert!(known_bits::validate(&source, &graph, &values, &returning(c(7))).is_err());
    known_bits::validate(&source, &graph, &values, &source).unwrap();
}

#[test]
fn checking_domain_preserves_selection_load_extensions_and_budget_units() {
    let zero = CheckingDomain::constant(0);
    let one = CheckingDomain::constant(1);
    let unknown = CheckingDomain::unknown();
    assert_eq!(CheckingDomain::select(zero, one, zero), zero);
    assert_eq!(CheckingDomain::select(one, one, zero), one);
    assert_eq!(CheckingDomain::select(unknown, one, one), one);
    assert_eq!(CheckingDomain::select(unknown, one, zero).number(), None);
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let CheckingDomain::Facts(bits) = CheckingDomain::load(width) else {
            unreachable!()
        };
        assert_eq!(bits.zero, !width.mask());
        assert_eq!(bits.one, 0);
    }
    assert_eq!(CheckingDomain::binary_cost(BinaryOp::Add, unknown, one), 0);
    let byte = CheckingDomain::Facts(KnownBits { zero: !255, one: 0 });
    assert_eq!(CheckingDomain::binary_cost(BinaryOp::Add, byte, one), 64);
    assert_eq!(
        CheckingDomain::binary_cost(BinaryOp::Shl, byte, unknown),
        64
    );
    assert_eq!(CheckingDomain::binary_cost(BinaryOp::Shl, byte, one), 1);
    assert_eq!(CheckingDomain::binary_cost(BinaryOp::Mul, one, zero), 0);
    // A sound extra lower bound on high products could turn this Unknown
    // into a nonconstant mask, increasing the next Add's charge from 0 to64.
    let near_top = CheckingDomain::Facts(KnownBits {
        zero: 0,
        one: u64::MAX ^ 1,
    });
    let high = CheckingDomain::binary(
        BinaryOp::UMulHigh,
        near_top,
        CheckingDomain::constant(u64::MAX),
    );
    assert_eq!(high, unknown);
    assert_eq!(CheckingDomain::binary_cost(BinaryOp::Add, high, one), 0);
    assert!(!CheckingDomain::Bottom.valid());
    assert!(!CheckingDomain::Facts(KnownBits { zero: 1, one: 1 }).valid());
    assert!(!zero.follows_from(CheckingDomain::Facts(KnownBits {
        zero: u64::MAX,
        one: u64::MAX,
    })));
}
