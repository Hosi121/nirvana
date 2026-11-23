use super::*;
use crate::dataflow::module_values::Projection;
use crate::dataflow::ssa::SsaFunction;
use crate::model::ir::AccessKind;

struct Fixture {
    source: Vec<Instruction>,
    events: Program,
    roles: BTreeMap<Site, PointRole>,
    summaries: call_footprint::Analysis,
    effects: Vec<Effect>,
    opaque: BTreeSet<Site>,
}
impl Fixture {
    fn new(source: Vec<Instruction>, effects: Vec<Effect>, closed: bool) -> Self {
        let summaries = call_footprint::Analysis {
            functions: if closed {
                vec![call_footprint::FunctionSummary {
                    address: 100,
                    closed: true,
                    reason: None,
                    reads: vec![Reg(RSP)],
                    clobbers: vec![Reg(RAX)],
                    preserved: (0..module_ir::REGISTER_COUNT)
                        .filter(|r| *r != RAX)
                        .map(Reg)
                        .collect(),
                    callees: Vec::new(),
                }]
            } else {
                Vec::new()
            },
        };
        let mut projection = Projection {
            instructions: Vec::new(),
            roles: BTreeMap::new(),
            boundaries: Vec::new(),
            assignments: 0,
            nodes: 0,
            guest_registers: module_ir::REGISTER_COUNT,
            summaries: &summaries,
            call_contracts: BTreeMap::new(),
        };
        for instruction in &source {
            projection.instruction(instruction).unwrap();
        }
        let events = Program::new(
            source[0].address(),
            module_ir::REGISTER_COUNT + 1,
            projection.instructions,
        )
        .unwrap();
        let roles = projection.roles;
        let opaque = roles
            .iter()
            .filter_map(|(site, role)| {
                matches!(role, PointRole::OpaqueOutput { .. }).then_some(*site)
            })
            .collect();
        Self {
            source,
            events,
            roles,
            summaries,
            effects,
            opaque,
        }
    }
    fn candidate(&self, effects: &[Effect], opaque: &BTreeSet<Site>) -> Analysis {
        let graph = SsaFunction::build(&self.events).unwrap();
        let candidate = crate::dataflow::memory_ssa::analyze_with_effects(
            &self.events,
            &graph,
            effects,
            opaque,
        )
        .unwrap();
        assert!(candidate.graph_evidence().is_some());
        candidate
    }
    fn check(
        &self,
        effects: &[Effect],
        opaque: &BTreeSet<Site>,
        candidate: &Analysis,
    ) -> Result<(), ValidationError> {
        validate(
            &self.source,
            &self.events,
            &self.roles,
            &self.summaries,
            effects,
            opaque,
            candidate,
        )
        .map(|_| ())
    }
    fn valid(&self) -> Analysis {
        let candidate = self.candidate(&self.effects, &self.opaque);
        self.check(&self.effects, &self.opaque, &candidate).unwrap();
        candidate
    }
    fn mutate_events(&mut self, edit: impl FnOnce(&mut Vec<IrInstruction>)) {
        let mut instructions = self.events.instructions().to_vec();
        edit(&mut instructions);
        self.events = Program::new(
            self.events.cfg().block(self.events.cfg().entry()).start,
            self.events.register_count(),
            instructions,
        )
        .unwrap();
    }
}
fn ret(address: u64) -> Instruction {
    Instruction::Return {
        address,
        size: 1,
        extra_pop: 0,
    }
}
fn call(target: Target) -> Instruction {
    Instruction::Transfer {
        address: 0,
        size: 1,
        target,
        link: Some(1),
    }
}
fn effect(instruction: u64, phase: Phase, kind: EffectKind) -> Effect {
    Effect {
        instruction,
        phase,
        kind,
    }
}
fn load(address: u64, register: usize) -> Instruction {
    Instruction::Core(IrInstruction {
        address,
        size: 1,
        assignments: vec![Assignment {
            destination: Reg(RAX).into(),
            value: Expr::load(Expr::Register(Reg(register)), Width::U64),
        }],
        control: Control::Next,
    })
}

#[test]
fn source_rejects_self_consistent_missing_moved_and_changed_call_effects() {
    let f = Fixture::new(
        vec![call(Target::Plt(200)), ret(1)],
        vec![
            effect(0, Phase::Before, EffectKind::CallStack),
            effect(0, Phase::After, EffectKind::Call),
        ],
        false,
    );
    f.valid();
    let mutations = [
        vec![f.effects[1]], // Omit stack clobber before GOT read.
        vec![f.effects[0]], // Omit callee RAM clobber on continuation.
        vec![
            effect(0, Phase::Before, EffectKind::StringStore),
            f.effects[1],
        ],
        vec![f.effects[0], effect(1, Phase::After, EffectKind::Call)],
    ];
    for effects in mutations {
        let candidate = f.candidate(&effects, &f.opaque);
        assert!(matches!(
            f.check(&effects, &f.opaque, &candidate),
            Err(Invalid(_))
        ));
    }
    // Ordinary memory target expressions precede the stack push. No Before
    // effect is allowed to clobber the target read in this projection.
    let f = Fixture::new(
        vec![
            call(Target::Value(Expr::load(
                Expr::Register(Reg(RDI)),
                Width::U64,
            ))),
            ret(1),
        ],
        vec![effect(0, Phase::After, EffectKind::Call)],
        false,
    );
    f.valid();
    let wrong = [effect(0, Phase::Before, EffectKind::Call)];
    let candidate = f.candidate(&wrong, &f.opaque);
    assert!(matches!(
        f.check(&wrong, &f.opaque, &candidate),
        Err(Invalid(_))
    ));
}

#[test]
fn strings_require_memory_clobbers_and_exact_normal_register_outputs() {
    for copy in [false, true] {
        for repeat in [false, true] {
            for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
                let (instruction, kind) = if copy {
                    (
                        Instruction::MoveString {
                            address: 0,
                            size: 1,
                            width,
                            repeat,
                        },
                        EffectKind::StringMove,
                    )
                } else {
                    (
                        Instruction::StoreString {
                            address: 0,
                            size: 1,
                            width,
                            repeat,
                        },
                        EffectKind::StringStore,
                    )
                };
                let f = Fixture::new(
                    vec![instruction, load(1, RDI), ret(2)],
                    vec![effect(0, Phase::After, kind)],
                    false,
                );
                f.valid();
                assert_eq!(f.opaque.len(), 1 + usize::from(copy) + usize::from(repeat));
                for effects in [
                    vec![],
                    vec![effect(0, Phase::Before, kind)],
                    vec![effect(0, Phase::After, EffectKind::Call)],
                ] {
                    let candidate = f.candidate(&effects, &f.opaque);
                    assert!(matches!(
                        f.check(&effects, &f.opaque, &candidate),
                        Err(Invalid(_))
                    ));
                }
            }
        }
    }
}

#[test]
fn missing_opaque_exclusion_would_turn_divide_result_into_placeholder_zero() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let f = Fixture::new(
            vec![
                Instruction::Divide {
                    address: 0,
                    size: 1,
                    source: Expr::Register(Reg(RCX)),
                    width,
                    signed: false,
                },
                load(1, RAX),
                ret(2),
            ],
            vec![],
            false,
        );
        f.valid();
        assert_eq!(f.opaque.len(), if width == Width::U8 { 1 } else { 2 });
        let rax = f
            .roles
            .iter()
            .find_map(|(site, role)| {
                (*role == PointRole::OpaqueOutput { register: Reg(RAX) }).then_some(*site)
            })
            .unwrap();
        let mut opaque = f.opaque.clone();
        opaque.remove(&rax);
        let candidate = f.candidate(&[], &opaque);
        assert!(
            candidate
                .accesses()
                .iter()
                .any(|a| a.source.site.instruction == 1
                    && a.source.kind == AccessKind::Read
                    && a.source.address
                        == crate::dataflow::address_identity::AddressShape::Absolute(0))
        );
        assert!(matches!(f.check(&[], &opaque, &candidate), Err(Invalid(_))));
        let effects = [effect(0, Phase::After, EffectKind::Call)];
        let candidate = f.candidate(&effects, &f.opaque);
        assert!(matches!(
            f.check(&effects, &f.opaque, &candidate),
            Err(Invalid(_))
        ));
    }
}

#[test]
fn closed_calls_preserve_footprint_registers_but_always_clobber_ram() {
    let mut f = Fixture::new(
        vec![call(Target::Value(Expr::Const(100))), load(1, RDI), ret(2)],
        vec![effect(0, Phase::After, EffectKind::Call)],
        true,
    );
    f.valid();
    assert_eq!(f.opaque.len(), 1);
    let site = *f.opaque.first().unwrap();
    // A destination and role changed together is still a valid register SSA
    // projection, but disagrees with the callee's supplied footprint contract.
    f.mutate_events(|instructions| {
        instructions[0].assignments[site.assignment.unwrap()].destination = Reg(RDI).into()
    });
    f.roles
        .insert(site, PointRole::OpaqueOutput { register: Reg(RDI) });
    let candidate = f.candidate(&f.effects, &f.opaque);
    assert!(matches!(
        f.check(&f.effects, &f.opaque, &candidate),
        Err(Invalid(_))
    ));
}

#[test]
fn source_operands_and_opaque_role_tags_are_not_trusted() {
    let mut f = Fixture::new(
        vec![call(Target::Plt(200)), ret(1)],
        vec![
            effect(0, Phase::Before, EffectKind::CallStack),
            effect(0, Phase::After, EffectKind::Call),
        ],
        false,
    );
    f.mutate_events(|instructions| instructions[0].assignments[0].value = Expr::Const(200));
    let candidate = f.candidate(&f.effects, &f.opaque);
    assert!(matches!(
        f.check(&f.effects, &f.opaque, &candidate),
        Err(Invalid(_))
    ));

    let mut f = Fixture::new(
        vec![call(Target::Value(Expr::Const(100))), ret(1)],
        vec![effect(0, Phase::After, EffectKind::Call)],
        true,
    );
    let site = *f.opaque.first().unwrap();
    f.roles.insert(site, PointRole::Assignment { original: 0 });
    let candidate = f.candidate(&f.effects, &f.opaque);
    assert!(matches!(
        f.check(&f.effects, &f.opaque, &candidate),
        Err(Invalid(_))
    ));
}

#[test]
fn unreachable_declarations_are_checked_without_requiring_retained_generations() {
    let mut unreachable_call = call(Target::Plt(200));
    if let Instruction::Transfer { address, link, .. } = &mut unreachable_call {
        *address = 1;
        *link = Some(2);
    }
    let f = Fixture::new(
        vec![
            Instruction::Core(IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Jump(3),
            }),
            unreachable_call,
            ret(2),
            ret(3),
        ],
        vec![
            effect(1, Phase::Before, EffectKind::CallStack),
            effect(1, Phase::After, EffectKind::Call),
        ],
        false,
    );
    let candidate = f.valid();
    assert!(
        !candidate
            .definitions()
            .iter()
            .any(|d| matches!(d, Definition::Opaque { .. }))
    );
    let missing = f.candidate(&[], &f.opaque);
    assert!(matches!(f.check(&[], &f.opaque, &missing), Err(Invalid(_))));
}

#[test]
fn retained_generations_cannot_omit_a_validated_source_effect() {
    let f = Fixture::new(
        vec![call(Target::Value(Expr::Const(100))), ret(1)],
        vec![effect(0, Phase::After, EffectKind::Call)],
        true,
    );
    let missing = f.candidate(&[], &f.opaque);
    assert!(matches!(
        f.check(&f.effects, &f.opaque, &missing),
        Err(Invalid(_))
    ));
}

#[test]
fn entry_and_normal_continuation_cannot_hide_source_effects() {
    let mut f = Fixture::new(
        vec![call(Target::Value(Expr::Const(100))), ret(1)],
        vec![effect(0, Phase::After, EffectKind::Call)],
        true,
    );
    f.events = Program::new(
        1,
        f.events.register_count(),
        f.events.instructions().to_vec(),
    )
    .unwrap();
    let candidate = f.candidate(&f.effects, &f.opaque);
    assert!(matches!(
        f.check(&f.effects, &f.opaque, &candidate),
        Err(Invalid(_))
    ));

    f.events = Program::new(
        0,
        f.events.register_count(),
        f.events.instructions().to_vec(),
    )
    .unwrap();
    f.mutate_events(|instructions| instructions[0].control = Control::Return(Expr::Const(0)));
    let candidate = f.candidate(&f.effects, &f.opaque);
    assert!(matches!(
        f.check(&f.effects, &f.opaque, &candidate),
        Err(Invalid(_))
    ));
}

#[test]
fn source_resource_limits_stay_distinct_from_malformed_correspondence() {
    let mut f = Fixture::new(vec![ret(0)], vec![], false);
    let candidate = f.valid();
    f.source[0] = Instruction::Divide {
        address: 0,
        size: 1,
        source: Expr::Register(Reg(module_ir::REGISTER_COUNT)),
        width: Width::U64,
        signed: false,
    };
    assert!(matches!(
        f.check(&[], &f.opaque, &candidate),
        Err(Invalid(_))
    ));
    let mut expression = Expr::Const(1);
    for _ in 0..ssa::MAX_DEPTH {
        expression = Expr::load(expression, Width::U64);
    }
    f.source[0] = Instruction::Divide {
        address: 0,
        size: 1,
        source: expression,
        width: Width::U64,
        signed: false,
    };
    assert!(matches!(
        f.check(&[], &f.opaque, &candidate),
        Err(Unavailable(_))
    ));
}
