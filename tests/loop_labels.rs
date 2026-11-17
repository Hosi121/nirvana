use nirvana::ir::{Assignment, BinaryOp, Expr, Place, Reg, Width};
use nirvana::loop_labels::{self, LoopId, LoopLabels, TransferKind, TransferTarget};
use nirvana::structure::Node;

fn condition() -> Expr {
    Expr::Register(Reg(usize::MAX))
}

#[test]
fn preorder_targets_distinguish_identical_loops_and_borrowed_subviews() {
    let nodes = vec![
        Node::Loop(vec![
            Node::If {
                condition: condition(),
                taken: vec![Node::Loop(vec![Node::Loop(vec![
                    Node::ContinueOuter { levels: 2 },
                    Node::BreakOuter { levels: 1 },
                ])])],
                not_taken: vec![Node::Loop(vec![Node::ContinueOuter { levels: 1 }])],
            },
            Node::Loop(vec![Node::Continue]),
        ]),
        Node::Loop(vec![Node::Break]),
        Node::Loop(vec![Node::Break]),
    ];
    let original = nodes.clone();
    let plan = LoopLabels::analyze(&nodes).unwrap();
    let Node::Loop(body) = &nodes[0] else {
        panic!()
    };
    let Node::If {
        taken, not_taken, ..
    } = &body[0]
    else {
        panic!()
    };
    let Node::Loop(middle) = &taken[0] else {
        panic!()
    };
    let Node::Loop(inner) = &middle[0] else {
        panic!()
    };
    let Node::Loop(other) = &not_taken[0] else {
        panic!()
    };
    assert_eq!(plan.loop_count(), 7);
    assert!(plan.has_transfers());
    for (node, id) in [
        (&nodes[0], 0),
        (&taken[0], 1),
        (&middle[0], 2),
        (&not_taken[0], 3),
        (&body[1], 4),
        (&nodes[1], 5),
        (&nodes[2], 6),
    ] {
        assert_eq!(plan.loop_id(node), Some(LoopId(id)));
    }
    let again = TransferTarget {
        loop_id: LoopId(0),
        kind: TransferKind::Continue,
    };
    let after = TransferTarget {
        loop_id: LoopId(1),
        kind: TransferKind::Break,
    };
    assert_eq!(plan.target(&inner[0]), Some(again));
    assert_eq!(plan.target(&inner[1]), Some(after));
    assert_eq!(plan.target(&other[..][0]), Some(again));
    assert_eq!(plan.continue_label(&nodes[0]), Some(again));
    assert_eq!(plan.break_label(&taken[0]), Some(after));
    assert_eq!(again.label(), "nirvana_loop_0_continue");
    assert_eq!(after.to_string(), "nirvana_loop_1_break");
    for node in [&middle[0], &not_taken[0], &body[1], &nodes[1], &nodes[2]] {
        assert_eq!(plan.continue_label(node), None);
        assert_eq!(plan.break_label(node), None);
    }
    assert_eq!(
        plan.loop_id(&original[0]),
        None,
        "cloned trees need a separate plan"
    );
    assert_eq!(plan.target(&Node::ContinueOuter { levels: 2 }), None);
    assert_eq!(nodes, original);
}

#[test]
fn local_and_outer_transfers_require_lexically_valid_targets() {
    for node in [
        Node::Break,
        Node::Continue,
        Node::BreakOuter { levels: 1 },
        Node::ContinueOuter { levels: 0 },
    ] {
        assert!(LoopLabels::analyze(&[node]).is_none());
    }
    for levels in [0, 1, 2, usize::MAX] {
        assert!(LoopLabels::analyze(&[Node::Loop(vec![Node::ContinueOuter { levels }])]).is_none());
    }
    for node in [
        Node::BreakOuter { levels: 0 },
        Node::ContinueOuter { levels: 2 },
        Node::BreakOuter { levels: usize::MAX },
    ] {
        assert!(LoopLabels::analyze(&[Node::Loop(vec![Node::Loop(vec![node])])]).is_none());
    }
    let nodes = vec![Node::Loop(vec![Node::If {
        condition: condition(),
        taken: vec![Node::Break],
        not_taken: vec![Node::Continue],
    }])];
    let plan = LoopLabels::analyze(&nodes).unwrap();
    assert!(!plan.has_transfers());
    assert_eq!(plan.continue_label(&nodes[0]), None);
    assert_eq!(plan.break_label(&nodes[0]), None);
    assert_eq!(plan.target(&Node::Break), None);
    assert_eq!(LoopLabels::analyze(&[]).unwrap().loop_count(), 0);
}

#[test]
fn sparse_registers_loads_and_lazy_memory_are_opaque_unchanged_data() {
    let value = Expr::select(
        condition(),
        Expr::load(Expr::Const(u64::MAX), Width::U64),
        Expr::binary(BinaryOp::Add, condition(), Expr::Const(1)),
    );
    let nodes = vec![Node::Step {
        address: u64::MAX,
        assignments: vec![Assignment {
            destination: Place::Register(Reg(usize::MAX)),
            value,
        }],
    }];
    let original = nodes.clone();
    assert!(!LoopLabels::analyze(&nodes).unwrap().has_transfers());
    assert_eq!(nodes, original);
}

#[test]
fn whole_tree_bounds_cover_nodes_values_addresses_and_unselected_arms() {
    assert!(
        LoopLabels::analyze(&vec![
            Node::Return(Expr::Const(0));
            loop_labels::MAX_NODES + 1
        ])
        .is_none()
    );
    let mut nested = Node::Return(Expr::Const(0));
    for _ in 0..=loop_labels::MAX_DEPTH {
        nested = Node::Loop(vec![nested]);
    }
    assert!(LoopLabels::analyze(&[nested]).is_none());
    let mut deep = Expr::Const(0);
    for _ in 0..=loop_labels::MAX_EXPRESSION_DEPTH {
        deep = Expr::load(deep, Width::U8);
    }
    let hidden = Node::Return(Expr::select(Expr::Const(1), Expr::Const(0), deep.clone()));
    assert!(LoopLabels::analyze(&[hidden]).is_none());
    let destination = Node::Step {
        address: 0,
        assignments: vec![Assignment {
            destination: Place::Memory {
                address: deep,
                width: Width::U8,
            },
            value: Expr::Const(0),
        }],
    };
    assert!(LoopLabels::analyze(&[destination]).is_none());
    fn balanced(leaves: usize) -> Expr {
        if leaves == 1 {
            return Expr::Const(0);
        }
        Expr::binary(
            BinaryOp::Add,
            balanced(leaves / 2),
            balanced(leaves - leaves / 2),
        )
    }
    assert!(LoopLabels::analyze(&[Node::Return(balanced(1 << 16))]).is_none());
    const {
        assert!(loop_labels::MAX_WORK > loop_labels::MAX_NODES);
    }
}

#[test]
fn label_budget_falls_back_atomically_to_cfg_and_preserves_structure_evidence() {
    use nirvana::ir::{Control, IrInstruction, Program};
    fn balanced(leaves: usize) -> Expr {
        if leaves == 1 {
            return Expr::Const(1);
        }
        Expr::binary(
            BinaryOp::Add,
            balanced(leaves / 2),
            balanced(leaves - leaves / 2),
        )
    }
    let program = Program::new(
        0,
        0,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(balanced(1 << 16)),
        }],
    )
    .unwrap();
    let function = nirvana::structure::StructuredFunction::recover(&program).unwrap();
    let output = nirvana::emit::emit_c(&program);
    assert_eq!(
        output.fallback_reason,
        Some(nirvana::structure::StructureError::LoopLabelsUnavailable)
    );
    assert!(output.code.contains("goto bb0;"));
    assert!(!output.code.contains("nirvana_loop_"));
    assert_eq!(output.structure_evidence, Some(function.evidence()));
    assert_eq!(output.structure_stats, Some(function.stats()));
}

#[allow(dead_code)]
#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

#[test]
fn full_register_c_matches_nested_effects_return_every_register_memory_and_first_fault() {
    use nirvana::ir::{AccessKind, RunStatus};
    use std::fmt::Write as _;
    let scratch = native::Scratch::new();
    let mut comparisons = 0;
    for source_opt in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("nested{source_opt}.o"));
        native::object(
            &native::fixture_root().join("recovery/nested-transfer-effects.c"),
            &object,
            source_opt,
            "fixture",
        );
        let lifted =
            nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
        let program = &lifted.program;
        let instructions = program.instructions().to_vec();
        let output = nirvana::emit::emit_c(program);
        assert!(
            output.fallback_reason.is_none(),
            "{:?}",
            output.fallback_reason
        );
        assert!(output.structure_evidence.is_some());
        assert!(!output.code.contains("nirvana_transfer"));
        assert!(!output.code.contains("nirvana_continue"));
        if source_opt == "-O2" {
            assert!(output.code.contains("goto nirvana_loop_"));
        }
        let count = program.register_count();
        let mut input = String::new();
        let mut expected = Vec::new();
        let (mut returns, mut faults) = (0, 0);
        for address in [4096u64, 4097, 4128, 4336, 4344, 4351, 0xffff, u64::MAX] {
            for mode in 0..8u64 {
                let words = [
                    mode,
                    0x8123456789abcdef,
                    0x1020304050607080,
                    0xfedcba9876543210,
                ];
                writeln!(
                    input,
                    "{address} {} {} {} {}",
                    words[0], words[1], words[2], words[3]
                )
                .unwrap();
                let mut memory = (0usize..256)
                    .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                    .collect::<Vec<_>>();
                for (i, word) in words.into_iter().enumerate() {
                    if let Some(offset) = address
                        .checked_add(i as u64 * 8)
                        .and_then(|p| p.checked_sub(4096))
                        .filter(|o| *o <= 248)
                    {
                        memory[offset as usize..offset as usize + 8]
                            .copy_from_slice(&word.to_le_bytes());
                    }
                }
                let mut registers = (0..count)
                    .map(|i| {
                        0x123456789abcdef0u64
                            .wrapping_add((i as u64).wrapping_mul(0x0102030405060708))
                    })
                    .collect::<Vec<_>>();
                registers[nirvana::x86::RDI] = address;
                registers[nirvana::x86::RSP] = 4352;
                let report = program
                    .run_with_memory(&registers, 4096, &memory, 100_000)
                    .unwrap();
                let mut row = match report.status {
                    RunStatus::Returned(value) => {
                        returns += 1;
                        vec![0, 0, 0, 0, value]
                    }
                    RunStatus::Fault(fault) => {
                        faults += 1;
                        vec![
                            1,
                            fault.address,
                            if fault.access == AccessKind::Read {
                                1
                            } else {
                                2
                            },
                            fault.width.bytes() as u64,
                            0,
                        ]
                    }
                    RunStatus::Suspended => panic!(
                        "bounded native cohort suspended: {source_opt} address={address:#x} mode={mode}"
                    ),
                };
                row.extend(report.state.registers);
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
                );
                expected.push(row);
            }
        }
        assert!(returns > 0 && faults > 0);
        let mut code = checked_c::instrument(&output.code);
        write!(code,r#"
#undef abort
#include <inttypes.h>
#include <stdio.h>
static jmp_buf jump;
static uint8_t memory[256];
static uint64_t registers[{count}],result;
static unsigned fault;
_Noreturn void nirvana_test_abort(void) {{ longjmp(jump,1); }}
int main(void) {{
    uint64_t address,input[4];
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,&address,&input[0],&input[1],&input[2],&input[3])==5) {{
        for(unsigned i=0;i<256;++i) memory[i]=(uint8_t)(i*29+7);
        for(unsigned j=0;j<4;++j) if(address<=UINT64_MAX-j*UINT64_C(8)) {{
            uint64_t at=address+j*UINT64_C(8);
            if(at>=4096 && at-4096<=248) for(unsigned i=0;i<8;++i) memory[at-4096+i]=(uint8_t)(input[j]>>(i*8));
        }}
        for(unsigned i=0;i<{count};++i) registers[i]=UINT64_C(0x123456789abcdef0)+(uint64_t)i*UINT64_C(0x0102030405060708);
        registers[{rdi}]=address; registers[{rsp}]=4352;
        result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        if(setjmp(jump)==0) result=nirvana_fn(registers,memory,4096,sizeof(memory)); else fault=1;
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64,fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,fault?nirvana_test_width:UINT64_C(0),result);
        for(unsigned i=0;i<{count};++i) printf(" %" PRIu64,registers[i]);
        for(unsigned j=0;j<32;++j) {{ uint64_t word=0; for(unsigned i=0;i<8;++i) word|=(uint64_t)memory[j*8+i]<<(i*8); printf(" %" PRIu64,word); }}
        putchar('\n');
    }}
}}
"#,rdi=nirvana::x86::RDI,rsp=nirvana::x86::RSP).unwrap();
        let source = scratch.0.join(format!("full-register{source_opt}.c"));
        std::fs::write(&source, &code).unwrap();
        if let Some(directory) = std::env::var_os("NIRVANA_LOOP_LABEL_ARTIFACTS") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            let stem = format!("full-register{}", &source_opt[1..]);
            std::fs::write(directory.join(format!("{stem}.c")), &code).unwrap();
            std::fs::write(directory.join(format!("{stem}.inputs")), &input).unwrap();
            std::fs::write(
                directory.join(format!("{stem}.expected.json")),
                format!("{expected:?}\n"),
            )
            .unwrap();
        }
        for generated_opt in ["-O0", "-O2"] {
            let object = scratch
                .0
                .join(format!("full-register{source_opt}{generated_opt}.o"));
            let binary = object.with_extension("bin");
            native::object(&source, &object, generated_opt, "nirvana_fn");
            native::link(&[&object], &binary);
            assert_eq!(
                native::run_fields(&binary, &input, 5 + count + 32),
                expected,
                "{source_opt} -> {generated_opt}"
            );
            comparisons += expected.len();
        }
        assert_eq!(program.instructions(), instructions);
        println!(
            "full-register {source_opt}: {returns} returns / {faults} exact faults across 64 inputs"
        );
    }
    assert_eq!(comparisons, 256);
}
