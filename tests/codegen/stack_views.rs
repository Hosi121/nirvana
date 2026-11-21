use crate::support::native;

use native::{Scratch, link, object, run};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c, emit_readable_c_with_options};
use std::fmt::Write as _;

use crate::support::ir::c;
use crate::support::ir::r;
fn offset(n: u64) -> Expr {
    Expr::binary(BinaryOp::Sub, r(0), c(n))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn options() -> ReadableOptions {
    ReadableOptions {
        stack_register: Some(Reg(0)),
        recover_objects: false,
        coalesce_locals: true,
        compact_memory: false,
    }
}

#[test]
fn named_views_preserve_overlaps_external_aliases_and_entry_stack_after_register_changes() {
    let program = Program::new(
        0,
        5,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    set(2, offset(8)),
                    store(r(2), Width::U64, c(0x8877665544332211)),
                    store(r(1), Width::U8, c(0xff)),
                    set(3, Expr::load(offset(6), Width::U32)),
                    set(0, Expr::binary(BinaryOp::Add, r(0), c(16))),
                ],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(4, Expr::load(offset(24), Width::U16))],
                control: Control::Return(Expr::binary(BinaryOp::Add, r(3), r(4))),
            },
        ],
    )
    .unwrap();
    let baseline = emit_readable_c(&program).unwrap();
    assert!(
        baseline.stack_views.is_empty(),
        "no architecture assumed by generic IR API"
    );
    let output = emit_readable_c_with_options(&program, options()).unwrap();
    assert_eq!(output.stack_views.len(), 2);
    assert_eq!(output.stack_views[0].offset, -8);
    assert_eq!(output.stack_views[0].overlaps, [1]);
    assert_eq!(output.stack_views[1].overlaps, [0]);
    assert!(output.code.contains("nirvana_view_load(&m, stack_0"));
    assert!(output.code.contains("nirvana_view_store(&m, stack_0"));
    assert!(
        output.code.contains("nirvana_store(&m, arg1"),
        "external alias retained"
    );
    let scratch = Scratch::new();
    let args = output
        .parameters
        .iter()
        .map(|r| format!("r[{}]", r.0))
        .collect::<Vec<_>>()
        .join(", ");
    let harness = format!(
        r#"
#include <stdio.h>
#include <inttypes.h>
int main(void) {{
    uint64_t base, alias;
    while (scanf("%" SCNu64 " %" SCNu64, &base, &alias) == 2) {{
        uint8_t memory[32];
        for (unsigned i = 0; i < 32; ++i) memory[i] = (uint8_t)(i * 7 + 3);
        uint64_t r[5] = {{base + 16, base + alias, 9, 13, 17}};
        uint64_t value = nirvana_readable({args}, memory, base, sizeof(memory));
        printf("%" PRIu64, value);
        for (unsigned i = 0; i < 4; ++i) {{
            uint64_t word = 0;
            for (unsigned j = 0; j < 8; ++j) word |= (uint64_t)memory[i*8+j] << (j*8);
            printf(" %" PRIu64, word);
        }}
        puts("");
    }}
}}
"#
    );
    let mut inputs = String::new();
    let mut expected = Vec::new();
    for base in [0, 0x1000, u64::MAX - 31] {
        for alias in [0, 8, 9, 10, 15, 31] {
            writeln!(inputs, "{base} {alias}").unwrap();
            let memory: Vec<_> = (0..32).map(|i| (i * 7 + 3) as u8).collect();
            let execution = program
                .execute_with_memory(&[base + 16, base + alias, 9, 13, 17], base, &memory, 2)
                .unwrap();
            let mut result = vec![execution.value];
            result.extend(
                execution
                    .memory
                    .chunks_exact(8)
                    .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
            );
            expected.push(result);
        }
    }
    for optimization in ["-O0", "-O2"] {
        let source = scratch.0.join(format!("views{optimization}.c"));
        std::fs::write(&source, output.code.clone() + &harness).unwrap();
        let compiled = source.with_extension("o");
        let binary = source.with_extension("bin");
        object(&source, &compiled, optimization, "nirvana_readable");
        link(&[&compiled], &binary);
        assert_eq!(run(&binary, &inputs), expected);
    }
}

#[test]
fn faulting_address_expressions_and_dynamic_stack_updates_remain_raw() {
    let faulting_address = Expr::select(Expr::load(c(0xffff), Width::U8), offset(8), offset(8));
    let program = Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                store(offset(8), Width::U64, c(7)),
                set(2, Expr::load(faulting_address, Width::U64)),
                set(0, r(1)),
                store(offset(8), Width::U8, c(9)),
            ],
            control: Control::Return(r(2)),
        }],
    )
    .unwrap();
    let output = emit_readable_c_with_options(&program, options()).unwrap();
    assert_eq!(output.stack_views.len(), 1);
    assert_eq!(output.stack_views[0].write_sites, 1);
    assert_eq!(output.stack_views[0].read_sites, 0);
    assert!(output.code.contains("nirvana_load(&m, 65535, 1)"));
    assert!(output.code.contains("nirvana_store(&m, arg1 - 8"));
}

#[test]
fn generated_c_checks_store_destination_before_rhs_and_keeps_pre_fault_memory() {
    let program = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                store(offset(8), Width::U64, c(0x8877665544332211)),
                store(offset(1), Width::U64, Expr::load(r(1), Width::U8)),
                store(offset(8), Width::U8, c(0xff)),
            ],
            control: Control::Return(c(17)),
        }],
    )
    .unwrap();
    compare_faulting_c(&program);
}

#[test]
fn generated_c_preserves_faulting_select_conditions_in_addresses() {
    let program = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                store(offset(8), Width::U64, c(0x8877665544332211)),
                set(
                    1,
                    Expr::load(
                        Expr::select(Expr::load(r(1), Width::U8), offset(8), offset(8)),
                        Width::U64,
                    ),
                ),
                store(offset(8), Width::U8, c(0xff)),
            ],
            control: Control::Return(c(17)),
        }],
    )
    .unwrap();
    compare_faulting_c(&program);
}

#[test]
fn generated_c_retains_dead_faulting_loads_and_full_width_bounds() {
    let program = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                store(offset(8), Width::U64, c(0x8877665544332211)),
                set(1, Expr::load(offset(1), Width::U64)),
                store(offset(8), Width::U8, c(0xff)),
            ],
            control: Control::Return(c(17)),
        }],
    )
    .unwrap();
    compare_faulting_c(&program);
}

fn compare_faulting_c(program: &Program) {
    let scratch = Scratch::new();
    for with_views in [false, true] {
        let output = if with_views {
            emit_readable_c_with_options(program, options()).unwrap()
        } else {
            emit_readable_c(program).unwrap()
        };
        let args = output
            .parameters
            .iter()
            .map(|r| format!("r[{}]", r.0))
            .collect::<Vec<_>>()
            .join(", ");
        // Instrument the existing bounds check and intercept its abort. Static
        // storage survives longjmp; no modified automatic local is read after it.
        let code = output.code.replace(
            "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {",
            "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) { nirvana_test_address = address;"
        );
        let harness = format!(
            r#"
#undef abort
#include <stdio.h>
#include <inttypes.h>
static jmp_buf nirvana_test_jump;
static uint8_t nirvana_test_memory[16];
static uint64_t nirvana_test_result;
static unsigned nirvana_test_fault;
_Noreturn void nirvana_test_abort(void) {{ longjmp(nirvana_test_jump, 1); }}
int main(void) {{
    uint64_t stack, rhs;
    while (scanf("%" SCNu64 " %" SCNu64, &stack, &rhs) == 2) {{
        for (unsigned i = 0; i < 16; ++i) nirvana_test_memory[i] = (uint8_t)(i + 1);
        nirvana_test_result = 0; nirvana_test_fault = 0;
        uint64_t r[2] = {{stack, rhs}};
        if (setjmp(nirvana_test_jump) == 0)
            nirvana_test_result = nirvana_readable({args}, nirvana_test_memory, UINT64_C(4096), sizeof(nirvana_test_memory));
        else nirvana_test_fault = 1;
        uint64_t words[2] = {{0, 0}};
        for (unsigned i = 0; i < 16; ++i) words[i/8] |= (uint64_t)nirvana_test_memory[i] << ((i%8)*8);
        printf("%u %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
            nirvana_test_fault, nirvana_test_fault ? nirvana_test_address : UINT64_C(0), words[0], words[1], nirvana_test_result);
    }}
}}
"#
        );
        let prefix = "#include <stdint.h>\n#include <setjmp.h>\nstatic uint64_t nirvana_test_address;\n_Noreturn void nirvana_test_abort(void);\n#define abort nirvana_test_abort\n";
        let mut inputs = String::new();
        let mut expected = Vec::new();
        for stack in [0x1008, 0x1010] {
            for rhs in [0x1000, 0xffff] {
                writeln!(inputs, "{stack} {rhs}").unwrap();
                let memory: Vec<u8> = (1..=16).collect();
                let report = program
                    .run_with_memory(&[stack, rhs], 0x1000, &memory, 1)
                    .unwrap();
                let (fault, address, result) = match report.status {
                    nirvana::ir::RunStatus::Fault(f) => (1, f.address, 0),
                    nirvana::ir::RunStatus::Returned(v) => (0, 0, v),
                    _ => unreachable!(),
                };
                let words: Vec<_> = report
                    .state
                    .memory
                    .chunks_exact(8)
                    .map(|word| u64::from_le_bytes(word.try_into().unwrap()))
                    .collect();
                expected.push(vec![fault, address, words[0], words[1], result]);
            }
        }
        for optimization in ["-O0", "-O2"] {
            let source = scratch
                .0
                .join(format!("faults{with_views}{optimization}.c"));
            std::fs::write(&source, prefix.to_owned() + &code + &harness).unwrap();
            let compiled = source.with_extension("o");
            let binary = source.with_extension("bin");
            object(&source, &compiled, optimization, "nirvana_readable");
            link(&[&compiled], &binary);
            assert_eq!(
                run(&binary, &inputs),
                expected,
                "views={with_views}, {optimization}"
            );
        }
    }
}
