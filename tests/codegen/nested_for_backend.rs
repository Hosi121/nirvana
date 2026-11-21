//! Actual O0 nested-loop fixtures, emitted as checked C with outer for headers.
//! Compare all 256 guest bytes, return values, and exact first faults against
//! lifted IR. Invalid and stack-aliased guest pointers never enter native source
//! C. Final registers and original traces are not compared.

use crate::support::checked_c;
use crate::support::native;

use nirvana::ir::{AccessKind, Reg, RunStatus};
use nirvana::readable::{ReadableC, ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const SIZE: usize = 256;
const ADDRESSES: [u64; 8] = [
    0x1000, 0x1010, 0x10d0, 0x10e0, 0x10f0, 0x10f8, 0x10ff, 0xffff,
];
const VALUES: [u64; 6] = [0, 1, 2, 3, 1 << 63, u64::MAX];

fn memory(address: u64, value: u64) -> Vec<u8> {
    let mut result: Vec<_> = (0..SIZE)
        .map(|index| index.wrapping_mul(29).wrapping_add(7) as u8)
        .collect();
    if let Some(offset) = address.checked_sub(BASE)
        && offset <= (SIZE - 8) as u64
    {
        result[offset as usize..offset as usize + 8].copy_from_slice(&value.to_le_bytes());
    }
    result
}

fn registers(count: usize, address: u64) -> Vec<u64> {
    let mut result: Vec<_> = (0..count)
        .map(|index| (index as u64).wrapping_mul(0x9e37_79b9) ^ 0x8123_4567_dead_beef)
        .collect();
    result[x86::RDI] = address;
    result[x86::RSP] = BASE + SIZE as u64;
    result
}

fn harness(output: &ReadableC, count: usize) -> String {
    let mut arguments: Vec<_> = output
        .parameters
        .iter()
        .map(|reg| format!("registers[{}]", reg.0))
        .collect();
    arguments.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
    let arguments = arguments.join(", ");
    format!(
        r#"
#undef abort
#include <inttypes.h>
#include <stdio.h>
static jmp_buf jump;
static uint8_t memory[256];
static uint64_t result;
static unsigned fault;
_Noreturn void nirvana_test_abort(void) {{ longjmp(jump,1); }}
int main(void) {{
    uint64_t address,value;
    while(scanf("%" SCNu64 " %" SCNu64,&address,&value)==2) {{
        for(unsigned i=0;i<256;++i) memory[i]=(uint8_t)(i*29+7);
        if(address>=UINT64_C(4096) && address-UINT64_C(4096)<=UINT64_C(248)) {{
            for(unsigned i=0;i<8;++i) memory[address-UINT64_C(4096)+i]=(uint8_t)(value>>(i*8));
        }}
        uint64_t registers[{count}];
        for(unsigned i=0;i<{count};++i) registers[i]=(uint64_t)i*UINT64_C(0x9e3779b9)^UINT64_C(0x81234567deadbeef);
        registers[{rdi}]=address;
        registers[{rsp}]=UINT64_C(4352);
        (void)registers;
        result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        if(setjmp(jump)==0) result=nirvana_readable({arguments});
        else fault=1;
        uint64_t words[32]={{0}};
        for(unsigned i=0;i<256;++i) words[i/8]|=(uint64_t)memory[i]<<((i%8)*8);
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64, fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,fault?nirvana_test_width:UINT64_C(0),result);
        for(unsigned i=0;i<32;++i) printf(" %" PRIu64,words[i]);
        putchar('\n');
    }}
}}
"#,
        rdi = x86::RDI,
        rsp = x86::RSP,
    )
}

#[test]
fn actual_nested_o0_outer_for_headers_keep_full_memory_and_first_faults() {
    let scratch = native::Scratch::new();
    let mut rows = 0;
    for (fixture, expected_for, expected_while) in
        [("nested-loops", 2, 0), ("nested-multi-exit", 1, 1)]
    {
        let object = scratch.0.join(format!("{fixture}-original-O0.o"));
        native::object(
            &native::fixture_root().join(format!("cases/{fixture}.c")),
            &object,
            "-O0",
            "fixture",
        );
        let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
        let program = &lifted.program;
        let original = program.instructions().to_vec();
        let mut text = String::new();
        let mut expected = Vec::new();
        let mut returned = 0;
        let mut faulted = 0;
        for address in ADDRESSES {
            for value in VALUES {
                writeln!(text, "{address} {value}").unwrap();
                let report = program
                    .run_with_memory(
                        &registers(program.register_count(), address),
                        BASE,
                        &memory(address, value),
                        100_000,
                    )
                    .unwrap();
                let (fault, first_address, access, width, result) = match report.status {
                    RunStatus::Returned(result) => {
                        returned += 1;
                        (0, 0, 0, 0, result)
                    }
                    RunStatus::Fault(fault) => {
                        faulted += 1;
                        (
                            1,
                            fault.address,
                            if fault.access == AccessKind::Read {
                                1
                            } else {
                                2
                            },
                            fault.width.bytes() as u64,
                            0,
                        )
                    }
                    RunStatus::Suspended => panic!("{fixture} unexpectedly suspended"),
                };
                let mut row = vec![fault, first_address, access, width, result];
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
                );
                assert_eq!(row.len(), 37);
                expected.push(row);
            }
        }
        assert_eq!(expected.len(), 48);
        assert!(returned > 0 && faulted > 0);
        for recover_objects in [false, true] {
            let output = emit_readable_c_with_options(
                program,
                ReadableOptions {
                    stack_register: Some(Reg(x86::RSP)),
                    recover_objects,
                    coalesce_locals: true,
                    compact_memory: true,
                },
            )
            .unwrap();
            let body = output
                .code
                .split("uint64_t nirvana_readable(")
                .nth(1)
                .unwrap();
            assert_eq!(body.matches("for (").count(), expected_for, "{body}");
            assert_eq!(body.matches("while (").count(), expected_while, "{body}");
            assert!(output.fallback_reason.is_none());
            assert_eq!(program.instructions(), original);
            let source_text =
                checked_c::instrument(&output.code) + &harness(&output, program.register_count());
            for optimization in ["-O0", "-O2"] {
                let source = scratch
                    .0
                    .join(format!("{fixture}-{recover_objects}{optimization}.c"));
                std::fs::write(&source, &source_text).unwrap();
                let object = source.with_extension("o");
                let binary = source.with_extension("bin");
                native::object(&source, &object, optimization, "nirvana_readable");
                native::link(&[&object], &binary);
                let actual = native::run_fields(&binary, &text, 37);
                assert_eq!(actual.len(), expected.len());
                for (index, (actual, expected)) in actual.iter().zip(&expected).enumerate() {
                    assert_eq!(
                        actual,
                        expected,
                        "{fixture}, views={recover_objects}, generated {optimization}, address={:#x}, value={}",
                        ADDRESSES[index / VALUES.len()],
                        VALUES[index % VALUES.len()],
                    );
                }
                rows += expected.len();
            }
        }
        eprintln!("{fixture}: {returned} returned/{faulted} faulted inputs");
    }
    assert_eq!(rows, 384);
    eprintln!("nested for backend: {rows} full-memory native rows");
}
