//! Shared fault interception for small checked-memory C backend cohorts.
//!
//! Input rows are an address and four words. `initialized_words` and the
//! memory size match the caller's IR setup. Output contains the first fault's
//! address, kind and width, return, and the guest bytes as complete u64 words.

use nirvana::readable::ReadableC;
use nirvana::x86;

/// Instrument checks, including a store's destination check before its RHS.
pub fn instrument(code: &str) -> String {
    let check = "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {";
    assert_eq!(code.matches(check).count(), 1);
    let code = code.replace(
        check,
        "static inline uint64_t nirvana_test_offset(struct nirvana_memory *m, uint64_t address, uint64_t width, unsigned access) { nirvana_test_address=address; nirvana_test_access=access; nirvana_test_width=width;",
    );
    let end = "    return address - m->base;\n}";
    assert_eq!(code.matches(end).count(), 1);
    // Direct offset calls are the renderer's pre-RHS store checks. They and
    // the final store check are writes; load checks use the read wrapper.
    let code = code.replace(end, &(end.to_owned() + r#"
static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {
    return nirvana_test_offset(m, address, width, 2);
}
static inline uint64_t nirvana_test_read_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {
    return nirvana_test_offset(m, address, width, 1);
}"#));
    let load = "uint64_t offset = nirvana_offset(m, address, width), value = 0;";
    assert_eq!(code.matches(load).count(), 1);
    let code = code.replace(
        load,
        "uint64_t offset = nirvana_test_read_offset(m, address, width), value = 0;",
    );
    let prefix = "#include <stdint.h>\n#include <setjmp.h>\nstatic uint64_t nirvana_test_address, nirvana_test_width;\nstatic unsigned nirvana_test_access;\n_Noreturn void nirvana_test_abort(void);\n#define abort nirvana_test_abort\n";
    prefix.to_owned() + &code
}

pub fn source(output: &ReadableC, register_count: usize, initialized_words: usize) -> String {
    source_with_size(output, register_count, initialized_words, 64)
}

pub fn source_with_size(
    output: &ReadableC,
    register_count: usize,
    initialized_words: usize,
    memory_size: usize,
) -> String {
    source_with_stack(
        output,
        register_count,
        initialized_words,
        memory_size,
        4096 + memory_size as u64,
    )
}

pub fn source_with_stack(
    output: &ReadableC,
    register_count: usize,
    initialized_words: usize,
    memory_size: usize,
    stack: u64,
) -> String {
    assert!((1..=4).contains(&initialized_words));
    assert!((8..=65_536).contains(&memory_size) && memory_size & 7 == 0);
    let last_word = memory_size - 8;
    let words = memory_size / 8;
    assert!((4096..=4096 + memory_size as u64).contains(&stack));
    let code = instrument(&output.code);
    let mut arguments: Vec<_> = output
        .parameters
        .iter()
        .map(|reg| format!("registers[{}]", reg.0))
        .collect();
    arguments.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
    let arguments = arguments.join(", ");
    let harness = format!(
        r#"
#undef abort
#include <inttypes.h>
#include <stdio.h>
static jmp_buf jump;
static uint8_t memory[{memory_size}];
static uint64_t result;
static unsigned fault;
_Noreturn void nirvana_test_abort(void) {{ longjmp(jump,1); }}
int main(void) {{
    uint64_t address, input[4];
    while (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                 &address, &input[0], &input[1], &input[2], &input[3])==5) {{
        for(unsigned i=0;i<{memory_size};++i) memory[i]=(uint8_t)(i*29+7);
        for(unsigned word=0;word<{initialized_words};++word) {{
            if(address<=UINT64_MAX-word*UINT64_C(8)) {{
                uint64_t location=address+word*UINT64_C(8);
                if(location>=UINT64_C(4096) && location-UINT64_C(4096)<=UINT64_C({last_word})) {{
                    for(unsigned i=0;i<8;++i)
                        memory[location-UINT64_C(4096)+i]=(uint8_t)(input[word]>>(i*8));
                }}
            }}
        }}
        uint64_t registers[{register_count}]={{0}};
        registers[{rdi}]=address;
        registers[{rsp}]=UINT64_C({stack});
        (void)registers;
        result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        if(setjmp(jump)==0) result=nirvana_readable({arguments});
        else fault=1;
        uint64_t words[{words}]={{0}};
        for(unsigned i=0;i<{memory_size};++i) words[i/8]|=(uint64_t)memory[i]<<((i%8)*8);
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64,
               fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,
               fault?nirvana_test_width:UINT64_C(0),result);
        for(unsigned i=0;i<{words};++i) printf(" %" PRIu64,words[i]);
        putchar('\n');
    }}
}}
"#,
        rdi = x86::RDI,
        rsp = x86::RSP,
    );
    code + &harness
}
