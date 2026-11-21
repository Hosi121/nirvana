//! Native stdio is the oracle; the ABI harness supplies guest varargs directly.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::{linked_elf::LinkedOptions, module_ir};
use std::time::Duration;

use native::{compile_c as compile, run_output};

const TIMEOUT: Duration = Duration::from_secs(5);

#[test]
fn mixed_integer_widths_stack_varargs_and_failed_scans_match_native() {
    let scratch = native::Scratch::new();
    for pie in [false, true] {
        for original_opt in ["-O0", "-O2"] {
            let directory = scratch.0.join(format!("{pie}-{original_opt}"));
            std::fs::create_dir(&directory).unwrap();
            let original = directory.join("original");
            compile(
                &native::fixture_root().join("formatted-io.c"),
                &original,
                &[
                    original_opt,
                    "-fno-builtin",
                    if pie { "-pie" } else { "-no-pie" },
                    if pie { "-fPIE" } else { "-fno-pie" },
                ],
            );
            let module = module_ir::lift_elf(
                &std::fs::read(&original).unwrap(),
                "main",
                LinkedOptions {
                    load_bias: if pie { 0x10000 } else { 0 },
                    ..LinkedOptions::default()
                },
            )
            .unwrap();
            let inputs = [
                "-2147483648 4294967295 ffffffffffffffff -9223372036854775808 -128 65535\n",
                "2147483647 0 0 9223372036854775807 127 0\n",
                "1 2 ff -4 -5 6\n",
                "\n",
                "bad\n",
                "12 34\n",
                "12 bad\n",
                "12 34 56 78 -9 bad\n",
            ];
            let expected: Vec<_> = inputs
                .iter()
                .map(|input| run_output(&original, Some(input), TIMEOUT))
                .collect();
            for (name, code) in [
                ("flat", nirvana::module_emit::emit_c(&module).unwrap()),
                (
                    "readable",
                    nirvana::module_readable::emit_c(&module).unwrap().code,
                ),
                (
                    "locals",
                    nirvana::module_readable::emit_c_with_locals(&module)
                        .unwrap()
                        .code,
                ),
            ] {
                let source = directory.join(format!("{name}.c"));
                std::fs::write(&source, code).unwrap();
                for optimization in ["-O0", "-O2"] {
                    let binary = directory.join(format!("{name}-{optimization}"));
                    compile(
                        &source,
                        &binary,
                        &[
                            optimization,
                            "-fsanitize=undefined",
                            "-fno-sanitize-recover=all",
                        ],
                    );
                    for (input, expected) in inputs.iter().zip(&expected) {
                        let actual = run_output(&binary, Some(input), TIMEOUT);
                        assert_eq!(
                            (actual.status.code(), &actual.stdout, &actual.stderr),
                            (expected.status.code(), &expected.stdout, &expected.stderr),
                            "{pie} {original_opt} {name} {optimization} {input:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn checked_formatted_abi_handles_bounds_partial_input_and_rejections() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("abi.c");
    std::fs::write(
        &source,
        [
            "#define _POSIX_C_SOURCE 200809L\n",
            include_str!("../src/module_emit/runtime.h"),
            PRELUDE,
            include_str!("../src/module_emit/formatted.h"),
            include_str!("../src/module_emit/posix.h"),
            HARNESS,
        ]
        .concat(),
    )
    .unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(opt);
        compile(
            &source,
            &binary,
            &[opt, "-fsanitize=undefined", "-fno-sanitize-recover=all"],
        );
        let output = run_output(&binary, Some(""), TIMEOUT);
        assert!(
            output.status.success(),
            "{opt}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stdout.is_empty());
    }
}

const PRELUDE: &str = r#"
#include <assert.h>
static FILE *input_stream, *output_stream;
#define NV_GUEST_STDIN(s) ((void)(s), input_stream)
#define NV_GUEST_STDOUT(s) ((void)(s), output_stream)
"#;

const HARNESS: &str = r#"
static struct nv_module state;
static uint8_t memory[8192];
#define BASE UINT64_C(0x100000)
#define FMT (BASE+64)
#define DEST (BASE+512)
static void reset(const char *format) {
    memset(&state, 0, sizeof(state)); memset(memory, 0xa5, sizeof(memory));
    state.base=BASE; state.size=sizeof(memory); state.memory=memory;
    state.errno_address=BASE; state.r[4]=BASE+7000;
    memcpy(memory+64, format, strlen(format)+1);
    nv_write(&state, BASE, 4, 0);
}
static void argument(unsigned i, uint64_t value) {
    static const unsigned gp[]={7,6,2,1,8,9};
    if(i<6) state.r[gp[i]]=value;
    else nv_write(&state,state.r[4]+8*(i-5),8,value);
}
static void input(const char *text) {
    if(input_stream) fclose(input_stream);
    input_stream=tmpfile(); assert(input_stream);
    assert(fwrite(text,1,strlen(text),input_stream)==strlen(text)); rewind(input_stream);
}
static unsigned call(const char *name) {
    if(setjmp(state.jump)) return 0;
    return nv_posix_call(&state,name);
}
int main(void) {
    char expected[256]; int n;
    output_stream=tmpfile(); assert(output_stream);
    reset("%hhd %hd %d %ld %lld %u %o %x %X");
    argument(0,DEST); argument(1,FMT);
    for(unsigned i=2;i<11;++i) argument(i,UINT64_MAX);
    assert(call("sprintf"));
    n=snprintf(expected,sizeof(expected),"%hhd %hd %d %ld %lld %u %o %x %X",-1,-1,-1,-1L,-1LL,UINT_MAX,UINT_MAX,UINT_MAX,UINT_MAX);
    assert(state.r[0]==(unsigned)n && !strcmp((char*)memory+512,expected));
    reset("%*.*s:%c"); memcpy(memory+1024,"abcde",6);
    argument(0,DEST); argument(1,5); argument(2,FMT);
    argument(3,-7); argument(4,3); argument(5,BASE+1024); argument(6,'!');
    assert(call("snprintf")); assert(state.r[0]==9);
    assert(!memcmp(memory+512,"abc \0",5)); assert(memory[517]==0xa5);
    reset("%s"); argument(0,0); argument(1,0); argument(2,FMT);
    memcpy(memory+1024,"hello",6); argument(3,BASE+1024);
    assert(call("snprintf") && state.r[0]==5);
    reset("%.3s"); memcpy(memory+sizeof(memory)-3,"xyz",3);
    argument(0,DEST);argument(1,FMT);argument(2,BASE+sizeof(memory)-3);
    assert(call("sprintf") && !strcmp((char*)memory+512,"xyz"));
    reset("%.0s"); argument(0,DEST);argument(1,FMT);argument(2,UINT64_MAX);
    assert(call("sprintf") && memory[512]==0);
    reset("%s"); memset(memory+sizeof(memory)-3,'x',3);
    argument(0,FMT);argument(1,BASE+sizeof(memory)-3);
    assert(!call("printf") && state.status==1 && ftell(output_stream)==0);
    reset("abc");argument(0,BASE+sizeof(memory)-2);argument(1,FMT);
    assert(!call("sprintf") && state.status==1);
    assert(memory[sizeof(memory)-1]==0xa5);
    reset("%d");argument(0,FMT);argument(1,BASE+sizeof(memory)-3);input("19x");
    assert(!call("scanf") && state.status==1 && ftell(input_stream)==0);
    reset("%d,%i %hx %hhu %ld %lld"); argument(0,FMT);
    for(unsigned i=1;i<=6;++i) argument(i,DEST+16*i);
    input("-7,012 ff 255 -99 -9223372036854775808!");
    assert(call("__isoc99_scanf") && state.r[0]==6);
    assert(nv_read(&state,DEST+16,4)==UINT32_MAX-6);
    assert(nv_read(&state,DEST+32,4)==10 && nv_read(&state,DEST+48,2)==255);
    assert(nv_read(&state,DEST+64,1)==255 && nv_read(&state,DEST+80,8)==(uint64_t)-99);
    assert(nv_read(&state,DEST+96,8)==UINT64_C(0x8000000000000000));
    assert(fgetc(input_stream)=='!');
    reset("%d %d");argument(0,FMT);argument(1,DEST);argument(2,DEST+4);input("12 bad");
    assert(call("scanf") && state.r[0]==1 && nv_read(&state,DEST,4)==12);
    assert(nv_read(&state,DEST+4,4)==UINT32_C(0xa5a5a5a5) && fgetc(input_stream)=='b');
    reset("%d");argument(0,FMT);argument(1,DEST);input("");
    assert(call("scanf") && state.r[0]==UINT32_MAX && nv_read(&state,DEST,4)==UINT32_C(0xa5a5a5a5));
    const char *bad[]={"prefix%n","%f","%2$d","%ls","%9999999999999999999d","%"};
    for(unsigned i=0;i<sizeof(bad)/sizeof(*bad);++i) {
        reset(bad[i]);argument(0,FMT);argument(1,DEST);
        assert(!call("printf") && state.status==3 && ftell(output_stream)==0);
    }
    reset("%d %n");argument(0,FMT);argument(1,DEST);argument(2,DEST+4);input("123");
    assert(!call("scanf") && state.status==3 && ftell(input_stream)==0);
    reset("%d %d");argument(0,FMT);argument(1,DEST);argument(2,BASE+sizeof(memory));input("12 34");
    assert(!call("scanf") && state.status==1 && nv_read(&state,DEST,4)==12);
    assert(fgetc(input_stream)=='3'); /* Format whitespace was already consumed. */
    reset("%lu %d %d %d %d %d");argument(0,FMT);argument(1,state.r[4]+8);
    for(unsigned i=2;i<=6;++i) argument(i,DEST+16*i);
    snprintf(expected,sizeof(expected),"%lu 2 3 4 5 73",(unsigned long)(DEST+1600));input(expected);
    assert(call("scanf") && state.r[0]==6 && nv_read(&state,DEST+1600,4)==73);
    assert(nv_read(&state,DEST+96,4)==UINT32_C(0xa5a5a5a5));
    reset("%x %x %x");argument(0,DEST);argument(1,2);argument(2,32);argument(3,FMT);
    argument(4,0xaa);argument(5,0xbb);argument(6,0xcc);
    assert(call("__sprintf_chk") && !strcmp((char*)memory+512,"aa bb cc"));
    reset("abcdef");argument(0,DEST);argument(1,3);argument(2,2);argument(3,3);argument(4,FMT);
    assert(call("__snprintf_chk") && state.r[0]==6 && !memcmp(memory+512,"ab\0",3));
    reset("abcdef");argument(0,DEST);argument(1,2);argument(2,3);argument(3,FMT);
    assert(!call("__sprintf_chk") && state.status==3 && memory[512]==0xa5);
    reset("abcdef");argument(0,DEST);argument(1,4);argument(2,2);argument(3,3);argument(4,FMT);
    assert(!call("__snprintf_chk") && state.status==3 && memory[512]==0xa5);
    reset("%d");argument(0,FMT);argument(1,DEST);input("42");
    FILE *saved=input_stream;input_stream=NULL;
    assert(!call("scanf") && state.status==3 && ftell(saved)==0);input_stream=saved;
    reset("%d");argument(0,FMT);state.r[4]=UINT64_MAX-3;
    if(setjmp(state.jump)==0) { (void)nv_format_argument(&state,6); assert(0); }
    assert(state.status==1 && state.fault_access==1);
    fclose(input_stream); fclose(output_stream); return 0;
}
"#;
