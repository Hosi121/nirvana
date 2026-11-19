#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Limits, RejectImports, Status};
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

const WRAPPER: &str = r#"
#include "http_server.h"
#include <unistd.h>
size_t process_request(const char *input,size_t length,char *output,size_t capacity) {
    struct http_request request;
    struct http_response response;
    if(http_parse_request(input,length,&request)) http_dispatch(&request,&response);
    else http_error_response(400,&response);
    return http_render_response(&response,output,capacity);
}
int main(void) {
    char input[1024],output[2048];
    ssize_t length=read(0,input,sizeof(input));
    if(length<0) return 2;
    size_t count=process_request(input,(size_t)length,output,sizeof(output));
    return write(1,output,count)==(ssize_t)count?0:3;
}
"#;

fn run(binary: &Path, input: &[u8]) -> std::process::Output {
    let mut child = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}: {}",
        binary.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}
fn compile(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn real_http_parser_routes_indirect_handlers_and_response_match_native_and_c() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("process.c");
    std::fs::write(&source, WRAPPER).unwrap();
    let fixture = native::fixture_root().join("http-server");
    let cases: Vec<&[u8]> = vec![
        b"GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n",
        b"GET /metrics HTTP/1.1\r\n\r\n",
        b"GET /missing HTTP/1.0\r\n\r\n",
        b"POST /health HTTP/1.1\r\n\r\n",
        b"GET /health BAD/1.1\r\n\r\n",
        b"GET /health HTTP/1.1\r\nNo-Colon\r\n\r\n",
        b"GET /health HTTP/1.1\r\nX-Test: \x01\r\n\r\n",
        b"GET /health HTTP/1.1\r\nHost: localhost",
        b"",
    ];
    let mut compared = 0;
    for opt in ["-O0", "-O2"] {
        for pie in [false, true] {
            let id = format!("{opt}-{pie}");
            let original = scratch.0.join(format!("native{id}"));
            let mut cc = Command::new("cc");
            cc.args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fno-lto",
                "-fno-stack-protector",
                opt,
            ])
            .args(if pie {
                ["-fPIE", "-pie"]
            } else {
                ["-fno-pie", "-no-pie"]
            })
            .arg("-I")
            .arg(&fixture)
            .arg(&source);
            for name in ["parser.c", "response.c", "routes.c", "routes_table.c"] {
                cc.arg(fixture.join(name));
            }
            compile(cc.arg("-o").arg(&original));
            let bytes = std::fs::read(&original).unwrap();
            let module = module_ir::lift_elf(
                &bytes,
                "process_request",
                LinkedOptions {
                    load_bias: if pie { 0x200000 } else { 0 },
                    ..Default::default()
                },
            )
            .unwrap_or_else(|error| panic!("{id}: {error}"));
            assert!(
                module
                    .program
                    .functions()
                    .iter()
                    .any(|function| function.name == "http_health_handler")
            );
            let input = module.image.stack_pointer - 0x8000;
            let output = module.image.stack_pointer - 0x4000;
            let harness = format!(
                r#"
#define main nv_generated_entry
{}
#undef main
int main(void) {{
    struct nv_module *s=nv_create(); if(!s) return 1;
    ssize_t length=read(0,s->memory+UINT64_C({}),1024); if(length<0)return 2;
    s->r[7]=UINT64_C({input});s->r[6]=(uint64_t)length;
    s->r[2]=UINT64_C({output});s->r[1]=2048;
    if(nv_run(s)!=0)return 3;
    if(write(1,s->memory+UINT64_C({}),s->r[0])!=(ssize_t)s->r[0])return 4;
    if(write(2,s->r,sizeof(s->r))!=(ssize_t)sizeof(s->r))return 5;
    if(write(2,s->memory,s->size)!=(ssize_t)s->size)return 6;
    free(s->memory);free(s);return 0;
}}
"#,
                nirvana::module_emit::emit_c(&module).unwrap(),
                input - module.image.memory_base,
                output - module.image.memory_base
            );
            let generated_source = scratch.0.join(format!("generated{id}.c"));
            std::fs::write(&generated_source, harness).unwrap();
            let mut binaries = Vec::new();
            for copt in ["-O0", "-O2"] {
                let generated = scratch.0.join(format!("generated{id}{copt}"));
                compile(
                    Command::new("cc")
                        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", copt])
                        .arg(&generated_source)
                        .arg("-o")
                        .arg(&generated),
                );
                binaries.push(generated);
            }
            for case in &cases {
                let mut registers = module.initial_registers();
                registers[7] = input;
                registers[6] = case.len() as u64;
                registers[2] = output;
                registers[1] = 2048;
                let mut memory = module.image.memory.clone();
                let offset = (input - module.image.memory_base) as usize;
                memory[offset..offset + case.len()].copy_from_slice(case);
                let report = module
                    .program
                    .run(
                        &registers,
                        module.image.memory_base,
                        &memory,
                        Limits::default(),
                        &mut RejectImports,
                    )
                    .unwrap();
                let Status::Returned(count) = report.status else {
                    panic!("{id}: {:?}", report.status)
                };
                assert_eq!(report.imports, 0);
                let offset = (output - module.image.memory_base) as usize;
                let response = &report.state.memory[offset..offset + count as usize];
                let native = run(&original, case);
                assert_eq!(native.stdout, response, "{id}: native response");
                assert!(native.stderr.is_empty());
                let expected: Vec<_> = report
                    .state
                    .registers
                    .iter()
                    .flat_map(|r| r.to_le_bytes())
                    .chain(report.state.memory.iter().copied())
                    .collect();
                for binary in &binaries {
                    let generated = run(binary, case);
                    assert_eq!(generated.stdout, response, "{id}: C response");
                    assert_eq!(
                        generated.stderr, expected,
                        "{id}: full C register/RAM state"
                    );
                    compared += 1;
                }
            }
        }
    }
    assert_eq!(compared, 72);
}
