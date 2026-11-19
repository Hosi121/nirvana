#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use nirvana::effects::{Limits, Output, PutsOutcome, Status};
use nirvana::{effects_emit, frontend, loader, x86};
use std::process::Command;

fn checked(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn tape(results: [i32; 2]) -> Vec<PutsOutcome> {
    results
        .into_iter()
        .map(|r| {
            let mut o = PutsOutcome::success(u64::from(r as u32));
            if r < 0 {
                o.output = Output::Prefix(2);
            }
            o
        })
        .collect()
}

fn original_harness(choice: bool) -> String {
    format!(
        r#"#include <stdio.h>
#include <stdlib.h>
#include <string.h>
{declaration}
static int values[2]; static unsigned consumed;
int puts(const char *s) {{
    if(consumed>=2) abort();
    int result=values[consumed++]; size_t length=strlen(s),written=result<0?2:length+1;
    if(written>length+1) abort();
    fwrite(s,1,written<length?written:length,stdout); if(written>length) putchar('\n');
    return result;
}}
int main(int argc,char **argv) {{
    if(argc!=4) return 2; values[0]=atoi(argv[1]); values[1]=atoi(argv[2]);
    int choice=atoi(argv[3]); (void)choice;
    int result={call}; fprintf(stderr,"%d %u\n",result,consumed);return 0;
}}
"#,
        declaration = if choice {
            "int fixture(int);"
        } else {
            "int fixture(void);"
        },
        call = if choice {
            "fixture(choice)"
        } else {
            "fixture()"
        }
    )
}
const GENERATED_HARNESS: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
int main(int argc,char **argv) {
    if(argc!=5) return 2;
    uint64_t r[NIRVANA_EFFECT_REGISTERS]; uint8_t memory[NIRVANA_EFFECT_MEMORY_SIZE],output[128]={0};
    nirvana_effect_init(r,memory); r[7]=(uint64_t)atoi(argv[3]);
    struct nirvana_puts_outcome tape[2]={0};
    for(unsigned i=0;i<2;++i){int result=atoi(argv[i+1]);tape[i].registers[0]=(uint32_t)result;tape[i].all=result>=0;tape[i].prefix=2;}
    struct nirvana_effects e={0};e.outcomes=tape;e.outcome_count=2;e.output=output;e.output_capacity=sizeof(output);
    e.instructions_left=10000;e.external_reads_left=1024;e.calls_left=2;
    unsigned status=nirvana_effect_run(r,memory,NIRVANA_EFFECT_MEMORY_BASE,sizeof(memory),&e);
    fwrite(output,1,(size_t)e.output_size,stdout);
    fprintf(stderr,"%u %" PRIu64 " %" PRIu64 "\n",status,e.result,e.consumed);
    FILE *file=fopen(argv[4],"wb");if(!file)return 3;
    if(fwrite(r,1,sizeof(r),file)!=sizeof(r)||fwrite(memory,1,sizeof(memory),file)!=sizeof(memory))return 4;
    return fclose(file)!=0;
}
"#;

#[test]
fn machine_objects_effect_ir_and_c_agree_with_an_independent_sysv_puts_oracle() {
    let scratch = native::Scratch::new();
    let mut source_oracles = 0;
    let mut generated_observations = 0;
    for name in [
        "hello",
        "two-calls",
        "choice",
        "mutable-message",
        "indirect-message",
        "puts-result",
    ] {
        for opt in ["-O0", "-O2"] {
            for got in [false, true] {
                let id = format!("{name}{opt}-{got}");
                let object = scratch.0.join(format!("{id}.o"));
                let mut command = Command::new("cc");
                command.args(["-std=c11", "-fno-lto", opt, "-c"]);
                if got {
                    command.arg("-fno-plt");
                }
                checked(
                    command
                        .arg(native::fixture_root().join(format!("references/{name}.c")))
                        .arg("-o")
                        .arg(&object),
                );
                let bytes = std::fs::read(&object).unwrap();
                let helper = scratch.0.join(format!("{id}-oracle.c"));
                std::fs::write(&helper, original_harness(name == "choice")).unwrap();
                let oracle = scratch.0.join(format!("{id}-oracle"));
                checked(
                    Command::new("cc")
                        .args(["-std=c11", "-fno-builtin", "-fno-lto", "-no-pie"])
                        .arg(&object)
                        .arg(&helper)
                        .arg("-o")
                        .arg(&oracle),
                );
                for base in [0x10000, 0x200000] {
                    let function = frontend::lift_elf_effects(
                        &bytes,
                        "fixture",
                        loader::LoadOptions {
                            base,
                            stack_size: 256,
                        },
                    )
                    .unwrap();
                    let source = scratch.0.join(format!("{id}-{base}.c"));
                    std::fs::write(
                        &source,
                        effects_emit::emit_image(&function.program, &function.image).unwrap()
                            + GENERATED_HARNESS,
                    )
                    .unwrap();
                    let mut generated = Vec::new();
                    for copt in ["-O0", "-O2"] {
                        let obj = scratch.0.join(format!("{id}-{base}{copt}.o"));
                        let binary = obj.with_extension("bin");
                        native::object(&source, &obj, copt, "fixture");
                        native::link(&[&obj], &binary);
                        generated.push(binary);
                    }
                    for results in [[0, 7], [3, -1], [-1, 7], [-1, -1]] {
                        for choice in [0, 1] {
                            let mut registers = vec![0; function.program.register_count()];
                            registers[x86::RSP] = function.image.stack_pointer;
                            registers[x86::RDI] = choice;
                            let report = function
                                .program
                                .run(
                                    &registers,
                                    function.image.memory_base,
                                    &function.image.memory,
                                    &tape(results),
                                    Limits {
                                        instructions: 10000,
                                        external_reads: 1024,
                                        output_bytes: 128,
                                        calls: 2,
                                    },
                                )
                                .unwrap();
                            let Status::Returned(value) = report.status else {
                                panic!("{id}: {:?}", report.status);
                            };
                            let mut state = Vec::new();
                            for r in &report.state.registers {
                                state.extend(r.to_le_bytes());
                            }
                            state.extend(&report.state.memory);
                            let args = [
                                results[0].to_string(),
                                results[1].to_string(),
                                choice.to_string(),
                            ];
                            let original = Command::new(&oracle).args(&args).output().unwrap();
                            assert!(original.status.success());
                            assert_eq!(
                                original.stdout, report.output,
                                "{id} original stdout {results:?}"
                            );
                            assert_eq!(
                                String::from_utf8(original.stderr).unwrap(),
                                format!("{} {}\n", value as u32 as i32, report.consumed),
                                "{id} original return/calls"
                            );
                            source_oracles += 1;
                            for binary in &generated {
                                let path = scratch.0.join("state.bin");
                                let observed = Command::new(binary)
                                    .args(&args)
                                    .arg(&path)
                                    .output()
                                    .unwrap();
                                assert!(observed.status.success());
                                assert_eq!(observed.stdout, report.output, "{id} generated stdout");
                                assert_eq!(
                                    String::from_utf8(observed.stderr).unwrap(),
                                    format!("0 {value} {}\n", report.consumed),
                                    "{id} generated return/calls"
                                );
                                assert_eq!(
                                    std::fs::read(path).unwrap(),
                                    state,
                                    "{id} full generated registers/RAM"
                                );
                                generated_observations += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(source_oracles, 384);
    assert_eq!(generated_observations, 768);
    println!(
        "{source_oracles} real SysV machine/oracle runs and {generated_observations} generated C full-register/RAM/output/return comparisons"
    );
}

#[test]
fn cli_runs_modeled_output_and_emits_a_complete_initialized_c_image() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("hello.o");
    native::object(
        &native::fixture_root().join("references/hello.c"),
        &object,
        "-O2",
        "fixture",
    );
    let binary = env!("CARGO_BIN_EXE_nirvana");
    let result = Command::new(binary)
        .arg(&object)
        .args(["--run-effects", "7"])
        .output()
        .unwrap();
    assert!(result.status.success());
    assert_eq!(result.stdout, b"Hello, world!\n");
    assert!(String::from_utf8_lossy(&result.stderr).contains("returned 7"));
    let result = Command::new(binary)
        .arg(&object)
        .args(["--emit", "effects-ir"])
        .output()
        .unwrap();
    assert!(result.status.success());
    assert!(String::from_utf8_lossy(&result.stdout).contains("Call("));
    let result = Command::new(binary)
        .arg(&object)
        .args(["--emit", "effects-c"])
        .output()
        .unwrap();
    assert!(result.status.success());
    let source = scratch.0.join("cli.c");
    std::fs::write(&source, result.stdout).unwrap();
    native::object(&source, &source.with_extension("o"), "-O2", "fixture");
    for flags in [
        vec!["--emit", "readable-c"],
        vec!["--emit", "effects-c", "--raw"],
        vec!["--run-effects", "7", "--run", "0,0,0,0"],
        vec!["--emit", "effects-ir", "--run-effects", "7"],
    ] {
        let result = Command::new(binary)
            .arg(&object)
            .args(flags)
            .output()
            .unwrap();
        assert!(!result.status.success());
    }
    // A scan limit or missing input never pretends that an external call completed.
    let result = Command::new(binary)
        .arg(&object)
        .args(["--run-effects", "7", "--steps", "0"])
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
}
