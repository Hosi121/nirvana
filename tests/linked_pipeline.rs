#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::effects::{CallTarget, Instruction, Limits, PutsOutcome, Status};
use nirvana::linked_elf::LinkedOptions;
use nirvana::{effects_emit, effects_readable, frontend, x86};
use std::process::Command;

fn checked(command: &mut Command) -> std::process::Output {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

const HARNESS: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
int main(int argc,char **argv) {
    if(argc!=3) return 2;
    uint64_t r[NIRVANA_EFFECT_REGISTERS];
    uint8_t memory[NIRVANA_EFFECT_MEMORY_SIZE],output[256]={0};
    nirvana_effect_init(r,memory);
    struct nirvana_puts_outcome tape[3]={0};
    for(unsigned i=0;i<3;++i) {tape[i].registers[0]=strtoull(argv[1],0,10);tape[i].all=1;}
    struct nirvana_effects e={0};e.outcomes=tape;e.outcome_count=3;
    e.output=output;e.output_capacity=sizeof(output);
    e.instructions_left=1000;e.external_reads_left=1024;e.calls_left=3;
    unsigned status=nirvana_effect_run(r,memory,NIRVANA_EFFECT_MEMORY_BASE,sizeof(memory),&e);
    fwrite(output,1,(size_t)e.output_size,stdout);
    fprintf(stderr,"%u %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",status,e.result,e.consumed,e.started);
    FILE *file=fopen(argv[2],"wb");if(!file)return 3;
    if(fwrite(r,1,sizeof(r),file)!=sizeof(r)||fwrite(memory,1,sizeof(memory),file)!=sizeof(memory))return 4;
    return fclose(file)!=0;
}
"#;

#[test]
fn linked_exec_pie_plt_and_got_reach_effect_ir_and_both_c_backends() {
    let scratch = native::Scratch::new();
    let main = scratch.0.join("main.c");
    std::fs::write(&main,"#include <unistd.h>\nint fixture(void); int main(void) {int result=fixture(); return write(2,&result,sizeof(result))==(ssize_t)sizeof(result)?0:1;}\n").unwrap();
    let mut compared = 0;
    for (name, expected_output) in [
        ("hello", b"Hello, world!\n".as_slice()),
        ("mutable-message", b"hello\n".as_slice()),
        ("two-calls", b"first\nsecond\n".as_slice()),
    ] {
        for opt in ["-O0", "-O2"] {
            for pie in [false, true] {
                for got in [false, true] {
                    let id = format!("{name}{opt}-{pie}-{got}");
                    let binary = scratch.0.join(&id);
                    let mut compiler = Command::new("cc");
                    compiler.args(["-std=c11", "-fno-lto", opt]);
                    compiler.args(if pie {
                        ["-fPIE", "-pie"]
                    } else {
                        ["-fno-pie", "-no-pie"]
                    });
                    if got {
                        compiler.arg("-fno-plt");
                    }
                    checked(
                        compiler
                            .arg(native::fixture_root().join(format!("references/{name}.c")))
                            .arg(&main)
                            .arg("-o")
                            .arg(&binary),
                    );
                    let native_output = Command::new(&binary).output().unwrap();
                    assert!(native_output.status.success());
                    assert_eq!(native_output.stdout, expected_output);
                    // puts' positive return magnitude is implementation-defined;
                    // the real observed final result is an explicit tape input.
                    let native_return =
                        i32::from_le_bytes(native_output.stderr.try_into().unwrap());
                    assert!(native_return >= 0);
                    let native_return = u64::from(native_return as u32);
                    let bytes = std::fs::read(&binary).unwrap();
                    for bias in if pie {
                        vec![0x10000, 0x200000]
                    } else {
                        vec![0]
                    } {
                        let function = frontend::lift_linked_elf_effects(
                            &bytes,
                            "fixture",
                            LinkedOptions {
                                load_bias: bias,
                                stack_size: 256,
                            },
                        )
                        .unwrap_or_else(|error| panic!("{id} bias{bias:#x}: {error}"));
                        assert!(function.program.instructions().iter().any(
                            |instruction| matches!(instruction, Instruction::Call(call) if
                                matches!(call.target, CallTarget::Plt(_) | CallTarget::Memory(_)))
                        ));
                        for result in [native_return, 0x1234_5678_0000_0007] {
                            let mut registers = vec![0; function.program.register_count()];
                            registers[x86::RSP] = function.image.stack_pointer;
                            let report = function
                                .program
                                .run(
                                    &registers,
                                    function.image.memory_base,
                                    &function.image.memory,
                                    &vec![PutsOutcome::success(result); 3],
                                    Limits {
                                        instructions: 1000,
                                        external_reads: 1024,
                                        output_bytes: 256,
                                        calls: 3,
                                    },
                                )
                                .unwrap();
                            assert!(
                                matches!(report.status, Status::Returned(_)),
                                "{id}: {:?}",
                                report.status
                            );
                            assert_eq!(report.output, expected_output);
                            let Status::Returned(value) = report.status else {
                                unreachable!()
                            };
                            if result == native_return {
                                assert_eq!(value as u32, native_return as u32);
                            }
                            let state: Vec<_> = report
                                .state
                                .registers
                                .iter()
                                .flat_map(|r| r.to_le_bytes())
                                .chain(report.state.memory.iter().copied())
                                .collect();
                            for (kind, code) in [
                                (
                                    "full",
                                    effects_emit::emit_image(&function.program, &function.image)
                                        .unwrap(),
                                ),
                                (
                                    "structured",
                                    effects_readable::emit_image(
                                        &function.program,
                                        &function.image,
                                    )
                                    .unwrap()
                                    .code,
                                ),
                            ] {
                                let source = scratch.0.join(format!("{id}-{bias}-{kind}.c"));
                                std::fs::write(&source, code + HARNESS).unwrap();
                                for copt in ["-O0", "-O2"] {
                                    let object = source.with_extension(format!("{copt}.o"));
                                    let generated = object.with_extension("bin");
                                    native::object(&source, &object, copt, "fixture");
                                    native::link(&[&object], &generated);
                                    let dump = scratch.0.join("state.bin");
                                    let actual = checked(
                                        Command::new(&generated).arg(result.to_string()).arg(&dump),
                                    );
                                    assert_eq!(actual.stdout, report.output, "{id} {kind} {copt}");
                                    assert_eq!(
                                        String::from_utf8(actual.stderr).unwrap(),
                                        format!(
                                            "0 {value} {} {}\n",
                                            report.consumed,
                                            report.state.trace.len()
                                        )
                                    );
                                    assert_eq!(
                                        std::fs::read(&dump).unwrap(),
                                        state,
                                        "{id} {kind} {copt} full state"
                                    );
                                    compared += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(compared, 288);
}

#[test]
fn linked_cli_runs_puts_and_pure_leaf_but_reports_internal_calls() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("mixed.c");
    std::fs::write(&source,"#include <stdio.h>\n__attribute__((noinline)) unsigned long leaf(unsigned long x){return (x*3+7)/10;}\n__attribute__((noinline)) int fixture(void){return puts(\"Hello, world!\");}\n__attribute__((noinline)) int wrapper(void){return fixture();}\nint main(void){return wrapper();}\n").unwrap();
    for pie in [false, true] {
        let binary = source.with_extension(if pie { "pie" } else { "exec" });
        checked(
            Command::new("cc")
                .args(["-O2", "-fno-lto", "-fno-optimize-sibling-calls"])
                .arg(if pie { "-pie" } else { "-no-pie" })
                .arg(&source)
                .arg("-o")
                .arg(&binary),
        );
        let cli = env!("CARGO_BIN_EXE_nirvana");
        let output = checked(Command::new(cli).arg(&binary).args(["--run-effects", "14"]));
        assert_eq!(output.stdout, b"Hello, world!\n");
        assert!(String::from_utf8_lossy(&output.stderr).contains("returned 14"));
        let code = checked(
            Command::new(cli)
                .arg(&binary)
                .args(["--emit", "effects-readable-c"]),
        );
        assert!(String::from_utf8_lossy(&code.stdout).contains("nirvana_call_puts"));
        let leaf = checked(Command::new(cli).arg(&binary).args([
            "--symbol",
            "leaf",
            "--emit",
            "readable-c",
        ]));
        assert!(String::from_utf8_lossy(&leaf.stdout).contains("nirvana_readable"));
        let rejected = Command::new(cli)
            .arg(&binary)
            .args(["--symbol", "wrapper", "--emit", "effects-ir"])
            .output()
            .unwrap();
        assert!(!rejected.status.success());
        assert!(String::from_utf8_lossy(&rejected.stderr).contains("internal-call"));
    }
}

#[test]
fn linked_calls_require_import_identity_and_recheck_the_runtime_slot() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("identity.c");
    std::fs::write(&source,"#include <stdio.h>\nchar *message=\"relocated pointer\"; int fixture(void){return puts(message);}\nint main(void){return fixture();}\n").unwrap();
    let binary = source.with_extension("pie");
    checked(
        Command::new("cc")
            .args(["-O0", "-fPIE", "-pie", "-fno-plt"])
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
    let bytes = std::fs::read(&binary).unwrap();
    let options = LinkedOptions {
        load_bias: 0x200000,
        stack_size: 256,
    };
    let function = frontend::lift_linked_elf_effects(&bytes, "fixture", options).unwrap();
    let slot = function
        .program
        .instructions()
        .iter()
        .find_map(|instruction| match instruction {
            Instruction::Call(call) => match call.target {
                CallTarget::Memory(slot) => Some(slot),
                _ => None,
            },
            _ => None,
        })
        .unwrap();
    let mut registers = vec![0; function.program.register_count()];
    registers[x86::RSP] = function.image.stack_pointer;
    let outcome = [PutsOutcome::success(18)];
    let report = function
        .program
        .run(
            &registers,
            function.image.memory_base,
            &function.image.memory,
            &outcome,
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.output, b"relocated pointer\n");
    assert_eq!(report.status, Status::Returned(18));
    let mut memory = function.image.memory.clone();
    let offset = (slot - function.image.memory_base) as usize;
    memory[offset..offset + 8].copy_from_slice(&77_u64.to_le_bytes());
    let report = function
        .program
        .run(
            &registers,
            function.image.memory_base,
            &memory,
            &outcome,
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::UnknownTarget(77));
    assert_eq!(report.consumed, 0);
    assert!(report.output.is_empty());

    let mut renamed = bytes.clone();
    let offsets: Vec<_> = renamed
        .windows(5)
        .enumerate()
        .filter_map(|(i, word)| (word == b"puts\0").then_some(i))
        .collect();
    assert!(!offsets.is_empty());
    for offset in offsets {
        renamed[offset + 1] = b'i';
    }
    let error = frontend::lift_linked_elf_effects(&renamed, "fixture", options)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("pits") && error.contains("external effect model"),
        "{error}"
    );
}
