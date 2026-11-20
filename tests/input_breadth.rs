//! Ordinary C binaries, native/oracle results, and computed-target execution.
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use nirvana::ir::AccessKind;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Limits, Module, RejectImports, Status};
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

fn compile(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn inputs() -> Vec<[u64; 4]> {
    let mut result = Vec::new();
    for key in (0..15).chain([
        u64::MAX,
        u64::MAX - 1,
        u64::MAX - 2,
        u64::MAX - 3,
        u64::MAX - 4,
        u64::MAX - 5,
        0x7fff_ffff,
        0x8000_0000,
        1 << 32,
        0xffff_ffff_0000_0004,
    ]) {
        result.push([
            key,
            u64::MAX - 17,
            0x1234_5678_9abc_def0,
            0x1111_3333_5555_7777,
        ]);
    }
    for outer in 0..8 {
        for inner in 0..8 {
            result.push([outer, 17, 23, inner]);
        }
    }
    let mut seed = 0x128a_5376_9172_ef01u64;
    for _ in 0..32 {
        result.push(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }));
    }
    result
}
fn reference(name: &str, mut r: [u64; 4]) -> Vec<u64> {
    let (a, b, d) = (r[1], r[2], r[3]);
    r[1] = match name {
        "dense-switch" => match r[0] {
            0 => a.wrapping_add(b),
            1 => a.wrapping_mul(3),
            2 => a ^ d,
            3 => a.rotate_left(7),
            4 => a.wrapping_sub(b),
            5 => a.wrapping_add(d.wrapping_mul(5)),
            6 => a.wrapping_add(b ^ d),
            7 => (a >> 3) | (d << 61),
            8 => a ^ (b & d),
            9 => a.wrapping_add(b & 255),
            10 => b.wrapping_add(17),
            11 => (a ^ d).wrapping_mul(7),
            _ => a ^ r[0],
        },
        "biased-switch" => match r[0] as u32 as i32 {
            -4 => a.wrapping_add(b),
            -3 => a ^ d,
            -2 => a.rotate_left(9),
            -1 => a.wrapping_mul(7),
            0 => a.wrapping_sub(b),
            1 => a.wrapping_add(d.wrapping_mul(3)),
            2 => a ^ (b & d),
            3 => b.wrapping_add(11),
            4 => (a >> 5) | (d << 59),
            _ => a ^ r[0],
        },
        _ => match r[0] & 7 {
            0 => a.wrapping_add(b),
            1 => a ^ d,
            2 => a.wrapping_mul(5),
            3 => a.rotate_left(11),
            4 => match d & 7 {
                0 => a.wrapping_sub(b),
                1 => a.wrapping_add(b.wrapping_mul(9)),
                2 => a ^ (b << 3),
                3 => a.rotate_right(7),
                4 => a.wrapping_mul(b),
                5 => a | b,
                _ => a & b,
            },
            5 => a.wrapping_sub(d),
            _ => a.wrapping_add(d & 255),
        },
    };
    let value = match name {
        "dense-switch" => r[1] ^ r[0] ^ r[2],
        "biased-switch" => r[1].wrapping_add(r[2]),
        _ => r[1] ^ r[2],
    };
    let mut result = vec![value];
    result.extend(r);
    result
}

#[derive(Clone)]
struct Case {
    input: [u64; 4],
    pc: u64,
    budget: usize,
    patch: Option<(u64, u64, usize)>,
}
fn state_address(module: &Module) -> u64 {
    module.image.stack_pointer - 512
}
fn prepare(module: &Module, case: &Case) -> (Vec<u64>, Vec<u8>) {
    let mut registers = module.initial_registers();
    registers[7] = state_address(module);
    let mut memory = module.image.memory.clone();
    let offset = (state_address(module) - module.image.memory_base) as usize;
    for (i, word) in case.input.iter().enumerate() {
        memory[offset + i * 8..offset + i * 8 + 8].copy_from_slice(&word.to_le_bytes());
    }
    if let Some((address, value, width)) = case.patch {
        let offset = (address - module.image.memory_base) as usize;
        memory[offset..offset + width].copy_from_slice(&value.to_le_bytes()[..width]);
    }
    (registers, memory)
}
fn expected(module: &Module, case: &Case) -> (Vec<u64>, Status) {
    let (registers, memory) = prepare(module, case);
    let report = module
        .program
        .run_from(
            case.pc,
            &registers,
            module.image.memory_base,
            &memory,
            Limits {
                instructions: case.budget,
                imports: 0,
            },
            &mut RejectImports,
        )
        .unwrap();
    let memory = &report.state.memory;
    let offset = (state_address(module) - module.image.memory_base) as usize;
    let mut result = vec![report.state.registers[0]];
    for i in 0..4 {
        result.push(u64::from_le_bytes(
            memory[offset + i * 8..offset + i * 8 + 8]
                .try_into()
                .unwrap(),
        ));
    }
    let (status, fault) = match &report.status {
        Status::Returned(_) => (0, [0; 3]),
        Status::UnknownTarget(_) => (2, [0; 3]),
        Status::Fault(f) => (
            1,
            [
                f.address,
                f.width,
                if f.access == AccessKind::Read { 1 } else { 2 },
            ],
        ),
        Status::Suspended(module_ir::Limit::Instructions) => (4, [0; 3]),
        other => panic!("unexpected {other:?}"),
    };
    result.extend([
        status,
        report.pc,
        report.state.trace.len() as u64,
        (case.budget - report.state.trace.len()) as u64,
        0,
        fault[0],
        fault[1],
        fault[2],
    ]);
    result.extend_from_slice(&report.state.registers);
    result.push(memory.iter().fold(0xcbf29ce484222325u64, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    }));
    assert_eq!(result.len(), 94);
    (result, report.status)
}
fn harness(code: &str, module: &Module) -> String {
    format!(
        r#"
#define main nv_generated_entry
{code}
#undef main
#include <assert.h>
#include <inttypes.h>
int main(void) {{
    uint64_t in[4],budget,pc,patch,value,width;
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                &in[0],&in[1],&in[2],&in[3],&budget,&pc,&patch,&value,&width)==9) {{
        struct nv_module *s=nv_create();assert(s);
        s->r[7]=UINT64_C({state});s->pc=pc;s->instructions_left=budget;s->imports_left=0;
        uint64_t offset=UINT64_C({offset});
        for(unsigned i=0;i<4;++i)for(unsigned j=0;j<8;++j)s->memory[offset+i*8+j]=(uint8_t)(in[i]>>(j*8));
        if(width) {{assert(width<=8 && patch>=s->base && patch-s->base+width<=s->size);for(unsigned j=0;j<width;++j)s->memory[patch-s->base+j]=(uint8_t)(value>>(j*8));}}
        unsigned status=nv_run(s);
        uint64_t hash=UINT64_C(14695981039346656037);
        for(uint64_t i=0;i<s->size;++i)hash=(hash^s->memory[i])*UINT64_C(1099511628211);
        printf("%" PRIu64,s->r[0]);
        for(unsigned i=0;i<4;++i) {{uint64_t word=0;for(unsigned j=0;j<8;++j)word|=(uint64_t)s->memory[offset+i*8+j]<<(j*8);printf(" %" PRIu64,word);}}
        uint64_t fields[8]={{status,s->pc,s->started,s->instructions_left,s->imports_left,s->fault_address,s->fault_width,s->fault_access}};
        for(unsigned i=0;i<8;++i)printf(" %" PRIu64,fields[i]);
        for(unsigned i=0;i<80;++i)printf(" %" PRIu64,s->r[i]);
        printf(" %" PRIu64 "\n",hash);free(s->memory);free(s);
    }}
    return 0;
}}
"#,
        state = state_address(module),
        offset = state_address(module) - module.image.memory_base
    )
}

fn build(source: &Path, output: &Path, opt: &str, pie: bool) {
    compile(
        Command::new("cc")
            .args([
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
            .arg(source)
            .arg(native::fixture_root().join("harness.c"))
            .arg("-o")
            .arg(output),
    );
}

#[test]
fn ordinary_switch_binaries_match_native_oracles_and_three_module_backends() {
    let scratch = native::Scratch::new();
    let inputs = inputs();
    let native_text: String = inputs
        .iter()
        .map(|r| format!("{} {} {} {}\n", r[0], r[1], r[2], r[3]))
        .collect();
    let mut generated_cases = 0;
    let mut native_cases = 0;
    let mut mutation_cases = 0;
    for name in ["dense-switch", "biased-switch", "nested-switch"] {
        let oracle: Vec<_> = inputs.iter().map(|r| reference(name, *r)).collect();
        for opt in ["-O0", "-O2"] {
            for pie in [false, true] {
                let directory = scratch.0.join(format!("{name}{opt}-{pie}"));
                std::fs::create_dir(&directory).unwrap();
                let original = directory.join("original");
                build(
                    &native::fixture_root().join(format!("input-breadth/{name}.c")),
                    &original,
                    opt,
                    pie,
                );
                let actual = native::run(&original, &native_text);
                assert_eq!(actual, oracle, "{name} {opt} PIE={pie}: native oracle");
                native_cases += inputs.len();
                let bytes = std::fs::read(&original).unwrap();
                let module = module_ir::lift_elf(
                    &bytes,
                    "fixture",
                    LinkedOptions {
                        load_bias: if pie { 0x20000 } else { 0 },
                        stack_size: 4096,
                    },
                )
                .unwrap();
                assert_eq!(
                    module.jump_tables.len(),
                    if name == "nested-switch" { 2 } else { 1 },
                    "{name} {opt} PIE={pie}: {:?}",
                    module.jump_table_diagnostics
                );
                assert!(module.jump_table_diagnostics.is_empty());
                for table in &module.jump_tables {
                    for target in table.targets() {
                        assert!(
                            module
                                .program
                                .instructions()
                                .iter()
                                .any(|i| i.address() == target)
                        );
                    }
                }
                let cli = Command::new(env!("CARGO_BIN_EXE_nirvana"))
                    .arg(&original)
                    .args(["--symbol", "fixture", "--emit", "module-jumps"])
                    .output()
                    .unwrap();
                assert!(cli.status.success());
                let json = String::from_utf8(cli.stdout).unwrap();
                assert!(json.contains("\"complete\":false"));
                assert!(json.contains("\"unknown_target\":true"));
                let mut cases: Vec<_> = inputs
                    .iter()
                    .map(|input| Case {
                        input: *input,
                        pc: module.program.entry(),
                        budget: 10_000,
                        patch: None,
                    })
                    .collect();
                let mut expected_rows = Vec::new();
                for (case, oracle) in cases.iter().zip(&oracle) {
                    let (row, status) = expected(&module, case);
                    assert!(
                        matches!(status, Status::Returned(_)),
                        "{name} {opt} PIE={pie}: {status:?}"
                    );
                    assert_eq!(&row[..5], oracle);
                    expected_rows.push(row);
                }
                for budget in [0, 1, 2, 4, 8, 16, 32, 64] {
                    cases.push(Case {
                        input: [4, 17, 23, 3],
                        pc: module.program.entry(),
                        budget,
                        patch: None,
                    });
                }
                // Every table entry is also tested as a resumption PC. The caller
                // state deliberately has no inherited frame or temporary values.
                for table in &module.jump_tables {
                    for target in table.targets() {
                        cases.push(Case {
                            input: [0, 17, 23, 3],
                            pc: target,
                            budget: 4,
                            patch: None,
                        });
                    }
                }
                if name == "dense-switch" {
                    let table = &module.jump_tables[0];
                    let address = table.entries[0].address;
                    let width = table.width.bytes();
                    let target = table.entries[1].target;
                    let value = target.wrapping_sub(table.bias);
                    let patched = Case {
                        input: [0, 17, 23, 3],
                        pc: module.program.entry(),
                        budget: 1000,
                        patch: Some((address, value, width)),
                    };
                    let (row, status) = expected(&module, &patched);
                    assert!(matches!(status, Status::Returned(_)));
                    assert_eq!(
                        row[2], 51,
                        "a rewritten entry must execute case1 using the actual guest table"
                    );
                    cases.push(patched);
                    mutation_cases += 1;
                    let target = state_address(&module);
                    let value = target.wrapping_sub(table.bias);
                    let unknown = Case {
                        input: [0, 17, 23, 3],
                        pc: module.program.entry(),
                        budget: 1000,
                        patch: Some((address, value, width)),
                    };
                    assert!(
                        matches!(expected(&module,&unknown).1,Status::UnknownTarget(pc) if pc==target)
                    );
                    cases.push(unknown);
                    mutation_cases += 1;
                }
                for case in &cases[inputs.len()..] {
                    expected_rows.push(expected(&module, case).0);
                }
                let mut text = String::new();
                for case in &cases {
                    let (address, value, width) = case.patch.unwrap_or((0, 0, 0));
                    writeln!(
                        text,
                        "{} {} {} {} {} {} {} {} {}",
                        case.input[0],
                        case.input[1],
                        case.input[2],
                        case.input[3],
                        case.budget,
                        case.pc,
                        address,
                        value,
                        width
                    )
                    .unwrap();
                }
                let modes = [
                    ("core", nirvana::module_emit::emit_c(&module).unwrap()),
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
                ];
                for (mode, code) in modes {
                    let source = directory.join(format!("{mode}.c"));
                    std::fs::write(&source, harness(&code, &module)).unwrap();
                    for generated_opt in ["-O0", "-O2"] {
                        let binary = directory.join(format!("{mode}{generated_opt}"));
                        compile(
                            Command::new("cc")
                                .args([
                                    "-std=c11",
                                    "-Wall",
                                    "-Wextra",
                                    "-Werror",
                                    "-pedantic",
                                    generated_opt,
                                ])
                                .arg(&source)
                                .arg("-o")
                                .arg(&binary),
                        );
                        assert_eq!(
                            native::run_fields(&binary, &text, 94),
                            expected_rows,
                            "{name} {opt} PIE={pie} {mode} {generated_opt}: all registers,PC,budgets,fault,RAM digest"
                        );
                        generated_cases += cases.len();
                    }
                }
                println!(
                    "{name} {opt} PIE={pie}: {} native/oracle/module inputs; {} boundary/resume/mutation inputs; three generated backends passed",
                    inputs.len(),
                    cases.len() - inputs.len()
                );
            }
        }
    }
    println!(
        "input breadth: 12 binary profiles, {native_cases} native/oracle/module cases, {generated_cases} generated full-state cases, {mutation_cases} table mutations"
    );
}
