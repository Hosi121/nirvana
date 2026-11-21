use crate::support::native;
use nirvana::{frontend, readable, x86};
use std::fmt::Write as _;

fn cases() -> Vec<(String, i64)> {
    [3, 5, 7, 10, 11, 13, 15, 17, 19, 31]
        .into_iter()
        .flat_map(|d| {
            [false, true].map(move |negative| {
                let name = if d == 15 && !negative {
                    "fixture".to_owned()
                } else {
                    format!("div_{}{d}", if negative { "n" } else { "p" })
                };
                (name, if negative { -d } else { d })
            })
        })
        .collect()
}
fn inputs(bits: u32) -> Vec<[u64; 4]> {
    let mut values = vec![
        0,
        1,
        2,
        3,
        9,
        10,
        11,
        14,
        15,
        16,
        30,
        31,
        32,
        1 << 31,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX,
    ];
    let mut seed = 0x8123_4567_89ab_cdefu64;
    for _ in 0..64 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    if bits == 32 {
        for d in [3u64, 5, 7, 10, 11, 13, 15, 17, 19, 31] {
            for q in [1, 2, 3, 0x7fff_ffff / d] {
                let n = q * d;
                for x in [n - 1, n, n + 1] {
                    values.extend([x, x.wrapping_neg()]);
                }
            }
        }
    }
    values
        .into_iter()
        .map(|v| {
            [
                v,
                0xaaaa_aaaa_aaaa_aaaa,
                0x5555_5555_5555_5555,
                0x1234_5678_9abc_def0,
            ]
        })
        .collect()
}
fn driver(names: &[String]) -> String {
    let mut s = String::from("\n#include <inttypes.h>\n#include <stdio.h>\n#include <stdint.h>\n");
    for name in names {
        writeln!(s, "uint64_t {name}(uint64_t state[4]);").unwrap();
    }
    writeln!(
        s,
        "static uint64_t (*const probes[])(uint64_t*)={{{}}};",
        names.join(",")
    )
    .unwrap();
    s.push_str(r#"
int main(void) {
    uint64_t input[4];
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,&input[0],&input[1],&input[2],&input[3])==4) {
        for(unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);++i) {
            uint64_t state[4]={input[0],input[1],input[2],input[3]};
            uint64_t result=probes[i](state);
            printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",result,state[0],state[1],state[2],state[3]);
        }
    }
    return 0;
}
"#);
    s
}

#[test]
fn gcc_signed_reciprocals_match_native_ir_and_sanitized_generated_c() {
    for bits in [32, 64] {
        check_width(bits);
    }
}
fn check_width(bits: u32) {
    let scratch = native::Scratch::new();
    let cases = cases();
    let inputs = inputs(bits);
    let mut text = String::new();
    let mut expected = Vec::new();
    for input in &inputs {
        writeln!(text, "{} {} {} {}", input[0], input[1], input[2], input[3]).unwrap();
        for (_, d) in &cases {
            let x = if bits == 32 {
                input[0] as i32 as i64
            } else {
                input[0] as i64
            };
            let mask = if bits == 32 {
                u32::MAX as u64
            } else {
                u64::MAX
            };
            let q = (x / d) as u64 & mask;
            let r = (x % d) as u64 & mask;
            expected.push(vec![q ^ (r << 8), input[0], q, r, input[3]]);
        }
    }
    let native_source = scratch.0.join("driver.c");
    std::fs::write(
        &native_source,
        driver(
            &cases
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>(),
        ),
    )
    .unwrap();
    let harness = scratch.0.join("driver.o");
    native::object(&native_source, &harness, "-O2", "fixture");
    let fixture = native::fixture_root().join(if bits == 32 {
        "recovery/word-signed-memory.c"
    } else {
        "recovery/signed-reciprocal.c"
    });
    let mut programs = Vec::new();
    for opt in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("fixture{opt}.o"));
        native::object(&fixture, &object, opt, "fixture");
        let executable = scratch.0.join(format!("native{opt}"));
        native::link(&[&object, &harness], &executable);
        assert_eq!(native::run(&executable, &text), expected);
        let bytes = std::fs::read(&object).unwrap();
        for (index, (name, _)) in cases.iter().enumerate() {
            let lifted = frontend::lift_elf(&bytes, name).unwrap();
            for (input, row) in inputs
                .iter()
                .zip(expected.iter().skip(index).step_by(cases.len()))
            {
                let mut regs = vec![0; lifted.program.register_count()];
                regs[x86::RDI] = 4112;
                regs[x86::RSP] = 4352;
                let mut memory = vec![0x91; 256];
                for (i, value) in input.iter().enumerate() {
                    memory[16 + i * 8..24 + i * 8].copy_from_slice(&value.to_le_bytes());
                }
                let run = lifted
                    .program
                    .execute_with_memory(&regs, 4096, &memory, 10000)
                    .unwrap();
                let mut actual = vec![run.value];
                actual.extend(
                    run.memory[16..48]
                        .chunks_exact(8)
                        .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
                );
                assert_eq!(&actual, row, "{name}/{opt}/{input:?}");
            }
            if opt == "-O2" {
                programs.push(lifted.program);
            }
        }
    }
    let mut generated = String::from("#include <stdint.h>\n#include <string.h>\n");
    let mut names = Vec::new();
    for (index, program) in programs.iter().enumerate() {
        let output = readable::emit_readable_c(program).unwrap();
        let evidence = output
            .semantic_evidence
            .expect("materialized reciprocal values");
        assert!(evidence.inputs > 0 && evidence.divisions > 0 && evidence.remainders > 0);
        let body = output
            .code
            .split("uint64_t nirvana_readable(")
            .nth(1)
            .unwrap();
        assert!(
            body.contains(if bits == 32 {
                "nirvana_sdiv_word("
            } else {
                "nirvana_sdiv64("
            }) && body.contains(if bits == 32 {
                "nirvana_srem_word("
            } else {
                "nirvana_srem64("
            }),
            "{}: {}",
            cases[index].0,
            output.code
        );
        generated.push_str(&output.code.replace("nirvana_", &format!("nv_case{index}_")));
        let name = format!("probe_{index}");
        names.push(name.clone());
        let mut args: Vec<_> = output
            .parameters
            .iter()
            .map(|r| format!("r[{}]", r.0))
            .collect();
        args.extend([
            "memory".to_owned(),
            "UINT64_C(4096)".to_owned(),
            "sizeof(memory)".to_owned(),
        ]);
        writeln!(generated,"\nuint64_t {name}(uint64_t state[4]) {{ uint8_t memory[256];memset(memory,0x91,sizeof(memory));memcpy(memory+16,state,32);uint64_t r[{}]={{0}};r[7]=4112;r[4]=4352;(void)r;uint64_t result=nv_case{index}_readable({});memcpy(state,memory+16,32);return result; }}",program.register_count(),args.join(",")).unwrap();
    }
    generated.push_str(&driver(&names));
    let source = scratch.0.join("generated.c");
    std::fs::write(&source, generated).unwrap();
    for opt in ["-O0", "-O2"] {
        let executable = scratch.0.join(format!("generated{opt}"));
        native::compile_c(
            &source,
            &executable,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run(&executable, &text), expected);
    }
    println!(
        "{bits}-bit: {} signed reciprocal native/oracle/IR observations; {} generated C observations under UBSan",
        expected.len() * 2,
        expected.len() * 2
    );
}
