#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use nirvana::ir::Width;
use nirvana::x86::divide::evaluate;
use std::fmt::Write as _;
use std::process::Command;

#[derive(Clone, Copy)]
struct Case {
    width: Width,
    signed: bool,
    form: usize,
    a: u64,
    d: u64,
    source: u64,
}
impl Case {
    fn divisor(self) -> u64 {
        match self.form {
            2 => self.a,
            3 => self.d,
            4 => self.a >> 8,
            _ => self.source,
        }
    }
    fn expected(self) -> Vec<u64> {
        match evaluate(self.width, self.signed, self.a, self.d, self.divisor()) {
            Some((a, d)) => vec![0, a, d],
            None => vec![1, self.a, self.d],
        }
    }
}
fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let mut seed = 0x8d71_23ab_5f69_e4c1u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let mask = width.mask();
        let half = 1u64 << (width.bits() - 1);
        let values = [0, 1, 2, 3, half - 1, half, half + 1, mask - 1, mask];
        for low in values {
            for high in values {
                for source in values {
                    let a = if width == Width::U8 {
                        (random() & !0xffff) | low | (high << 8)
                    } else {
                        (random() & !mask) | low
                    };
                    let d = (random() & !mask) | high;
                    for signed in [false, true] {
                        for form in 0..if width == Width::U8 { 5 } else { 4 } {
                            cases.push(Case {
                                width,
                                signed,
                                form,
                                a,
                                d,
                                source,
                            });
                        }
                    }
                }
            }
        }
        for _ in 0..512 {
            let (a, d, source) = (random(), random(), random());
            for signed in [false, true] {
                for form in 0..if width == Width::U8 { 5 } else { 4 } {
                    cases.push(Case {
                        width,
                        signed,
                        form,
                        a,
                        d,
                        source,
                    });
                }
            }
        }
    }
    // Exhaust all ordinary byte dividend/divisor pairs, including every signed
    // sign-extension pattern. The Cartesian cases above add arbitrary AX.
    for value in 0..=255u64 {
        for source in 0..=255u64 {
            for signed in [false, true] {
                let ax = if signed {
                    (value as u8 as i8 as i16) as u16 as u64
                } else {
                    value
                };
                cases.push(Case {
                    width: Width::U8,
                    signed,
                    form: 0,
                    a: 0x1a23_4567_89ab_0000 | ax,
                    d: 0xdeaf_beef_9876_5432,
                    source,
                });
            }
        }
    }
    cases
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
fn native_div_idiv_and_portable_c_match_double_width_arithmetic() {
    let scratch = native::Scratch::new();
    let cases = cases();
    let mut input = String::new();
    for case in &cases {
        writeln!(
            input,
            "{} {} {} {} {} {}",
            case.width.bits(),
            u8::from(case.signed),
            case.form,
            case.a,
            case.d,
            case.source
        )
        .unwrap();
    }
    let expected: Vec<_> = cases.iter().map(|case| case.expected()).collect();
    let mut assembly = String::from(".text\n");
    let mut declarations = String::new();
    let mut table = String::new();
    for (index, width) in [Width::U8, Width::U16, Width::U32, Width::U64]
        .into_iter()
        .enumerate()
    {
        for signed in [false, true] {
            for form in 0..if width == Width::U8 { 5 } else { 4 } {
                let name = format!("nv_native_{index}_{}_{form}", u8::from(signed));
                let divisor = match form {
                    0 => ["%r9b", "%r9w", "%r9d", "%r9"][index],
                    1 => "16(%r8)",
                    2 => ["%al", "%ax", "%eax", "%rax"][index],
                    3 => ["%dl", "%dx", "%edx", "%rdx"][index],
                    4 => "%ah",
                    _ => unreachable!(),
                };
                let mnemonic = format!(
                    "{}{}",
                    if signed { "idiv" } else { "div" },
                    ["b", "w", "l", "q"][index]
                );
                writeln!(assembly,".globl {name}\n.type {name},@function\n{name}:\n mov %rdx,16(%rcx)\n mov %rcx,%r8\n mov %rdx,%r9\n mov %rdi,%rax\n mov %rsi,%rdx\n.globl {name}_site\n{name}_site:\n {mnemonic} {divisor}\n mov %rax,0(%r8)\n mov %rdx,8(%r8)\n ret\n.size {name},.-{name}").unwrap();
                writeln!(declarations,"extern void {name}(uint64_t,uint64_t,uint64_t,uint64_t*);extern const char {name}_site[];").unwrap();
                writeln!(
                    table,
                    "[{index}][{}][{form}]={{{name},{name}_site}},",
                    u8::from(signed)
                )
                .unwrap();
            }
        }
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    let native_source = format!(
        r#"
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include <signal.h>
#include <setjmp.h>
#include <stdlib.h>
#include <ucontext.h>
{declarations}
typedef void (*native_fn)(uint64_t,uint64_t,uint64_t,uint64_t*);
struct entry {{ native_fn function;const char *site; }};
static const struct entry entries[4][2][5]={{{table}}};
static sigjmp_buf jump;
static volatile uint64_t trap_a,trap_d;
static const char *site;
static void trap(int signal,siginfo_t *info,void *context) {{
    (void)info; ucontext_t *u=context;
    if(signal!=SIGFPE || (uintptr_t)u->uc_mcontext.gregs[REG_RIP]!=(uintptr_t)site) _Exit(3);
    trap_a=(uint64_t)u->uc_mcontext.gregs[REG_RAX];trap_d=(uint64_t)u->uc_mcontext.gregs[REG_RDX];
    siglongjmp(jump,1);
}}
int main(void) {{
    struct sigaction action={{0}};action.sa_sigaction=trap;action.sa_flags=SA_SIGINFO;
    if(sigemptyset(&action.sa_mask)!=0 || sigaction(SIGFPE,&action,NULL)!=0)return 2;
    unsigned bits,is_signed,form;uint64_t a,d,source;
    while(scanf("%u %u %u %" SCNu64 " %" SCNu64 " %" SCNu64,&bits,&is_signed,&form,&a,&d,&source)==6) {{
        unsigned index=bits==8 ? 0 : bits==16 ? 1 : bits==32 ? 2 : 3;
        const struct entry *entry=&entries[index][is_signed][form];site=entry->site;
        uint64_t out[3]={{0,0,0}};
        if(sigsetjmp(jump,1)==0) {{entry->function(a,d,source,out);printf("0 %" PRIu64 " %" PRIu64 "\n",out[0],out[1]);}}
        else printf("1 %" PRIu64 " %" PRIu64 "\n",trap_a,trap_d);
    }}return 0;
}}
"#
    );
    let c = scratch.0.join("native.c");
    let asm = scratch.0.join("native.S");
    let binary = scratch.0.join("native");
    std::fs::write(&c, native_source).unwrap();
    std::fs::write(&asm, assembly).unwrap();
    compile(
        Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-O2",
            ])
            .arg(&c)
            .arg(&asm)
            .arg("-o")
            .arg(&binary),
    );
    assert_eq!(
        native::run_fields(&binary, &input, 3),
        expected,
        "native#DE/quotient/remainder/partial writes"
    );
    let helper = include_str!("../src/x86/divide.h");
    let source = format!(
        r#"
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
{helper}
int main(void) {{
    unsigned bits,is_signed,form;uint64_t a,d,source;
    while(scanf("%u %u %u %" SCNu64 " %" SCNu64 " %" SCNu64,&bits,&is_signed,&form,&a,&d,&source)==6) {{
        if(form==2)source=a;else if(form==3)source=d;else if(form==4)source=a>>8;
        unsigned ok=nv_divide(bits,is_signed,a,d,source,&a,&d);
        printf("%u %" PRIu64 " %" PRIu64 "\n",!ok,a,d);
    }}return 0;
}}
"#
    );
    let c = scratch.0.join("helper.c");
    std::fs::write(&c, source).unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(format!("helper{opt}"));
        compile(
            Command::new("cc")
                .args([
                    "-std=c11",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-pedantic",
                    "-fsanitize=undefined",
                    "-fno-sanitize-recover=undefined",
                    opt,
                ])
                .arg(&c)
                .arg("-o")
                .arg(&binary),
        );
        assert_eq!(
            native::run_fields(&binary, &input, 3),
            expected,
            "portable C {opt}"
        );
    }
    println!(
        "DIV/IDIV: {} native+Rust cases; {} Chelper comparisons with UBSan",
        cases.len(),
        cases.len() * 2
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn restoring_division_lemmas_have_positive_and_broken_controls() {
    use std::io::Write;
    use std::process::Stdio;
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    let directory =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/division-step");
    std::fs::create_dir_all(&directory).unwrap();
    for bits in [8, 16, 32, 64] {
        let model = include_str!("models/division_step.smt2.in")
            .replace("@W@", &bits.to_string())
            .replace("@STEP@", &(bits + 1).to_string())
            .replace("@MSB@", &(bits - 1).to_string());
        std::fs::write(directory.join(format!("width{bits}.smt2")), &model).unwrap();
        let mut process = Command::new(&solver)
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        process
            .stdin
            .take()
            .unwrap()
            .write_all(model.as_bytes())
            .unwrap();
        let output = process.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let text = String::from_utf8(output.stdout).unwrap();
        std::fs::write(directory.join(format!("width{bits}.out")), &text).unwrap();
        let statuses: Vec<_> = text
            .lines()
            .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
            .collect();
        assert_eq!(
            statuses,
            ["unsat", "sat", "sat", "unsat", "unsat"],
            "width{bits}: {text}"
        );
    }
}
