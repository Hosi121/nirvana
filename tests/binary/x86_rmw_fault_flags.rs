//! Scalar RMW commits flags after its checked Store. Native architectural
//! comparisons exclude private lifter scratch; generated C compares full state.
use crate::support::{module_fixture, native};
use nirvana::{
    ir::AccessKind,
    ir::Width,
    linked_elf::LinkedOptions,
    memory::{READ, WRITE},
    module_ir::{self, Limits, Module, RejectImports, Status},
    x86,
};
use std::fmt::Write as _;
use std::process::Command;

const READ_ONLY: u64 = 0x2337_0000;
const UNMAPPED: u64 = 0x2000_0000;
const FLAGS: [(usize, u32); 5] = [
    (x86::CF, 0),
    (x86::PF, 2),
    (x86::ZF, 6),
    (x86::SF, 7),
    (x86::OF, 11),
];

#[derive(Clone, Copy, Debug)]
enum Kind {
    Add,
    Adc,
    Sbb,
    Neg,
    Inc,
    Dec,
    Shl,
    Shr,
    Sar,
    Rol,
    Ror,
    Shld,
    Shrd,
}

#[derive(Clone, Copy, Debug)]
struct Profile {
    width: Width,
    kind: Kind,
    count: u8,
}

impl Profile {
    fn bytes(self) -> Vec<u8> {
        let mut code = match self.width {
            Width::U16 => vec![0x66],
            Width::U64 => vec![0x48],
            _ => Vec::new(),
        };
        let byte = self.width == Width::U8;
        match self.kind {
            Kind::Add | Kind::Adc | Kind::Sbb => code.extend([
                if byte { 0x80 } else { 0x83 },
                match self.kind {
                    Kind::Add => 0x06,
                    Kind::Adc => 0x16,
                    _ => 0x1e,
                },
                1,
            ]),
            Kind::Neg => code.extend([if byte { 0xf6 } else { 0xf7 }, 0x1e]),
            Kind::Inc | Kind::Dec => code.extend([
                if byte { 0xfe } else { 0xff },
                if matches!(self.kind, Kind::Inc) {
                    0x06
                } else {
                    0x0e
                },
            ]),
            Kind::Shld | Kind::Shrd => code.extend([
                0x0f,
                if matches!(self.kind, Kind::Shld) {
                    0xa4
                } else {
                    0xac
                },
                0x16, // source RDX, destination [RSI]
                self.count,
            ]),
            _ => code.extend([
                if byte { 0xc0 } else { 0xc1 },
                match self.kind {
                    Kind::Rol => 0x06,
                    Kind::Ror => 0x0e,
                    Kind::Shl => 0x26,
                    Kind::Shr => 0x2e,
                    Kind::Sar => 0x3e,
                    _ => unreachable!(),
                },
                self.count,
            ]),
        }
        code
    }
}

fn profiles() -> Vec<Profile> {
    let mut result = Vec::new();
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for kind in [
            Kind::Add,
            Kind::Adc,
            Kind::Sbb,
            Kind::Neg,
            Kind::Inc,
            Kind::Dec,
        ] {
            result.push(Profile {
                width,
                kind,
                count: 1,
            });
        }
        for kind in [
            Kind::Shl,
            Kind::Shr,
            Kind::Sar,
            Kind::Rol,
            Kind::Ror,
            Kind::Shld,
            Kind::Shrd,
        ] {
            if width == Width::U8 && matches!(kind, Kind::Shld | Kind::Shrd) {
                continue;
            }
            for count in [0, 1, if width == Width::U64 { 64 } else { 32 }] {
                result.push(Profile { width, kind, count });
            }
        }
    }
    result
}

fn fixture(directory: &std::path::Path, profiles: &[Profile]) -> Module {
    let mut source = String::from(".text\n");
    for (index, profile) in profiles.iter().enumerate() {
        writeln!(
            source,
            ".globl rmw_{index}\n.type rmw_{index},@function\nrmw_{index}:"
        )
        .unwrap();
        // Load the destination supplied by module_fixture and establish flags
        // for whole-function validation. Tests may resume directly at the RMW
        // with independently seeded flags, using the normal resume API.
        source.push_str(".byte 0x48,0x8b,0x37,0x4d,0x39,0xc0\n");
        for byte in profile.bytes() {
            writeln!(source, ".byte {byte}").unwrap();
        }
        writeln!(source, ".byte 0xc3\n.size rmw_{index},.-rmw_{index}").unwrap();
    }
    source.push_str(
        ".section .rofar,\"a\",@progbits\n.quad 5,7,11,13\n\
         .section .note.GNU-stack,\"\",@progbits\n",
    );
    let assembly = directory.join("rmw.S");
    let binary = directory.join("rmw");
    std::fs::write(&assembly, source).unwrap();
    native::compile(
        Command::new("cc")
            .args([
                "-nostdlib",
                "-fno-pie",
                "-no-pie",
                "-Wl,-e,rmw_0",
                "-Wl,--section-start=.rofar=0x23370000",
            ])
            .arg(assembly)
            .arg("-o")
            .arg(&binary),
    );
    let module = module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "rmw_0",
        LinkedOptions {
            load_bias: 0,
            stack_size: 4096,
        },
    )
    .unwrap();
    let layout = module.program.memory_layout().unwrap();
    assert!(layout.offset(READ_ONLY, 8, READ).is_some());
    assert_eq!(layout.offset(READ_ONLY, 8, WRITE), None);
    assert_eq!(layout.offset(UNMAPPED, 8, READ), None);
    assert!(
        module.rejected_functions.is_empty(),
        "{:?}",
        module.rejected_functions
    );
    module
}

fn entry(module: &Module, index: usize) -> u64 {
    module
        .program
        .functions()
        .iter()
        .find(|function| function.name == format!("rmw_{index}"))
        .unwrap()
        .address
}

fn input(module: &Module, address: u64, seed: u64) -> Vec<u64> {
    let mut registers = module.initial_registers();
    for (index, value) in registers.iter_mut().enumerate() {
        if index != x86::RSP {
            *value = 0x1234_5678_9abc_def0u64.wrapping_mul(index as u64 + 1);
        }
    }
    registers[x86::RSI] = address;
    registers[x86::DF] = 0;
    for (register, bit) in FLAGS {
        registers[register] = (seed >> bit) & 1;
    }
    registers
}

fn run(
    module: &Module,
    pc: u64,
    registers: &[u64],
    memory: &[u8],
    budget: usize,
) -> module_ir::Report {
    module
        .program
        .run_from(
            pc,
            registers,
            module.image.memory_base,
            memory,
            Limits {
                instructions: budget,
                imports: 0,
            },
            &mut RejectImports,
        )
        .unwrap()
}

#[test]
fn readonly_rmw_faults_preserve_architecture_and_zero_count_store_attempts() {
    let scratch = native::Scratch::new();
    let profiles = profiles();
    let module = fixture(&scratch.0, &profiles);
    for (index, profile) in profiles.iter().enumerate() {
        let pc = entry(&module, index) + 6;
        for seed in [0x202, 0xad7] {
            for (address, access) in [(READ_ONLY, AccessKind::Write), (UNMAPPED, AccessKind::Read)]
            {
                let registers = input(&module, address, seed);
                for budget in [0, 1, 2] {
                    let report = run(&module, pc, &registers, &module.image.memory, budget);
                    assert_eq!(report.pc, pc, "{profile:?}");
                    assert_eq!(report.state.instruction, Some(pc));
                    assert_eq!(report.state.memory, module.image.memory, "{profile:?}");
                    assert_eq!(report.state.memory_layout, module.image.memory_layout);
                    assert_eq!(
                        report.state.registers[..21],
                        registers[..21],
                        "{profile:?} seed={seed:#x} address={address:#x}"
                    );
                    assert_eq!(report.state.registers[x86::DF], registers[x86::DF]);
                    assert_eq!(report.state.registers[32..64], registers[32..64]);
                    assert_eq!(report.imports, 0);
                    if budget == 0 {
                        assert_eq!(
                            report.status,
                            Status::Suspended(module_ir::Limit::Instructions)
                        );
                        assert!(report.state.trace.is_empty());
                        assert_eq!(report.state.registers, registers);
                    } else {
                        assert!(
                            matches!(report.status, Status::Fault(f) if f.address == address && f.width == profile.width.bytes() as u64 && f.access == access),
                            "{profile:?}: {:?}",
                            report.status
                        );
                        assert_eq!(report.state.trace, [pc]);
                    }
                }
            }
        }
    }
}

#[test]
fn checked_c_backends_match_full_rmw_fault_and_success_state() {
    let scratch = native::Scratch::new();
    // Every operation and zero/masked-zero case at 64 bits; the architectural
    // gate above covers all scalar widths. One compile per backend/optimization.
    let profiles: Vec<_> = profiles()
        .into_iter()
        .filter(|p| p.width == Width::U64)
        .collect();
    let module = fixture(&scratch.0, &profiles);
    let writable = module_fixture::state_address(&module) + 64;
    let initial = input(&module, writable, 0xad7);
    let mut cases = Vec::new();
    let mut rows = Vec::new();
    let mut memories = Vec::new();
    for (index, _) in profiles.iter().enumerate() {
        for address in [READ_ONLY, writable, UNMAPPED] {
            for budget in [0, 2, 3, 4] {
                let case = module_fixture::Case {
                    input: [address, 0, 0, 0],
                    pc: entry(&module, index),
                    budget,
                    patch: Some((writable, 5, 8)),
                };
                rows.push(module_fixture::expected_with_state(&module, &case, Some(&initial)).0);
                let (registers, memory) =
                    module_fixture::prepare_with_state(&module, &case, Some(&initial));
                memories.push(
                    run(&module, case.pc, &registers, &memory, budget)
                        .state
                        .memory,
                );
                cases.push(case);
            }
        }
    }
    let count = module_fixture::check_generated_with_memory(
        &module, &cases, &rows, &memories, &scratch.0, &initial,
    );
    assert_eq!(count, cases.len() * 6);
}

#[cfg(target_arch = "x86_64")]
fn native_success(profile: Profile, memory: &mut [u8], seed: u64, source: u64) -> u64 {
    use std::arch::asm;
    let flags: u64;
    macro_rules! instruction {
        ($operation:literal) => {
            unsafe {
                asm!("push {seed}", "popfq", $operation, "pushfq", "pop rdi",
                    seed = in(reg) seed, in("rsi") memory.as_mut_ptr(),
                    in("rcx") u64::from(profile.count), in("rdx") source,
                    lateout("rdi") flags);
            }
        };
    }
    macro_rules! sized {
        ($byte:literal, $word:literal, $dword:literal, $qword:literal) => {
            match profile.width {
                Width::U8 => instruction!($byte),
                Width::U16 => instruction!($word),
                Width::U32 => instruction!($dword),
                Width::U64 => instruction!($qword),
            }
        };
    }
    match profile.kind {
        Kind::Add => sized!(
            "add byte ptr [rsi],1",
            "add word ptr [rsi],1",
            "add dword ptr [rsi],1",
            "add qword ptr [rsi],1"
        ),
        Kind::Adc => sized!(
            "adc byte ptr [rsi],1",
            "adc word ptr [rsi],1",
            "adc dword ptr [rsi],1",
            "adc qword ptr [rsi],1"
        ),
        Kind::Sbb => sized!(
            "sbb byte ptr [rsi],1",
            "sbb word ptr [rsi],1",
            "sbb dword ptr [rsi],1",
            "sbb qword ptr [rsi],1"
        ),
        Kind::Neg => sized!(
            "neg byte ptr [rsi]",
            "neg word ptr [rsi]",
            "neg dword ptr [rsi]",
            "neg qword ptr [rsi]"
        ),
        Kind::Inc => sized!(
            "inc byte ptr [rsi]",
            "inc word ptr [rsi]",
            "inc dword ptr [rsi]",
            "inc qword ptr [rsi]"
        ),
        Kind::Dec => sized!(
            "dec byte ptr [rsi]",
            "dec word ptr [rsi]",
            "dec dword ptr [rsi]",
            "dec qword ptr [rsi]"
        ),
        Kind::Shl => sized!(
            "shl byte ptr [rsi],cl",
            "shl word ptr [rsi],cl",
            "shl dword ptr [rsi],cl",
            "shl qword ptr [rsi],cl"
        ),
        Kind::Shr => sized!(
            "shr byte ptr [rsi],cl",
            "shr word ptr [rsi],cl",
            "shr dword ptr [rsi],cl",
            "shr qword ptr [rsi],cl"
        ),
        Kind::Sar => sized!(
            "sar byte ptr [rsi],cl",
            "sar word ptr [rsi],cl",
            "sar dword ptr [rsi],cl",
            "sar qword ptr [rsi],cl"
        ),
        Kind::Rol => sized!(
            "rol byte ptr [rsi],cl",
            "rol word ptr [rsi],cl",
            "rol dword ptr [rsi],cl",
            "rol qword ptr [rsi],cl"
        ),
        Kind::Ror => sized!(
            "ror byte ptr [rsi],cl",
            "ror word ptr [rsi],cl",
            "ror dword ptr [rsi],cl",
            "ror qword ptr [rsi],cl"
        ),
        Kind::Shld => match profile.width {
            Width::U16 => instruction!("shld word ptr [rsi],dx,cl"),
            Width::U32 => instruction!("shld dword ptr [rsi],edx,cl"),
            Width::U64 => instruction!("shld qword ptr [rsi],rdx,cl"),
            _ => unreachable!(),
        },
        Kind::Shrd => match profile.width {
            Width::U16 => instruction!("shrd word ptr [rsi],dx,cl"),
            Width::U32 => instruction!("shrd dword ptr [rsi],edx,cl"),
            Width::U64 => instruction!("shrd qword ptr [rsi],rdx,cl"),
            _ => unreachable!(),
        },
    }
    flags
}

#[test]
#[cfg(target_arch = "x86_64")]
fn writable_rmw_matches_native_values_and_defined_flags() {
    let scratch = native::Scratch::new();
    let profiles = profiles();
    let module = fixture(&scratch.0, &profiles);
    let destination = module_fixture::state_address(&module) + 65;
    let offset = module.image.memory_offset(destination, 8).unwrap();
    for (index, profile) in profiles.iter().enumerate() {
        for seed in [0x202, 0xad7] {
            for value in [0, 5, u64::MAX, 0x8000_0000_8000_8080] {
                let mut registers = input(&module, destination, seed);
                registers[x86::RDX] = 0x8765_4321_fedc_ba98;
                let mut memory = module.image.memory.clone();
                memory[offset - 1..offset + 9].fill(0x5a);
                memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
                let mut expected = memory.clone();
                let flags = native_success(
                    *profile,
                    &mut expected[offset..offset + 8],
                    seed,
                    registers[x86::RDX],
                );
                let pc = entry(&module, index) + 6;
                let report = run(&module, pc, &registers, &memory, 1);
                assert_eq!(
                    report.status,
                    Status::Suspended(module_ir::Limit::Instructions)
                );
                assert_eq!(report.pc, pc + profile.bytes().len() as u64);
                assert_eq!(report.state.instruction, Some(report.pc));
                assert_eq!(report.state.trace, [pc]);
                assert_eq!(report.state.registers[..16], registers[..16], "{profile:?}");
                assert_eq!(report.state.registers[x86::DF], registers[x86::DF]);
                assert_eq!(report.state.registers[32..64], registers[32..64]);
                assert_eq!(
                    report.state.memory, expected,
                    "{profile:?} seed={seed:#x} value={value:#x}"
                );
                for (register, bit) in FLAGS {
                    assert_eq!(
                        report.state.registers[register],
                        (flags >> bit) & 1,
                        "{profile:?} flag={register} seed={seed:#x} value={value:#x}"
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn native_rmw_faults_preserve_flags_register_inputs_and_shared_ram() {
    let scratch = native::Scratch::new();
    let profiles = profiles();
    let mut source = String::from(
        r#"
#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>
static volatile sig_atomic_t output_fd;
static void fault(int number,siginfo_t *info,void *context) {
    (void)number;
    ucontext_t *u=context;
    uint64_t row[]={
        (uint64_t)u->uc_mcontext.gregs[REG_EFL],(uintptr_t)info->si_addr,
        (uint64_t)u->uc_mcontext.gregs[REG_RAX],
        (uint64_t)u->uc_mcontext.gregs[REG_RCX],
        (uint64_t)u->uc_mcontext.gregs[REG_RDX],
        (uint64_t)u->uc_mcontext.gregs[REG_ERR]
    };
    ssize_t count=write(output_fd,row,sizeof row);
    _exit(count==(ssize_t)sizeof row?0:71);
}
#define EXEC(bytes,count) do { \
    uint64_t a=UINT64_C(0x1111222233334444),c=count,d=UINT64_C(0x87654321fedcba98); \
    __asm__ volatile("pushq %[seed];popfq;" bytes \
        : "+a"(a),"+c"(c),"+d"(d) \
        : [seed]"r"(UINT64_C(0xad7)),"S"(pointer) : "cc","memory"); \
    _exit(72); \
} while(0)
static void operation(unsigned profile,void *pointer) {
    switch(profile) {
"#,
    );
    for (index, profile) in profiles.iter().enumerate() {
        let bytes = profile
            .bytes()
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            source,
            "case {index}: EXEC(\".byte {bytes}\",{});",
            profile.count
        )
        .unwrap();
    }
    source.push_str("default: _exit(73);\n}}\nstatic const uint64_t counts[]={");
    for profile in &profiles {
        write!(source, "{},", profile.count).unwrap();
    }
    source.push_str(
        r#"};
int main(void) {
    struct sigaction action={0};
    action.sa_sigaction=fault;action.sa_flags=SA_SIGINFO;
    assert(!sigemptyset(&action.sa_mask));assert(!sigaction(SIGSEGV,&action,NULL));
    long page_size=sysconf(_SC_PAGESIZE);assert(page_size>=4096);
    size_t size=(size_t)page_size;
    uint8_t *memory=mmap(NULL,size,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);
    assert(memory!=MAP_FAILED);
    memset(memory,0x5a,size);uint64_t value=5;memcpy(memory+3,&value,sizeof value);
    uint8_t *expected=malloc(size);assert(expected);memcpy(expected,memory,size);
    for(unsigned profile=0;profile<sizeof counts/sizeof counts[0];++profile) {
        for(unsigned unmapped=0;unmapped<2;++unmapped) {
            int channel[2];assert(!pipe(channel));
            pid_t child=fork();assert(child>=0);
            if(!child) {
                close(channel[0]);output_fd=channel[1];
                if(unmapped) {if(munmap(memory,size))_exit(74);}
                else if(mprotect(memory,size,PROT_READ))_exit(75);
                operation(profile,memory+3);
                _exit(76);
            }
            close(channel[1]);uint64_t row[6];size_t used=0;
            while(used<sizeof row) {
                ssize_t n=read(channel[0],(uint8_t *)row+used,sizeof row-used);
                if(n<0 && errno==EINTR)continue;
                if(n<=0)break;
                used+=(size_t)n;
            }
            close(channel[0]);int status;assert(waitpid(child,&status,0)==child);
            assert(WIFEXITED(status) && WEXITSTATUS(status)==0 && used==sizeof row);
            assert((row[0]&UINT64_C(0x8c5))==UINT64_C(0x8c5));
            assert(row[1]==(uintptr_t)(memory+3));
            assert(row[2]==UINT64_C(0x1111222233334444));
            assert(row[3]==counts[profile]);assert(row[4]==UINT64_C(0x87654321fedcba98));
            /* Native W/R intent remains a documented gap for unmapped IR RMW. */
            assert(row[5]&2);
            /* Observe actual shared backing in the parent after the child fault. */
            assert(!memcmp(memory,expected,size));
        }
    }
    free(expected);assert(!munmap(memory,size));return 0;
}
"#,
    );
    let path = scratch.0.join("fault.c");
    let binary = scratch.0.join("fault");
    std::fs::write(&path, source).unwrap();
    native::compile_c(&path, &binary, &["-O2"]);
    let observed = native::run_output(&binary, Some(""), std::time::Duration::from_secs(10));
    assert!(
        observed.status.success(),
        "{}",
        String::from_utf8_lossy(&observed.stderr)
    );
}
