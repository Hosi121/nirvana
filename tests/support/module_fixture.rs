use super::native;
use nirvana::ir::AccessKind;
use nirvana::module_ir::{self, Limits, Module, RejectImports, Status};
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

pub(crate) use super::native::compile;
#[derive(Clone)]
pub(crate) struct Case {
    pub(crate) input: [u64; 4],
    pub(crate) pc: u64,
    pub(crate) budget: usize,
    pub(crate) patch: Option<(u64, u64, usize)>,
}
pub(crate) fn state_address(module: &Module) -> u64 {
    module.image.stack_pointer - 512
}
pub(crate) fn prepare_with_state(
    module: &Module,
    case: &Case,
    initial: Option<&[u64]>,
) -> (Vec<u64>, Vec<u8>) {
    let mut registers = initial.map_or_else(|| module.initial_registers(), |r| r.to_vec());
    assert_eq!(registers.len(), 80);
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
pub(crate) fn expected(module: &Module, case: &Case) -> (Vec<u64>, Status) {
    expected_with_state(module, case, None)
}
pub(crate) fn expected_with_state(
    module: &Module,
    case: &Case,
    initial: Option<&[u64]>,
) -> (Vec<u64>, Status) {
    let (registers, memory) = prepare_with_state(module, case, initial);
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
        Status::Suspended(module_ir::Limit::Imports) => (5, [0; 3]),
        Status::DivideError => (10, [0; 3]),
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
fn harness(code: &str, module: &Module, initial: Option<&[u64]>) -> String {
    let mut initialization = String::new();
    if let Some(registers) = initial {
        assert_eq!(registers.len(), 80);
        for (i, value) in registers.iter().enumerate() {
            writeln!(initialization, "s->r[{i}]=UINT64_C({value});").unwrap();
        }
    }
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
        {initialization}
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

pub(crate) fn build(compiler: &str, source: &Path, output: &Path, opt: &str, pie: bool) {
    compile(
        Command::new(compiler)
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

pub(crate) fn check_generated(
    module: &Module,
    cases: &[Case],
    expected_rows: &[Vec<u64>],
    directory: &Path,
    sanitize: bool,
) -> usize {
    check_generated_at_depths(module, cases, expected_rows, directory, sanitize, &[64])
}

pub(crate) fn check_generated_at_depths(
    module: &Module,
    cases: &[Case],
    expected_rows: &[Vec<u64>],
    directory: &Path,
    sanitize: bool,
    depths: &[u32],
) -> usize {
    check_generated_with_state(
        module,
        cases,
        expected_rows,
        directory,
        sanitize,
        depths,
        None,
    )
}

pub(crate) fn check_generated_with_state(
    module: &Module,
    cases: &[Case],
    expected_rows: &[Vec<u64>],
    directory: &Path,
    sanitize: bool,
    depths: &[u32],
    initial: Option<&[u64]>,
) -> usize {
    assert!(!depths.is_empty());
    let mut generated_cases = 0;
    let mut text = String::new();
    for case in cases {
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
        ("core", nirvana::module_emit::emit_c(module).unwrap()),
        (
            "readable",
            nirvana::module_readable::emit_c(module).unwrap().code,
        ),
        (
            "locals",
            nirvana::module_readable::emit_c_with_locals(module)
                .unwrap()
                .code,
        ),
    ];
    for (mode, code) in modes {
        let source = directory.join(format!("{mode}.c"));
        std::fs::write(&source, harness(&code, module, initial)).unwrap();
        for generated_opt in ["-O0", "-O2"] {
            for &depth in if mode == "core" { &depths[..1] } else { depths } {
                let binary = directory.join(format!("{mode}{generated_opt}-{depth}"));
                let mut command = Command::new("cc");
                command.args([
                    "-std=c11",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-pedantic",
                    generated_opt,
                ]);
                if sanitize {
                    command.args(["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]);
                }
                command.arg(format!("-DNV_HOST_DEPTH_LIMIT={depth}"));
                compile(command.arg(&source).arg("-o").arg(&binary));
                assert_eq!(
                    native::run_fields(&binary, &text, 94),
                    expected_rows,
                    "{mode} {generated_opt} depth{depth}: all registers,PC,budgets,fault,RAM digest"
                );
                generated_cases += cases.len();
            }
        }
    }
    generated_cases
}
