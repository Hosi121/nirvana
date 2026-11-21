//! Standalone C11 lowering for a complete checked module.
//!
//! Every lifted instruction is emitted once in a global guest-PC dispatcher.
//! Calls and returns communicate only through the checked guest stack; the
//! host C stack is never used to implement guest control flow.

use std::fmt::Write;

use crate::emit::{Expressions, MULTIPLY_HELPER, validate_program};
use crate::ir::{AccessKind, Control};
use crate::module_ir::{Instruction, Module, REGISTER_COUNT, ROOT_RETURN, Target};

const RUNTIME: &str = include_str!("module_emit/runtime.h");
const POSIX: &str = include_str!("module_emit/posix.h");
const FORMATTED: &str = include_str!("module_emit/formatted.h");

/// Lower a module to a self-contained C11 executable with bounded execution.
/// The module's original instruction bytes are data, never host code.
pub fn emit_c(module: &Module) -> Result<String, String> {
    let program = &module.program;
    if program.register_count() != REGISTER_COUNT || REGISTER_COUNT != 80 {
        return Err("module C requires exactly 80 guest registers".to_owned());
    }
    validate_program(program.shape()).map_err(|error| error.to_string())?;
    image_layout(module)?;
    // A fixed shape describes expression metadata; it never rewrites the
    // module's call/return dispatch or ordered lifted assignments.
    let expressions = Expressions::new(program.shape());
    let mut code = String::from("#define _POSIX_C_SOURCE 200809L\n");
    code.push_str(&runtime_header(module));
    // Keep this helper unconditional: all expressions, including transfer and
    // vector guard expressions, can use the ordinary IR multiply operation.
    code.push_str(MULTIPLY_HELPER);
    if program
        .instructions()
        .iter()
        .any(|i| matches!(i, Instruction::Divide { .. }))
    {
        code.push_str(crate::x86::divide::C_HELPER);
    }
    code.push_str(&posix_header(module));
    code.push_str("\nstatic unsigned nv_run(struct nv_module *s) {\n    uint64_t *r=s->r;\n    struct nirvana_memory m={s};\n    (void)r; (void)m;\n    if(setjmp(s->jump)!=0) return s->status;\n    for(;;) {\n");
    writeln!(
        code,
        "        if(s->pc==UINT64_C({ROOT_RETURN})) return s->status=0;"
    )
    .unwrap();
    code.push_str("        switch(s->pc) {\n");
    for function in program.functions() {
        writeln!(
            code,
            "        /* function {} at {:#x}, size {} */",
            comment(&function.name),
            function.address,
            function.size
        )
        .unwrap();
    }
    for instruction in program.instructions() {
        writeln!(code, "        case UINT64_C({}): {{", instruction.address()).unwrap();
        code.push_str("            if(!nv_step(s)) return s->status;\n");
        let next = instruction
            .address()
            .checked_add(u64::from(instruction.size()))
            .ok_or("instruction end address overflows")?;
        match instruction {
            Instruction::Divide { .. } => {
                divide_statement(&mut code, &expressions, instruction, 3, "return s->status;")?;
                set_pc(&mut code, next);
            }
            Instruction::Core(instruction) => {
                expressions
                    .assignments(&mut code, 3, &instruction.assignments)
                    .map_err(|error| error.to_string())?;
                match &instruction.control {
                    Control::Next => set_pc(&mut code, next),
                    Control::Jump(target) => set_pc(&mut code, *target),
                    Control::Branch { condition, target } => {
                        expressions
                            .statement(
                                &mut code,
                                3,
                                condition,
                                "s->pc = (",
                                &format!(") ? UINT64_C({target}) : UINT64_C({next});"),
                            )
                            .map_err(|error| error.to_string())?;
                    }
                    Control::Return(_) => {
                        return Err("module Core cannot contain Return".to_owned());
                    }
                }
            }
            Instruction::Transfer { target, link, .. } => {
                code.push_str("            uint64_t nv_target;\n");
                if let Target::Value(value) = target {
                    expressions
                        .statement(&mut code, 3, value, "nv_target = ", ";")
                        .map_err(|error| error.to_string())?;
                }
                if let Some(link) = link {
                    writeln!(code, "            r[4]-=UINT64_C(8);\n            nv_write(s,r[4],8,UINT64_C({link}));").unwrap();
                }
                if let Target::Plt(slot) = target {
                    writeln!(code, "            nv_target=nv_read(s,UINT64_C({slot}),8);").unwrap();
                }
                code.push_str("            s->pc=nv_target;\n");
            }
            Instruction::Return { extra_pop, .. } => {
                code.push_str("            s->pc=nv_read(s,r[4],8);\n");
                writeln!(
                    code,
                    "            r[4]+=UINT64_C({});",
                    8u32 + u32::from(*extra_pop)
                )
                .unwrap();
            }
            Instruction::Vector(instruction) => {
                if let Some(memory) = &instruction.memory {
                    code.push_str("            uint64_t nv_vector_address;\n");
                    expressions
                        .statement(&mut code, 3, &memory.address, "nv_vector_address = ", ";")
                        .map_err(|error| error.to_string())?;
                    let access = match memory.access {
                        AccessKind::Read => 1,
                        AccessKind::Write => 2,
                    };
                    writeln!(
                        code,
                        "            (void)nv_check(s,nv_vector_address,UINT64_C({}),{access});",
                        memory.width
                    )
                    .unwrap();
                    if memory.alignment != 1 {
                        let condition = if memory.alignment == 0 {
                            "1".to_owned()
                        } else {
                            format!("nv_vector_address%UINT64_C({})!=0", memory.alignment)
                        };
                        writeln!(code, "            if({condition}) {{\n                s->status=9; s->fault_address=nv_vector_address; s->fault_width=UINT64_C({}); s->fault_access={access};\n                return s->status;\n            }}", memory.width).unwrap();
                    }
                }
                expressions
                    .assignments(&mut code, 3, &instruction.assignments)
                    .map_err(|error| error.to_string())?;
                set_pc(&mut code, next);
            }
        }
        code.push_str("            break;\n        }\n");
    }
    for import in program.imports() {
        writeln!(code, "        case UINT64_C({}): {{", import.address).unwrap();
        code.push_str("            if(s->imports_left==0) return s->status=5;\n            --s->imports_left;\n");
        writeln!(
            code,
            "            if(!nv_posix_call(s,{})) return s->status=3;",
            c_string(&import.name)
        )
        .unwrap();
        code.push_str("            s->pc=nv_read(s,r[4],8);\n            r[4]+=UINT64_C(8);\n            break;\n        }\n");
    }
    code.push_str("        default: return s->status=2;\n        }\n    }\n}\n");
    code.push_str(&image_initialization(module)?);
    Ok(code)
}

pub(crate) fn runtime_header(module: &Module) -> String {
    let mut code = format!("/* execution profile: {} */\n", module.program.model_id());
    if let Some(layout) = &module.image.memory_layout {
        writeln!(
            code,
            "#define NV_SPARSE_REGION_COUNT {}",
            layout.regions().len()
        )
        .unwrap();
        code.push_str("#define NV_SPARSE_REGIONS {");
        for region in layout.regions() {
            write!(
                code,
                "{{UINT64_C({}),UINT64_C({}),UINT64_C({}),{}}},",
                region.address, region.size, region.offset, region.permissions
            )
            .unwrap();
        }
        code.push_str("}\n");
    }
    code.push_str(RUNTIME);
    code
}

pub(crate) fn divide_statement(
    code: &mut String,
    expressions: &Expressions,
    instruction: &Instruction,
    indent: usize,
    failure: &str,
) -> Result<(), String> {
    let Instruction::Divide {
        source,
        width,
        signed,
        ..
    } = instruction
    else {
        return Err("expected module division".into());
    };
    let pad = "    ".repeat(indent);
    writeln!(code, "{pad}uint64_t nv_divisor;").unwrap();
    expressions
        .statement(code, indent, source, "nv_divisor = ", ";")
        .map_err(|e| e.to_string())?;
    writeln!(
        code,
        "{pad}if(!nv_divide({},{},r[0],r[2],nv_divisor,&r[0],&r[2])) {{ s->status=10; {failure} }}",
        width.bits(),
        u8::from(*signed)
    )
    .unwrap();
    Ok(())
}
pub(crate) fn posix_header(module: &Module) -> String {
    use crate::loader::StandardStream;
    let mut code = String::from(
        "\n#define NV_GUEST_STDOUT(s) nv_guest_stdout(s)\nstatic inline FILE *nv_guest_stdout(struct nv_module *s) {\n",
    );
    if let Some(stdout) = module
        .image
        .external_data
        .iter()
        .find(|b| b.stream == StandardStream::Stdout)
    {
        writeln!(code, "    uint64_t handle=nv_read(s,UINT64_C({}),8);\n    if(handle==UINT64_C({})) return stdout;",
            stdout.address, stdout.handle).unwrap();
        if let Some(stderr) = module
            .image
            .external_data
            .iter()
            .find(|b| b.stream == StandardStream::Stderr)
        {
            writeln!(
                code,
                "    if(handle==UINT64_C({})) return stderr;",
                stderr.handle
            )
            .unwrap();
        }
        code.push_str("    return NULL;\n");
    } else {
        code.push_str("    (void)s; return stdout;\n");
    }
    code.push_str("}\n");
    code.push_str("#define NV_GUEST_STDIN(s) nv_guest_stdin(s)\nstatic inline FILE *nv_guest_stdin(struct nv_module *s) {\n");
    if let Some(stdin) = module
        .image
        .external_data
        .iter()
        .find(|b| b.stream == StandardStream::Stdin)
    {
        writeln!(
            code,
            "    if(nv_read(s,UINT64_C({}),8)==UINT64_C({})) return stdin;\n    return NULL;",
            stdin.address, stdin.handle
        )
        .unwrap();
    } else {
        code.push_str("    (void)s; return stdin;\n");
    }
    code.push_str("}\n");
    code.push_str(FORMATTED);
    code.push_str(POSIX);
    code
}

pub(crate) fn image_initialization(module: &Module) -> Result<String, String> {
    let (size, base, root_sp) = image_layout(module)?;
    let program = &module.program;
    let mut code = String::new();
    for binding in &module.image.external_data {
        writeln!(
            code,
            "/* external {}: guest pointer variable at {:#x} */\n#define NV_{}_HANDLE UINT64_C({})",
            binding.stream.name(),
            binding.address,
            binding.stream.name().to_ascii_uppercase(),
            binding.handle
        )
        .unwrap();
    }
    if let Some(tls) = &module.image.thread_local {
        writeln!(code, "/* guest FS stack guard; supplied by the initial image */\n#define NV_TLS_GUARD_ADDRESS UINT64_C({})",
            tls.base + crate::x86::FS_GUARD_OFFSET).unwrap();
    }
    writeln!(code, "\nstatic const uint8_t nv_initial_image[{}]={{", size).unwrap();
    let mut any = false;
    for (index, byte) in module.image.memory.iter().enumerate() {
        if *byte != 0 {
            writeln!(code, "    [{index}]=0x{byte:02x},").unwrap();
            any = true;
        }
    }
    if !any {
        code.push_str("    0\n");
    }
    code.push_str("};\n\nstatic struct nv_module *nv_create(void) {\n    struct nv_module *s=calloc(1,sizeof(*s));\n    if(s==NULL) return NULL;\n    s->memory=malloc(sizeof(nv_initial_image));\n    if(s->memory==NULL) { free(s); return NULL; }\n    memcpy(s->memory,nv_initial_image,sizeof(nv_initial_image));\n");
    writeln!(code, "    s->base=UINT64_C({base}); s->size=UINT64_C({size});\n    s->pc=UINT64_C({}); s->errno_address=UINT64_C({});\n    s->r[4]=UINT64_C({root_sp});", program.entry(), program.errno_address()).unwrap();
    code.push_str(
        "    s->instructions_left=NV_INSTRUCTION_LIMIT; s->imports_left=NV_IMPORT_LIMIT;\n",
    );
    code.push_str("    return s;\n}\n\nint main(void) {\n    struct nv_module *s=nv_create();\n    if(s==NULL) { fputs(\"nirvana module: allocation failed\\n\",stderr); return 1; }\n    unsigned status=nv_run(s);\n    int result=(int)(uint32_t)s->r[0];\n    if(status!=0) {\n        fprintf(stderr,\"nirvana module: status=%u pc=0x%llx started=%llu fault=0x%llx width=%llu access=%u\\n\",status,(unsigned long long)s->pc,(unsigned long long)s->started,(unsigned long long)s->fault_address,(unsigned long long)s->fault_width,s->fault_access);\n        result=(int)status;\n    }\n    free(s->memory); free(s);\n    return result;\n}\n");
    Ok(code)
}

fn image_layout(module: &Module) -> Result<(u64, u64, u64), String> {
    let program = &module.program;
    let size = u64::try_from(module.image.memory.len())
        .map_err(|_| "guest image length does not fit u64")?;
    let base = module.image.memory_base;
    if module.image.memory_layout.as_ref() != program.memory_layout()
        || module
            .image
            .memory_layout
            .as_ref()
            .is_some_and(|layout| layout.size() != size as usize)
    {
        return Err("image and program memory layouts disagree".into());
    }
    base.checked_add(size)
        .ok_or("guest image address range overflows")?;
    let root_sp = module
        .image
        .stack_pointer
        .checked_sub(16)
        .ok_or("guest root stack pointer underflows")?;
    for (name, address) in [
        ("root return slot", root_sp),
        ("errno slot", program.errno_address()),
    ] {
        if module.image.memory_offset(address, 8).is_none() {
            return Err(format!("{name} lies outside the guest image"));
        }
    }
    Ok((size, base, root_sp))
}

fn set_pc(code: &mut String, address: u64) {
    writeln!(code, "            s->pc=UINT64_C({address});").unwrap();
}

pub(crate) fn c_string(value: &str) -> String {
    let mut result = String::from("\"");
    for byte in value.bytes() {
        if (b' '..=b'~').contains(&byte) && !matches!(byte, b'"' | b'\\' | b'?') {
            result.push(char::from(byte));
        } else {
            write!(result, "\\{byte:03o}").unwrap();
        }
    }
    result.push('"');
    result
}

pub(crate) fn comment(value: &str) -> String {
    let mut result = String::new();
    for byte in value.bytes() {
        if (b' '..=b'~').contains(&byte) && !matches!(byte, b'*' | b'/' | b'\\') {
            result.push(char::from(byte));
        } else {
            write!(result, "\\x{byte:02x}").unwrap();
        }
    }
    result
}
