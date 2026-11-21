//! Checked C11 for explicit effect IR, using the same outcome tape as Rust.
use crate::codegen::emit::{Expressions, integer, validate_program};
use crate::model::effects::{CallTarget, Instruction, Program};
use crate::model::ir::Control;
use crate::transform::sequence::SequenceError;
use std::collections::BTreeSet;
use std::fmt::Write as _;
mod helpers;

pub(crate) fn runtime_header() -> &'static str {
    helpers::HEADER
}

pub(crate) const FUNCTION_OPEN: &str = "\nunsigned nirvana_effect_run(uint64_t *r, uint8_t *memory, uint64_t base, uint64_t size, struct nirvana_effects *e) {\n    jmp_buf jump;\n    struct nirvana_memory m = {memory,base,size,e,&jump};\n    (void)r; (void)m;\n    e->status=0; e->result=0; e->output_size=0; e->consumed=0; e->started=0;\n    e->fault_address=0; e->fault_width=0; e->fault_access=0; e->unknown_target=0;\n    if(setjmp(jump)!=0) return e->status;\n";

/// Registers, memory, output and outcome storage are distinct host objects.
/// Result/fault/output metadata lives in `struct nirvana_effects` in the C API.
pub fn emit_c(program: &Program) -> Result<String, SequenceError> {
    validate_program(program.shape())?;
    let expressions = Expressions::new(program.shape());
    let mut code = String::from("#include <stdint.h>\n#include <setjmp.h>\n");
    integer::append_helpers(program.shape(), &mut code);
    code.push_str(runtime_header());
    writeln!(
        code,
        "\n#define NIRVANA_EFFECT_REGISTERS {}",
        program.register_count()
    )
    .unwrap();
    code.push_str(FUNCTION_OPEN);
    writeln!(code, "    goto nirvana_pc_{};", program.entry()).unwrap();
    let reachable: BTreeSet<_> = program
        .cfg()
        .reachable_blocks()
        .into_iter()
        .flat_map(|id| {
            program.shape().instructions()[program.cfg().block(id).instructions.clone()]
                .iter()
                .map(|i| i.address)
        })
        .collect();
    for instruction in program.instructions() {
        let (address, size) = match instruction {
            Instruction::Core(i) => (i.address, i.size),
            Instruction::Call(i) => (i.address, i.size),
        };
        if !reachable.contains(&address) {
            continue;
        }
        writeln!(code, "nirvana_pc_{address}: ;").unwrap();
        writeln!(code, "    e->instruction=UINT64_C({address});").unwrap();
        code.push_str("    if(e->instructions_left==0) {e->status=5;return e->status;}\n    --e->instructions_left; ++e->started;\n");
        match instruction {
            Instruction::Core(i) => {
                expressions.assignments(&mut code, 1, &i.assignments)?;
                match &i.control {
                    Control::Next => jump(&mut code, address + u64::from(size)),
                    Control::Jump(target) => jump(&mut code, *target),
                    Control::Branch { condition, target } => {
                        expressions.statement(
                            &mut code,
                            1,
                            condition,
                            "if (",
                            &format!(") goto nirvana_pc_{target};"),
                        )?;
                        jump(&mut code, address + u64::from(size));
                    }
                    Control::Return(value) => {
                        expressions.statement(&mut code, 1, value, "e->result=", ";")?;
                        code.push_str("    e->status=0; return e->status;\n");
                    }
                }
            }
            Instruction::Call(call) => {
                let (kind, operand) = match call.target {
                    CallTarget::Direct(value) => (0, format!("UINT64_C({value})")),
                    CallTarget::Register(reg) => (0, format!("r[{}]", reg.0)),
                    CallTarget::Memory(address) => (1, format!("UINT64_C({address})")),
                    CallTarget::Plt(address) => (2, format!("UINT64_C({address})")),
                };
                writeln!(code,"    if(!nirvana_call_puts(&m,r,{kind},{operand},UINT64_C({}),{},UINT64_C({}))) return e->status;",address+u64::from(size),u8::from(call.tail),program.puts_address()).unwrap();
                if call.tail {
                    code.push_str("        e->result=r[0]; e->status=0; return e->status;\n");
                } else {
                    writeln!(
                        code,
                        "        goto nirvana_pc_{};",
                        address + u64::from(size)
                    )
                    .unwrap();
                }
            }
        }
    }
    code.push_str("}\n");
    Ok(code)
}
fn jump(code: &mut String, address: u64) {
    writeln!(code, "    goto nirvana_pc_{address};").unwrap();
}

/// Emit the executable model together with its relocated initial guest image.
pub fn emit_image(
    program: &Program,
    image: &crate::binary::loader::LinkedImage,
) -> Result<String, String> {
    let mut code = emit_c(program).map_err(|e| e.to_string())?;
    code.push_str(&image_initialization(image)?);
    Ok(code)
}

pub(crate) fn image_initialization(
    image: &crate::binary::loader::LinkedImage,
) -> Result<String, String> {
    let mut code = String::new();
    let nonzero = image.memory.iter().filter(|&&b| b != 0).count();
    if nonzero > 500_000 {
        return Err("initial image exceeds C output bound".into());
    }
    writeln!(code,"\n#define NIRVANA_EFFECT_MEMORY_BASE UINT64_C({})\n#define NIRVANA_EFFECT_MEMORY_SIZE {}\n#define NIRVANA_EFFECT_STACK_POINTER UINT64_C({})",image.memory_base,image.memory.len(),image.stack_pointer).unwrap();
    code.push_str("static const uint8_t nirvana_initial_memory[NIRVANA_EFFECT_MEMORY_SIZE]={\n");
    if nonzero == 0 {
        code.push_str("0\n");
    }
    for (i, &byte) in image.memory.iter().enumerate().filter(|(_, b)| **b != 0) {
        writeln!(code, "[{i}]={byte},").unwrap();
    }
    code.push_str("};\nvoid nirvana_effect_init(uint64_t *r,uint8_t *memory) {\n    for(unsigned i=0;i<NIRVANA_EFFECT_REGISTERS;++i) r[i]=0;\n    r[4]=NIRVANA_EFFECT_STACK_POINTER;\n    for(uint64_t i=0;i<NIRVANA_EFFECT_MEMORY_SIZE;++i) memory[i]=nirvana_initial_memory[i];\n}\n");
    Ok(code)
}
