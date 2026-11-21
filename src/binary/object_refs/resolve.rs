use super::{Literal, MAX_STRING_BYTES, Reference, ReferenceUse, Target};
use crate::binary::elf::{FunctionContext, RelocationTarget};
use crate::binary::x86::{DecodedInstruction, Operand, Operation};
use crate::model::ir::Width;

/// Bind only the exact trailing field of a supported instruction. Extra or
/// overlapping relocations keep the instruction's reference unresolved.
pub(super) fn bind(
    context: &FunctionContext<'_>,
    instruction: DecodedInstruction,
    indices: &[usize],
    references: &mut [Reference],
) -> Option<usize> {
    if indices.len() != 1 {
        return None;
    }
    let id = indices[0];
    let reference = &references[id].relocation;
    let addend = reference.addend?;
    let (usage, width, bias, allowed): (ReferenceUse, u64, i64, &[u32]) =
        match instruction.operation {
            Operation::Lea {
                destination,
                address,
            } if destination.width == Width::U64 && address.rip_relative => {
                (ReferenceUse::Address, 4, 4, &[2])
            }
            Operation::Mov {
                destination: Operand::Register(destination),
                source: Operand::Immediate(_),
            } if destination.shift == 0 && destination.width == Width::U64 => {
                (ReferenceUse::Address, 8, 0, &[1])
            }
            Operation::Mov {
                destination: Operand::Register(destination),
                source: Operand::Immediate(_),
            } if destination.shift == 0 && destination.width == Width::U32 => {
                (ReferenceUse::Address, 4, 0, &[10])
            }
            Operation::Call(_) => (ReferenceUse::Call, 4, 4, &[2, 4]),
            Operation::Jump(_) => (ReferenceUse::TailCall, 4, 4, &[2, 4]),
            Operation::IndirectCall(Operand::Memory {
                address,
                width: Width::U64,
            })
            | Operation::IndirectJump(Operand::Memory {
                address,
                width: Width::U64,
            }) if address.rip_relative => (ReferenceUse::GotCall, 4, 4, &[9, 41, 42]),
            _ => return None,
        };
    let start = instruction.address.checked_sub(context.image.address)?;
    let end = start.checked_add(u64::from(instruction.size))?;
    if !allowed.contains(&reference.kind)
        || reference.width != Some(width)
        || reference.offset.checked_add(width)? != end
        || u64::from(instruction.size) <= width
        || !encoded_field(context, instruction, width)
    {
        return None;
    }
    let adjusted = addend.checked_add(bias)?;
    // A GOT displacement selects a slot, whose contents are the symbol value.
    // An offset from that slot is not an offset from the symbol's code/data.
    if usage == ReferenceUse::GotCall && adjusted != 0 {
        return None;
    }
    let target = match &reference.target {
        RelocationTarget::Undefined => Target::External {
            name: reference.symbol.clone()?,
            addend: adjusted,
        },
        RelocationTarget::Section { index, offset } => {
            let section = context.sections.get(*index)?;
            let value = i128::from(*offset) + i128::from(adjusted);
            if value < 0 || value > i128::from(section.size) {
                return None;
            }
            Target::Section {
                index: *index,
                offset: value as u64,
            }
        }
        RelocationTarget::Absolute(value) => {
            let value = i128::from(*value) + i128::from(adjusted);
            Target::Absolute(u64::try_from(value).ok()?)
        }
        RelocationTarget::Reserved(_) => return None,
    };
    references[id].instruction = Some(start);
    references[id].usage = Some(usage);
    references[id].target = Some(target);
    Some(id)
}

// Operation normalizes encoding distinctions such as EB/E9 and C7/B8. Check
// those distinctions directly against the original bytes before binding a
// relocation; prefixes/opcodes themselves must never become address fields.
fn encoded_field(
    context: &FunctionContext<'_>,
    instruction: DecodedInstruction,
    width: u64,
) -> bool {
    let Some(start) = instruction
        .address
        .checked_sub(context.image.address)
        .and_then(|s| usize::try_from(s).ok())
    else {
        return false;
    };
    let Some(code) = context
        .image
        .bytes
        .get(start..start + usize::from(instruction.size))
    else {
        return false;
    };
    let Some(op) = code.iter().position(|b| !matches!(b, 0x66 | 0x40..=0x4f)) else {
        return false;
    };
    let opcode = code[op];
    let rip_modrm = code.get(op + 1).is_some_and(|b| b & 0xc7 == 5);
    match instruction.operation {
        Operation::Lea { .. } => opcode == 0x8d && rip_modrm && op + 6 == code.len() && width == 4,
        Operation::Mov {
            destination: Operand::Register(reg),
            source: Operand::Immediate(_),
        } => {
            if (0xb8..=0xbf).contains(&opcode) {
                op + 1 + width as usize == code.len()
            } else {
                reg.width == Width::U32
                    && opcode == 0xc7
                    && code.get(op + 1).is_some_and(|b| b & 0xf8 == 0xc0)
                    && op + 6 == code.len()
                    && width == 4
            }
        }
        Operation::Call(_) => opcode == 0xe8 && op + 5 == code.len() && width == 4,
        Operation::Jump(_) => opcode == 0xe9 && op + 5 == code.len() && width == 4,
        Operation::IndirectCall(_) | Operation::IndirectJump(_) => {
            opcode == 0xff && rip_modrm && op + 6 == code.len() && width == 4
        }
        _ => false,
    }
}

pub(super) fn literal(
    context: &FunctionContext<'_>,
    target: &Target,
    budget: &mut usize,
) -> Result<Option<Literal>, super::ReferenceError> {
    let Target::Section { index, offset } = *target else {
        return Ok(None);
    };
    let Some(section) = context.sections.get(index) else {
        return Ok(None);
    };
    // File-backed, allocated read-only data. Executable, TLS and compressed
    // sections have different interpretation/layout contracts.
    if section.kind != 1 || section.flags & 2 == 0 || section.flags & (1 | 4 | 0x400 | 0x800) != 0 {
        return Ok(None);
    }
    let Some(tail) = section
        .bytes
        .and_then(|b| usize::try_from(offset).ok().and_then(|o| b.get(o..)))
    else {
        return Ok(None);
    };
    let scan = tail.len().min(MAX_STRING_BYTES + 1);
    super::flow::spend(budget, scan)?;
    let Some(length) = tail[..scan].iter().position(|&b| b == 0) else {
        return Ok(None);
    };
    super::flow::spend(budget, length + section.name.map_or(0, str::len))?;
    Ok(Some(Literal {
        section: index,
        section_name: section.name.map(str::to_owned),
        offset,
        bytes: tail[..length].to_vec(),
    }))
}
