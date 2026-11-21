//! Selected linked functions and dynamic-import identity at the lift boundary.

use super::{EffectFrontendError, EffectFunction, FrontendError, LiftedFunction};
use crate::binary::linked_elf::{self, BinaryImage, LinkedOptions};
use crate::binary::x86::{self, DecodedInstruction, EffectLiftError, Operand, Operation};
use crate::model::effects::CallTarget;

fn options(object: &[u8]) -> LinkedOptions {
    LinkedOptions {
        load_bias: if object.get(16..18) == Some(&[2, 0]) {
            0
        } else {
            0x10000
        },
        ..Default::default()
    }
}

/// Load a selected sized function from ET_EXEC or PIE, then use the pure
/// integer lifter. Guest memory is supplied separately to the resulting IR.
pub fn lift_linked_elf(
    object: &[u8],
    symbol: &str,
    options: LinkedOptions,
) -> Result<LiftedFunction, FrontendError> {
    let binary = linked_elf::load(object, symbol, options)
        .map_err(|error| FrontendError::Linked(error.to_string()))?;
    let image = &binary.image.function;
    let program = x86::lift(&image.bytes, image.address, image.address).map_err(|error| {
        if let x86::LiftError::Decode(decode) = &error
            && decode.reason == "control flow leaves the supplied function"
            && let Some(import) = binary.plt_slot(decode.address)
        {
            return FrontendError::Linked(format!(
                "unsupported pure linked function: tail jump to import {:?} requires an external effect model",
                import.name
            ));
        }
        FrontendError::Lift(error)
    })?;
    let image = binary.image.function;
    Ok(LiftedFunction { image, program })
}

/// Dispatch object files and linked images without changing either explicit
/// format-specific API's placement rules.
pub fn lift_elf_auto(object: &[u8], symbol: &str) -> Result<LiftedFunction, FrontendError> {
    if object.get(16..18) == Some(&[1, 0]) {
        super::lift_elf(object, symbol)
    } else {
        lift_linked_elf(object, symbol, options(object))
    }
}

pub fn lift_elf_effects_auto(
    object: &[u8],
    symbol: &str,
) -> Result<EffectFunction, EffectFrontendError> {
    if object.get(16..18) == Some(&[1, 0]) {
        super::lift_elf_effects(object, symbol, Default::default())
    } else {
        lift_linked_elf_effects(object, symbol, options(object))
    }
}

/// Bind only imports proven by dynamic relocation records and actual PLT
/// instruction bytes. Internal and register-indirect calls need separate
/// interprocedural evidence and are reported at their original address.
pub fn lift_linked_elf_effects(
    object: &[u8],
    symbol: &str,
    options: LinkedOptions,
) -> Result<EffectFunction, EffectFrontendError> {
    let binary = linked_elf::load(object, symbol, options)
        .map_err(|error| EffectFrontendError::Linked(error.to_string()))?;
    let image = &binary.image;
    let mut rejected = None;
    let program = x86::lift_effects_with_resolver(
        &image.function.bytes,
        image.function.address,
        image.function.address,
        image.puts_address,
        |instruction| match import_target(&binary, instruction) {
            Ok(target) => Ok(Some(target)),
            Err(detail) => {
                rejected = Some(format!(
                    "linked call at {:#x}: {detail}",
                    instruction.address
                ));
                Err(EffectLiftError::UnsupportedTarget {
                    address: instruction.address,
                    reason: "linked target lacks a modeled import identity",
                })
            }
        },
    );
    let program = program.map_err(|error| match rejected {
        Some(detail) => EffectFrontendError::Linked(detail),
        None => EffectFrontendError::Lift(error),
    })?;
    Ok(EffectFunction {
        image: binary.image,
        program,
    })
}

fn import_target(
    binary: &BinaryImage,
    instruction: DecodedInstruction,
) -> Result<CallTarget, String> {
    let (slot, target) = match instruction.operation {
        Operation::Call(address) | Operation::Jump(address) => {
            let slot = binary.plt_slot(address).ok_or_else(|| {
                format!("target {address:#x} requires internal-call or PLT analysis")
            })?;
            (slot, CallTarget::Plt(slot.address))
        }
        Operation::IndirectCall(Operand::Memory { address, .. })
        | Operation::IndirectJump(Operand::Memory { address, .. })
            if address.rip_relative && address.base.is_none() && address.index.is_none() =>
        {
            let pointer = (instruction.address + u64::from(instruction.size))
                .wrapping_add(address.displacement as u64);
            let slot = binary
                .imports
                .iter()
                .find(|slot| slot.address == pointer && slot.width == 8)
                .ok_or_else(|| format!("slot {pointer:#x} lacks dynamic import evidence"))?;
            (slot, CallTarget::Memory(pointer))
        }
        _ => return Err("indirect target requires value-flow evidence".into()),
    };
    if slot.name != "puts" || !slot.modeled {
        return Err(format!(
            "import {:?} requires an external effect model",
            slot.name
        ));
    }
    Ok(target)
}
