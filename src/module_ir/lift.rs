use super::{
    Function, Import, Instruction, Module, ModuleError, Program, REGISTER_COUNT, ROOT_RETURN,
    Target,
};
use crate::cfg::{Cfg, Flow, Instruction as Location};
use crate::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Reg};
use crate::linked_elf::{self, BinaryImage, FunctionSymbol, LinkedOptions};
use crate::x86::{self, Addressing, DecodedInstruction, Operand, Operation};
use std::collections::{BTreeMap, BTreeSet};

const MAX_FUNCTIONS: usize = 512;
const MAX_INSTRUCTIONS: usize = 65_536;
const MAX_NODES: usize = 1_048_576;
const MAX_TABLE_CONTEXT_SEARCHES: usize = 64;
fn error(message: impl Into<String>) -> ModuleError {
    ModuleError(message.into())
}

pub fn lift_elf(
    object: &[u8],
    symbol: &str,
    options: LinkedOptions,
) -> Result<Module, ModuleError> {
    if options.stack_size < 32 {
        return Err(error("module stack requires at least 32 bytes"));
    }
    let binary =
        linked_elf::load_module(object, symbol, options).map_err(|e| error(e.to_string()))?;
    lift_binary(binary)
}

/// Lift an exact link-time region entry, using sized symbols and unwind bounds.
pub fn lift_elf_at(
    object: &[u8],
    entry: u64,
    options: LinkedOptions,
) -> Result<Module, ModuleError> {
    if options.stack_size < 32 {
        return Err(error("module stack requires at least 32 bytes"));
    }
    let binary =
        linked_elf::load_module_at(object, entry, options).map_err(|e| error(e.to_string()))?;
    lift_binary(binary)
}

fn lift_binary(mut binary: BinaryImage) -> Result<Module, ModuleError> {
    if binary.functions.len() > MAX_FUNCTIONS {
        return Err(error("module function catalog exceeds 512 entries"));
    }
    if binary.image.puts_address == ROOT_RETURN {
        return Err(error("image conflicts with root return marker"));
    }
    let imports = imports(&binary)?;
    let catalog: BTreeMap<_, _> = binary.functions.iter().map(|f| (f.address, f)).collect();
    let mut built = BTreeMap::new();
    let mut rejected = BTreeMap::new();
    let mut nodes = MAX_NODES;
    let mut total = 0usize;
    for function in &binary.functions {
        match lift_function(&binary, function, &mut nodes) {
            Ok(body) => {
                total += body.instructions.len();
                if total > MAX_INSTRUCTIONS {
                    return Err(error("module instruction limit exceeded"));
                }
                built.insert(function.address, body);
            }
            Err(e) => {
                rejected.insert(function.address, (function.name.clone(), e.to_string()));
            }
        }
    }
    let entry = binary.image.function.address;
    // Every statically called function in the root's closure must be available.
    // Dynamic targets remain checked against the module's decoded addresses.
    let mut pending = vec![entry];
    let mut required = BTreeSet::new();
    while let Some(address) = pending.pop() {
        if !required.insert(address) || imports.iter().any(|i| i.address == address) {
            continue;
        }
        let function = built.get(&address).ok_or_else(|| {
            if let Some((name, reason)) = rejected.get(&address) {
                error(format!("module function {name:?}: {reason}"))
            } else {
                error(format!(
                    "module direct target {address:#x} lacks a bounded code region"
                ))
            }
        })?;
        pending.extend(function.direct.iter().copied());
    }
    let mut instructions = Vec::new();
    let mut functions = Vec::new();
    let mut jump_tables = Vec::new();
    let mut jump_table_diagnostics = Vec::new();
    let mut jump_table_context_limits = Vec::new();
    for (address, body) in built {
        let symbol = catalog[&address];
        functions.push(Function {
            name: symbol.name.clone(),
            address,
            size: symbol.size,
        });
        instructions.extend(body.instructions);
        jump_tables.extend(body.jump_tables);
        jump_table_context_limits.extend(body.context_limits);
        if let Some(reason) = body.discovery_declined {
            jump_table_diagnostics.push((address, reason));
        }
    }
    instructions.sort_by_key(Instruction::address);
    for pair in instructions.windows(2) {
        if pair[0]
            .address()
            .checked_add(u64::from(pair[0].size()))
            .is_none_or(|end| end > pair[1].address())
        {
            return Err(error("module code regions overlap instruction streams"));
        }
    }
    let function_ends: BTreeSet<_> = functions.iter().map(|f| f.address + f.size).collect();
    let shape = crate::ir::Program::new(
        entry,
        REGISTER_COUNT,
        instructions
            .iter()
            .map(|i| {
                let mut metadata = shape(i);
                if let Instruction::Transfer {
                    link: Some(next), ..
                } = i
                    && function_ends.contains(next)
                {
                    // This is a host-body exit, not an executed guest RET.
                    metadata.control = Control::Return(Expr::Const(0));
                }
                metadata
            })
            .collect(),
    )
    .map_err(|e| error(format!("module layout: {e}")))?;
    crate::emit::validate_program(&shape).map_err(|e| error(format!("module syntax: {e}")))?;
    let errno_address = binary.image.stack_pointer;
    let root = errno_address
        .checked_sub(16)
        .ok_or_else(|| error("root stack address underflows"))?;
    let offset = binary
        .image
        .memory_offset(root, 8)
        .ok_or_else(|| error("root stack lies outside image"))?;
    binary
        .image
        .memory
        .get_mut(offset..offset + 8)
        .ok_or_else(|| error("root stack lies outside image"))?
        .copy_from_slice(&ROOT_RETURN.to_le_bytes());
    Ok(Module {
        program: Program {
            memory_layout: binary.image.memory_layout.clone(),
            instructions,
            imports,
            functions,
            shape,
            entry,
            errno_address,
        },
        image: binary.image,
        rejected_functions: rejected.into_values().collect(),
        jump_tables,
        jump_table_diagnostics,
        jump_table_context_limits,
    })
}

fn imports(binary: &BinaryImage) -> Result<Vec<Import>, ModuleError> {
    let mut imports = BTreeMap::<u64, String>::new();
    for slot in &binary.imports {
        let offset = binary
            .image
            .memory_offset(slot.address, 8)
            .ok_or_else(|| error("import field outside image"))?;
        let bytes = binary
            .image
            .memory
            .get(offset..offset + 8)
            .ok_or_else(|| error("import field outside image"))?;
        let value = u64::from_le_bytes(bytes.try_into().unwrap());
        let value = u64::try_from(i128::from(value) - i128::from(slot.addend))
            .map_err(|_| error("canonical import address overflows"))?;
        if binary.image.memory_offset(value, 1).is_some() || value == ROOT_RETURN {
            return Err(error(
                "canonical import target aliases guest RAM or root return",
            ));
        }
        if let Some(old) = imports.insert(value, slot.name.clone())
            && old != slot.name
        {
            return Err(error("different imports share a canonical address"));
        }
    }
    Ok(imports
        .into_iter()
        .map(|(address, name)| Import { address, name })
        .collect())
}

fn shape(instruction: &Instruction) -> IrInstruction {
    let marker = |value| Assignment {
        destination: Reg(79).into(),
        value,
    };
    match instruction {
        Instruction::Core(i) => i.clone(),
        Instruction::StoreString { address, size, .. } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![],
            control: Control::Next,
        },
        Instruction::Divide {
            address,
            size,
            source,
            ..
        } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![marker(source.clone())],
            control: Control::Next,
        },
        Instruction::Transfer {
            address,
            size,
            target,
            link,
        } => IrInstruction {
            address: *address,
            size: *size,
            assignments: match target {
                Target::Value(v) => vec![marker(v.clone())],
                Target::Plt(a) => vec![marker(Expr::load(Expr::Const(*a), crate::ir::Width::U64))],
            },
            control: if link.is_some() {
                Control::Next
            } else {
                Control::Return(Expr::Const(0))
            },
        },
        Instruction::Return { address, size, .. } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![],
            control: Control::Return(Expr::Register(Reg(x86::RAX))),
        },
        Instruction::Vector(i) => {
            let mut assignments = Vec::new();
            if let Some(m) = &i.memory {
                assignments.push(marker(m.address.clone()));
            }
            assignments.extend(i.assignments.clone());
            IrInstruction {
                address: i.address,
                size: i.size,
                assignments,
                control: Control::Next,
            }
        }
    }
}

struct Body {
    instructions: Vec<Instruction>,
    direct: BTreeSet<u64>,
    jump_tables: Vec<crate::jump_tables::Candidate>,
    discovery_declined: Option<String>,
    context_limits: BTreeSet<u64>,
}
fn lift_function(
    binary: &BinaryImage,
    function: &FunctionSymbol,
    nodes: &mut usize,
) -> Result<Body, ModuleError> {
    let remaining = *nodes;
    match lift_function_inner(binary, function, nodes, true) {
        Ok(body) => Ok(body),
        Err(reason) => {
            // Discovery is optional. A malformed/unsupported proposed stream
            // retains the original dynamic transfer and original decode scope.
            *nodes = remaining;
            let mut body = lift_function_inner(binary, function, nodes, false)?;
            body.discovery_declined = Some(reason.to_string());
            Ok(body)
        }
    }
}

fn lift_function_inner(
    binary: &BinaryImage,
    function: &FunctionSymbol,
    nodes: &mut usize,
    discovery: bool,
) -> Result<Body, ModuleError> {
    let base = function.address;
    let end = base
        .checked_add(function.size)
        .ok_or_else(|| error("function range overflow"))?;
    let start = binary
        .image
        .memory_offset(base, function.size as usize)
        .ok_or_else(|| error("function outside RAM"))?;
    let bytes = binary
        .image
        .memory
        .get(start..start + function.size as usize)
        .ok_or_else(|| error("function outside RAM"))?;
    let mut pending = vec![base];
    let mut decoded = BTreeMap::<u64, (Instruction, DecodedInstruction)>::new();
    let mut direct = BTreeSet::new();
    let mut jump_tables = Vec::new();
    let mut roots = BTreeSet::from([base]);
    let mut context_limits = BTreeSet::new();
    let mut searches_left = MAX_TABLE_CONTEXT_SEARCHES;
    loop {
        while let Some(address) = pending.pop() {
            if decoded.contains_key(&address) {
                continue;
            }
            if !(base..end).contains(&address) {
                return Err(error(format!(
                    "control leaves bounded code region at {address:#x}"
                )));
            }
            if decoded.len() >= 16_384 {
                return Err(error("function instruction limit exceeded"));
            }
            let source = &bytes[(address - base) as usize..];
            let decoded_instruction = x86::decode_reference_at(source, address).or_else(|scalar| {
                if source.first() == Some(&0x64) {
                    let guard = binary
                        .image
                        .thread_local
                        .as_ref()
                        .ok_or_else(|| scalar.clone())?
                        .base
                        + x86::FS_GUARD_OFFSET;
                    x86::decode_fs_guard_at(source, address, guard)
                } else {
                    Err(scalar)
                }
            });
            let (instruction, original) = match decoded_instruction {
                Ok(original) => {
                    let next = address + u64::from(original.size);
                    let transfer = match original.operation {
                        Operation::Call(target) => {
                            Some((Target::Value(Expr::Const(target)), Some(next)))
                        }
                        Operation::Jump(target) if !(base..end).contains(&target) => {
                            Some((Target::Value(Expr::Const(target)), None))
                        }
                        Operation::IndirectCall(operand) => {
                            Some((operand_target(operand, next)?, Some(next)))
                        }
                        Operation::IndirectJump(operand) => {
                            Some((operand_target(operand, next)?, None))
                        }
                        _ => None,
                    };
                    let instruction = if let Some((mut target, link)) = transfer {
                        if let Target::Value(Expr::Const(value)) = &target {
                            if let Some(slot) = binary.plt_slot(*value) {
                                target = Target::Plt(slot.address);
                            } else {
                                if !binary
                                    .functions
                                    .iter()
                                    .any(|function| function.address == *value)
                                {
                                    return Err(error(format!(
                                        "unsupported direct target {value:#x}: requires a bounded code region or proven PLT"
                                    )));
                                }
                                direct.insert(*value);
                            }
                        }
                        Instruction::Transfer {
                            address,
                            size: u32::from(original.size),
                            target,
                            link,
                        }
                    } else if let Operation::Divide { source, signed } = original.operation {
                        Instruction::Divide {
                            address,
                            size: u32::from(original.size),
                            source: operand_value(source, next)?,
                            width: source
                                .width()
                                .ok_or_else(|| error("division operand width missing"))?,
                            signed,
                        }
                    } else if let Operation::Return { extra_pop } = original.operation {
                        Instruction::Return {
                            address,
                            size: u32::from(original.size),
                            extra_pop,
                        }
                    } else {
                        Instruction::Core(
                            x86::lift_instruction(original).map_err(|e| error(e.to_string()))?,
                        )
                    };
                    (instruction, original)
                }
                Err(scalar) => {
                    if let Ok(string) = x86::decode_string_at(source, address) {
                        let instruction = match string.operation {
                            x86::StringOperation::Direction(backwards) => {
                                Instruction::Core(IrInstruction {
                                    address,
                                    size: u32::from(string.size),
                                    assignments: vec![Assignment {
                                        destination: Reg(x86::DF).into(),
                                        value: Expr::Const(u64::from(backwards)),
                                    }],
                                    control: Control::Next,
                                })
                            }
                            x86::StringOperation::Store { width, repeat } => {
                                Instruction::StoreString {
                                    address,
                                    size: u32::from(string.size),
                                    width,
                                    repeat,
                                }
                            }
                        };
                        (
                            instruction,
                            DecodedInstruction {
                                address,
                                size: string.size,
                                operation: Operation::Nop,
                            },
                        )
                    } else {
                        let vector = x86::decode_vector_at(source, address).map_err(|vector| {
                            error(format!("{scalar}; vector fallback: {vector}"))
                        })?;
                        let original = DecodedInstruction {
                            address,
                            size: vector.size as u8,
                            operation: Operation::Nop,
                        };
                        (Instruction::Vector(vector), original)
                    }
                }
            };
            let next = address + u64::from(instruction.size());
            if next > end {
                return Err(error("instruction exceeds bounded code region"));
            }
            if let Some((_, (previous, _))) = decoded.range(..address).next_back()
                && previous.address() + u64::from(previous.size()) > address
            {
                return Err(error("branch enters an instruction"));
            }
            if decoded.range(address..next).next().is_some() {
                return Err(error("overlapping instruction streams"));
            }
            match &instruction {
                Instruction::Core(i) => match &i.control {
                    Control::Next => pending.push(next),
                    Control::Jump(target) => pending.push(*target),
                    Control::Branch { target, .. } => {
                        pending.push(next);
                        pending.push(*target);
                    }
                    Control::Return(_) => return Err(error("unexpected scalar return")),
                },
                Instruction::Transfer {
                    link: Some(next), ..
                } => {
                    // A final CALL may be a stack-check failure path. Keep its
                    // real return slot, but leave an out-of-region continuation
                    // to checked module dispatch if the callee does return.
                    if *next != end {
                        pending.push(*next);
                    }
                }
                Instruction::Vector(_)
                | Instruction::Divide { .. }
                | Instruction::StoreString { .. } => pending.push(next),
                _ => {}
            }
            charge(&instruction, nodes)?;
            decoded.insert(address, (instruction, original));
        }
        if !discovery {
            break;
        }
        // Drain direct flow before inspecting predecessors, so physical layout
        // and worklist ordering cannot select just one incoming table base.
        // Vector placeholders carry flag metadata only; they are context barriers.
        let originals: Vec<_> = decoded
            .values()
            .filter_map(|(i, original)| {
                (!matches!(i, Instruction::Vector(_) | Instruction::StoreString { .. }))
                    .then_some(*original)
            })
            .collect();
        for branch in originals
            .iter()
            .filter(|i| matches!(i.operation, Operation::IndirectJump(_)))
        {
            if searches_left == 0 {
                context_limits.insert(branch.address);
                continue;
            }
            searches_left -= 1;
            let search = crate::jump_tables::discover_cfg_mapped(
                &originals,
                branch.address,
                binary.image.memory_view(),
                base..end,
            );
            if search.reached_limit {
                context_limits.insert(branch.address);
            }
            for table in search.candidates {
                let before: usize = jump_tables
                    .iter()
                    .map(|t: &crate::jump_tables::Candidate| t.entries.len())
                    .sum();
                let mut combined = jump_tables.clone();
                crate::jump_tables::merge_candidate(&mut combined, table.clone());
                if combined.len() > 16 {
                    context_limits.insert(branch.address);
                    continue;
                }
                let after: usize = combined.iter().map(|t| t.entries.len()).sum();
                *nodes = nodes
                    .checked_sub((after - before) * 2)
                    .ok_or_else(|| error("jump table metadata limit exceeded"))?;
                for target in table.targets() {
                    roots.insert(target);
                    if !decoded.contains_key(&target) {
                        pending.push(target);
                    }
                }
                if roots.len() > 1024 {
                    return Err(error("jump table entry-root limit exceeded"));
                }
                jump_tables = combined;
            }
        }
        if pending.is_empty() {
            break;
        }
    }
    let mut locations = Vec::new();
    let mut originals = Vec::new();
    let mut instructions = Vec::new();
    for (instruction, original) in decoded.into_values() {
        let flow = match &instruction {
            Instruction::Core(i) => match i.control {
                Control::Next => Flow::Next,
                Control::Jump(t) => Flow::Jump(t),
                Control::Branch { target, .. } => Flow::Branch(target),
                Control::Return(_) => Flow::Return,
            },
            Instruction::Transfer { link: None, .. } | Instruction::Return { .. } => Flow::Return,
            _ => Flow::Next,
        };
        locations.push(Location::new(
            instruction.address(),
            instruction.size(),
            flow,
        ));
        originals.push(original);
        instructions.push(instruction);
    }
    if roots
        .len()
        .checked_mul(locations.len())
        .is_none_or(|n| n > 1_048_576)
    {
        return Err(error("jump table flag-validation work limit exceeded"));
    }
    // A candidate entry is conservatively checked with no inherited flag
    // facts. This also checks branches reachable only through table entries.
    for root in roots {
        let cfg = Cfg::build(root, locations.clone()).map_err(|e| error(e.to_string()))?;
        x86::check_effect_flags(&cfg, &originals).map_err(|e| error(e.to_string()))?;
    }
    Ok(Body {
        instructions,
        direct,
        jump_tables,
        discovery_declined: None,
        context_limits,
    })
}

fn operand_target(operand: Operand, next: u64) -> Result<Target, ModuleError> {
    Ok(Target::Value(match operand {
        Operand::Register(reg) if reg.width == crate::ir::Width::U64 && reg.shift == 0 => {
            Expr::Register(Reg(reg.index as usize))
        }
        Operand::Memory {
            address,
            width: crate::ir::Width::U64,
        } => Expr::load(address_expr(address, next), crate::ir::Width::U64),
        _ => return Err(error("module transfer requires a near 64-bit target")),
    }))
}

fn operand_value(operand: Operand, next: u64) -> Result<Expr, ModuleError> {
    Ok(match operand {
        Operand::Register(reg) => {
            let value = Expr::Register(Reg(reg.index as usize));
            let value = if reg.shift == 0 {
                value
            } else {
                Expr::binary(BinaryOp::Shr, value, Expr::Const(u64::from(reg.shift)))
            };
            Expr::binary(BinaryOp::And, value, Expr::Const(reg.width.mask()))
        }
        Operand::Memory { address, width } => Expr::load(address_expr(address, next), width),
        _ => return Err(error("division requires a register or memory operand")),
    })
}
fn address_expr(address: Addressing, next: u64) -> Expr {
    let mut value = Expr::Const(address.displacement as u64);
    if address.rip_relative {
        value = Expr::binary(BinaryOp::Add, value, Expr::Const(next));
    }
    if let Some(base) = address.base {
        value = Expr::binary(BinaryOp::Add, value, Expr::Register(Reg(base as usize)));
    }
    if let Some(index) = address.index {
        value = Expr::binary(
            BinaryOp::Add,
            value,
            Expr::binary(
                BinaryOp::Mul,
                Expr::Register(Reg(index as usize)),
                Expr::Const(u64::from(address.scale)),
            ),
        );
    }
    value
}

fn charge(instruction: &Instruction, remaining: &mut usize) -> Result<(), ModuleError> {
    let s = shape(instruction);
    let mut pending = Vec::new();
    for assignment in &s.assignments {
        if let Place::Memory { address, .. } = &assignment.destination {
            pending.push((address, 1));
        }
        pending.push((&assignment.value, 1));
    }
    match &s.control {
        Control::Branch { condition, .. } => pending.push((condition, 1)),
        Control::Return(value) => pending.push((value, 1)),
        _ => {}
    }
    while let Some((expression, depth)) = pending.pop() {
        if depth > 128 {
            return Err(error("module expression depth exceeds bound"));
        }
        *remaining = remaining
            .checked_sub(1)
            .ok_or_else(|| error("module syntax node limit exceeded"))?;
        match expression {
            Expr::Binary(_, a, b) => {
                pending.push((a, depth + 1));
                pending.push((b, depth + 1));
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push((condition, depth + 1));
                pending.push((taken, depth + 1));
                pending.push((not_taken, depth + 1));
            }
            _ => {}
        }
    }
    Ok(())
}
