use super::{
    ArgumentRegister, Call, Literal, MAX_INSTRUCTIONS, MAX_WORK, ObjectReferences, Reference,
    ReferenceError, ReferenceUse, Target,
};
use crate::elf::FunctionContext;
use crate::ir::Width;
use crate::x86::{self, Alu, DecodedInstruction, Operand, Operation};
use std::collections::{BTreeMap, VecDeque};

type State = [Option<usize>; 16];
struct Node {
    instruction: DecodedInstruction,
    reference: Option<usize>,
    successors: Vec<u64>,
    call: bool,
    tail: bool,
    target: Option<Target>,
    symbol: Option<String>,
}
struct Value {
    target: Target,
    bits: u32,
    literal: Option<usize>,
}
#[derive(Default)]
struct Values {
    values: Vec<Value>,
    by_target: BTreeMap<(Target, u32), usize>,
    literals: Vec<Literal>,
    by_literal: BTreeMap<Target, Option<usize>>,
    literal_bytes: usize,
}
impl Values {
    fn intern(
        &mut self,
        context: &FunctionContext<'_>,
        target: &Target,
        bits: u32,
        budget: &mut usize,
    ) -> Result<usize, ReferenceError> {
        spend(budget, target_work(target).saturating_mul(4))?;
        let key = (target.clone(), bits);
        if let Some(&id) = self.by_target.get(&key) {
            return Ok(id);
        }
        let literal = if let Some(id) = self.by_literal.get(target) {
            *id
        } else {
            let id = if let Some(literal) = super::resolve::literal(context, target, budget)? {
                self.literal_bytes += literal.bytes.len();
                if self.literal_bytes > 1_048_576 {
                    return Err(ReferenceError::Limit("literal bytes"));
                }
                let id = self.literals.len();
                self.literals.push(literal);
                Some(id)
            } else {
                None
            };
            self.by_literal.insert(target.clone(), id);
            id
        };
        let id = self.values.len();
        self.values.push(Value {
            target: target.clone(),
            bits,
            literal,
        });
        self.by_target.insert(key, id);
        Ok(id)
    }
}

pub(super) fn spend(budget: &mut usize, amount: usize) -> Result<(), ReferenceError> {
    *budget = budget
        .checked_sub(amount)
        .ok_or(ReferenceError::Limit("analysis work"))?;
    Ok(())
}
fn target_work(target: &Target) -> usize {
    match target {
        Target::External { name, .. } => name.len().saturating_add(1),
        _ => 1,
    }
}
fn local(context: &FunctionContext<'_>, target: &Target) -> Option<u64> {
    match target {
        Target::Section { index, offset } if *index == context.section => offset
            .checked_sub(context.offset)
            .filter(|&o| o < context.image.bytes.len() as u64),
        _ => None,
    }
}
fn raw_target(context: &FunctionContext<'_>, address: u64) -> Option<Target> {
    let section = context.sections.get(context.section)?;
    let offset = address.checked_sub(section.address)?;
    (offset < section.size).then_some(Target::Section {
        index: context.section,
        offset,
    })
}

pub(super) fn analyze(context: &FunctionContext<'_>) -> Result<ObjectReferences, ReferenceError> {
    if context.references.iter().any(|r| r.width.is_none()) {
        return Err(ReferenceError::Invalid("unknown relocation field width"));
    }
    let mut budget = MAX_WORK;
    spend(&mut budget, context.image.name.len())?;
    for reference in &context.references {
        spend(
            &mut budget,
            reference
                .symbol
                .as_ref()
                .map_or(1, |s| s.len().saturating_add(1)),
        )?;
    }
    let mut references: Vec<_> = context
        .references
        .iter()
        .cloned()
        .map(|relocation| Reference {
            relocation,
            instruction: None,
            usage: None,
            target: None,
            literal: None,
        })
        .collect();
    let mut by_offset: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
    for (id, reference) in references.iter().enumerate() {
        if reference.relocation.width == Some(0) {
            continue;
        }
        by_offset
            .entry(reference.relocation.offset)
            .or_default()
            .push(id);
    }
    let mut nodes: BTreeMap<u64, Node> = BTreeMap::new();
    let mut pending = vec![0];
    while let Some(offset) = pending.pop() {
        spend(&mut budget, 1)?;
        if nodes.contains_key(&offset) {
            continue;
        }
        if nodes.len() >= MAX_INSTRUCTIONS {
            return Err(ReferenceError::Limit("instruction count"));
        }
        let bytes = context
            .image
            .bytes
            .get(usize::try_from(offset).map_err(|_| ReferenceError::Invalid("code offset"))?..)
            .ok_or(ReferenceError::Invalid("control flow leaves function"))?;
        if bytes.is_empty() {
            return Err(ReferenceError::Invalid("control flow leaves function"));
        }
        if let Some((_, previous)) = nodes.range(..offset).next_back()
            && offset
                < previous.instruction.address - context.image.address
                    + u64::from(previous.instruction.size)
        {
            return Err(ReferenceError::Invalid("branch enters an instruction"));
        }
        let address = context
            .image
            .address
            .checked_add(offset)
            .ok_or(ReferenceError::Invalid("code address overflow"))?;
        let instruction = x86::decode_reference_at(bytes, address)?;
        let next = offset + u64::from(instruction.size);
        if nodes.range((offset + 1)..next).next().is_some() {
            return Err(ReferenceError::Invalid("overlapping instructions"));
        }
        let mut indices = Vec::new();
        for (&start, ids) in by_offset.range(offset.saturating_sub(16)..next) {
            spend(&mut budget, ids.len())?;
            for &id in ids {
                let width = references[id].relocation.width.unwrap_or(1);
                if start.checked_add(width).is_none_or(|end| end > offset) {
                    indices.push(id);
                }
            }
        }
        for &id in &indices {
            spend(
                &mut budget,
                references[id]
                    .relocation
                    .symbol
                    .as_ref()
                    .map_or(1, |s| s.len().saturating_add(1))
                    .saturating_mul(4),
            )?;
        }
        let reference = super::resolve::bind(context, instruction, &indices, &mut references);
        let resolved = reference.and_then(|id| references[id].target.clone());
        let symbol = reference.and_then(|id| references[id].relocation.symbol.clone());
        let mut node = Node {
            instruction,
            reference,
            successors: Vec::new(),
            call: false,
            tail: false,
            target: resolved.clone(),
            symbol,
        };
        let mut fallthrough = true;
        match instruction.operation {
            Operation::Return { .. } => fallthrough = false,
            Operation::Call(target) => {
                node.call = true;
                if indices.is_empty() {
                    node.target = raw_target(context, target);
                }
            }
            Operation::IndirectCall(_) => node.call = true,
            Operation::IndirectJump(_) => {
                if reference.is_none() {
                    return Err(ReferenceError::Invalid("unresolved indirect jump"));
                }
                node.call = true;
                node.tail = true;
                fallthrough = false;
            }
            Operation::Jump(target) => {
                fallthrough = false;
                if !indices.is_empty() && reference.is_none() {
                    return Err(ReferenceError::Invalid("unresolved jump relocation"));
                }
                node.target = resolved.or_else(|| raw_target(context, target));
                if let Some(destination) = node.target.as_ref().and_then(|t| local(context, t)) {
                    node.successors.push(destination);
                    if let Some(id) = reference {
                        references[id].usage = Some(ReferenceUse::Branch);
                    }
                } else {
                    node.call = true;
                    node.tail = true;
                }
            }
            Operation::Branch { target, .. } => {
                if !indices.is_empty() {
                    return Err(ReferenceError::Invalid("conditional branch relocation"));
                }
                let destination = target
                    .checked_sub(context.image.address)
                    .filter(|&o| o < context.image.bytes.len() as u64)
                    .ok_or(ReferenceError::Invalid(
                        "conditional branch leaves function",
                    ))?;
                node.successors.push(destination);
            }
            _ => {}
        }
        if fallthrough {
            if next >= context.image.bytes.len() as u64 {
                return Err(ReferenceError::Invalid("fallthrough leaves function"));
            }
            node.successors.push(next);
        }
        pending.extend(&node.successors);
        nodes.insert(offset, node);
    }
    let ordered: Vec<_> = nodes.keys().copied().collect();
    let index: BTreeMap<_, _> = ordered
        .iter()
        .copied()
        .enumerate()
        .map(|(i, o)| (o, i))
        .collect();
    let nodes: Vec<_> = nodes.into_values().collect();
    let mut values = Values::default();
    let mut produced = vec![None; nodes.len()];
    for (i, node) in nodes.iter().enumerate() {
        if let Some(id) = node.reference
            && references[id].usage == Some(ReferenceUse::Address)
            && let Some(target) = &references[id].target
        {
            let bits = match node.instruction.operation {
                Operation::Mov {
                    destination: Operand::Register(reg),
                    ..
                } => reg.width.bits(),
                _ => 64,
            };
            let value = values.intern(context, target, bits, &mut budget)?;
            references[id].literal = values.values[value].literal;
            produced[i] = Some(value);
        }
    }
    let mut states = vec![None; nodes.len()];
    let mut queue = VecDeque::from([0]);
    let mut queued = vec![false; nodes.len()];
    queued[0] = true;
    states[0] = Some([None; 16]);
    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        spend(&mut budget, 16)?;
        let mut state = states[i].expect("reachable state");
        transfer(&mut state, &nodes[i], produced[i], &values);
        for successor in &nodes[i].successors {
            spend(&mut budget, 16)?;
            let s = index[successor];
            let changed = if let Some(previous) = &mut states[s] {
                let mut changed = false;
                for (old, new) in previous.iter_mut().zip(state) {
                    if *old != new && old.is_some() {
                        *old = None;
                        changed = true;
                    }
                }
                changed
            } else {
                states[s] = Some(state);
                true
            };
            if changed && !queued[s] {
                queue.push_back(s);
                queued[s] = true;
            }
        }
    }
    let mut calls = Vec::new();
    for (i, node) in nodes.iter().enumerate().filter(|(_, n)| n.call) {
        let state = states[i].expect("reachable call");
        let integer_argument_registers = [x86::RDI, x86::RSI, x86::RDX, x86::RCX, 8, 9]
            .into_iter()
            .map(|register| -> Result<_, ReferenceError> {
                let value = state[register].map(|id| &values.values[id]);
                if let Some(value) = value {
                    spend(&mut budget, target_work(&value.target))?;
                }
                Ok(ArgumentRegister {
                    register,
                    target: value.map(|v| v.target.clone()),
                    literal: value.and_then(|v| v.literal),
                })
            })
            .collect::<Result<_, _>>()?;
        let target = node
            .target
            .as_ref()
            .or_else(|| match node.instruction.operation {
                Operation::IndirectCall(Operand::Register(reg)) if reg.width == Width::U64 => {
                    state[usize::from(reg.index)].map(|id| &values.values[id].target)
                }
                _ => None,
            });
        if let Some(target) = target {
            spend(&mut budget, target_work(target))?;
        }
        spend(&mut budget, node.symbol.as_ref().map_or(0, String::len))?;
        calls.push(Call {
            instruction: ordered[i],
            tail: node.tail,
            target: target.cloned(),
            symbol: node.symbol.clone(),
            integer_argument_registers,
        });
    }
    Ok(ObjectReferences {
        function: context.image.name.clone(),
        section: context.section,
        section_offset: context.offset,
        function_size: context.image.bytes.len(),
        references,
        literals: values.literals,
        calls,
    })
}

fn transfer(state: &mut State, node: &Node, produced: Option<usize>, values: &Values) {
    let kill = |state: &mut State, operand: Operand| {
        if let Operand::Register(reg) = operand {
            state[usize::from(reg.index)] = None;
        }
    };
    match node.instruction.operation {
        Operation::Mov {
            destination: Operand::Register(reg),
            source,
        } => {
            let value = produced.or_else(|| {
                if let Operand::Register(src) = source {
                    let id = state[usize::from(src.index)]?;
                    (reg.shift == 0
                        && src.shift == 0
                        && (reg.width == Width::U64 && src.width == Width::U64
                            || reg.width == Width::U32
                                && src.width == Width::U32
                                && values.values[id].bits <= 32))
                        .then_some(id)
                } else {
                    None
                }
            });
            state[usize::from(reg.index)] = value;
        }
        Operation::Lea { destination, .. } => state[usize::from(destination.index)] = produced,
        Operation::Extend { destination, .. }
        | Operation::ByteSwap { destination }
        | Operation::Imul { destination, .. }
        | Operation::Pop(destination)
        | Operation::Cmov { destination, .. } => {
            state[usize::from(destination.index)] = None;
            if matches!(node.instruction.operation, Operation::Pop(_)) {
                state[x86::RSP] = None;
            }
        }
        Operation::Alu {
            kind: Alu::Cmp | Alu::Test,
            ..
        } => {}
        Operation::Alu { destination, .. }
        | Operation::Unary { destination, .. }
        | Operation::Shift { destination, .. }
        | Operation::Rotate { destination, .. }
        | Operation::Set { destination, .. }
        | Operation::Movbe { destination, .. } => kill(state, destination),
        Operation::Exchange { left, right } => {
            kill(state, left);
            state[usize::from(right.index)] = None;
        }
        Operation::Mul { .. } => {
            state[x86::RAX] = None;
            state[x86::RDX] = None;
        }
        Operation::Push(_) => state[x86::RSP] = None,
        Operation::Leave => {
            state[x86::RBP] = None;
            state[x86::RSP] = None;
        }
        Operation::Call(_) | Operation::IndirectCall(_) => {
            for reg in [
                x86::RAX,
                x86::RCX,
                x86::RDX,
                x86::RSI,
                x86::RDI,
                8,
                9,
                10,
                11,
            ] {
                state[reg] = None;
            }
        }
        _ => {}
    }
}
