//! Basic-block recovery from a supplied set of decoded instruction locations.
//!
//! This module does not discover instructions or function boundaries. Missing
//! destinations remain explicit, so incomplete input cannot silently become a
//! complete CFG. The supplied set may contain unreachable instructions.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write};
use std::ops::Range;

pub type Address = u64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Flow {
    /// Continue at address + size. Includes calls known to return normally.
    Next,
    Jump(Address),
    /// Taken destination; the other destination is address + size.
    Branch(Address),
    Return,
    /// Destination has not yet been recovered.
    IndirectJump,
    /// A known stop, such as a trap or a call known not to return.
    Stop,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Instruction {
    pub address: Address,
    pub size: u32,
    pub flow: Flow,
}

impl Instruction {
    pub const fn new(address: Address, size: u32, flow: Flow) -> Self {
        Self {
            address,
            size,
            flow,
        }
    }

    fn end(self) -> Result<Address, BuildError> {
        if self.size == 0 {
            return Err(BuildError::ZeroSize(self.address));
        }
        self.address
            .checked_add(u64::from(self.size))
            .ok_or(BuildError::AddressOverflow(self.address))
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(usize);

impl BlockId {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EdgeKind {
    Fallthrough,
    Jump,
    Taken,
    NotTaken,
    Indirect,
}

impl fmt::Display for EdgeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Fallthrough => "next",
            Self::Jump => "jump",
            Self::Taken => "taken",
            Self::NotTaken => "not taken",
            Self::Indirect => "indirect",
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Target {
    Block(BlockId),
    /// Not present in the supplied instructions. Not necessarily another function.
    Outside(Address),
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Edge {
    pub kind: EdgeKind,
    pub target: Target,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BasicBlock {
    pub id: BlockId,
    pub start: Address,
    /// Exclusive end address.
    pub end: Address,
    /// Indices into Cfg::instructions(), in address order.
    pub instructions: Range<usize>,
    /// Edges retain their kinds even when both arms have the same destination.
    pub successors: Vec<Edge>,
    /// Unique internal predecessor blocks, in block order.
    pub predecessors: Vec<BlockId>,
}

#[derive(Clone, Debug)]
pub struct Cfg {
    entry: BlockId,
    instructions: Vec<Instruction>,
    blocks: Vec<BasicBlock>,
    by_start: BTreeMap<Address, BlockId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    EmptyInput,
    ZeroSize(Address),
    AddressOverflow(Address),
    DuplicateAddress(Address),
    OverlappingInstructions {
        first: Address,
        second: Address,
    },
    MissingEntry(Address),
    TargetInsideInstruction {
        source: Address,
        target: Address,
        instruction: Address,
    },
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => f.write_str("no instructions supplied"),
            Self::ZeroSize(a) => write!(f, "instruction at {a:#x} has zero size"),
            Self::AddressOverflow(a) => {
                write!(f, "instruction at {a:#x} overflows the address space")
            }
            Self::DuplicateAddress(a) => write!(f, "duplicate instruction address {a:#x}"),
            Self::OverlappingInstructions { first, second } => {
                write!(f, "instructions at {first:#x} and {second:#x} overlap")
            }
            Self::MissingEntry(a) => write!(f, "entry {a:#x} is not an instruction start"),
            Self::TargetInsideInstruction {
                source,
                target,
                instruction,
            } => write!(
                f,
                "branch at {source:#x} targets {target:#x}, inside instruction at {instruction:#x}"
            ),
        }
    }
}

impl std::error::Error for BuildError {}

impl Cfg {
    /// Recover blocks without guessing any missing destinations.
    ///
    /// Instructions may arrive in any order. Overlapping instruction streams
    /// are rejected; this first version models one decoding per address range.
    pub fn build(entry: Address, mut instructions: Vec<Instruction>) -> Result<Self, BuildError> {
        if instructions.is_empty() {
            return Err(BuildError::EmptyInput);
        }
        instructions.sort_by_key(|instruction| instruction.address);
        for (i, instruction) in instructions.iter().enumerate() {
            instruction.end()?;
            if i > 0 {
                let previous = instructions[i - 1];
                if previous.address == instruction.address {
                    return Err(BuildError::DuplicateAddress(instruction.address));
                }
                if previous.end()? > instruction.address {
                    return Err(BuildError::OverlappingInstructions {
                        first: previous.address,
                        second: instruction.address,
                    });
                }
            }
        }

        let indices: BTreeMap<_, _> = instructions
            .iter()
            .enumerate()
            .map(|(i, instruction)| (instruction.address, i))
            .collect();
        let entry_index = *indices.get(&entry).ok_or(BuildError::MissingEntry(entry))?;
        let mut leaders = BTreeSet::from([0, entry_index]);

        for (i, instruction) in instructions.iter().enumerate() {
            if let Flow::Jump(target) | Flow::Branch(target) = instruction.flow {
                if let Some(&target_index) = indices.get(&target) {
                    leaders.insert(target_index);
                } else if let Some((&start, &index)) = indices.range(..target).next_back()
                    && target < instructions[index].end()?
                {
                    return Err(BuildError::TargetInsideInstruction {
                        source: instruction.address,
                        target,
                        instruction: start,
                    });
                }
            }
            if let Some(next) = instructions.get(i + 1)
                && (instruction.flow != Flow::Next || instruction.end()? != next.address)
            {
                leaders.insert(i + 1);
            }
        }

        let starts: Vec<_> = leaders.into_iter().collect();
        let mut blocks = Vec::with_capacity(starts.len());
        let mut by_start = BTreeMap::new();
        for (i, &start) in starts.iter().enumerate() {
            let end = starts.get(i + 1).copied().unwrap_or(instructions.len());
            let id = BlockId(i);
            by_start.insert(instructions[start].address, id);
            blocks.push(BasicBlock {
                id,
                start: instructions[start].address,
                end: instructions[end - 1].end()?,
                instructions: start..end,
                successors: Vec::new(),
                predecessors: Vec::new(),
            });
        }

        let resolve = |address| {
            by_start
                .get(&address)
                .copied()
                .map(Target::Block)
                .unwrap_or(Target::Outside(address))
        };
        for block in &mut blocks {
            let last = instructions[block.instructions.end - 1];
            let mut add = |kind, target| block.successors.push(Edge { kind, target });
            match last.flow {
                Flow::Next => add(EdgeKind::Fallthrough, resolve(last.end()?)),
                Flow::Jump(target) => add(EdgeKind::Jump, resolve(target)),
                Flow::Branch(target) => {
                    add(EdgeKind::Taken, resolve(target));
                    add(EdgeKind::NotTaken, resolve(last.end()?));
                }
                Flow::IndirectJump => add(EdgeKind::Indirect, Target::Unknown),
                Flow::Return | Flow::Stop => {}
            }
        }
        for source in 0..blocks.len() {
            let targets: BTreeSet<_> = blocks[source]
                .successors
                .iter()
                .filter_map(|edge| match edge.target {
                    Target::Block(id) => Some(id),
                    _ => None,
                })
                .collect();
            for target in targets {
                blocks[target.0].predecessors.push(BlockId(source));
            }
        }

        Ok(Self {
            entry: by_start[&entry],
            instructions,
            blocks,
            by_start,
        })
    }

    pub fn entry(&self) -> BlockId {
        self.entry
    }

    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }

    pub fn blocks(&self) -> &[BasicBlock] {
        &self.blocks
    }

    pub fn block(&self, id: BlockId) -> &BasicBlock {
        &self.blocks[id.0]
    }

    /// Look up an exact block start, not an address inside a block.
    pub fn block_at(&self, address: Address) -> Option<BlockId> {
        self.by_start.get(&address).copied()
    }

    /// Reachability through known internal edges only. Unresolved edges can
    /// hide additional reachable code; this is not a completeness claim.
    pub fn reachable_blocks(&self) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![self.entry];
        while let Some(id) = pending.pop() {
            if reachable.insert(id) {
                pending.extend(self.block(id).successors.iter().filter_map(|edge| {
                    if let Target::Block(target) = edge.target {
                        Some(target)
                    } else {
                        None
                    }
                }));
            }
        }
        reachable
    }

    /// Graphviz DOT, including missing destinations and unreachable blocks.
    pub fn to_dot(&self) -> String {
        let reachable = self.reachable_blocks();
        let mut dot = String::from("digraph cfg {\n  node [shape=box];\n");
        writeln!(dot, "  entry [shape=point];\n  entry -> {};", self.entry).unwrap();
        for block in &self.blocks {
            let terminal = match self.instructions[block.instructions.end - 1].flow {
                Flow::Return => "\\nreturn",
                Flow::Stop => "\\nstop",
                _ => "",
            };
            let style = if reachable.contains(&block.id) {
                ""
            } else {
                ", style=dashed"
            };
            writeln!(
                dot,
                "  {} [label=\"{}\\n{:#x}..{:#x}{}\"{}];",
                block.id, block.id, block.start, block.end, terminal, style
            )
            .unwrap();
            for (i, edge) in block.successors.iter().enumerate() {
                let target = match edge.target {
                    Target::Block(target) => target.to_string(),
                    Target::Outside(address) => {
                        let name = format!("missing_{}_{}", block.id, i);
                        writeln!(
                            dot,
                            "  {name} [label=\"outside {address:#x}\", shape=ellipse];"
                        )
                        .unwrap();
                        name
                    }
                    Target::Unknown => {
                        let name = format!("unknown_{}_{}", block.id, i);
                        writeln!(dot, "  {name} [label=\"unknown\", shape=ellipse];").unwrap();
                        name
                    }
                };
                writeln!(dot, "  {} -> {target} [label=\"{}\"];", block.id, edge.kind).unwrap();
            }
        }
        dot.push_str("}\n");
        dot
    }
}
