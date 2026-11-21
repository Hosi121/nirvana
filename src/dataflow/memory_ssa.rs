//! Source-bound memory generations and conservative reaching-write candidates.
//!
//! Uses describe successful, syntactically possible reads. Definitions order
//! stores and explicit opaque effects; phis retain every reachable CFG edge,
//! including virtual entry and loop backedges. This metadata leaves checked
//! memory operations, faults and arbitrary-PC execution at their source sites.

use std::collections::{BTreeMap, BTreeSet};

use crate::control_flow::cfg::Target;
use crate::dataflow::address_identity::MemoryAccess;
use crate::dataflow::ssa::{Site, SsaFunction};
use crate::model::ir::{AccessKind, Program};

mod report;
mod translate;
mod walk;

const MAX_EFFECTS: usize = 32768;
const MAX_MEMBERS: usize = 1_000_000;
const MAX_WORK: usize = 8_000_000;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MemoryId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Phase {
    Before,
    After,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EffectKind {
    CallStack,
    Call,
    StringStore,
    StringMove,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Effect {
    pub instruction: u64,
    pub phase: Phase,
    pub kind: EffectKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PhiInput {
    pub predecessor: Option<u64>,
    pub memory: MemoryId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Definition {
    Initial,
    Phi { block: u64, inputs: Vec<PhiInput> },
    Store { access: usize, previous: MemoryId },
    Opaque { effect: Effect, previous: MemoryId },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Access {
    pub source: MemoryAccess,
    pub incoming: MemoryId,
    pub definition: Option<MemoryId>,
    /// Exact modular identity before edge translation, when representable.
    pub address: Option<crate::dataflow::address_identity::ModularAddress>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Event {
    Access(usize),
    Effect(MemoryId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub start: u64,
    pub entry: MemoryId,
    pub exit: MemoryId,
    pub events: Vec<Event>,
}

/// Relations concern byte intervals after successful address evaluation.
/// Exact requires identical intervals. Different symbolic bases remain May.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Alias {
    Disjoint,
    Exact,
    Overlap,
    May,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Clobber {
    pub definition: MemoryId,
    pub alias: Alias,
    /// Bit i denotes a possible contribution to byte i of the queried Load.
    pub byte_mask: u8,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Query {
    pub access: usize,
    /// Possible reaching writers, preserving older contributions only for
    /// bytes that a later definite Store leaves untouched. May-alias stores
    /// and opaque effects retain older contributions to every pending byte.
    pub candidates: Vec<Clobber>,
    pub translated_edges: usize,
    /// An unavailable address or growing loop expression was widened to May.
    pub address_widened: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Analysis {
    definitions: Vec<Definition>,
    blocks: Vec<Block>,
    accesses: Vec<Access>,
    queries: Result<Vec<Query>, String>,
}

impl Analysis {
    pub fn definitions(&self) -> &[Definition] {
        &self.definitions
    }
    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }
    pub fn accesses(&self) -> &[Access] {
        &self.accesses
    }
    pub fn queries(&self) -> &Result<Vec<Query>, String> {
        &self.queries
    }
    pub fn to_json(&self) -> Result<String, String> {
        report::render(self)
    }

    pub(crate) fn members(&self) -> usize {
        self.definitions.len()
            + self.blocks.len()
            + self.accesses.len()
            + self
                .definitions
                .iter()
                .map(|d| match d {
                    Definition::Phi { inputs, .. } => inputs.len(),
                    _ => 0,
                })
                .sum::<usize>()
            + self.blocks.iter().map(|b| b.events.len()).sum::<usize>()
            + self
                .accesses
                .iter()
                .map(|a| a.source.path.len() + a.address.as_ref().map_or(0, |a| a.terms.len()))
                .sum::<usize>()
            + self.queries.as_ref().map_or(0, |q| {
                q.len() + q.iter().map(|q| q.candidates.len()).sum::<usize>()
            })
    }
}

pub fn analyze(source: &Program, graph: &SsaFunction) -> Result<Analysis, String> {
    analyze_with_effects(source, graph, &[], &BTreeSet::new())
}

/// Module adapters supply effects hidden by the register-event projection.
/// Opaque register definitions are excluded from address arithmetic facts.
pub(crate) fn analyze_with_effects(
    source: &Program,
    graph: &SsaFunction,
    effects: &[Effect],
    opaque: &BTreeSet<Site>,
) -> Result<Analysis, String> {
    crate::dataflow::ssa::validate(source, graph).map_err(|e| e.to_string())?;
    if effects.len() > MAX_EFFECTS || opaque.len() > crate::dataflow::ssa::MAX_ASSIGNMENTS {
        return Err("memory SSA effect limit".into());
    }
    let mut by_effect = BTreeMap::new();
    for effect in effects {
        if source
            .instructions()
            .binary_search_by_key(&effect.instruction, |i| i.address)
            .is_err()
            || by_effect
                .insert((effect.instruction, effect.phase), *effect)
                .is_some()
        {
            return Err("memory SSA effect source mismatch".into());
        }
    }
    for site in opaque {
        let i = source
            .instructions()
            .binary_search_by_key(&site.instruction, |i| i.address)
            .map_err(|_| "memory SSA opaque source mismatch")?;
        if !site.assignment.is_some_and(|n| {
            source.instructions()[i]
                .assignments
                .get(n)
                .is_some_and(|a| matches!(a.destination, crate::model::ir::Place::Register(_)))
        }) {
            return Err("memory SSA opaque definition mismatch".into());
        }
    }
    let addresses =
        crate::dataflow::address_identity::ordered_memory_addresses(source, graph, opaque)
            .ok_or("memory SSA address/control resource limit")?;
    let accesses = addresses.accesses;
    let mut by_instruction: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
    for (index, access) in accesses.iter().enumerate() {
        by_instruction
            .entry(access.site.instruction)
            .or_default()
            .push(index);
    }
    let cfg = source.cfg();
    let reachable = cfg.reachable_blocks();
    let mut result = Analysis {
        definitions: vec![Definition::Initial],
        blocks: Vec::new(),
        accesses: Vec::with_capacity(accesses.len()),
        queries: Ok(Vec::new()),
    };
    let mut entries = BTreeMap::new();
    for id in &reachable {
        let start = cfg.block(*id).start;
        let entry = MemoryId(result.definitions.len());
        result.definitions.push(Definition::Phi {
            block: start,
            inputs: Vec::new(),
        });
        entries.insert(start, entry);
    }
    let mut exits = BTreeMap::new();
    for id in &reachable {
        let block = cfg.block(*id);
        let entry = entries[&block.start];
        let mut current = entry;
        let mut events = Vec::new();
        for i in &source.instructions()[block.instructions.clone()] {
            append_effect(
                &mut result,
                &mut current,
                &mut events,
                by_effect.get(&(i.address, Phase::Before)),
            );
            for &original in by_instruction.get(&i.address).into_iter().flatten() {
                let access = accesses[original].clone();
                let index = result.accesses.len();
                let definition = if access.kind == AccessKind::Write {
                    let id = MemoryId(result.definitions.len());
                    result.definitions.push(Definition::Store {
                        access: index,
                        previous: current,
                    });
                    Some(id)
                } else {
                    None
                };
                result.accesses.push(Access {
                    source: access,
                    incoming: current,
                    definition,
                    address: addresses.forms[original].clone(),
                });
                events.push(Event::Access(index));
                if let Some(id) = definition {
                    current = id;
                }
            }
            append_effect(
                &mut result,
                &mut current,
                &mut events,
                by_effect.get(&(i.address, Phase::After)),
            );
        }
        exits.insert(block.start, current);
        result.blocks.push(Block {
            start: block.start,
            entry,
            exit: current,
            events,
        });
    }
    for id in &reachable {
        let block = cfg.block(*id);
        let mut inputs = Vec::new();
        if *id == cfg.entry() {
            inputs.push(PhiInput {
                predecessor: None,
                memory: MemoryId(0),
            });
        }
        for pred in &block.predecessors {
            if reachable.contains(pred) {
                let start = cfg.block(*pred).start;
                inputs.push(PhiInput {
                    predecessor: Some(start),
                    memory: exits[&start],
                });
            }
        }
        if block
            .successors
            .iter()
            .any(|e| !matches!(e.target, Target::Block(_)))
        {
            return Err("memory SSA unresolved edge".into());
        }
        result.definitions[entries[&block.start].0] = Definition::Phi {
            block: block.start,
            inputs,
        };
    }
    if result.members() > MAX_MEMBERS {
        return Err("memory SSA storage limit".into());
    }
    result.queries = match addresses.phi_values {
        Ok(values) => walk::queries(&result, graph, &values),
        Err(reason) => Err(reason),
    };
    if result.members() > MAX_MEMBERS {
        return Err("memory SSA query storage limit".into());
    }
    Ok(result)
}

fn append_effect(
    result: &mut Analysis,
    current: &mut MemoryId,
    events: &mut Vec<Event>,
    effect: Option<&Effect>,
) {
    if let Some(&effect) = effect {
        let id = MemoryId(result.definitions.len());
        result.definitions.push(Definition::Opaque {
            effect,
            previous: *current,
        });
        events.push(Event::Effect(id));
        *current = id;
    }
}
