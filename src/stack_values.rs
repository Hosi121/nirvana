//! Conservative reaching definitions for exact entry-stack-relative cells.
//!
//! This is a may-access analysis, not an execution trace or a recovery of source
//! variables. Nested loads and both lazy-select arms are reported. Stores and
//! loads remain in the IR: no memory operation, bounds check, or fault is removed.

use std::cmp::Ordering;
use std::collections::{BTreeMap, VecDeque};
use std::hash::{Hash, Hasher};

use crate::cfg::Target;
use crate::ir::{Control, Expr, Place, Program, Reg, Width};
use crate::stack::StackAnalysis;

const MAX_REGISTERS: usize = 65_536;
const MAX_POINTS: usize = 100_000;
const MAX_EXPRESSION_NODES: usize = 250_000;
const MAX_EXPRESSION_DEPTH: usize = 128;
const MAX_LOCATIONS: usize = 4_096;
const MAX_EVENTS: usize = 100_000;
const MAX_STATE_CELLS: usize = 500_000;
const MAX_SET_MEMBERS: usize = 1_000_000;
const MAX_WORK: usize = 8_000_000;

/// An exact byte range relative to the entry value of the stack register.
/// Offsets are modulo 2^64, using the public i64's bit pattern.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StackLocation {
    pub offset: i64,
    pub width: Width,
}

impl Ord for StackLocation {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.offset, self.width.bytes()).cmp(&(other.offset, other.width.bytes()))
    }
}

impl PartialOrd for StackLocation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for StackLocation {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.offset.hash(state);
        self.width.bytes().hash(state);
    }
}

/// A reachable, precisely addressed store. IDs are dense in instruction and
/// sequential-assignment order; repeated loop executions retain the same ID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StackDefinition {
    pub id: usize,
    pub instruction: u64,
    pub assignment: usize,
    pub location: StackLocation,
}

/// A potential exact-cell load, including loads in addresses and control.
/// The assignment count denotes the control expression. Several nested loads
/// can share the same instruction/assignment pair and location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StackRead {
    pub instruction: u64,
    pub assignment: usize,
    pub location: StackLocation,
    /// Sorted IDs of exact-cell stores that may be the last definition.
    pub definitions: Vec<usize>,
    /// Some path has no known exact-cell definition, including initial memory,
    /// an unknown-address store, or an overlapping different-cell store.
    pub has_unknown: bool,
}

/// Whole-pass results. Failure or exhaustion is reported as None by analyze;
/// partially converged definitions or read facts are never exposed.
#[derive(Clone, Debug)]
pub struct StackValues {
    definitions: Vec<StackDefinition>,
    reads: Vec<StackRead>,
}

impl StackValues {
    pub fn analyze(program: &Program, stack_register: Reg) -> Option<Self> {
        let mut work = Work(MAX_WORK);
        validate(program, stack_register, &mut work)?;
        let stack = StackAnalysis::try_analyze(program, stack_register)?;
        let cfg = program.cfg();
        let blocks = cfg.blocks().len();
        let entry = cfg.entry().index();

        let mut reachable = vec![false; blocks];
        reachable[entry] = true;
        let mut pending = VecDeque::from([cfg.entry()]);
        while let Some(id) = pending.pop_front() {
            work.spend(1)?;
            for edge in &cfg.block(id).successors {
                work.spend(1)?;
                let Target::Block(target) = edge.target else {
                    return None;
                };
                if !reachable[target.index()] {
                    reachable[target.index()] = true;
                    pending.push_back(target);
                }
            }
        }

        let mut collector = Collector {
            stack: &stack,
            work: &mut work,
            locations: BTreeMap::new(),
            definitions: Vec::new(),
            reads: Vec::new(),
            events: 0,
        };
        let mut plans: Vec<Vec<Event>> = (0..blocks).map(|_| Vec::new()).collect();
        for block in cfg.blocks() {
            if !reachable[block.id.index()] {
                continue;
            }
            let plan = &mut plans[block.id.index()];
            for instruction in &program.instructions()[block.instructions.clone()] {
                for (assignment, write) in instruction.assignments.iter().enumerate() {
                    let site = Site {
                        instruction: instruction.address,
                        assignment,
                    };
                    if let Place::Memory { address, .. } = &write.destination {
                        collector.expression(address, site, plan)?;
                    }
                    // A store's RHS, including all nested loads, sees the state
                    // before that store. The store event is appended last.
                    collector.expression(&write.value, site, plan)?;
                    if let Place::Memory { address, width } = &write.destination {
                        let exact = collector.location(address, *width, site)?;
                        let definition = if let Some(location) = exact {
                            let cell = collector.intern(location)?;
                            let id = collector.definitions.len();
                            if id >= MAX_EVENTS {
                                return None;
                            }
                            collector.definitions.push(StackDefinition {
                                id,
                                instruction: site.instruction,
                                assignment: site.assignment,
                                location,
                            });
                            Some((cell, id))
                        } else {
                            None
                        };
                        collector.event(plan, Event::Store(definition))?;
                    }
                }
                let site = Site {
                    instruction: instruction.address,
                    assignment: instruction.assignments.len(),
                };
                match &instruction.control {
                    Control::Branch { condition, .. } => {
                        collector.expression(condition, site, plan)?;
                    }
                    Control::Return(value) => collector.expression(value, site, plan)?,
                    Control::Next | Control::Jump(_) => {}
                }
            }
        }
        let Collector {
            locations,
            definitions,
            mut reads,
            ..
        } = collector;
        let mut cells = vec![
            StackLocation {
                offset: 0,
                width: Width::U8,
            };
            locations.len()
        ];
        for (location, index) in locations {
            cells[index] = location;
        }
        // All incoming states, the current transfer state, and a spare state
        // fit before any dense cell states are allocated.
        if blocks.checked_add(2)?.checked_mul(cells.len())? > MAX_STATE_CELLS {
            return None;
        }
        work.spend(cells.len().checked_add(blocks)?)?;
        let mut incoming: Vec<Option<State>> = (0..blocks).map(|_| None).collect();
        incoming[entry] = Some(State::unknown(cells.len()));
        pending.push_back(cfg.entry());
        let mut queued = vec![false; blocks];
        queued[entry] = true;
        let mut retained_members = 0usize;

        while let Some(id) = pending.pop_front() {
            work.spend(1)?;
            queued[id.index()] = false;
            let mut state = incoming[id.index()]
                .as_ref()?
                .copy(retained_members, &mut work)?;
            for &event in &plans[id.index()] {
                work.spend(1)?;
                if let Event::Store(definition) = event {
                    state.store(definition, &cells, retained_members, &mut work)?;
                }
            }
            for edge in &cfg.block(id).successors {
                work.spend(1)?;
                let Target::Block(target) = edge.target else {
                    return None;
                };
                let changed = if let Some(previous) = &mut incoming[target.index()] {
                    previous.join(&state, &mut retained_members, &mut work)?
                } else {
                    let next =
                        state.copy(retained_members.checked_add(state.members)?, &mut work)?;
                    retained_members = retained_members.checked_add(next.members)?;
                    incoming[target.index()] = Some(next);
                    true
                };
                if changed && !queued[target.index()] {
                    queued[target.index()] = true;
                    pending.push_back(target);
                }
            }
        }

        // Read facts are collected only after the fixed point. In particular,
        // an early visit of a join cannot leak a too-small definition set.
        for block in cfg.blocks() {
            let Some(start) = &incoming[block.id.index()] else {
                continue;
            };
            let mut state = start.copy(retained_members, &mut work)?;
            for &event in &plans[block.id.index()] {
                work.spend(1)?;
                match event {
                    Event::Store(definition) => {
                        state.store(definition, &cells, retained_members, &mut work)?;
                    }
                    Event::Read { read, cell } => {
                        let fact = &state.cells[cell];
                        member_limit(
                            retained_members
                                .checked_add(state.members)?
                                .checked_add(fact.definitions.len())?,
                        )?;
                        work.spend(fact.definitions.len())?;
                        reads[read].definitions = fact.definitions.clone();
                        reads[read].has_unknown = fact.unknown;
                        retained_members = retained_members.checked_add(fact.definitions.len())?;
                    }
                }
            }
        }
        Some(Self { definitions, reads })
    }

    pub fn definitions(&self) -> &[StackDefinition] {
        &self.definitions
    }

    pub fn reads(&self) -> &[StackRead] {
        &self.reads
    }
}

struct Work(usize);

impl Work {
    fn spend(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}

fn member_limit(count: usize) -> Option<()> {
    (count <= MAX_SET_MEMBERS).then_some(())
}

// Validate the whole input before invoking StackAnalysis or walking any
// expression recursively. This scan neither clones nor compares expressions.
fn validate(program: &Program, stack_register: Reg, work: &mut Work) -> Option<()> {
    let registers = program.register_count();
    if registers > MAX_REGISTERS || stack_register.0 >= registers {
        return None;
    }
    let instructions = program.instructions();
    if instructions.len() > MAX_POINTS || program.cfg().blocks().len() > MAX_POINTS {
        return None;
    }
    let mut points = 0usize;
    let mut nodes = 0usize;
    for instruction in instructions {
        work.spend(1)?;
        points = points
            .checked_add(instruction.assignments.len())?
            .checked_add(1)?;
        if points > MAX_POINTS {
            return None;
        }
        for assignment in &instruction.assignments {
            if let Place::Memory { address, .. } = &assignment.destination {
                validate_expression(address, registers, &mut nodes, work)?;
            }
            validate_expression(&assignment.value, registers, &mut nodes, work)?;
        }
        match &instruction.control {
            Control::Branch { condition, .. } => {
                validate_expression(condition, registers, &mut nodes, work)?;
            }
            Control::Return(value) => {
                validate_expression(value, registers, &mut nodes, work)?;
            }
            Control::Next | Control::Jump(_) => {}
        }
    }
    Some(())
}

fn validate_expression(
    root: &Expr,
    registers: usize,
    nodes: &mut usize,
    work: &mut Work,
) -> Option<()> {
    let mut pending = vec![(root, 0usize)];
    while let Some((expression, depth)) = pending.pop() {
        work.spend(1)?;
        *nodes = nodes.checked_add(1)?;
        if depth > MAX_EXPRESSION_DEPTH || *nodes > MAX_EXPRESSION_NODES {
            return None;
        }
        match expression {
            Expr::Const(_) => {}
            Expr::Register(reg) => {
                if reg.0 >= registers {
                    return None;
                }
            }
            Expr::Binary(_, left, right) => {
                pending.push((right, depth + 1));
                pending.push((left, depth + 1));
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push((not_taken, depth + 1));
                pending.push((taken, depth + 1));
                pending.push((condition, depth + 1));
            }
        }
    }
    Some(())
}

#[derive(Clone, Copy)]
struct Site {
    instruction: u64,
    assignment: usize,
}

#[derive(Clone, Copy)]
enum Event {
    Read { read: usize, cell: usize },
    Store(Option<(usize, usize)>),
}

struct Collector<'a> {
    stack: &'a StackAnalysis,
    work: &'a mut Work,
    locations: BTreeMap<StackLocation, usize>,
    definitions: Vec<StackDefinition>,
    reads: Vec<StackRead>,
    events: usize,
}

impl Collector<'_> {
    fn intern(&mut self, location: StackLocation) -> Option<usize> {
        self.work
            .spend(self.locations.len().checked_ilog2().unwrap_or(0) as usize + 2)?;
        if let Some(&index) = self.locations.get(&location) {
            return Some(index);
        }
        let index = self.locations.len();
        if index >= MAX_LOCATIONS {
            return None;
        }
        self.locations.insert(location, index);
        Some(index)
    }

    fn event(&mut self, plan: &mut Vec<Event>, event: Event) -> Option<()> {
        self.work.spend(1)?;
        self.events = self.events.checked_add(1)?;
        if self.events > MAX_EVENTS {
            return None;
        }
        plan.push(event);
        Some(())
    }

    fn location(
        &mut self,
        address: &Expr,
        width: Width,
        site: Site,
    ) -> Option<Option<StackLocation>> {
        // Charge query traversal too: independently bounded StackAnalysis
        // queries must not multiply this pass's total work without a limit.
        let mut pending = vec![address];
        let mut nodes = 0usize;
        while let Some(expression) = pending.pop() {
            self.work.spend(1)?;
            nodes = nodes.checked_add(1)?;
            match expression {
                Expr::Load { .. } => return Some(None),
                Expr::Binary(_, left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push(not_taken);
                    pending.push(taken);
                    pending.push(condition);
                }
                Expr::Const(_) | Expr::Register(_) => {}
            }
        }
        self.work.spend(nodes)?;
        Some(
            self.stack
                .offset_before(site.instruction, site.assignment, address)
                .map(|offset| StackLocation { offset, width }),
        )
    }

    fn expression(&mut self, root: &Expr, site: Site, plan: &mut Vec<Event>) -> Option<()> {
        enum Visit<'a> {
            Expression(&'a Expr),
            Load(&'a Expr, Width),
        }
        let mut pending = vec![Visit::Expression(root)];
        while let Some(visit) = pending.pop() {
            self.work.spend(1)?;
            match visit {
                Visit::Load(address, width) => {
                    if let Some(location) = self.location(address, width, site)? {
                        let cell = self.intern(location)?;
                        let read = self.reads.len();
                        if read >= MAX_EVENTS {
                            return None;
                        }
                        self.reads.push(StackRead {
                            instruction: site.instruction,
                            assignment: site.assignment,
                            location,
                            definitions: Vec::new(),
                            has_unknown: true,
                        });
                        self.event(plan, Event::Read { read, cell })?;
                    }
                }
                Visit::Expression(expression) => match expression {
                    Expr::Load { address, width } => {
                        pending.push(Visit::Load(address, *width));
                        pending.push(Visit::Expression(address));
                    }
                    Expr::Binary(_, left, right) => {
                        pending.push(Visit::Expression(right));
                        pending.push(Visit::Expression(left));
                    }
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        pending.push(Visit::Expression(not_taken));
                        pending.push(Visit::Expression(taken));
                        pending.push(Visit::Expression(condition));
                    }
                    Expr::Const(_) | Expr::Register(_) => {}
                },
            }
        }
        Some(())
    }
}

#[derive(Clone)]
struct Fact {
    definitions: Vec<usize>,
    unknown: bool,
}

struct State {
    cells: Vec<Fact>,
    members: usize,
}

impl State {
    fn unknown(count: usize) -> Self {
        Self {
            cells: vec![
                Fact {
                    definitions: Vec::new(),
                    unknown: true,
                };
                count
            ],
            members: 0,
        }
    }

    fn copy(&self, retained: usize, work: &mut Work) -> Option<Self> {
        member_limit(retained.checked_add(self.members)?)?;
        work.spend(self.cells.len().checked_add(self.members)?)?;
        Some(Self {
            cells: self.cells.clone(),
            members: self.members,
        })
    }

    fn store(
        &mut self,
        definition: Option<(usize, usize)>,
        locations: &[StackLocation],
        retained: usize,
        work: &mut Work,
    ) -> Option<()> {
        for (index, fact) in self.cells.iter_mut().enumerate() {
            work.spend(1)?;
            let invalidated = match definition {
                Some((cell, _)) => overlaps(locations[index], locations[cell]),
                None => true,
            };
            if invalidated {
                work.spend(fact.definitions.len())?;
                self.members -= fact.definitions.len();
                fact.definitions.clear();
                fact.unknown = true;
            }
        }
        if let Some((cell, id)) = definition {
            member_limit(retained.checked_add(self.members)?.checked_add(1)?)?;
            work.spend(1)?;
            self.cells[cell].definitions.push(id);
            self.cells[cell].unknown = false;
            self.members += 1;
        }
        Some(())
    }

    fn join(&mut self, source: &Self, retained: &mut usize, work: &mut Work) -> Option<bool> {
        let mut changed = false;
        for (previous, incoming) in self.cells.iter_mut().zip(&source.cells) {
            work.spend(1)?;
            if incoming.unknown && !previous.unknown {
                previous.unknown = true;
                changed = true;
            }
            for &id in &incoming.definitions {
                work.spend(previous.definitions.len().checked_add(1)?)?;
                if let Err(index) = previous.definitions.binary_search(&id) {
                    member_limit(retained.checked_add(source.members)?.checked_add(1)?)?;
                    previous.definitions.insert(index, id);
                    *retained += 1;
                    self.members += 1;
                    changed = true;
                }
            }
        }
        Some(changed)
    }
}

fn overlaps(left: StackLocation, right: StackLocation) -> bool {
    // Widths are at most eight bytes. For circular ranges this short, overlap
    // holds exactly when one start lies in the other range. No signed addition
    // or endpoint ordering is used, including across the i64 and u64 boundaries.
    let left_start = left.offset as u64;
    let right_start = right.offset as u64;
    left_start.wrapping_sub(right_start) < right.width.bytes() as u64
        || right_start.wrapping_sub(left_start) < left.width.bytes() as u64
}
