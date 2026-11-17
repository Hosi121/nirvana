//! Bounded, naming-only role candidates across exact stack spill/reload webs.
//!
//! The projected tree is analysis input only. It never replaces the executable
//! IR or AST, removes a load, or establishes equality of source variables.
//! Unknown reads, ambiguous register lifetimes and overlapping cells suppress
//! names. Control loads without a Step's exact program point remain opaque.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{Assignment, Control, Expr, Place, Program, Reg};
use crate::stack::StackAnalysis;
use crate::stack_values::{StackLocation, StackValues};
use crate::structure::Node;
use crate::value_role::{self, ValueRole};

const MAX_DEPTH: usize = 64;
const MAX_NODES: usize = 24_000;
const MAX_REGISTERS: usize = 65_536;
const MAX_DEFINITIONS: usize = 2048;
const MAX_READS: usize = 8192;
const MAX_WORK: usize = 500_000;

type Site = (u64, usize);
type ReadKey = (u64, usize, i64, usize);

#[derive(Clone, Debug, Default)]
pub struct StackRoles {
    registers: BTreeMap<usize, ValueRole>,
    offsets: BTreeMap<i64, ValueRole>,
    webs: BTreeMap<usize, usize>,
    locations: BTreeMap<usize, StackLocation>,
}

impl StackRoles {
    pub fn register_role(&self, register: Reg) -> Option<ValueRole> {
        self.registers.get(&register.0).copied()
    }

    pub fn offset_role(&self, offset: i64) -> Option<ValueRole> {
        self.offsets.get(&offset).copied()
    }

    /// A candidate spill/reload lineage, even when its role is unknown. IDs
    /// are local to this analysis. Members need not hold equal values at once;
    /// consumers may use them as allocation preferences, never as permission
    /// to share storage or eliminate a memory operation.
    pub fn register_web(&self, register: Reg) -> Option<usize> {
        self.webs.get(&register.0).copied()
    }

    pub fn web_location(&self, web: usize) -> Option<StackLocation> {
        self.locations.get(&web).copied()
    }

    /// Own/upstream exhaustion returns None. The bounded role inference may
    /// also yield no names; a missing role provides no positive evidence.
    pub fn analyze(program: &Program, stack_register: Reg, nodes: &[Node]) -> Option<Self> {
        let count = program.register_count();
        if count > MAX_REGISTERS || stack_register.0 >= count {
            return None;
        }
        let mut budget = Budget(MAX_NODES);
        for instruction in program.instructions() {
            budget.take(1)?;
            for assignment in &instruction.assignments {
                validate_assignment(assignment, count, 0, &mut budget)?;
            }
            match &instruction.control {
                Control::Branch { condition, .. } | Control::Return(condition) => {
                    validate_expr(condition, count, 0, &mut budget)?;
                }
                _ => {}
            }
        }
        validate_nodes(nodes, count, 0, &mut budget)?;
        let stack = StackAnalysis::try_analyze(program, stack_register)?;
        let values = StackValues::analyze(program, stack_register)?;
        let definitions = values.definitions();
        if definitions.len() > MAX_DEFINITIONS || values.reads().len() > MAX_READS {
            return None;
        }
        let mut budget = Budget(MAX_WORK);
        let mut dsu = Dsu((0..definitions.len()).collect());
        for read in values.reads() {
            budget.take(read.definitions.len() + 1)?;
            if read.has_unknown || read.definitions.is_empty() {
                continue;
            }
            let first = *read.definitions.first()?;
            for &id in &read.definitions {
                if definitions.get(id)?.location != read.location {
                    return None;
                }
                dsu.union(first, id);
            }
        }
        let roots: Vec<_> = (0..definitions.len()).map(|id| dsu.root(id)).collect();
        let mut loads = BTreeMap::new();
        for read in values.reads() {
            if !read.has_unknown && !read.definitions.is_empty() {
                let root = roots[*read.definitions.first()?];
                let key = read_key((read.instruction, read.assignment), read.location);
                if let Some(old) = loads.insert(key, root)
                    && old != root
                {
                    return None;
                }
            }
        }
        let stores: BTreeMap<_, _> = definitions
            .iter()
            .map(|definition| {
                (
                    (definition.instruction, definition.assignment),
                    (definition.location, roots[definition.id]),
                )
            })
            .collect();
        let mut projection = Projection {
            instructions: program
                .instructions()
                .iter()
                .map(|i| (i.address, i))
                .collect(),
            stack: &stack,
            loads,
            stores,
            registers: BTreeMap::new(),
            first: count,
        };
        count.checked_add(definitions.len())?;

        // A virtual register reused by several static definitions is not a
        // variable identity. Web-split input improves coverage without making
        // that assumption here. Copy edges propagate only naming candidates.
        let reachable: BTreeSet<_> = program
            .cfg()
            .reachable_blocks()
            .iter()
            .flat_map(|id| program.cfg().block(*id).instructions.clone())
            .collect();
        let mut writes = vec![0usize; count];
        let mut sources = vec![None; count];
        for &index in &reachable {
            let instruction = &program.instructions()[index];
            for (ordinal, assignment) in instruction.assignments.iter().enumerate() {
                budget.take(1)?;
                if let Place::Register(reg) = assignment.destination {
                    writes[reg.0] += 1;
                    sources[reg.0] = Some(((instruction.address, ordinal), &assignment.value));
                }
            }
        }
        let mut evidence: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); count];
        let mut copies = Vec::new();
        for &index in &reachable {
            let instruction = &program.instructions()[index];
            for (ordinal, assignment) in instruction.assignments.iter().enumerate() {
                budget.take(1)?;
                let site = (instruction.address, ordinal);
                if let Place::Register(reg) = assignment.destination
                    && writes[reg.0] == 1
                {
                    if let Some(root) = projection.loaded(&assignment.value, site) {
                        evidence[reg.0].insert(root);
                    }
                    if let Expr::Register(source) = assignment.value
                        && writes[source.0] <= 1
                    {
                        copies.push((reg.0, source.0));
                    }
                }
                if let Expr::Register(reg) = assignment.value
                    && writes[reg.0] <= 1
                    && let Some(&(_, root)) = projection.stores.get(&site)
                {
                    // Opaque/mixed reads and lazy choices cannot seed a
                    // register identity merely because their value is spilled.
                    let safe = sources[reg.0].is_none_or(|(site, value)| match value {
                        Expr::Load { .. } => projection.loaded(value, site).is_some(),
                        Expr::Select { .. } => false,
                        _ => true,
                    });
                    if safe {
                        evidence[reg.0].insert(root);
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            for &(a, b) in &copies {
                budget.take(evidence[a].len() + evidence[b].len() + 1)?;
                let union: BTreeSet<_> = evidence[a].union(&evidence[b]).copied().collect();
                if evidence[a] != union || evidence[b] != union {
                    evidence[a] = union.clone();
                    evidence[b] = union;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for (register, candidates) in evidence.iter().enumerate() {
            let safe = sources[register].is_none_or(|(site, value)| match value {
                Expr::Load { .. } => projection.loaded(value, site).is_some(),
                Expr::Select { .. } => false,
                _ => true,
            });
            if candidates.len() == 1 && writes[register] <= 1 && safe {
                projection.registers.insert(register, *candidates.first()?);
            }
        }
        let projected = projection.nodes(nodes, &mut budget)?;
        let roles = value_role::infer(&projected, |reg| reg.0.checked_sub(count));
        let registers = projection
            .registers
            .iter()
            .filter_map(|(&reg, root)| Some((reg, *roles.get(root)?)))
            .collect();

        // Offset names require every lifetime at that cell to agree. A byte
        // owner map detects modular overlap, including mixed widths, cheaply.
        let mut cells: BTreeMap<i64, BTreeSet<usize>> = BTreeMap::new();
        let mut bytes = BTreeMap::<u64, StackLocation>::new();
        let mut blocked = BTreeSet::new();
        let locations: BTreeSet<_> = definitions
            .iter()
            .map(|d| d.location)
            .chain(values.reads().iter().map(|r| r.location))
            .collect();
        for location in locations {
            for byte in 0..location.width.bytes() {
                budget.take(1)?;
                let address = (location.offset as u64).wrapping_add(byte as u64);
                if let Some(old) = bytes.insert(address, location)
                    && old != location
                {
                    blocked.insert(old.offset);
                    blocked.insert(location.offset);
                }
            }
        }
        for definition in definitions {
            cells
                .entry(definition.location.offset)
                .or_default()
                .insert(roots[definition.id]);
        }
        for read in values.reads() {
            if read.has_unknown || read.definitions.is_empty() {
                blocked.insert(read.location.offset);
            }
        }
        let offsets = cells
            .into_iter()
            .filter_map(|(offset, roots)| {
                if blocked.contains(&offset) {
                    return None;
                }
                let mut names = roots.iter().map(|root| roles.get(root).copied());
                let role = names.next()??;
                (role != ValueRole::Address && names.all(|other| other == Some(role)))
                    .then_some((offset, role))
            })
            .collect();
        let locations = definitions
            .iter()
            .map(|definition| (roots[definition.id], definition.location))
            .collect();
        Some(Self {
            registers,
            offsets,
            webs: projection.registers,
            locations,
        })
    }
}

struct Budget(usize);
impl Budget {
    fn take(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}
struct Dsu(Vec<usize>);
impl Dsu {
    fn root(&mut self, mut id: usize) -> usize {
        while self.0[id] != id {
            self.0[id] = self.0[self.0[id]];
            id = self.0[id];
        }
        id
    }
    fn union(&mut self, a: usize, b: usize) {
        let (a, b) = (self.root(a), self.root(b));
        self.0[a.max(b)] = a.min(b);
    }
}
fn read_key(site: Site, location: StackLocation) -> ReadKey {
    (site.0, site.1, location.offset, location.width.bytes())
}

struct Projection<'a> {
    instructions: BTreeMap<u64, &'a crate::ir::IrInstruction>,
    stack: &'a StackAnalysis,
    loads: BTreeMap<ReadKey, usize>,
    stores: BTreeMap<Site, (StackLocation, usize)>,
    registers: BTreeMap<usize, usize>,
    first: usize,
}
impl Projection<'_> {
    fn loaded(&self, value: &Expr, site: Site) -> Option<usize> {
        let Expr::Load { address, width } = value else {
            return None;
        };
        let offset = self.stack.offset_before(site.0, site.1, address)?;
        self.loads
            .get(&read_key(
                site,
                StackLocation {
                    offset,
                    width: *width,
                },
            ))
            .copied()
    }
    fn reg(&self, reg: Reg) -> Reg {
        self.registers
            .get(&reg.0)
            .map_or(reg, |root| Reg(self.first + root))
    }
    fn expression(&self, value: &Expr, site: Option<Site>, budget: &mut Budget) -> Option<Expr> {
        budget.take(1)?;
        Some(match value {
            Expr::Register(reg) => Expr::Register(self.reg(*reg)),
            Expr::Const(_) => value.clone(),
            Expr::Load { .. } => {
                if let Some(root) = site.and_then(|site| self.loaded(value, site)) {
                    Expr::Register(Reg(self.first + root))
                } else {
                    // Keep the entire unannotated/unknown load opaque.
                    value.clone()
                }
            }
            Expr::Binary(op, a, b) => Expr::binary(
                *op,
                self.expression(a, site, budget)?,
                self.expression(b, site, budget)?,
            ),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Expr::select(
                self.expression(condition, site, budget)?,
                self.expression(taken, site, budget)?,
                self.expression(not_taken, site, budget)?,
            ),
        })
    }
    fn nodes(&self, nodes: &[Node], budget: &mut Budget) -> Option<Vec<Node>> {
        nodes
            .iter()
            .map(|node| {
                budget.take(1)?;
                Some(match node {
                    Node::Step {
                        address,
                        assignments,
                    } => {
                        let original = self.instructions.get(address).copied();
                        let assignments = assignments
                            .iter()
                            .enumerate()
                            .map(|(ordinal, assignment)| {
                                budget.take(1)?;
                                let site = original
                                    .filter(|i| i.assignments.len() == assignments.len())
                                    .and_then(|i| i.assignments.get(ordinal))
                                    .filter(|a| a.destination == assignment.destination)
                                    .map(|_| (*address, ordinal));
                                let destination = match &assignment.destination {
                                    Place::Register(reg) => Place::Register(self.reg(*reg)),
                                    Place::Memory { address, width } => {
                                        let known = site.and_then(|site| {
                                            let (location, root) = self.stores.get(&site)?;
                                            (location.width == *width
                                                && self
                                                    .stack
                                                    .offset_before(site.0, site.1, address)
                                                    == Some(location.offset))
                                            .then_some(*root)
                                        });
                                        known.map_or_else(
                                            || assignment.destination.clone(),
                                            |root| Place::Register(Reg(self.first + root)),
                                        )
                                    }
                                };
                                Some(Assignment {
                                    destination,
                                    value: self.expression(&assignment.value, site, budget)?,
                                })
                            })
                            .collect::<Option<Vec<_>>>()?;
                        Node::Step {
                            address: *address,
                            assignments,
                        }
                    }
                    Node::If {
                        condition,
                        taken,
                        not_taken,
                    } => Node::If {
                        condition: self.expression(condition, None, budget)?,
                        taken: self.nodes(taken, budget)?,
                        not_taken: self.nodes(not_taken, budget)?,
                    },
                    Node::Loop(body) => Node::Loop(self.nodes(body, budget)?),
                    Node::Return(value) => Node::Return(self.expression(value, None, budget)?),
                    Node::Evaluate(value) => Node::Evaluate(self.expression(value, None, budget)?),
                    _ => node.clone(),
                })
            })
            .collect()
    }
}
fn validate_expr(value: &Expr, count: usize, depth: usize, budget: &mut Budget) -> Option<()> {
    if depth > MAX_DEPTH {
        return None;
    }
    budget.take(1)?;
    match value {
        Expr::Register(reg) if reg.0 >= count => return None,
        Expr::Binary(_, a, b) => {
            validate_expr(a, count, depth + 1, budget)?;
            validate_expr(b, count, depth + 1, budget)?;
        }
        Expr::Load { address, .. } => validate_expr(address, count, depth + 1, budget)?,
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            validate_expr(condition, count, depth + 1, budget)?;
            validate_expr(taken, count, depth + 1, budget)?;
            validate_expr(not_taken, count, depth + 1, budget)?;
        }
        _ => {}
    }
    Some(())
}
fn validate_assignment(
    a: &Assignment,
    count: usize,
    depth: usize,
    budget: &mut Budget,
) -> Option<()> {
    budget.take(1)?;
    match &a.destination {
        Place::Register(reg) if reg.0 >= count => return None,
        Place::Memory { address, .. } => validate_expr(address, count, depth + 1, budget)?,
        _ => {}
    }
    validate_expr(&a.value, count, depth + 1, budget)
}
fn validate_nodes(nodes: &[Node], count: usize, depth: usize, budget: &mut Budget) -> Option<()> {
    if depth > MAX_DEPTH {
        return None;
    }
    for node in nodes {
        budget.take(1)?;
        match node {
            Node::Step { assignments, .. } => {
                for a in assignments {
                    validate_assignment(a, count, depth + 1, budget)?;
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                validate_expr(condition, count, depth + 1, budget)?;
                validate_nodes(taken, count, depth + 1, budget)?;
                validate_nodes(not_taken, count, depth + 1, budget)?;
            }
            Node::Loop(body) => validate_nodes(body, count, depth + 1, budget)?,
            Node::Return(value) | Node::Evaluate(value) => {
                validate_expr(value, count, depth + 1, budget)?
            }
            _ => {}
        }
    }
    Some(())
}
