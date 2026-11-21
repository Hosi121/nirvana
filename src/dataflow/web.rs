//! Bounded definition/use webs for display-only register renaming.
//!
//! Reaching definitions are joined at every syntactic read of the same source
//! register, including lazy arms. Entry reads keep their ABI register IDs.
//! This does not remove operations or preserve the final complete register file.

use crate::control_flow::cfg::Target;
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

const MAX_DEPTH: usize = 128;
const MAX_EXPRESSION_NODES: usize = 200_000;
const MAX_POINTS: usize = 100_000;
const MAX_ACTIVE: usize = 4096;
const MAX_BLOCKS: usize = 4096;
const MAX_DEFINITIONS: usize = 20_000;
const MAX_STATE_CELLS: usize = 1_000_000;
const MAX_MEMBERS: usize = 1_000_000;
const MAX_WORK: usize = 10_000_000;
const MAX_STEPS: usize = 100_000;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct WebStats {
    /// Entry seeds plus reachable register assignments, including unread ones.
    pub definitions: usize,
    /// Components reaching at least one syntactic read.
    pub webs: usize,
    pub split_registers: usize,
    pub fresh_registers: usize,
}

#[derive(Clone, Debug)]
pub struct WebSplit {
    program: Program,
    stats: WebStats,
}
impl WebSplit {
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn stats(&self) -> WebStats {
        self.stats
    }
}

/// Split useful webs of reused registers, or return `None` on any bounded
/// analysis/validation failure. Unreachable instructions stay exactly equal.
pub fn split(program: &Program) -> Option<WebSplit> {
    validate(program)?;
    let mut model = Model::new(program)?;
    model.propagate(program)?;
    let mut components = Components {
        parent: (0..model.definitions.len()).collect(),
    };
    let mut used = vec![false; model.definitions.len()];
    for &block in &model.reachable.clone() {
        let mut state = model.start(block)?;
        for index in program.cfg().blocks()[block].instructions.clone() {
            let instruction = &program.instructions()[index];
            for (assignment, value) in instruction.assignments.iter().enumerate() {
                // Use separate field borrows so all traversal/root work shares
                // one real budget, including destination address reads.
                read_assignment(
                    value,
                    &state,
                    &model.indices,
                    &model.definitions,
                    &mut components,
                    &mut used,
                    &mut model.work,
                )?;
                model.write(index, assignment, &mut state)?;
            }
            match &instruction.control {
                Control::Branch { condition, .. } | Control::Return(condition) => {
                    read(
                        condition,
                        &state,
                        &model.indices,
                        &model.definitions,
                        &mut components,
                        &mut used,
                        &mut model.work,
                    )?;
                }
                _ => {}
            }
        }
    }
    let (names, count, stats) = names(
        program.register_count(),
        &model.indices,
        &model.definitions,
        &used,
        &mut components,
        &mut model.work,
    )?;
    if stats.fresh_registers == 0 {
        return Some(WebSplit {
            program: program.clone(),
            stats,
        });
    }
    let mut instructions = program.instructions().to_vec();
    for &block in &model.reachable.clone() {
        let mut state = model.start(block)?;
        for index in program.cfg().blocks()[block].instructions.clone() {
            let original = &program.instructions()[index];
            let mut assignments = Vec::with_capacity(original.assignments.len());
            for (assignment, old) in original.assignments.iter().enumerate() {
                let destination = match &old.destination {
                    Place::Register(_) => Place::Register(names[model.ids[&(index, assignment)]]),
                    Place::Memory { address, width } => Place::Memory {
                        address: rename(address, &state, &model.indices, &names, &mut model.work)?,
                        width: *width,
                    },
                };
                let value = rename(&old.value, &state, &model.indices, &names, &mut model.work)?;
                assignments.push(Assignment { destination, value });
                model.write(index, assignment, &mut state)?;
            }
            let control = match &original.control {
                Control::Return(value) => Control::Return(rename(
                    value,
                    &state,
                    &model.indices,
                    &names,
                    &mut model.work,
                )?),
                Control::Branch { condition, target } => Control::Branch {
                    condition: rename(condition, &state, &model.indices, &names, &mut model.work)?,
                    target: *target,
                },
                other => other.clone(),
            };
            instructions[index] = IrInstruction {
                assignments,
                control,
                ..original.clone()
            };
        }
    }
    let program = Program::new(
        program.cfg().block(program.cfg().entry()).start,
        count,
        instructions,
    )
    .ok()?;
    Some(WebSplit { program, stats })
}

struct Budget(usize);
impl Budget {
    fn spend(&mut self, amount: usize) -> Option<()> {
        self.0 = self.0.checked_sub(amount)?;
        Some(())
    }
}

fn visit(
    expr: &Expr,
    work: &mut Budget,
    mut register: impl FnMut(Reg, &mut Budget) -> Option<()>,
) -> Option<()> {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        work.spend(1)?;
        match expr {
            Expr::Register(reg) => register(*reg, work)?,
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, b) => {
                pending.push(b);
                pending.push(a);
            }
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(not_taken);
                pending.push(taken);
                pending.push(condition);
            }
            Expr::Const(_) => {}
        }
    }
    Some(())
}

fn validate(program: &Program) -> Option<()> {
    let mut nodes = MAX_EXPRESSION_NODES;
    let mut points = 0usize;
    let mut expression = |expr: &Expr| {
        let mut pending = vec![(expr, 1)];
        while let Some((expr, depth)) = pending.pop() {
            if depth > MAX_DEPTH {
                return None;
            }
            nodes = nodes.checked_sub(1)?;
            match expr {
                Expr::Unary(_, value) => pending.push((value, depth + 1)),
                Expr::Binary(_, a, b) => {
                    pending.push((b, depth + 1));
                    pending.push((a, depth + 1));
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
                _ => {}
            }
        }
        Some(())
    };
    for instruction in program.instructions() {
        points = points
            .checked_add(instruction.assignments.len())?
            .checked_add(1)?;
        if points > MAX_POINTS {
            return None;
        }
        for assignment in &instruction.assignments {
            if let Place::Memory { address, .. } = &assignment.destination {
                expression(address)?;
            }
            expression(&assignment.value)?;
        }
        match &instruction.control {
            Control::Return(value)
            | Control::Branch {
                condition: value, ..
            } => expression(value)?,
            _ => {}
        }
    }
    Some(())
}

type State = Vec<BTreeSet<usize>>;
struct Model {
    indices: BTreeMap<usize, usize>,
    definitions: Vec<usize>,
    ids: BTreeMap<(usize, usize), usize>,
    incoming: Vec<Option<State>>,
    reachable: Vec<usize>,
    retained: usize,
    work: Budget,
}
impl Model {
    fn new(program: &Program) -> Option<Self> {
        if program.cfg().blocks().len() > MAX_BLOCKS {
            return None;
        }
        let reachable: Vec<_> = program
            .cfg()
            .reachable_blocks()
            .iter()
            .map(|id| id.index())
            .collect();
        let mut registers = BTreeSet::new();
        let mut work = Budget(MAX_WORK);
        for &block in &reachable {
            for instruction in
                &program.instructions()[program.cfg().blocks()[block].instructions.clone()]
            {
                work.spend(1)?;
                let mut add = |reg: Reg, _: &mut Budget| {
                    registers.insert(reg.0);
                    (registers.len() <= MAX_ACTIVE).then_some(())
                };
                for assignment in &instruction.assignments {
                    work.spend(1)?;
                    match &assignment.destination {
                        Place::Register(reg) => add(*reg, &mut work)?,
                        Place::Memory { address, .. } => visit(address, &mut work, &mut add)?,
                    }
                    visit(&assignment.value, &mut work, &mut add)?;
                }
                match &instruction.control {
                    Control::Return(value)
                    | Control::Branch {
                        condition: value, ..
                    } => visit(value, &mut work, &mut add)?,
                    _ => {}
                }
            }
        }
        if program
            .cfg()
            .blocks()
            .len()
            .checked_add(1)?
            .checked_mul(registers.len())?
            > MAX_STATE_CELLS
        {
            return None;
        }
        let indices: BTreeMap<_, _> = registers
            .iter()
            .enumerate()
            .map(|(index, &reg)| (reg, index))
            .collect();
        let mut definitions: Vec<_> = registers.into_iter().collect();
        let mut ids = BTreeMap::new();
        for &block in &reachable {
            for index in program.cfg().blocks()[block].instructions.clone() {
                for (assignment, value) in
                    program.instructions()[index].assignments.iter().enumerate()
                {
                    if let Place::Register(reg) = value.destination {
                        if definitions.len() >= MAX_DEFINITIONS {
                            return None;
                        }
                        ids.insert((index, assignment), definitions.len());
                        definitions.push(reg.0);
                    }
                }
            }
        }
        let mut incoming = vec![None; program.cfg().blocks().len()];
        incoming[program.cfg().entry().index()] =
            Some((0..indices.len()).map(|id| BTreeSet::from([id])).collect());
        let retained = indices.len();
        Some(Self {
            indices,
            definitions,
            ids,
            incoming,
            reachable,
            retained,
            work,
        })
    }

    fn start(&mut self, block: usize) -> Option<State> {
        let state = self.incoming[block].as_ref()?;
        self.work.spend(state.len())?;
        let members: usize = state.iter().map(BTreeSet::len).sum();
        if self.retained.checked_add(members)? > MAX_MEMBERS {
            return None;
        }
        self.work.spend(members)?;
        Some(state.clone())
    }

    fn write(&mut self, instruction: usize, assignment: usize, state: &mut State) -> Option<()> {
        self.work.spend(1)?;
        if let Some(&id) = self.ids.get(&(instruction, assignment)) {
            state[self.indices[&self.definitions[id]]] = BTreeSet::from([id]);
        }
        Some(())
    }

    fn propagate(&mut self, program: &Program) -> Option<()> {
        let entry = program.cfg().entry().index();
        let mut pending = VecDeque::from([entry]);
        let mut queued = vec![false; self.incoming.len()];
        queued[entry] = true;
        let mut steps = MAX_STEPS;
        while let Some(block) = pending.pop_front() {
            steps = steps.checked_sub(1)?;
            queued[block] = false;
            let mut state = self.start(block)?;
            for index in program.cfg().blocks()[block].instructions.clone() {
                for assignment in 0..program.instructions()[index].assignments.len() {
                    self.write(index, assignment, &mut state)?;
                }
            }
            self.work.spend(state.len())?;
            let members: usize = state.iter().map(BTreeSet::len).sum();
            for edge in &program.cfg().blocks()[block].successors {
                let Target::Block(target) = edge.target else {
                    return None;
                };
                let target = target.index();
                let changed = if let Some(previous) = &mut self.incoming[target] {
                    let mut changed = false;
                    for (before, after) in previous.iter_mut().zip(&state) {
                        self.work.spend(1)?;
                        for &id in after {
                            self.work.spend(1)?;
                            if !before.contains(&id) {
                                if self.retained.checked_add(members)?.checked_add(1)? > MAX_MEMBERS
                                {
                                    return None;
                                }
                                before.insert(id);
                                self.retained += 1;
                                changed = true;
                            }
                        }
                    }
                    changed
                } else {
                    if self.retained.checked_add(members.checked_mul(2)?)? > MAX_MEMBERS {
                        return None;
                    }
                    self.work.spend(members + state.len())?;
                    self.incoming[target] = Some(state.clone());
                    self.retained += members;
                    true
                };
                if changed && !queued[target] {
                    pending.push_back(target);
                    queued[target] = true;
                }
            }
        }
        Some(())
    }
}

struct Components {
    parent: Vec<usize>,
}
impl Components {
    fn root(&mut self, mut id: usize, work: &mut Budget) -> Option<usize> {
        while self.parent[id] != id {
            work.spend(1)?;
            self.parent[id] = self.parent[self.parent[id]];
            id = self.parent[id];
        }
        work.spend(1)?;
        Some(id)
    }
    fn join(&mut self, a: usize, b: usize, work: &mut Budget) -> Option<()> {
        let a = self.root(a, work)?;
        let b = self.root(b, work)?;
        self.parent[a.max(b)] = a.min(b);
        Some(())
    }
}

fn read(
    expr: &Expr,
    state: &State,
    indices: &BTreeMap<usize, usize>,
    definitions: &[usize],
    components: &mut Components,
    used: &mut [bool],
    work: &mut Budget,
) -> Option<()> {
    visit(expr, work, |reg, work| {
        let reaching = &state[*indices.get(&reg.0)?];
        let first = *reaching.first()?;
        for &id in reaching {
            if definitions[id] != reg.0 {
                return None;
            }
            used[id] = true;
            components.join(first, id, work)?;
        }
        Some(())
    })
}

fn read_assignment(
    assignment: &Assignment,
    state: &State,
    indices: &BTreeMap<usize, usize>,
    definitions: &[usize],
    components: &mut Components,
    used: &mut [bool],
    work: &mut Budget,
) -> Option<()> {
    if let Place::Memory { address, .. } = &assignment.destination {
        read(address, state, indices, definitions, components, used, work)?;
    }
    read(
        &assignment.value,
        state,
        indices,
        definitions,
        components,
        used,
        work,
    )
}

fn names(
    original_count: usize,
    indices: &BTreeMap<usize, usize>,
    definitions: &[usize],
    used: &[bool],
    components: &mut Components,
    work: &mut Budget,
) -> Option<(Vec<Reg>, usize, WebStats)> {
    let mut useful: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for (id, &read) in used.iter().enumerate() {
        if read {
            useful
                .entry(definitions[id])
                .or_default()
                .insert(components.root(id, work)?);
        }
    }
    let mut stats = WebStats {
        definitions: definitions.len(),
        ..WebStats::default()
    };
    let mut chosen = BTreeMap::new();
    let mut next = original_count;
    for (&register, roots) in &useful {
        stats.webs += roots.len();
        let entry = indices[&register];
        let original_root = if used[entry] {
            components.root(entry, work)?
        } else {
            *roots.first()?
        };
        if roots.len() > 1 {
            stats.split_registers += 1;
        }
        for &root in roots {
            let target = if root == original_root {
                Reg(register)
            } else {
                let reg = Reg(next);
                next = next.checked_add(1)?;
                reg
            };
            chosen.insert(root, target);
        }
    }
    stats.fresh_registers = next.checked_sub(original_count)?;
    let mut names = Vec::with_capacity(definitions.len());
    for (id, &register) in definitions.iter().enumerate() {
        // An unread definition reaches no reachable syntactic read, so keeping
        // its original destination cannot clobber any later used component.
        names.push(
            chosen
                .get(&components.root(id, work)?)
                .copied()
                .unwrap_or(Reg(register)),
        );
    }
    Some((names, next, stats))
}

fn rename(
    expr: &Expr,
    state: &State,
    indices: &BTreeMap<usize, usize>,
    names: &[Reg],
    work: &mut Budget,
) -> Option<Expr> {
    work.spend(1)?;
    Some(match expr {
        Expr::Unary(op, value) => Expr::unary(*op, rename(value, state, indices, names, work)?),
        Expr::Register(reg) => {
            let reaching = &state[*indices.get(&reg.0)?];
            let target = names[*reaching.first()?];
            for &id in reaching {
                work.spend(1)?;
                if names[id] != target {
                    return None;
                }
            }
            Expr::Register(target)
        }
        Expr::Const(_) => expr.clone(),
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            rename(a, state, indices, names, work)?,
            rename(b, state, indices, names, work)?,
        ),
        Expr::Load { address, width } => {
            Expr::load(rename(address, state, indices, names, work)?, *width)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            rename(condition, state, indices, names, work)?,
            rename(taken, state, indices, names, work)?,
            rename(not_taken, state, indices, names, work)?,
        ),
    })
}
