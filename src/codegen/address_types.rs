//! Conservative guest-address element-width hints for raw registers.
//!
//! A hint describes uniform observed guest-memory access widths. It does not
//! turn the register's `u64` into a host pointer or establish bounds, objects,
//! allocations, alignment, or separation from other addresses.
use crate::dataflow::ssa::{Definition, PointValues, Site, ValueId};
use crate::dataflow::type_infer::{AddressShape, Operand, PathEdge, TypeAnalysis};
use crate::model::ir::{BinaryOp as B, Control, Expr, Place, Program, Width};
use std::collections::{BTreeMap, VecDeque};

/// Keys are raw register numbers. Every actually read SSA value of a returned
/// register must alias an exact layout root with the same observed width.
/// Unread initial values and unused definitions do not participate.
pub fn register_hints(program: &Program) -> BTreeMap<usize, Width> {
    hints(program).unwrap_or_default()
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
enum Demand {
    #[default]
    None,
    Base(ValueId),
    Scalar,
}

struct Uses<'a> {
    aliases: &'a [ValueId],
    demands: Vec<Demand>,
    queue: VecDeque<usize>,
}
impl Uses<'_> {
    fn merge(&mut self, value: ValueId, demand: Demand) {
        let root = self.aliases[value.0].0;
        let old = self.demands[root];
        let next = match (old, demand) {
            (old, Demand::None) | (Demand::None, old) => old,
            (Demand::Base(a), Demand::Base(b)) if a == b => old,
            _ => Demand::Scalar,
        };
        if next != old {
            self.demands[root] = next;
            self.queue.push_back(root);
        }
    }

    // Each alias class changes at most twice. A construction is traversed once
    // per change, rather than expanding it again for every memory access.
    fn propagate(&mut self, inputs: &[Vec<ValueId>], constructions: &[bool], phis: &[bool]) {
        while let Some(root) = self.queue.pop_front() {
            let demand = self.demands[root];
            if (phis[root] && demand != Demand::Scalar)
                || (!constructions[root] && matches!(demand, Demand::Base(base) if base.0 != root))
            {
                self.merge(ValueId(root), Demand::Scalar);
                continue;
            }
            for &input in &inputs[root] {
                self.merge(input, demand);
            }
        }
    }
}

type Accesses = BTreeMap<(Site, u8, Vec<u8>), AddressShape>;

fn hints(program: &Program) -> Option<BTreeMap<usize, Width>> {
    // TypeAnalysis already bounds source syntax, SSA size, address collection,
    // alias resolution and layout work. The remaining passes are linear apart
    // from bounded syntax-path and source-site map lookups.
    let analysis = TypeAnalysis::analyze(program)?;
    let graph = analysis.graph();
    let aliases = analysis.aliases();
    let count = graph.values.len();
    let mut widths = vec![None; count];
    for layout in analysis.layouts() {
        if layout.ambiguous_intervals || !layout.overlaps.is_empty() {
            continue;
        }
        let mut observed = layout
            .fields
            .iter()
            .map(|field| field.width)
            .chain(layout.arrays.iter().map(|array| array.width));
        if let Some(width) = observed.next()
            && observed.all(|other| other == width)
        {
            widths[layout.base.0] = Some(width);
        }
    }
    let accesses: Accesses = analysis
        .accesses()
        .iter()
        .map(|access| {
            (
                (
                    access.site,
                    operand(access.operand),
                    access.path.iter().copied().map(edge).collect(),
                ),
                access.address,
            )
        })
        .collect();
    let mut uses = Uses {
        aliases,
        demands: vec![Demand::None; count],
        queue: VecDeque::new(),
    };
    let mut inputs = vec![Vec::new(); count];
    let mut constructions = vec![false; count];
    let mut phis = vec![false; count];
    for (id, definition) in graph.values.iter().enumerate() {
        if aliases[id].0 != id {
            continue;
        }
        if let Definition::Phi {
            inputs: incoming, ..
        } = definition
        {
            // Distinct alternatives are not a proven common layout. Trivial
            // phis have already been collapsed by TypeAnalysis's aliases.
            phis[id] = true;
            widths[id] = None;
            inputs[id].extend(incoming.iter().map(|input| input.value));
        }
    }
    for (id, facts) in analysis.values().iter().enumerate() {
        let roles = facts.flow_uses;
        if roles.address_index || roles.bitwise || roles.logical_shift || roles.signed_compare {
            uses.merge(ValueId(id), Demand::Scalar);
        }
    }
    for block in &graph.blocks {
        for point in &block.points {
            let instruction = program
                .instructions()
                .binary_search_by_key(&point.site.instruction, |instruction| instruction.address)
                .ok()?;
            let instruction = &program.instructions()[instruction];
            let mut cursor = 0;
            let mut walker = Walker {
                point,
                accesses: &accesses,
                uses: &mut uses,
            };
            if let Some(index) = point.site.assignment {
                let assignment = instruction.assignments.get(index)?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    let demand = walker.address(Operand::Destination, &[])?;
                    walker.expr(
                        address,
                        demand,
                        Operand::Destination,
                        &mut vec![edge(PathEdge::Address)],
                        &mut cursor,
                    )?;
                }
                let copy = matches!(assignment.destination, Place::Register(_))
                    && matches!(assignment.value, Expr::Register(_));
                let construction = matches!(assignment.destination, Place::Register(_))
                    && matches!(assignment.value, Expr::Binary(..))
                    && affine(&assignment.value);
                if construction {
                    let id = point.definition?;
                    // Non-copy arithmetic retains its own canonical identity.
                    if aliases[id.0] != id {
                        return None;
                    }
                    constructions[id.0] = true;
                    inputs[id.0].extend(point.reads.iter().map(|read| read.value));
                    cursor = point.reads.len();
                } else {
                    walker.expr(
                        &assignment.value,
                        if copy { Demand::None } else { Demand::Scalar },
                        Operand::Value,
                        &mut Vec::new(),
                        &mut cursor,
                    )?;
                }
            } else {
                let expression = match &instruction.control {
                    Control::Return(expression)
                    | Control::Branch {
                        condition: expression,
                        ..
                    } => expression,
                    _ => return None,
                };
                walker.expr(
                    expression,
                    Demand::Scalar,
                    Operand::Control,
                    &mut Vec::new(),
                    &mut cursor,
                )?;
            }
            if cursor != point.reads.len() {
                return None;
            }
        }
    }
    uses.propagate(&inputs, &constructions, &phis);
    // A dead arithmetic result does not make its original input reads into
    // address uses. Wait until all real demands have propagated before this.
    for (id, construction) in constructions.iter().enumerate() {
        if *construction && uses.demands[id] == Demand::None {
            uses.merge(ValueId(id), Demand::Scalar);
        }
    }
    uses.propagate(&inputs, &constructions, &phis);

    let mut seen = vec![false; graph.register_count];
    let mut rejected = vec![false; graph.register_count];
    let mut registers = vec![None; graph.register_count];
    for read in graph
        .blocks
        .iter()
        .flat_map(|block| &block.points)
        .flat_map(|point| &point.reads)
    {
        let reg = read.register.0;
        let root = aliases[read.value.0];
        let width = widths[root.0].filter(|_| uses.demands[root.0] == Demand::Base(root));
        if width.is_none() || (seen[reg] && registers[reg] != width) {
            rejected[reg] = true;
        }
        seen[reg] = true;
        registers[reg] = width;
    }
    Some(
        registers
            .into_iter()
            .enumerate()
            .filter_map(|(reg, width)| {
                width
                    .filter(|_| seen[reg] && !rejected[reg])
                    .map(|width| (reg, width))
            })
            .collect(),
    )
}

// Only pure supported address construction can defer its input classification
// to actual uses of its result. Masking is deliberately an integer role.
fn affine(expression: &Expr) -> bool {
    match expression {
        Expr::Register(_) | Expr::Const(_) => true,
        Expr::Binary(B::Add | B::Sub, left, right) => affine(left) && affine(right),
        Expr::Binary(B::Mul, left, right) => match (&**left, &**right) {
            (Expr::Const(_), value) | (value, Expr::Const(_)) => affine(value),
            _ => false,
        },
        Expr::Binary(B::Shl, left, right) => matches!(**right, Expr::Const(_)) && affine(left),
        _ => false,
    }
}

struct Walker<'a, 'b> {
    point: &'a PointValues,
    accesses: &'a Accesses,
    uses: &'b mut Uses<'a>,
}
impl Walker<'_, '_> {
    fn address(&self, part: Operand, path: &[u8]) -> Option<Demand> {
        Some(
            match self
                .accesses
                .get(&(self.point.site, operand(part), path.to_vec()))?
            {
                AddressShape::Base { base, .. } => Demand::Base(*base),
                _ => Demand::Scalar,
            },
        )
    }

    fn expr(
        &mut self,
        expression: &Expr,
        demand: Demand,
        part: Operand,
        path: &mut Vec<u8>,
        cursor: &mut usize,
    ) -> Option<()> {
        match expression {
            Expr::Register(register) => {
                let read = self.point.reads.get(*cursor)?;
                if read.register != *register {
                    return None;
                }
                *cursor += 1;
                self.uses.merge(read.value, demand);
            }
            Expr::Const(_) => {}
            Expr::Load { address, .. } => {
                let demand = self.address(part, path)?;
                self.child(address, demand, part, path, PathEdge::Address, cursor)?;
            }
            Expr::Binary(_, left, right) => {
                self.child(left, demand, part, path, PathEdge::Left, cursor)?;
                self.child(right, demand, part, path, PathEdge::Right, cursor)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.child(condition, demand, part, path, PathEdge::Condition, cursor)?;
                self.child(taken, demand, part, path, PathEdge::Taken, cursor)?;
                self.child(not_taken, demand, part, path, PathEdge::NotTaken, cursor)?;
            }
        }
        Some(())
    }

    fn child(
        &mut self,
        expression: &Expr,
        demand: Demand,
        part: Operand,
        path: &mut Vec<u8>,
        next: PathEdge,
        cursor: &mut usize,
    ) -> Option<()> {
        path.push(edge(next));
        self.expr(expression, demand, part, path, cursor)?;
        path.pop();
        Some(())
    }
}
fn operand(operand: Operand) -> u8 {
    match operand {
        Operand::Destination => 0,
        Operand::Value => 1,
        Operand::Control => 2,
    }
}
fn edge(edge: PathEdge) -> u8 {
    match edge {
        PathEdge::Left => 0,
        PathEdge::Right => 1,
        PathEdge::Address => 2,
        PathEdge::Condition => 3,
        PathEdge::Taken => 4,
        PathEdge::NotTaken => 5,
    }
}
