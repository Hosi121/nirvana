//! Pure definition expansion stops at phi/initial values and captured loads.
use super::*;

type Instructions<'a> = BTreeMap<u64, &'a IrInstruction>;
type Points<'a> = BTreeMap<Site, &'a PointValues>;

fn root(parents: &mut [usize], id: usize, budget: &mut Budget) -> Option<usize> {
    let mut end = id;
    while parents[end] != end {
        budget.spend(1)?;
        end = parents[end];
    }
    let mut next = id;
    while parents[next] != end {
        budget.spend(1)?;
        let old = parents[next];
        parents[next] = end;
        next = old;
    }
    Some(end)
}

pub(super) fn aliases(
    graph: &SsaFunction,
    instructions: &Instructions<'_>,
    points: &Points<'_>,
    budget: &mut Budget,
) -> Option<Vec<ValueId>> {
    let mut parents: Vec<_> = (0..graph.values.len()).collect();
    for (id, value) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        if let Definition::Assignment { site, .. } = value
            && let Some(next) = copy_source(assignment(instructions, *site)?, points.get(site)?)
        {
            parents[id] = next.0;
        }
    }
    loop {
        let mut changed = false;
        for (id, value) in graph.values.iter().enumerate() {
            budget.spend(1)?;
            let Definition::Phi { inputs, .. } = value else {
                continue;
            };
            if parents[id] != id {
                continue;
            }
            let mut unique = None;
            let mut distinct = false;
            for input in inputs {
                let incoming = root(&mut parents, input.value.0, budget)?;
                if incoming == id {
                    continue;
                }
                if unique.is_some_and(|old| old != incoming) {
                    distinct = true;
                    break;
                }
                unique = Some(incoming);
            }
            if !distinct && let Some(value) = unique {
                parents[id] = value;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    (0..parents.len())
        .map(|id| root(&mut parents, id, budget).map(ValueId))
        .collect()
}

fn assignment<'a>(instructions: &Instructions<'a>, site: Site) -> Option<&'a Assignment> {
    instructions
        .get(&site.instruction)?
        .assignments
        .get(site.assignment?)
}
fn copy_source(assignment: &Assignment, point: &PointValues) -> Option<ValueId> {
    if matches!(assignment.value, Expr::Register(_)) && point.reads.len() == 1 {
        Some(point.reads[0].value)
    } else {
        None
    }
}
fn update_site(
    graph: &SsaFunction,
    instructions: &Instructions<'_>,
    points: &Points<'_>,
    mut value: ValueId,
    budget: &mut Budget,
) -> Option<Site> {
    loop {
        budget.spend(1)?;
        let Definition::Assignment { site, .. } = graph.values.get(value.0)? else {
            return None;
        };
        let source = assignment(instructions, *site)?;
        if let Some(next) = copy_source(source, points.get(site)?) {
            value = next;
        } else {
            return Some(*site);
        }
    }
}

struct Captured {
    site: Site,
    width: Width,
    address: PatternExpr,
}
struct Resolve<'a, 'b> {
    graph: &'a SsaFunction,
    instructions: &'a Instructions<'a>,
    points: &'a Points<'a>,
    aliases: &'a [ValueId],
    cut: ValueId,
    load: Option<Captured>,
    budget: &'b mut Budget,
}
impl Resolve<'_, '_> {
    fn value(&mut self, mut value: ValueId, depth: usize) -> Option<PatternExpr> {
        loop {
            self.budget.spend(1)?;
            value = self.aliases[value.0];
            if depth > MAX_DEPTH {
                return None;
            }
            if value == self.cut {
                self.budget.node()?;
                return Some(PatternExpr::Accumulator);
            }
            let site = match self.graph.values.get(value.0)? {
                Definition::Initial { .. } | Definition::Phi { .. } => {
                    self.budget.node()?;
                    return Some(PatternExpr::Value(value));
                }
                Definition::Assignment { site, .. } => *site,
            };
            let source = assignment(self.instructions, site)?;
            let point = *self.points.get(&site)?;
            if let Some(next) = copy_source(source, point) {
                value = next;
                continue;
            }
            let mut reads = point.reads.iter();
            let result = self.expression(&source.value, &mut reads, site, depth + 1, true)?;
            if reads.next().is_some() {
                return None;
            }
            return Some(result);
        }
    }
    fn expression(
        &mut self,
        expression: &Expr,
        reads: &mut std::slice::Iter<'_, RegisterValue>,
        site: Site,
        depth: usize,
        allow_load: bool,
    ) -> Option<PatternExpr> {
        self.budget.spend(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        self.budget.node()?;
        Some(match expression {
            Expr::Const(value) => PatternExpr::Constant(*value),
            Expr::Register(register) => {
                let read = reads.next()?;
                if read.register != *register {
                    return None;
                }
                return self.value(read.value, depth + 1);
            }
            Expr::Unary(op, value) => PatternExpr::Unary(
                *op,
                Box::new(self.expression(value, reads, site, depth + 1, false)?),
            ),
            Expr::Binary(op, left, right) => {
                let mut left = self.expression(left, reads, site, depth + 1, false)?;
                let mut right = self.expression(right, reads, site, depth + 1, false)?;
                if matches!(
                    op,
                    BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor
                ) && ((right == PatternExpr::Accumulator && left != PatternExpr::Accumulator)
                    || (right == PatternExpr::Loaded
                        && left != PatternExpr::Accumulator
                        && left != PatternExpr::Loaded))
                {
                    std::mem::swap(&mut left, &mut right);
                }
                PatternExpr::Binary(*op, Box::new(left), Box::new(right))
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => PatternExpr::Select(
                Box::new(self.expression(condition, reads, site, depth + 1, false)?),
                Box::new(self.expression(taken, reads, site, depth + 1, false)?),
                Box::new(self.expression(not_taken, reads, site, depth + 1, false)?),
            ),
            Expr::Load { address, width } if allow_load => {
                let address = self.expression(address, reads, site, depth + 1, false)?;
                if let Some(captured) = &self.load {
                    if captured.site != site
                        || captured.width != *width
                        || captured.address != address
                    {
                        return None;
                    }
                } else {
                    self.load = Some(Captured {
                        site,
                        width: *width,
                        address,
                    });
                }
                PatternExpr::Loaded
            }
            Expr::Load { .. } => return None,
        })
    }
}

pub(super) fn pure_value(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    value: ValueId,
) -> Option<PatternExpr> {
    let instructions = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let points = graph
        .blocks
        .iter()
        .flat_map(|block| &block.points)
        .map(|point| (point.site, point))
        .collect();
    let mut budget = Budget::new();
    let mut context = Resolve {
        graph,
        instructions: &instructions,
        points: &points,
        aliases,
        cut: ValueId(usize::MAX),
        load: None,
        budget: &mut budget,
    };
    let expression = context.value(value, 0)?;
    if context.load.is_some() || context.budget.exhausted {
        None
    } else {
        Some(expression)
    }
}

pub(super) fn kernel(
    graph: &SsaFunction,
    instructions: &Instructions<'_>,
    points: &Points<'_>,
    aliases: &[ValueId],
    store: Site,
    budget: &mut Budget,
) -> Option<Kernel> {
    let source = assignment(instructions, store)?;
    let Place::Memory { address, width } = &source.destination else {
        return None;
    };
    let Expr::Register(accumulator) = source.value else {
        return None;
    };
    let store_point = *points.get(&store)?;
    let result = store_point.reads.last()?;
    if result.register != accumulator {
        return None;
    }
    let update = update_site(graph, instructions, points, result.value, budget)?;
    let update_assignment = assignment(instructions, update)?;
    let Expr::Binary(_, left, right) = &update_assignment.value else {
        return None;
    };
    if **left != Expr::Register(accumulator) && **right != Expr::Register(accumulator) {
        return None;
    }
    let update_point = *points.get(&update)?;
    let cut = aliases[update_point
        .reads
        .iter()
        .find(|read| read.register == accumulator)?
        .value
        .0];
    let mut context = Resolve {
        graph,
        instructions,
        points,
        aliases,
        cut,
        load: None,
        budget,
    };
    let mut reads = update_point.reads.iter();
    let update_expression =
        context.expression(&update_assignment.value, &mut reads, update, 0, false)?;
    if reads.next().is_some() {
        return None;
    }
    let mut reads = store_point.reads.iter();
    let store_address = context.expression(address, &mut reads, store, 0, false)?;
    let last = reads.next()?;
    if last.value != result.value || reads.next().is_some() {
        return None;
    }
    let captured = context.load?;
    Some(Kernel {
        load: captured.site,
        update,
        store,
        accumulator,
        load_width: captured.width,
        store_width: *width,
        load_address: captured.address,
        update_expression,
        store_address,
    })
}
