//! Source-bound pure value numbering for one acyclic execution. Every memory
//! producing definition is a distinct opaque word; memory equality is unused.
use super::*;
use crate::model::ir::{BinaryOp, UnaryOp};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Value {
    Constant(u64),
    Opaque(usize),
    Control(u64),
    Unary(UnaryOp, usize),
    Binary(BinaryOp, usize, usize),
    Select(usize, usize, usize),
}
impl Value {
    pub fn is_boolean(&self) -> bool {
        matches!(
            self,
            Self::Constant(0 | 1)
                | Self::Binary(
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule,
                    _,
                    _
                )
        )
    }
}
pub(super) struct Values {
    pub nodes: Vec<Value>,
    pub definitions: BTreeMap<ssa::Site, usize>,
    pub controls: BTreeMap<u64, usize>,
    ssa: Vec<Option<usize>>,
    intern: BTreeMap<Value, usize>,
    work: ssa::Budget,
}
impl Values {
    pub fn build(
        source: &Program,
        graph: &ssa::SsaFunction,
        order: &[BlockId],
    ) -> Result<Self, ssa::SsaError> {
        let mut values = Self {
            nodes: Vec::new(),
            definitions: BTreeMap::new(),
            controls: BTreeMap::new(),
            ssa: vec![None; graph.values.len()],
            intern: BTreeMap::new(),
            work: ssa::Budget::new(),
        };
        for (id, definition) in graph.values.iter().enumerate() {
            if matches!(definition, ssa::Definition::Initial { .. }) {
                values.ssa[id] = Some(values.node(Value::Opaque(id))?);
            }
        }
        let points: BTreeMap<_, _> = graph
            .blocks
            .iter()
            .flat_map(|b| &b.points)
            .map(|p| (p.site, p))
            .collect();
        let blocks: BTreeMap<_, _> = graph.blocks.iter().map(|b| (b.start, b)).collect();
        for &id in order {
            let block = source.cfg().block(id);
            for phi in &blocks[&block.start].phis {
                let ssa::Definition::Phi { inputs, .. } = &graph.values[phi.0] else {
                    return Err(invalid("predicate phi"));
                };
                let incoming = inputs
                    .iter()
                    .map(|p| values.get(p.value))
                    .collect::<Result<Vec<_>, _>>()?;
                let first = *incoming.first().ok_or(invalid("predicate phi inputs"))?;
                values.ssa[phi.0] = Some(if incoming.iter().all(|v| *v == first) {
                    first
                } else {
                    values.node(Value::Opaque(phi.0))?
                });
            }
            for instruction in &source.instructions()[block.instructions.clone()] {
                for (n, assignment) in instruction.assignments.iter().enumerate() {
                    if matches!(assignment.destination, Place::Register(_)) {
                        let site = ssa::Site {
                            instruction: instruction.address,
                            assignment: Some(n),
                        };
                        let point = points[&site];
                        let definition = point.definition.ok_or(invalid("predicate definition"))?;
                        let node = if assignment.value.uses_memory() {
                            values.node(Value::Opaque(definition.0))?
                        } else {
                            values.expression(&assignment.value, point)?
                        };
                        values.ssa[definition.0] = Some(node);
                        values.definitions.insert(site, node);
                    }
                }
                if let Control::Branch {
                    condition: value, ..
                }
                | Control::Return(value) = &instruction.control
                {
                    let site = ssa::Site {
                        instruction: instruction.address,
                        assignment: None,
                    };
                    let node = if value.uses_memory() {
                        values.node(Value::Control(instruction.address))?
                    } else {
                        values.expression(value, points[&site])?
                    };
                    values.controls.insert(instruction.address, node);
                }
            }
        }
        Ok(values)
    }
    fn get(&self, id: ssa::ValueId) -> Result<usize, ssa::SsaError> {
        self.ssa
            .get(id.0)
            .copied()
            .flatten()
            .ok_or(invalid("predicate SSA order"))
    }
    fn expression(
        &mut self,
        expr: &Expr,
        point: &ssa::PointValues,
    ) -> Result<usize, ssa::SsaError> {
        fn walk(
            values: &mut Values,
            expr: &Expr,
            point: &ssa::PointValues,
            cursor: &mut usize,
        ) -> Result<usize, ssa::SsaError> {
            values.work.spend(1)?;
            let node = match expr {
                Expr::Const(n) => Value::Constant(*n),
                Expr::Register(reg) => {
                    let read = point
                        .reads
                        .get(*cursor)
                        .ok_or(invalid("predicate read count"))?;
                    *cursor += 1;
                    if read.register != *reg {
                        return Err(invalid("predicate read version"));
                    }
                    return values.get(read.value);
                }
                Expr::Unary(op, x) => Value::Unary(*op, walk(values, x, point, cursor)?),
                Expr::Binary(op, a, b) => Value::Binary(
                    *op,
                    walk(values, a, point, cursor)?,
                    walk(values, b, point, cursor)?,
                ),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => Value::Select(
                    walk(values, condition, point, cursor)?,
                    walk(values, taken, point, cursor)?,
                    walk(values, not_taken, point, cursor)?,
                ),
                Expr::Load { .. } => return Err(invalid("predicate load expansion")),
            };
            values.node(node)
        }
        let mut cursor = 0;
        let value = walk(self, expr, point, &mut cursor)?;
        if cursor != point.reads.len() {
            return Err(invalid("predicate unused read"));
        }
        Ok(value)
    }
    fn node(&mut self, mut node: Value) -> Result<usize, ssa::SsaError> {
        self.work.spend(1)?;
        node = match node {
            Value::Unary(op, a) => {
                if let Value::Constant(a) = self.nodes[a] {
                    Value::Constant(op.evaluate(a))
                } else {
                    Value::Unary(op, a)
                }
            }
            Value::Binary(op, a, b) => match (&self.nodes[a], &self.nodes[b]) {
                (Value::Constant(x), Value::Constant(y)) => Value::Constant(op.evaluate(*x, *y)),
                _ => {
                    if matches!(op, BinaryOp::Eq | BinaryOp::Ne) && b < a {
                        Value::Binary(op, b, a)
                    } else {
                        Value::Binary(op, a, b)
                    }
                }
            },
            other => other,
        };
        if let Some(&id) = self.intern.get(&node) {
            return Ok(id);
        }
        if self.nodes.len() >= 2 * ssa::MAX_NODES {
            return Err(ssa::SsaError::Unavailable("predicate value nodes"));
        }
        let id = self.nodes.len();
        self.intern.insert(node.clone(), id);
        self.nodes.push(node);
        Ok(id)
    }
}
