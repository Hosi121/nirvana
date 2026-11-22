use super::*;
use crate::model::ir::{Control, Expr, Place};
use std::collections::BTreeMap;

struct Cursor<'a> {
    point: Option<&'a ssa::PointValues>,
    next_read: usize,
}
impl Cursor<'_> {
    fn read(&mut self, reg: Reg) -> Result<Option<ssa::ValueId>, Error> {
        let Some(point) = self.point else {
            return Ok(None);
        };
        let read = point
            .reads
            .get(self.next_read)
            .ok_or(Error::Invalid("missing SSA read"))?;
        if read.register != reg {
            return Err(Error::Invalid("SSA read order"));
        }
        self.next_read += 1;
        Ok(Some(read.value))
    }
    fn finish(&self) -> Result<(), Error> {
        if self.point.is_some_and(|p| self.next_read != p.reads.len()) {
            Err(Error::Invalid("unused SSA reads"))
        } else {
            Ok(())
        }
    }
}
struct Builder {
    next_value: usize,
    source_values: usize,
}
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum Key {
    Pure(Pure),
    Read(StorageId, Option<ssa::ValueId>),
}
impl Builder {
    fn region(
        &mut self,
        expr: &Expr,
        origin: Origin,
        cursor: &mut Cursor<'_>,
    ) -> Result<Region, Error> {
        let mut bindings = Vec::new();
        let result = self.value(expr, origin, cursor, &mut bindings, &mut BTreeMap::new())?;
        Ok(Region {
            origin,
            bindings,
            result,
        })
    }
    fn value(
        &mut self,
        expr: &Expr,
        origin: Origin,
        cursor: &mut Cursor<'_>,
        bindings: &mut Vec<Binding>,
        intern: &mut BTreeMap<Key, ValueId>,
    ) -> Result<ValueId, Error> {
        self.source_values += 1;
        let operation = match expr {
            Expr::Const(n) => Operation::Pure(Pure::Constant(*n)),
            Expr::Register(reg) => Operation::ReadStorage {
                storage: StorageId(reg.0),
                version: cursor.read(*reg)?,
            },
            Expr::Unary(op, input) => {
                let input = self.value(input, origin, cursor, bindings, intern)?;
                Operation::Pure(Pure::Unary(*op, input))
            }
            Expr::Binary(op, a, b) => {
                let a = self.value(a, origin, cursor, bindings, intern)?;
                let b = self.value(b, origin, cursor, bindings, intern)?;
                Operation::Pure(Pure::Binary(*op, a, b))
            }
            Expr::Load { address, width } => {
                let address = self.value(address, origin, cursor, bindings, intern)?;
                Operation::Load {
                    address,
                    width: *width,
                }
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.value(condition, origin, cursor, bindings, intern)?;
                Operation::Select {
                    condition,
                    taken: self.region(taken, origin, cursor)?,
                    not_taken: self.region(not_taken, origin, cursor)?,
                }
            }
        };
        let key = match &operation {
            Operation::Pure(pure) => Some(Key::Pure(pure.clone())),
            Operation::ReadStorage { storage, version } => Some(Key::Read(*storage, *version)),
            Operation::Load { .. } | Operation::KnownLoad { .. } | Operation::Select { .. } => None,
        };
        if let Some(id) = key.as_ref().and_then(|key| intern.get(key)) {
            return Ok(*id);
        }
        if self.next_value >= ssa::MAX_NODES {
            return Err(Error::Limit("values"));
        }
        let id = ValueId(self.next_value);
        self.next_value += 1;
        if let Some(key) = key {
            intern.insert(key, id);
        }
        bindings.push(Binding {
            id,
            origin,
            operation,
        });
        Ok(id)
    }
}

pub(super) fn build(source: &Program) -> Result<Function, Error> {
    ssa::preflight(source, &mut ssa::Budget::new()).map_err(Error::Ssa)?;
    let graph = SsaFunction::build(source).ok_or(Error::Limit("register SSA"))?;
    let points: BTreeMap<_, _> = graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect();
    let mut builder = Builder {
        next_value: 0,
        source_values: 0,
    };
    let mut blocks = Vec::new();
    for block in source.cfg().blocks() {
        let mut steps = Vec::new();
        let instructions = &source.instructions()[block.instructions.clone()];
        for instruction in instructions {
            let mut statements = Vec::new();
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                let site = ssa::Site {
                    instruction: instruction.address,
                    assignment: Some(index),
                };
                let mut cursor = Cursor {
                    point: points.get(&site).copied(),
                    next_read: 0,
                };
                let value_origin = Origin {
                    site,
                    operand: Operand::Value,
                };
                let statement = match &assignment.destination {
                    Place::Register(reg) => Statement::WriteStorage {
                        storage: StorageId(reg.0),
                        version: cursor.point.and_then(|p| p.definition),
                        value: builder.region(&assignment.value, value_origin, &mut cursor)?,
                    },
                    Place::Memory { address, width } => Statement::Store {
                        address: builder.region(
                            address,
                            Origin {
                                site,
                                operand: Operand::Address,
                            },
                            &mut cursor,
                        )?,
                        width: *width,
                        value: builder.region(&assignment.value, value_origin, &mut cursor)?,
                    },
                };
                cursor.finish()?;
                statements.push(statement);
            }
            steps.push(Step {
                address: instruction.address,
                size: instruction.size,
                statements,
            });
        }
        let last = instructions.last().ok_or(Error::Invalid("empty block"))?;
        let site = ssa::Site {
            instruction: last.address,
            assignment: None,
        };
        let origin = Origin {
            site,
            operand: Operand::Control,
        };
        let mut cursor = Cursor {
            point: points.get(&site).copied(),
            next_read: 0,
        };
        let end = last.address + u64::from(last.size);
        let terminator = match &last.control {
            Control::Next => Terminator::Fallthrough(end),
            Control::Jump(target) => Terminator::Jump(*target),
            Control::Branch { condition, target } => Terminator::Branch {
                condition: builder.region(condition, origin, &mut cursor)?,
                taken: *target,
                not_taken: end,
            },
            Control::Return(value) => {
                Terminator::Return(builder.region(value, origin, &mut cursor)?)
            }
        };
        cursor.finish()?;
        blocks.push(Block {
            address: block.start,
            steps,
            terminator,
        });
    }
    Ok(Function {
        entry: source.cfg().block(source.cfg().entry()).start,
        storages: (0..source.register_count()).map(Reg).collect(),
        blocks,
        ssa: graph,
        value_count: builder.next_value,
        source_value_count: builder.source_values,
    })
}
