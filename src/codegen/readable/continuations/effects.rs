//! Effects of frozen C fragments, after storage names and views are fixed.
//! The small pure grammar borrows its operands from the printed expression;
//! contextual remainder/address substitutions and memory reads are barriers.
use super::*;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Effect {
    Store {
        span: order::Span,
        reads: BTreeSet<String>,
    },
    Local {
        written: String,
        reads: BTreeSet<String>,
    },
}

fn reads(printer: &Printer<'_>, expression: &Expr) -> Option<BTreeSet<String>> {
    let mut result = BTreeSet::new();
    let mut pending = vec![expression];
    let mut budget = MAX_ITEMS;
    while let Some(value) = pending.pop() {
        budget = budget.checked_sub(1)?;
        match value {
            Expr::Const(_) => {}
            Expr::Register(reg) if reg.0 < printer.first_temporary => {
                result.insert(printer.names.get(&reg.0)?.clone());
            }
            Expr::Binary(BinaryOp::Add | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor, a, b) => {
                pending.extend([a.as_ref(), b.as_ref()]);
            }
            _ => return None,
        }
    }
    Some(result)
}

pub(super) fn describe(printer: &Printer<'_>, node: &Node) -> Option<Effect> {
    let Node::Step {
        address: pc,
        assignments,
    } = node
    else {
        return None;
    };
    let [assignment] = assignments.as_slice() else {
        return None;
    };
    let reads = reads(printer, &assignment.value)?;
    match &assignment.destination {
        Place::Memory { .. } => Some(Effect::Store {
            span: order::store(printer, node)?,
            reads,
        }),
        Place::Register(reg) => {
            if !printer.read.contains(&reg.0)
                || reg.0 >= printer.first_temporary
                || printer.address_uses.contains(&reg.0)
                || printer
                    .address_value(*reg, Some((*pc, 0)), &assignment.value)
                    .is_some()
            {
                return None;
            }
            Some(Effect::Local {
                written: printer.names.get(&reg.0)?.clone(),
                reads,
            })
        }
    }
}

pub(super) fn witnessed(effect: Effect, facts: &order::Facts) -> Option<Effect> {
    if let Effect::Store { span, .. } = &effect
        && !facts.contains(*span)
    {
        return None;
    }
    Some(effect)
}

// A canonical direction only: stores ascend by offset, and independent scalar
// updates precede stores. Local/local order and all effect barriers remain.
fn inversion(a: &Effect, b: &Effect) -> bool {
    match (a, b) {
        (Effect::Store { span: a, .. }, Effect::Store { span: b, .. }) => {
            a.offset > b.offset && a.disjoint(*b)
        }
        (Effect::Store { reads, .. }, Effect::Local { written, .. }) => !reads.contains(written),
        _ => false,
    }
}

pub(super) fn propose(
    nodes: &[Node],
    facts: &order::Facts,
    effect: &impl Fn(&Node) -> Option<Effect>,
) -> Option<(Vec<Node>, EffectOrderEvidence)> {
    let tag = |node: &Node| effect(node).and_then(|e| witnessed(e, facts));
    let swapped = |a: &Effect, b: &Effect| {
        inversion(a, b).then_some({
            if matches!(b, Effect::Local { .. }) {
                permutations::Swap::Local
            } else {
                permutations::Swap::Store
            }
        })
    };
    let (result, counts) = permutations::propose(nodes, facts.prefix_len(), &tag, &swapped)?;
    (counts.locals > 0).then_some((
        result,
        EffectOrderEvidence {
            prefix_nodes: facts.prefix_len(),
            range_witnesses: facts.range_count(),
            store_pairs: counts.stores,
            local_pairs: counts.locals,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_footprints_use_c_names_after_coalescing_and_reject_contextual_reads() {
        let program = Program::new(
            0,
            4,
            vec![crate::model::ir::IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            }],
        )
        .unwrap();
        let printer = Printer {
            source_program: &program,
            context_remainders: None,
            graph_remainders: None,
            names: BTreeMap::from([
                (0, "address".into()),
                (1, "shared".into()),
                (2, "shared".into()),
                (3, "other".into()),
            ]),
            read: BTreeSet::from([0, 1, 2, 3]),
            views: None,
            first_temporary: 4,
            widths: BTreeMap::new(),
            address_types: BTreeMap::new(),
            address_uses: BTreeSet::from([0]),
            recover_objects: false,
            compact_memory: true,
            slots: BTreeMap::new(),
            initial_slots: vec![],
            declarations: Rc::new(DeclarationPlan::default()),
        };
        let r = |i| Expr::Register(Reg(i));
        let step = |reg, value| Node::Step {
            address: 0,
            assignments: vec![Assignment {
                destination: Reg(reg).into(),
                value,
            }],
        };
        let update = step(2, Expr::binary(BinaryOp::Add, r(1), Expr::Const(17)));
        let Some(Effect::Local { written, reads }) = describe(&printer, &update) else {
            panic!()
        };
        assert_eq!(written, "shared");
        assert_eq!(reads, BTreeSet::from(["shared".into()]));
        for value in [
            Expr::load(r(0), Width::U64),
            Expr::binary(BinaryOp::Sub, r(1), r(3)),
            Expr::select(r(1), r(2), r(3)),
            r(4),
        ] {
            assert!(describe(&printer, &step(2, value)).is_none());
        }
        assert!(
            describe(
                &printer,
                &step(0, Expr::binary(BinaryOp::Add, r(0), Expr::Const(8)))
            )
            .is_none()
        );
    }
}
