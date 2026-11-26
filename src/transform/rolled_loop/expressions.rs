use super::*;

pub(super) fn has_lane(expression: &PatternExpr) -> bool {
    match expression {
        PatternExpr::Lane => true,
        PatternExpr::Unary(_, v) => has_lane(v),
        PatternExpr::Binary(_, a, b) => has_lane(a) || has_lane(b),
        PatternExpr::Select(c, a, b) => has_lane(c) || has_lane(a) || has_lane(b),
        _ => false,
    }
}
pub(super) fn index(expression: &PatternExpr) -> Option<&PatternExpr> {
    match expression {
        PatternExpr::Binary(op, a, b) => index(a).or_else(|| index(b)).or_else(|| {
            (matches!(op, BinaryOp::Add | BinaryOp::Sub) && has_lane(expression))
                .then_some(expression)
        }),
        PatternExpr::Unary(_, v) => index(v),
        _ => None,
    }
}
pub(super) fn at_offset(expression: &PatternExpr, offset: u64) -> PatternExpr {
    match expression {
        PatternExpr::Lane => PatternExpr::Constant(offset),
        PatternExpr::Unary(op, v) => PatternExpr::Unary(*op, Box::new(at_offset(v, offset))),
        PatternExpr::Binary(op, a, b) => PatternExpr::Binary(
            *op,
            Box::new(at_offset(a, offset)),
            Box::new(at_offset(b, offset)),
        ),
        PatternExpr::Select(c, a, b) => PatternExpr::Select(
            Box::new(at_offset(c, offset)),
            Box::new(at_offset(a, offset)),
            Box::new(at_offset(b, offset)),
        ),
        _ => expression.clone(),
    }
}
pub(super) fn instantiate(
    expression: &PatternExpr,
    discovery: &Discovery,
    sites: &[Site],
    counter: Reg,
) -> Result<Expr, Error> {
    Ok(match expression {
        PatternExpr::Constant(value) => Expr::Const(*value),
        PatternExpr::Lane => Expr::Register(counter),
        PatternExpr::Value(value) => {
            let reg = discovery
                .available_register(sites[0], *value)
                .ok_or(Error::Pattern)?;
            if sites
                .iter()
                .any(|&site| discovery.available_register(site, *value) != Some(reg))
            {
                return Err(Error::Pattern);
            }
            Expr::Register(reg)
        }
        PatternExpr::Unary(op, v) => Expr::unary(*op, instantiate(v, discovery, sites, counter)?),
        PatternExpr::Binary(op, a, b) => {
            let (a, b) = if matches!(
                op,
                BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor
            ) && matches!(**a, PatternExpr::Lane)
            {
                (b, a)
            } else {
                (a, b)
            };
            Expr::binary(
                *op,
                instantiate(a, discovery, sites, counter)?,
                instantiate(b, discovery, sites, counter)?,
            )
        }
        PatternExpr::Select(c, a, b) => Expr::select(
            instantiate(c, discovery, sites, counter)?,
            instantiate(a, discovery, sites, counter)?,
            instantiate(b, discovery, sites, counter)?,
        ),
        _ => return Err(Error::Pattern),
    })
}
pub(super) fn address_selector(
    expression: &PatternExpr,
    discovery: &Discovery,
    sites: &[Site],
) -> Option<(Reg, u8)> {
    fn values(expression: &PatternExpr, found: &mut BTreeSet<crate::dataflow::ssa::ValueId>) {
        match expression {
            PatternExpr::Value(value) => {
                found.insert(*value);
            }
            PatternExpr::Unary(_, value) => values(value, found),
            PatternExpr::Binary(_, a, b) => {
                values(a, found);
                values(b, found);
            }
            PatternExpr::Select(c, a, b) => {
                values(c, found);
                values(a, found);
                values(b, found);
            }
            _ => {}
        }
    }
    if let PatternExpr::Binary(BinaryOp::And, a, b) = expression {
        let bounded = match (&**a, &**b) {
            (value, PatternExpr::Constant(mask)) | (PatternExpr::Constant(mask), value) => {
                Some((value, *mask))
            }
            _ => None,
        };
        if let Some((value, mask)) = bounded {
            let bits = mask.trailing_ones() as u8;
            if (1..=4).contains(&bits) && mask == (1u64 << bits) - 1 && has_lane(value) {
                let mut found = BTreeSet::new();
                values(value, &mut found);
                if found.len() == 1 {
                    let value = *found.first()?;
                    let reg = discovery.available_register(sites[0], value)?;
                    if sites
                        .iter()
                        .all(|&site| discovery.available_register(site, value) == Some(reg))
                    {
                        return Some((reg, bits));
                    }
                }
            }
        }
    }
    match expression {
        PatternExpr::Unary(_, value) => address_selector(value, discovery, sites),
        PatternExpr::Binary(_, a, b) => {
            address_selector(a, discovery, sites).or_else(|| address_selector(b, discovery, sites))
        }
        _ => None,
    }
}
