//! Independent bit-origin checker for proposed reaching-byte equalities.
//! It evaluates every source operand and register read into 64 individual
//! origins, instead of using the proposer's byte-window descent.
use super::*;
use crate::model::ir::BinaryOp as B;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bit {
    Unknown,
    Literal(bool),
    Register(ValueId, u8),
    Stored(Site, u8),
}
type Word = [Bit; 64];
fn opaque(value: ValueId) -> Word {
    std::array::from_fn(|bit| Bit::Register(value, bit as u8))
}
#[derive(Default)]
struct NormalValues {
    cache: BTreeMap<ValueId, Word>,
    active: BTreeSet<ValueId>,
}
impl NormalValues {
    fn word(
        &mut self,
        context: &Context<'_>,
        value: ValueId,
        budget: &mut Budget,
        depth: usize,
    ) -> Result<Word, SsaError> {
        budget.spend(1)?;
        if let Some(word) = self.cache.get(&value) {
            return Ok(*word);
        }
        if depth >= 32 || !self.active.insert(value) {
            return Ok(opaque(value));
        }
        let mut word =
            if let Some(Definition::Assignment { site, .. }) = context.graph.values.get(value.0) {
                let assignment = context
                    .assignment(*site)
                    .ok_or(invalid("bit origin producer"))?;
                if !matches!(assignment.destination, Place::Register(_)) {
                    return Err(invalid("bit origin producer destination"));
                }
                let point = context
                    .point(*site)
                    .ok_or(invalid("bit origin producer point"))?;
                let mut cursor = 0;
                let word = expression(
                    &assignment.value,
                    context,
                    point,
                    &mut cursor,
                    budget,
                    self,
                    depth + 1,
                )?;
                if cursor != point.reads.len() {
                    return Err(invalid("bit origin producer reads"));
                }
                word
            } else {
                opaque(value)
            };
        // An unsupported bit still denotes this exact SSA result, rather
        // than equating unrelated unknown expressions or re-reading memory.
        for (bit, origin) in word.iter_mut().enumerate() {
            if *origin == Bit::Unknown {
                *origin = Bit::Register(value, bit as u8);
            }
        }
        self.active.remove(&value);
        self.cache.insert(value, word);
        Ok(word)
    }
}
#[derive(Default)]
pub(super) struct Values {
    stores: BTreeMap<Site, Word>,
    values: NormalValues,
}
impl Values {
    pub(super) fn matches(
        &mut self,
        context: &Context<'_>,
        key: Key,
        writers: &[ReachingWriter],
        budget: &mut Budget,
    ) -> Result<bool, SsaError> {
        if u32::from(key.start) + key.width.bits() > 64 {
            return Ok(false);
        }
        let expected = match key.value {
            SavedValue::Register(value) => self.values.word(context, value, budget, 0)?,
            SavedValue::Stored(site) => self.stored(context, site, budget)?,
        };
        for byte in 0..key.width.bytes() {
            let mut found = false;
            for writer in writers {
                budget.spend(1)?;
                let assignment = context
                    .assignment(writer.site)
                    .ok_or(invalid("byte origin store"))?;
                if !matches!(assignment.destination, Place::Memory { width, .. } if width == writer.width)
                {
                    return Err(invalid("byte origin source width"));
                }
                let word = self.stored(context, writer.site, budget)?;
                for source in 0..writer.width.bytes() {
                    if writer.sources[byte] & (1 << source) == 0 {
                        continue;
                    }
                    found = true;
                    for bit in 0..8 {
                        budget.spend(1)?;
                        if word[source * 8 + bit] == Bit::Unknown
                            || word[source * 8 + bit]
                                != expected[usize::from(key.start) + byte * 8 + bit]
                        {
                            return Ok(false);
                        }
                    }
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn stored(
        &mut self,
        context: &Context<'_>,
        site: Site,
        budget: &mut Budget,
    ) -> Result<Word, SsaError> {
        budget.spend(1)?;
        if let Some(word) = self.stores.get(&site) {
            return Ok(*word);
        }
        let point = context.point(site).ok_or(invalid("byte origin point"))?;
        let assignment = context
            .assignment(site)
            .ok_or(invalid("byte origin store"))?;
        let Place::Memory { address, .. } = &assignment.destination else {
            return Err(invalid("byte origin destination"));
        };
        let mut cursor = 0;
        expression(
            address,
            context,
            point,
            &mut cursor,
            budget,
            &mut self.values,
            0,
        )?;
        let mut word = expression(
            &assignment.value,
            context,
            point,
            &mut cursor,
            budget,
            &mut self.values,
            0,
        )?;
        if cursor != point.reads.len() {
            return Err(invalid("byte origin read count"));
        }
        // A pure Store RHS can be captured after this exact Store succeeds.
        // Distinct Store expressions retain distinct opaque result bits.
        for (bit, origin) in word.iter_mut().enumerate() {
            if *origin == Bit::Unknown {
                *origin = Bit::Stored(site, bit as u8);
            }
        }
        self.stores.insert(site, word);
        Ok(word)
    }
}
fn constant(word: &Word) -> Option<u64> {
    let mut n = 0;
    for (i, bit) in word.iter().enumerate() {
        match bit {
            Bit::Literal(true) => n |= 1u64 << i,
            Bit::Literal(false) => {}
            _ => return None,
        }
    }
    Some(n)
}
fn expression(
    e: &Expr,
    context: &Context<'_>,
    point: &PointValues,
    cursor: &mut usize,
    budget: &mut Budget,
    values: &mut NormalValues,
    depth: usize,
) -> Result<Word, SsaError> {
    budget.spend(64)?;
    let no = Bit::Literal(false);
    let yes = Bit::Literal(true);
    let unknown = [Bit::Unknown; 64];
    Ok(match e {
        Expr::Const(n) => std::array::from_fn(|bit| Bit::Literal(n & (1u64 << bit) != 0)),
        Expr::Register(register) => {
            let read = point
                .reads
                .get(*cursor)
                .ok_or(invalid("byte origin register index"))?;
            *cursor += 1;
            if read.register != *register {
                return Err(invalid("byte origin register"));
            }
            let value = *context
                .aliases
                .get(read.value.0)
                .ok_or(invalid("byte origin value class"))?;
            values.word(context, value, budget, depth + 1)?
        }
        Expr::Unary(op, value) => {
            let value = expression(value, context, point, cursor, budget, values, depth + 1)?;
            match op {
                UnaryOp::SignExtend(width) => {
                    std::array::from_fn(|bit| value[bit.min(width.bits() as usize - 1)])
                }
                UnaryOp::Extract { start, width } => std::array::from_fn(|bit| {
                    let source = usize::from(*start) + bit;
                    if bit < width.bits() as usize && source < 64 {
                        value[source]
                    } else {
                        no
                    }
                }),
            }
        }
        Expr::Load { address, width } => {
            expression(address, context, point, cursor, budget, values, depth + 1)?;
            std::array::from_fn(|bit| {
                if bit < width.bits() as usize {
                    Bit::Unknown
                } else {
                    no
                }
            })
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            expression(condition, context, point, cursor, budget, values, depth + 1)?;
            let a = expression(taken, context, point, cursor, budget, values, depth + 1)?;
            let b = expression(not_taken, context, point, cursor, budget, values, depth + 1)?;
            std::array::from_fn(|i| if a[i] == b[i] { a[i] } else { Bit::Unknown })
        }
        Expr::Binary(op, left, right) => {
            let a = expression(left, context, point, cursor, budget, values, depth + 1)?;
            let b = expression(right, context, point, cursor, budget, values, depth + 1)?;
            match op {
                B::And => std::array::from_fn(|i| {
                    if a[i] == no || b[i] == no {
                        no
                    } else if a[i] == yes {
                        b[i]
                    } else if b[i] == yes || a[i] == b[i] {
                        a[i]
                    } else {
                        Bit::Unknown
                    }
                }),
                B::Or => std::array::from_fn(|i| {
                    if a[i] == yes || b[i] == yes {
                        yes
                    } else if a[i] == no {
                        b[i]
                    } else if b[i] == no || a[i] == b[i] {
                        a[i]
                    } else {
                        Bit::Unknown
                    }
                }),
                B::Xor => std::array::from_fn(|i| {
                    if a[i] == no {
                        b[i]
                    } else if b[i] == no {
                        a[i]
                    } else if a[i] != Bit::Unknown && a[i] == b[i] {
                        no
                    } else {
                        Bit::Unknown
                    }
                }),
                B::Insert { start, width } => std::array::from_fn(|bit| {
                    let start = usize::from(*start);
                    if bit >= start && bit - start < width.bits() as usize {
                        b[bit - start]
                    } else {
                        a[bit]
                    }
                }),
                B::Shl | B::Shr | B::AShr => {
                    if let Some(count) = constant(&b) {
                        let count = (count & 63) as usize;
                        std::array::from_fn(|bit| match op {
                            B::Shl if bit >= count => a[bit - count],
                            B::Shr | B::AShr if bit + count < 64 => a[bit + count],
                            B::AShr => a[63],
                            _ => no,
                        })
                    } else {
                        unknown
                    }
                }
                _ => unknown,
            }
        }
    })
}
