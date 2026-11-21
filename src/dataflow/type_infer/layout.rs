//! Tentative field and array grouping from exact access evidence.
use super::*;
use std::collections::BTreeMap;
const MAX_ACCESSES: usize = 16384;
const MAX_OVERLAP_PAIRS: usize = 65536;
struct Budget(usize);
impl Budget {
    fn spend(&mut self, n: usize) -> Result<(), ()> {
        self.0 = self.0.checked_sub(n).ok_or(())?;
        Ok(())
    }
}
pub(crate) fn collect(accesses: &[MemoryAccess]) -> Option<Vec<LayoutCandidate>> {
    if accesses.len() > MAX_ACCESSES {
        return None;
    }
    let mut budget = Budget(crate::dataflow::ssa::MAX_WORK);
    let mut groups = BTreeMap::<ValueId, LayoutCandidate>::new();
    for access in accesses {
        budget.spend(1).ok()?;
        let AddressShape::Base {
            base,
            offset,
            index,
        } = access.address
        else {
            continue;
        };
        let group = groups.entry(base).or_insert_with(|| LayoutCandidate {
            base,
            fields: Vec::new(),
            arrays: Vec::new(),
            overlaps: Vec::new(),
            ambiguous_intervals: false,
        });
        group.ambiguous_intervals |= (offset as i64)
            .checked_add(access.width.bytes() as i64)
            .is_none();
        let (reads, writes) = match access.kind {
            AccessKind::Read => (true, false),
            AccessKind::Write => (false, true),
        };
        if let Some(index) = index {
            budget.spend(group.arrays.len()).ok()?;
            let slot = group.arrays.iter().position(|f| {
                f.offset == offset && f.stride == index.stride && f.width == access.width
            });
            let slot = slot.unwrap_or_else(|| {
                group.arrays.push(ArrayCandidate {
                    offset,
                    stride: index.stride,
                    width: access.width,
                    indices: Vec::new(),
                    loaded_values: Vec::new(),
                    reads: false,
                    writes: false,
                });
                group.arrays.len() - 1
            });
            let field = &mut group.arrays[slot];
            budget
                .spend(field.indices.len() + field.loaded_values.len())
                .ok()?;
            if !field.indices.contains(&index.value) {
                field.indices.push(index.value);
            }
            if let Some(value) = access.result
                && !field.loaded_values.contains(&value)
            {
                field.loaded_values.push(value);
            }
            field.reads |= reads;
            field.writes |= writes;
        } else {
            budget.spend(group.fields.len()).ok()?;
            let slot = group
                .fields
                .iter()
                .position(|f| f.offset == offset && f.width == access.width);
            let slot = slot.unwrap_or_else(|| {
                group.fields.push(FieldCandidate {
                    offset,
                    width: access.width,
                    loaded_values: Vec::new(),
                    reads: false,
                    writes: false,
                });
                group.fields.len() - 1
            });
            let field = &mut group.fields[slot];
            budget.spend(field.loaded_values.len()).ok()?;
            if let Some(value) = access.result
                && !field.loaded_values.contains(&value)
            {
                field.loaded_values.push(value);
            }
            field.reads |= reads;
            field.writes |= writes;
        }
    }
    let mut pairs = 0usize;
    for group in groups.values_mut() {
        let mut intervals = Vec::with_capacity(group.fields.len());
        for field in &group.fields {
            budget.spend(1).ok()?;
            let start = field.offset as i64;
            let end = start.checked_add(field.width.bytes() as i64);
            group.ambiguous_intervals |= end.is_none();
            intervals.push(end.map(|end| (start, end)));
        }
        for (a, left) in intervals.iter().enumerate() {
            for (b, right) in intervals.iter().enumerate().skip(a + 1) {
                budget.spend(1).ok()?;
                if let (Some((l0, l1)), Some((r0, r1))) = (left, right)
                    && l0 < r1
                    && r0 < l1
                {
                    pairs = pairs.checked_add(1)?;
                    if pairs > MAX_OVERLAP_PAIRS {
                        return None;
                    }
                    group.overlaps.push((a, b));
                }
            }
        }
    }
    Some(groups.into_values().collect())
}
