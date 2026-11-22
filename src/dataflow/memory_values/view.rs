//! Checked, owned descriptors for consumers above the executable IR. IDs refer
//! to one plan; SSA versions and capture points refer to its supplied source.
use super::analyze::Context;
use super::*;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SnapshotId(pub usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Snapshot {
    pub origin: SavedValue,
    pub point: CapturePoint,
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SavedSlice {
    pub snapshot: SnapshotId,
    pub start: u8,
    pub width: Width,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SavedLoad {
    pub site: Site,
    pub definition: ValueId,
    pub slice: SavedSlice,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SavedValueView {
    pub snapshots: Vec<Snapshot>,
    pub loads: Vec<SavedLoad>,
    /// Closed saved-slice invariants, including equal phi inputs.
    pub values: Vec<Option<SavedSlice>>,
    /// Values the checked rewrite substitutes; trivial source anchors stay reads.
    pub substitutions: BTreeMap<ValueId, SavedSlice>,
}
impl MemoryValuePlan {
    /// Recheck source proofs, actual rewriting and capture initialization before
    /// publishing descriptors. This also works for a retained plan on a new input.
    pub fn inspect(&self, source: &Program) -> Result<SavedValueView, SsaError> {
        let context =
            Context::new(source).ok_or(SsaError::Unavailable("saved value view source"))?;
        verify::plan(source, self, &context)?;
        let (candidate, _) = rewrite::construct(source, self, &context)
            .ok_or(SsaError::Unavailable("saved value view rewrite"))?;
        verify::check(source, self, &candidate, &context)?;
        let ids: BTreeMap<_, _> = self
            .captures
            .iter()
            .enumerate()
            .map(|(n, capture)| (capture.value, SnapshotId(n)))
            .collect();
        let slice = |key: Key| -> Result<SavedSlice, SsaError> {
            Ok(SavedSlice {
                snapshot: *ids
                    .get(&key.value)
                    .ok_or(SsaError::Malformed("saved snapshot ID"))?,
                start: key.start,
                width: key.width,
            })
        };
        let values = self
            .facts
            .iter()
            .map(|key| key.map(slice).transpose())
            .collect::<Result<Vec<_>, _>>()?;
        let substitutions = rewrite::mapping(self, &context)
            .ok_or(SsaError::Malformed("saved value view mapping"))?
            .keys()
            .map(|&id| {
                Ok((
                    id,
                    values[id.0].ok_or(SsaError::Malformed("saved value view fact"))?,
                ))
            })
            .collect::<Result<_, SsaError>>()?;
        Ok(SavedValueView {
            snapshots: self
                .captures
                .iter()
                .map(|c| Snapshot {
                    origin: c.value,
                    point: c.point,
                })
                .collect(),
            loads: self
                .proofs
                .iter()
                .map(|p| {
                    Ok(SavedLoad {
                        site: p.site,
                        definition: context
                            .point(p.site)
                            .and_then(|p| p.definition)
                            .ok_or(SsaError::Malformed("saved load result"))?,
                        slice: slice(p.key)?,
                    })
                })
                .collect::<Result<_, SsaError>>()?,
            values,
            substitutions,
        })
    }
}
