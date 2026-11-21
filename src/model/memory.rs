//! Validated virtual ranges over a packed byte backing. Gaps occupy no bytes.

pub const READ: u8 = 4;
pub const WRITE: u8 = 2;
pub const EXECUTE: u8 = 1;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Region {
    pub address: u64,
    pub size: u64,
    pub offset: usize,
    /// ELF PF_R/PF_W/PF_X bit positions.
    pub permissions: u8,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Layout {
    regions: Vec<Region>,
    size: usize,
}
impl Layout {
    /// Regions are ordered, nonoverlapping virtual ranges. Their backing ranges
    /// partition the whole packed image in that same order, without aliases.
    pub fn new(regions: Vec<Region>, size: usize) -> Result<Self, &'static str> {
        if regions.is_empty() || regions.len() > 4097 {
            return Err("missing or excessive memory regions");
        }
        let mut used = 0usize;
        let mut previous_end = None;
        for region in &regions {
            let end = region
                .address
                .checked_add(region.size)
                .ok_or("virtual range overflow")?;
            if region.size == 0
                || region.permissions & !7 != 0
                || previous_end.is_some_and(|p| region.address < p)
                || region.offset != used
            {
                return Err("invalid virtual or backing region");
            }
            used = used
                .checked_add(usize::try_from(region.size).map_err(|_| "region exceeds host")?)
                .ok_or("backing range overflow")?;
            if used > size {
                return Err("region exceeds backing");
            }
            previous_end = Some(end);
        }
        if used != size {
            return Err("regions do not cover backing");
        }
        Ok(Self { regions, size })
    }
    pub fn regions(&self) -> &[Region] {
        &self.regions
    }
    pub fn size(&self) -> usize {
        self.size
    }

    /// A range can cross adjacent segments when every byte grants the requested
    /// permissions. Empty ranges use closed mapped intervals and do not access
    /// bytes. A zero permission mask is for loader initialization/inspection.
    pub fn offset(&self, address: u64, width: usize, permissions: u8) -> Option<usize> {
        let stop = address.checked_add(u64::try_from(width).ok()?)?;
        for (index, region) in self.regions.iter().enumerate() {
            let end = region.address + region.size;
            if address < region.address {
                return None;
            }
            if width == 0 && address <= end {
                return region
                    .offset
                    .checked_add((address - region.address) as usize);
            }
            if address >= end {
                continue;
            }
            let offset = region.offset + (address - region.address) as usize;
            let mut covered = address;
            for region in &self.regions[index..] {
                if region.address > covered || region.permissions & permissions != permissions {
                    return None;
                }
                covered = region.address + region.size;
                if stop <= covered {
                    return Some(offset);
                }
            }
            return None;
        }
        None
    }

    /// Contiguous accessible bytes to the next gap or permission boundary.
    pub fn available(&self, address: u64, permissions: u8) -> Option<usize> {
        let index = self
            .regions
            .partition_point(|r| r.address + r.size <= address);
        let first = self.regions.get(index)?;
        if address < first.address || first.permissions & permissions != permissions {
            return None;
        }
        let mut end = first.address + first.size;
        for region in &self.regions[index + 1..] {
            if region.address != end || region.permissions & permissions != permissions {
                break;
            }
            end = region.address + region.size;
        }
        usize::try_from(end - address).ok()
    }
}

#[derive(Clone, Copy)]
pub struct View<'a> {
    pub base: u64,
    pub bytes: &'a [u8],
    pub layout: Option<&'a Layout>,
}
impl<'a> View<'a> {
    pub fn offset(self, address: u64, width: usize, permissions: u8) -> Option<usize> {
        if let Some(layout) = self.layout {
            return layout.offset(address, width, permissions);
        }
        if width != 0 {
            address.checked_add((width - 1) as u64)?;
        }
        let offset = usize::try_from(address.checked_sub(self.base)?).ok()?;
        (offset.checked_add(width)? <= self.bytes.len()).then_some(offset)
    }
    pub fn read(self, address: u64, width: usize) -> Option<&'a [u8]> {
        let offset = self.offset(address, width, READ)?;
        self.bytes.get(offset..offset.checked_add(width)?)
    }
}
