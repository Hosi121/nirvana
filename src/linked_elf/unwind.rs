//! Optional numeric-entry catalog. Symbol selection never depends on unwind data.
use super::*;

pub(super) fn catalog(
    mapping: &Mapping<'_>,
    sections: &[Section],
    relocations: &[Relocation],
    symbols: Vec<FunctionSymbol>,
    work: &mut Work,
) -> Result<Vec<FunctionSymbol>> {
    let mut catalog: BTreeMap<_, _> = symbols.into_iter().map(|s| (s.address, s)).collect();
    let mut previous_end = 0;
    for function in catalog.values() {
        if function.address < previous_end {
            return Err(BinaryError::AmbiguousFunctionAddress(function.address));
        }
        previous_end = end(function.address, function.size)?;
    }
    let name_index = u16_at(mapping.data, 62)? as usize;
    if name_index == 0 {
        return Ok(catalog.into_values().collect());
    }
    let names = sections
        .get(name_index)
        .filter(|s| s.kind == 3)
        .ok_or_else(|| invalid("section names require a string table"))?;
    if names.size > MAX_MEMORY {
        return Err(BinaryError::Limit("section names exceed 16 MiB"));
    }
    let names = range(mapping.data, names.offset, names.size)?;
    if names.first() != Some(&0) || names.last() != Some(&0) {
        return Err(invalid("section names lack boundary NUL"));
    }
    let mut frame = None;
    for section in sections {
        if work.name(names, section.name)? == ".eh_frame" && frame.replace(section).is_some() {
            return Err(invalid("multiple .eh_frame sections"));
        }
    }
    let Some(frame) = frame else {
        return Ok(catalog.into_values().collect());
    };
    if frame.kind != 1 || frame.flags & 2 == 0 || frame.flags & 0x800 != 0 {
        return Err(unsupported(
            ".eh_frame requires allocated uncompressed PROGBITS",
        ));
    }
    if frame.size == 0 {
        return Ok(catalog.into_values().collect());
    }
    if frame.size > 4 * 1024 * 1024 {
        return Err(BinaryError::Limit(".eh_frame exceeds 4 MiB"));
    }
    if mapping.offset(frame.address, frame.size)? != frame.offset {
        return Err(invalid(".eh_frame disagrees with PT_LOAD file mapping"));
    }
    let frame_end = end(frame.address, frame.size)?;
    if relocations
        .iter()
        .any(|r| r.address < frame_end && r.address + 8 > frame.address)
    {
        return Err(unsupported("dynamic relocations within .eh_frame"));
    }
    let bytes = mapping.bytes(frame.address, frame.size)?;
    work.use_bytes(bytes.len())?;
    let mut regions = crate::eh_frame::read(bytes, frame.address).map_err(BinaryError::Unwind)?;
    regions.sort_by_key(|r| (r.address, r.size, r.record));
    for region in regions {
        if region.size > MAX_FUNCTION {
            return Err(BinaryError::Limit("unwind region exceeds 1 MiB"));
        }
        if !mapping.contains(region.address, region.size, true) {
            return Err(invalid("unwind code region is outside executable PT_LOAD"));
        }
        mapping.bytes(region.address, region.size)?;
        let stop = end(region.address, region.size)?;
        if let Some((_, old)) = catalog.range(..=region.address).next_back()
            && end(old.address, old.size)? > region.address
        {
            // Sized symbols can contain multiple cold/hot CFI fragments.
            if (old.origin == FunctionOrigin::Symbol && stop <= end(old.address, old.size)?)
                || (old.address == region.address && old.size == region.size)
            {
                continue;
            }
            return Err(BinaryError::AmbiguousFunctionAddress(region.address));
        }
        if catalog.range(region.address..stop).next().is_some() {
            return Err(BinaryError::AmbiguousFunctionAddress(region.address));
        }
        if catalog.len() == 4096 {
            return Err(BinaryError::Limit("function catalog exceeds 4096 entries"));
        }
        catalog.insert(
            region.address,
            FunctionSymbol {
                name: format!("sub_{:x}", region.address),
                address: region.address,
                size: region.size,
                origin: FunctionOrigin::Unwind {
                    record_offset: end(frame.offset, region.record as u64)?,
                },
            },
        );
    }
    Ok(catalog.into_values().collect())
}
