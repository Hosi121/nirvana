//! Compact C11 surface over the same checked guest-memory operations.
//!
//! _Generic inspects the location's type without evaluating it. The selected
//! conversion evaluates it once, so a load used as an address is not duplicated.

pub(super) const COMPACT_MEMORY: &str = r#"
static inline struct nirvana_view nirvana_location_address(uint64_t address) {
    struct nirvana_view result = {address}; return result;
}
static inline struct nirvana_view nirvana_location_view(struct nirvana_view view) { return view; }
#define NIRVANA_LOCATION(location) _Generic((location), struct nirvana_view: nirvana_location_view, default: nirvana_location_address)((location))
#define read8(location) nirvana_view_load(&m, NIRVANA_LOCATION(location), 1)
#define read16(location) nirvana_view_load(&m, NIRVANA_LOCATION(location), 2)
#define read32(location) nirvana_view_load(&m, NIRVANA_LOCATION(location), 4)
#define read64(location) nirvana_view_load(&m, NIRVANA_LOCATION(location), 8)
#define write8(location, value) nirvana_view_store(&m, NIRVANA_LOCATION(location), 1, (value))
#define write16(location, value) nirvana_view_store(&m, NIRVANA_LOCATION(location), 2, (value))
#define write32(location, value) nirvana_view_store(&m, NIRVANA_LOCATION(location), 4, (value))
#define write64(location, value) nirvana_view_store(&m, NIRVANA_LOCATION(location), 8, (value))
#define element(base, index, stride) nirvana_view_index(NIRVANA_LOCATION(base), (index), (stride), UINT64_C(0))
#define field(base, offset) nirvana_view_index(NIRVANA_LOCATION(base), UINT64_C(0), UINT64_C(1), (offset))
"#;

pub(super) const COMPACT_END: &str = r#"
#undef read8
#undef read16
#undef read32
#undef read64
#undef write8
#undef write16
#undef write32
#undef write64
#undef element
#undef field
#undef NIRVANA_LOCATION
"#;

/// This spelling is used only in uint64_t function-argument contexts.
pub(super) fn argument(value: u64) -> String {
    if value <= i32::MAX as u64 {
        value.to_string()
    } else if value.wrapping_neg() <= i32::MAX as u64 {
        format!("-{}", value.wrapping_neg())
    } else {
        format!("UINT64_C(0x{value:x})")
    }
}
