use nirvana::memory::{Layout, READ, Region, View, WRITE};

fn region(address: u64, size: u64, offset: usize, permissions: u8) -> Region {
    Region {
        address,
        size,
        offset,
        permissions,
    }
}

#[test]
fn sparse_ranges_preserve_virtual_gaps_permissions_and_adjacent_accesses() {
    let layout = Layout::new(
        vec![
            region(0x1000, 4, 0, 6),
            region(0x1004, 4, 4, 4),
            region(0x9000, 4, 8, 0),
            region(u64::MAX - 8, 8, 12, 6),
        ],
        20,
    )
    .unwrap();
    let bytes: Vec<_> = (0..20).collect();
    let view = View {
        base: 0x1000,
        bytes: &bytes,
        layout: Some(&layout),
    };
    assert_eq!(view.read(0x1002, 6), Some(&bytes[2..8]));
    assert_eq!(layout.offset(0x1002, 6, WRITE), None);
    assert_eq!(layout.offset(0x1000, 4, WRITE), Some(0));
    assert_eq!(view.read(0x1007, 2), None);
    assert_eq!(view.read(0x1008, 1), None);
    assert_eq!(view.read(0x8000, 1), None);
    assert_eq!(view.read(0x9000, 1), None);
    assert_eq!(layout.offset(0x9000, 4, 0), Some(8));
    assert_eq!(layout.offset(0x1008, 0, WRITE), Some(8));
    assert_eq!(layout.offset(0x8000, 0, READ), None);
    assert_eq!(view.read(u64::MAX - 8, 8), Some(&bytes[12..20]));
    assert_eq!(view.read(u64::MAX - 8, 9), None);
    assert_eq!(layout.available(0x1001, READ), Some(7));
    assert_eq!(layout.available(0x1001, WRITE), Some(3));
    assert_eq!(layout.available(0x9000, READ), None);
}

#[test]
fn malformed_layouts_and_backing_aliases_are_rejected() {
    for (regions, size) in [
        (vec![], 0),
        (vec![region(0, 0, 0, 6)], 0),
        (vec![region(u64::MAX, 1, 0, 6)], 1),
        (vec![region(10, 4, 0, 6), region(12, 4, 4, 6)], 8),
        (vec![region(10, 4, 0, 6), region(20, 4, 0, 6)], 8),
        (vec![region(10, 4, 1, 6)], 5),
        (vec![region(10, 4, 0, 8)], 4),
        (vec![region(10, 4, 0, 6)], 3),
        (vec![region(10, 4, 0, 6)], 5),
    ] {
        assert!(Layout::new(regions, size).is_err());
    }
    let view = View {
        base: u64::MAX,
        bytes: &[7],
        layout: None,
    };
    assert_eq!(view.read(u64::MAX, 1), Some(&[7][..]));
    assert_eq!(view.read(u64::MAX, 2), None);
}

#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

#[test]
fn c_translation_matches_region_boundaries_and_atomic_permission_checks() {
    use std::fmt::Write;
    let layout = Layout::new(
        vec![
            region(0x1000, 4, 0, 6),
            region(0x1004, 4, 4, 4),
            region(0x9000, 4, 8, 0),
            region(u64::MAX - 8, 8, 12, 6),
        ],
        20,
    )
    .unwrap();
    let scratch = native::Scratch::new();
    let mut code = String::from(
        "#define NV_SPARSE_REGION_COUNT 4\n#define NV_SPARSE_REGIONS {{4096,4,0,6},{4100,4,4,4},{36864,4,8,0},{UINT64_C(18446744073709551607),8,12,6}}\n",
    );
    code.push_str(include_str!("../src/module_emit/runtime.h"));
    code.push_str(r#"
#include <assert.h>
static struct nv_module state;
static void check(uint64_t address,uint64_t width,unsigned access,uint64_t expected) {
    if(setjmp(state.jump)) {
        assert(expected==UINT64_MAX && state.status==1);
        assert(state.fault_address==address && state.fault_width==width && state.fault_access==access);
        return;
    }
    uint64_t offset=nv_check(&state,address,width,access);
    assert(expected!=UINT64_MAX && offset==expected);
}
static void available(uint64_t address,unsigned access,uint64_t expected) {
    if(setjmp(state.jump)) {assert(expected==UINT64_MAX);return;}
    uint64_t count=nv_available(&state,address,access);
    assert(expected!=UINT64_MAX && count==expected);
}
int main(void) {state.size=20;state.base=4096;
"#);
    for address in (0xffe..=0x100a)
        .chain(0x8ffe..=0x9006)
        .chain(u64::MAX - 10..=u64::MAX)
    {
        for (access, permission) in [(1, READ), (2, WRITE)] {
            for width in [0, 1, 2, 4, 8, 16] {
                let expected = layout
                    .offset(address, width, permission)
                    .map_or(u64::MAX, |n| n as u64);
                writeln!(
                    code,
                    "check(UINT64_C({address}),{width},{access},UINT64_C({expected}));"
                )
                .unwrap();
            }
            let expected = layout
                .available(address, permission)
                .map_or(u64::MAX, |n| n as u64);
            writeln!(
                code,
                "available(UINT64_C({address}),{access},UINT64_C({expected}));"
            )
            .unwrap();
        }
    }
    code.push_str("return 0;}\n");
    let source = scratch.0.join("sparse.c");
    std::fs::write(&source, code).unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(opt);
        native::compile_c(
            &source,
            &binary,
            &[opt, "-fsanitize=undefined", "-fno-sanitize-recover=all"],
        );
        let result = native::run_output(&binary, Some(""), std::time::Duration::from_secs(5));
        assert!(
            result.status.success(),
            "{opt}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}
