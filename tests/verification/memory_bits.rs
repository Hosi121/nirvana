//! Scalar facts after successful exact stores. Writer completeness and checked
//! fault order are exercised separately by MemorySSA, IR and C integration tests.
use crate::support::ir::c;
use nirvana::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Width};
fn address(base: &str, byte: usize) -> String {
    format!("(bvadd {base} (_ bv{byte} 64))")
}
fn put(memory: &str, base: &str, value: &str, bytes: usize) -> String {
    let mut result = memory.to_owned();
    for byte in 0..bytes {
        result = format!(
            "(store {result} {} ((_ extract {} {}) {value}))",
            address(base, byte),
            byte * 8 + 7,
            byte * 8
        );
    }
    result
}
fn get(memory: &str, base: &str, bytes: usize) -> String {
    let mut result = "#x0000000000000000".to_owned();
    for byte in 0..bytes {
        result = format!(
            "(bvor {result} (bvshl ((_ zero_extend 56) (select {memory} {})) (_ bv{} 64)))",
            address(base, byte),
            byte * 8
        );
    }
    result
}
const HEADER: &str = "(set-logic QF_AUFBV)\n(declare-const m (Array (_ BitVec 64) (_ BitVec 8)))\n(declare-const a (_ BitVec 64))\n(declare-const b (_ BitVec 64))\n(declare-const x (_ BitVec 64))\n(declare-const y (_ BitVec 64))\n(declare-const choice Bool)\n";
fn check(name: &str, query: &str, expected: &str) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/memory-bit-facts");
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join(format!("{name}.smt2"));
    std::fs::write(&path, format!("{HEADER}{query}\n(check-sat)\n")).unwrap();
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    let output = std::process::Command::new(solver)
        .args(["-T:2", "-smt2"])
        .arg(&path)
        .output()
        .unwrap();
    let text = String::from_utf8(output.stdout).unwrap();
    std::fs::write(path.with_extension("out"), &text).unwrap();
    assert!(
        output.status.success(),
        "{name}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(text.trim(), expected, "{name}");
}
fn replay(partial: bool) -> u64 {
    let mut assignments = vec![Assignment {
        destination: Place::Memory {
            address: c(4096),
            width: if partial { Width::U8 } else { Width::U16 },
        },
        value: c(128),
    }];
    if !partial {
        assignments.push(Assignment {
            destination: Place::Memory {
                address: c(4096),
                width: Width::U8,
            },
            value: c(0),
        });
    }
    let p = Program::new(
        0,
        0,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(Expr::load(c(4096), Width::U16)),
        }],
    )
    .unwrap();
    let mut memory = [0; 16];
    if partial {
        memory[1] = 0xa5;
    }
    p.execute_with_memory(&[], 4096, &memory, 1).unwrap().value
}
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn exact_memory_bit_facts_have_array_models_and_fixed_witness_controls() {
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut proved = 0;
    for width in widths {
        let bytes = width.bytes();
        let first = put("m", "a", "x", bytes);
        let expected = format!("(bvand x #x{:016x})", width.mask());
        check(
            &format!("exact-{}", width.bits()),
            &format!("(assert (distinct {} {expected}))", get(&first, "a", bytes)),
            "unsat",
        );
        proved += 1;
        // Byte noninterference below applies independently to every byte.
        // Prove the composition separately, without expanding both store words
        // into every read and making the solver rediscover that decomposition.
        let mut equal_bytes =
            String::from("(declare-const n (Array (_ BitVec 64) (_ BitVec 8)))\n");
        for i in 0..bytes {
            let p = address("a", i);
            equal_bytes.push_str(&format!("(assert (= (select m {p}) (select n {p})))\n"));
        }
        check(
            &format!("byte-composition-{}", width.bits()),
            &format!(
                "{equal_bytes}(assert (distinct {} {}))",
                get("m", "a", bytes),
                get("n", "a", bytes)
            ),
            "unsat",
        );
        proved += 1;
        let x = "(bvor (bvand x #x000000000000000f) #x0000000000000080)";
        let y = "(bvor (bvand y #x000000000000001f) #x0000000000000080)";
        let joined = format!(
            "(ite choice {} {})",
            put("m", "a", x, bytes),
            put("m", "a", y, bytes)
        );
        check(
            &format!("phi-bit-{}", width.bits()),
            &format!(
                "(assert (distinct (bvand {} #x0000000000000080) #x0000000000000080))",
                get(&joined, "a", bytes)
            ),
            "unsat",
        );
        proved += 1;
    }
    for width in widths {
        let after = put("m", "b", "y", width.bytes());
        let mut disjoint = String::new();
        for i in 0..width.bytes() {
            disjoint.push_str(&format!("(assert (distinct a {}))\n", address("b", i)));
        }
        check(
            &format!("byte-noninterference-{}", width.bits()),
            &format!("{disjoint}(assert (distinct (select {after} a) (select m a)))"),
            "unsat",
        );
        proved += 1;
    }
    let first = put("m", "a", "#x0000000000000080", 2);
    let aliased = put(&first, "a", "#x0000000000000000", 1);
    check(
        "omitted-alias-writer",
        &format!(
            "(assert (= a (_ bv4096 64)))\n(assert (distinct (bvand {} #x0000000000000080) #x0000000000000080))",
            get(&aliased, "a", 2)
        ),
        "sat",
    );
    assert_eq!(replay(false), 0);
    let partial = put("m", "a", "#x0000000000000080", 1);
    check(
        "omitted-initial-byte",
        &format!(
            "(assert (= a (_ bv4096 64)))\n(assert (= (select m {}) #xa5))\n(assert (distinct {} #x0000000000000080))",
            address("a", 1),
            get(&partial, "a", 2)
        ),
        "sat",
    );
    assert_eq!(replay(true), 0xa580);
    assert_eq!(proved, 16);
    println!(
        "{proved} universal array identities; 2 SAT controls with fixed relevant inputs replayed through checked IR"
    );
}
