use crate::support::native;
use std::process::Command;
use std::time::Duration;

#[test]
fn middle_value_dump_and_c_bridge_retain_the_readable_backend_on_real_objects() {
    let scratch = native::Scratch::new();
    for source in ["shared-tail", "multi-exit-prefix"] {
        for opt in ["-O0", "-O2", "-O3"] {
            let object = scratch.0.join(format!("{source}-{opt}.o"));
            native::object(
                &native::fixture_root().join(format!("cases/{source}.c")),
                &object,
                opt,
                "fixture",
            );
            let dump = native::command_output(
                Command::new(env!("CARGO_BIN_EXE_nirvana"))
                    .arg(&object)
                    .args(["--emit", "middle-ir"]),
                None,
                Duration::from_secs(15),
            );
            assert!(
                dump.status.success(),
                "{}",
                String::from_utf8_lossy(&dump.stderr)
            );
            let dump = String::from_utf8(dump.stdout).unwrap();
            assert!(dump.starts_with("middle-ir-v1 entry @"));
            assert!(dump.contains("read s7 [ssa v"));
            assert!(dump.contains("check-write64"));
            for coalesce in [false, true] {
                let emit = |mode| {
                    let mut command = Command::new(env!("CARGO_BIN_EXE_nirvana"));
                    command.arg(&object).args(["--emit", mode]);
                    if !coalesce {
                        command.arg("--no-coalesce-locals");
                    }
                    let output =
                        native::command_output(&mut command, None, Duration::from_secs(15));
                    assert!(
                        output.status.success(),
                        "{}",
                        String::from_utf8_lossy(&output.stderr)
                    );
                    output.stdout
                };
                let old = emit("readable-c");
                let new = emit("middle-c");
                assert_eq!(old, new);
                let path = scratch.0.join(format!("{source}-{opt}-{coalesce}.c"));
                std::fs::write(&path, new).unwrap();
                native::compile_c(&path, &path.with_extension("o"), &["-O2", "-c"]);
            }
        }
    }
}
