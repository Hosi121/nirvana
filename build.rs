//! Build identity for retained evaluation binaries, without timestamps.
use std::{path::Path, process::Command};

const INPUTS: &[&str] = &[
    "src",
    "examples",
    "tests",
    "build.rs",
    "Cargo.toml",
    "Cargo.lock",
    ".cargo",
    "rust-toolchain.toml",
];

fn git(args: &[&str]) -> Option<String> {
    let output = Command::new("git").args(args).output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8(output.stdout).ok())
        .flatten()
}

fn main() {
    for input in INPUTS {
        if Path::new(input).exists() {
            println!("cargo::rerun-if-changed={input}");
        }
    }
    // Archives may be extracted inside somebody else's repository. Only this
    // package's own checkout is a source of Git identity; worktree .git files
    // are supported through git-path rather than assuming .git is a directory.
    let checkout = Path::new(".git").exists();
    let revision = checkout
        .then(|| git(&["rev-parse", "--verify", "HEAD"]))
        .flatten()
        .map(|s| s.trim().to_owned())
        .filter(|s| matches!(s.len(), 40 | 64) && s.bytes().all(|b| b.is_ascii_hexdigit()))
        .unwrap_or_else(|| "unknown".into());
    let dirty = if checkout {
        let mut args = vec!["status", "--porcelain=v1", "--untracked-files=normal", "--"];
        args.extend(INPUTS.iter().copied());
        git(&args)
            .map(|s| if s.is_empty() { "false" } else { "true" })
            .unwrap_or("unknown")
    } else {
        "unknown"
    };
    if checkout {
        let mut paths = vec![
            "HEAD".to_owned(),
            "index".into(),
            "refs".into(),
            "packed-refs".into(),
        ];
        if let Some(reference) = git(&["symbolic-ref", "-q", "HEAD"]) {
            paths.push(reference.trim().to_owned());
        }
        for name in paths {
            if let Some(path) = git(&["rev-parse", "--git-path", &name]) {
                let path = path.trim();
                if name == "index" || Path::new(path).exists() {
                    println!("cargo::rerun-if-changed={path}");
                }
            }
        }
    }
    println!("cargo::rustc-env=NIRVANA_BUILD_REVISION={revision}");
    println!("cargo::rustc-env=NIRVANA_SOURCE_DIRTY={dirty}");
}
