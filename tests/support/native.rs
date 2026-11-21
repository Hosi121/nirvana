use std::io::{Read, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

pub fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

pub struct Scratch(pub PathBuf);

impl Scratch {
    pub fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("nirvana-native-{}-{nonce}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

pub fn object(source: &Path, output: &Path, optimization: &str, entry: &str) {
    compile_c(
        source,
        output,
        &[
            "-fno-lto",
            optimization,
            &format!("-DFIXTURE_ENTRY={entry}"),
            "-c",
        ],
    );
}

pub fn compile_c(source: &Path, output: &Path, flags: &[&str]) {
    compile(
        Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic"])
            .args(flags)
            .arg(source)
            .arg("-o")
            .arg(output),
    );
}

pub fn compile(command: &mut Command) {
    let compilation = command
        .output()
        .unwrap_or_else(|error| panic!("could not run {command:?}: {error}"));
    assert!(
        compilation.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&compilation.stderr)
    );
}

pub fn link(objects: &[&Path], output: &Path) {
    let result = Command::new("cc")
        .arg("-fno-lto")
        .args(objects)
        .arg("-o")
        .arg(output)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "link {}: {}",
        output.display(),
        String::from_utf8_lossy(&result.stderr)
    );
}

pub fn run(binary: &Path, input: &str) -> Vec<Vec<u64>> {
    run_fields(binary, input, 5)
}

pub fn run_fields(binary: &Path, input: &str, fields: usize) -> Vec<Vec<u64>> {
    let output = run_output(binary, Some(input), Duration::from_secs(5));
    assert!(
        output.status.success(),
        "{}: {}",
        binary.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| {
            let result: Vec<_> = line
                .split_whitespace()
                .map(|word| word.parse().unwrap())
                .collect();
            assert_eq!(result.len(), fields);
            result
        })
        .collect()
}

/// Capture raw output without requiring a successful exit status.
/// `None` leaves stdin inherited; `Some` writes the input and then closes it.
pub fn run_output(binary: &Path, input: Option<&str>, timeout: Duration) -> Output {
    let mut command = Command::new(binary);
    if input.is_some() {
        command.stdin(Stdio::piped());
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // Drain output while writing input: an expanded fixture corpus can exceed
    // OS pipe capacity, and a non-returning case must still be timed out.
    let writer = input.map(|input| {
        let mut stdin = child.stdin.take().unwrap();
        let input = input.as_bytes().to_owned();
        std::thread::spawn(move || stdin.write_all(&input))
    });
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    let stdout_reader = std::thread::spawn(move || drain(stdout));
    let stderr_reader = std::thread::spawn(move || drain(stderr));
    let deadline = Instant::now() + timeout;
    let mut timed_out = false;
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            timed_out = true;
            break;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let status = child.wait().unwrap();
    let written = writer.map(|writer| writer.join().unwrap());
    let stdout = stdout_reader.join().unwrap().unwrap();
    let stderr = stderr_reader.join().unwrap().unwrap();
    assert!(
        !timed_out,
        "{} exceeded the execution timeout",
        binary.display()
    );
    if let Some(written) = written {
        written.unwrap();
    }
    Output {
        status,
        stdout,
        stderr,
    }
}

fn drain(mut reader: impl Read) -> std::io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    Ok(bytes)
}
