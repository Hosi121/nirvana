"""Build storage stays disposable while source and final outputs survive."""
import fcntl
from contextlib import redirect_stderr
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import dev
import process_job

ROOT = Path(__file__).resolve().parents[2]


class Storage(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.layout = dev.Layout(self.root, self.root / ".locks")

    def file(self, relative, content=b"retained"):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def run_record(self, name, amount, order, keep=True):
        self.file(f"target/runs/run-{name}/out/data", b"x" * amount)
        marker = self.file(f"target/runs/run-{name}/run.json", json.dumps(
            {"schema": dev.RUN_SCHEMA, "keep": keep}).encode())
        os.utime(marker, ns=(order, order))
        return marker.parent

    def test_cache_cleanup_keeps_binaries_evidence_and_symlink_targets(self):
        binary = self.file("target/debug/nirvana")
        evidence = self.file("target/checkpoint/report.json")
        source = self.file("src/main.rs")
        self.file("target/cargo-cache/debug/old", b"x" * 20)
        (self.root / "target/cargo-cache/linked").symlink_to(source)
        dev.refresh_cache(self.layout, 10)
        self.assertFalse((self.root / "target/cargo-cache").exists())
        for path in [binary, evidence, source]:
            self.assertEqual(path.read_bytes(), b"retained")

    def test_symlinked_storage_root_or_cache_is_rejected(self):
        outside = self.root / "outside"
        outside.mkdir()
        (self.root / "target").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError):
            dev.refresh_cache(self.layout, 1, force=True)
        (self.root / "target").unlink()
        (self.root / "target").mkdir()
        (self.root / "target/cargo-cache").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError):
            dev.refresh_cache(self.layout, 1, force=True)
        self.assertTrue(outside.exists())

    def test_run_count_byte_budget_and_abandoned_scratch(self):
        old = self.run_record("old", 100, 1)
        middle = self.run_record("middle", 100, 2)
        new = self.run_record("new", 100, 3)
        orphan = self.run_record("abandoned", 1, 4, keep=False)
        dev.prune_runs(self.layout, 10_000, 2)
        self.assertFalse(old.exists())
        self.assertFalse(orphan.exists())
        self.assertTrue(middle.exists())
        self.assertTrue(new.exists())
        dev.prune_runs(self.layout, dev.size(new), 2)
        self.assertFalse(middle.exists())
        self.assertTrue(new.exists())

    def test_run_cleanup_preserves_foreign_directories_and_symlinks(self):
        known = self.run_record("owned", 100, 1)
        unknown = self.file("target/runs/run-foreign/data")
        evidence = self.file("checkpoint/data")
        linked = self.root / "target/runs/run-linked"
        linked.symlink_to(evidence.parent, target_is_directory=True)
        dev.prune_runs(self.layout, 1, 1, all_runs=True)
        self.assertFalse(known.exists())
        self.assertTrue(unknown.exists())
        self.assertEqual(evidence.read_bytes(), b"retained")
        self.assertTrue(linked.is_symlink())

    def test_temporary_experiments_cleanup_on_success_and_failure(self):
        command = [sys.executable, "-c",
                   "import pathlib,sys; p=pathlib.Path(sys.argv[1]); p.mkdir(); "
                   "(p/'output').write_text('data'); sys.exit(int(sys.argv[2]))", "{out}"]
        for code in [0, 17]:
            self.assertEqual(dev.experiment(self.layout, [*command, str(code)], False, 1000, 2), code)
            self.assertEqual(list(dev.runs(self.layout)), [])

    def test_existing_unmanaged_output_blocks_jobs_and_survives_cleanup(self):
        evidence = self.file("target/checkpoint/data", b"x" * 8192)
        marker = self.root / "started"
        command = [sys.executable, "-c", "import pathlib,sys; pathlib.Path(sys.argv[1]).touch()", str(marker)]
        result = dev.child(command, guard=lambda: dev.target_limit(self.layout, 4096))
        self.assertEqual(result, dev.LIMIT_EXIT)
        self.assertFalse(marker.exists())
        self.assertEqual(evidence.read_bytes(), b"x" * 8192)

    def test_live_writer_is_stopped_and_temporary_output_is_removed(self):
        marker = self.root / "completed"
        command = [sys.executable, "-c",
                   "import pathlib,signal,sys,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                   "p=pathlib.Path(sys.argv[1]); p.mkdir(); (p/'data').write_bytes(b'x'*8192); "
                   "time.sleep(2); pathlib.Path(sys.argv[2]).touch()", "{out}", str(marker)]
        # Same writer completes when it is allowed enough storage.
        self.assertEqual(dev.experiment(self.layout, command, False, 1000, 2, 100_000), 0)
        self.assertTrue(marker.exists())
        marker.unlink()
        self.assertEqual(dev.experiment(self.layout, command, False, 1000, 2, 4096), dev.LIMIT_EXIT)
        self.assertFalse(marker.exists())
        self.assertEqual(list(dev.runs(self.layout)), [])

    def test_fast_writer_is_checked_at_exit_too(self):
        command = [sys.executable, "-c",
                   "import pathlib,sys; p=pathlib.Path(sys.argv[1]); p.mkdir(); (p/'data').write_bytes(b'x'*8192)",
                   "{out}"]
        self.assertEqual(dev.experiment(self.layout, command, False, 1000, 2, 4096), dev.LIMIT_EXIT)
        self.assertEqual(list(dev.runs(self.layout)), [])

    def test_background_writer_is_stopped_before_cleanup(self):
        pidfile = self.root / "writer.pid"
        writer = ("import json,os,pathlib,signal,sys,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                  "s=pathlib.Path('/proc/self/stat').read_text().rsplit(')',1)[1].split(); "
                  "pathlib.Path(sys.argv[1]).write_text(json.dumps([os.getpid(),int(s[19])])); time.sleep(30)")
        parent = ("import pathlib,subprocess,sys,time; "
                  "subprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2]]); "
                  "p=pathlib.Path(sys.argv[2]); "
                  "deadline=time.monotonic()+5\n"
                  "while not p.exists() and time.monotonic()<deadline: time.sleep(0.01)\n"
                  "assert p.exists()")
        pid = start = None
        try:
            self.assertEqual(dev.child([sys.executable, "-c", parent, writer, str(pidfile)]), 0)
            pid, start = json.loads(pidfile.read_text())
            # A killed orphan may briefly remain a zombie until init reaps it.
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                try:
                    state = Path(f"/proc/{pid}/stat").read_text().split()[2]
                except FileNotFoundError:
                    return
                if state == "Z":
                    return
                time.sleep(0.01)
            self.fail("background writer is still alive after the managed job returned")
        finally:
            current = process_job.identity(pid) if pid is not None else None
            if current is not None and current[1] == start:
                descriptor = None
                try:
                    descriptor = os.pidfd_open(pid, 0)
                    if process_job.identity(pid) == current:
                        signal.pidfd_send_signal(descriptor, signal.SIGKILL, None, 0)
                except ProcessLookupError:
                    pass
                finally:
                    if descriptor is not None:
                        os.close(descriptor)

    def test_nested_capture_writer_is_drained_on_limit_and_interrupt(self):
        writer = ("import json,os,pathlib,time,sys; "
                  "s=pathlib.Path('/proc/self/stat').read_text().rsplit(')',1)[1].split(); "
                  "pathlib.Path(sys.argv[1]).write_text(json.dumps([os.getpid(),int(s[19])])); time.sleep(10)")
        parent = ("import sys; sys.path.insert(0,sys.argv[1]); import evaluate_structure; "
                  "evaluate_structure.capture([sys.executable,'-c',sys.argv[2],sys.argv[3]],20)")
        for mode in ['limit', 'interrupt']:
            marker = self.root / mode
            pinned = []
            def guard():
                if marker.exists() and not pinned:
                    pid, start = json.loads(marker.read_text())
                    descriptor = os.pidfd_open(pid, 0)
                    self.assertEqual(process_job.identity(pid)[1], start)
                    pinned.append((pid, start, descriptor))
                    if mode == 'interrupt':
                        raise KeyboardInterrupt
                    return 'test-owned nested writer limit'
                return None
            try:
                command = [sys.executable, '-c', parent, str(ROOT/'tools'), writer, str(marker)]
                if mode == 'interrupt':
                    with self.assertRaises(KeyboardInterrupt):
                        dev.child(command, guard=guard)
                else:
                    self.assertEqual(dev.child(command, guard=guard), dev.LIMIT_EXIT)
                self.assertEqual(len(pinned), 1)
                pid, start, _ = pinned[0]
                current = process_job.identity(pid)
                self.assertTrue(current is None or current[1] != start)
            finally:
                for _, _, descriptor in pinned:
                    try:
                        signal.pidfd_send_signal(descriptor, signal.SIGKILL, None, 0)
                    except ProcessLookupError:
                        pass
                    finally:
                        os.close(descriptor)

    def test_job_signal_returncode_keeps_shell_style_dev_result(self):
        command = [sys.executable, '-c', 'import os,signal; os.kill(os.getpid(),signal.SIGTERM)']
        self.assertEqual(dev.child(command), 128 + signal.SIGTERM)

    def test_total_budget_includes_worktree_outputs_and_deduplicates_hardlinks(self):
        linked = self.root / "linked"
        payload = self.file("target/debug/nirvana", b"x" * 8192)
        other = self.file("linked/target/experiment/output", b"y" * 8192)
        layout = dev.Layout(self.root, self.layout.locks, (linked,))
        message = dev.target_limit(layout, 10_000)
        self.assertIn(str(other.parent), message)
        other.unlink()
        other.hardlink_to(payload)
        self.assertIsNone(dev.target_limit(layout, 10_000))

    def test_repeated_builds_and_kept_runs_have_bounded_storage(self):
        compiler = self.file("bin/cargo", (
            f"#!{sys.executable}\n"
            "import os,pathlib\n"
            "p=pathlib.Path(os.environ['CARGO_BUILD_BUILD_DIR'])/'debug'; p.mkdir(parents=True,exist_ok=True)\n"
            "(p/str(len(list(p.iterdir())))).write_bytes(b'x'*2048)\n").encode())
        compiler.chmod(0o755)
        binary = self.file("target/debug/nirvana")
        command = [sys.executable, "-c",
                   "import pathlib,sys; p=pathlib.Path(sys.argv[1]); p.mkdir(); (p/'data').write_bytes(b'x'*2048)",
                   "{out}"]
        sizes = []
        with patch.dict(os.environ, PATH=str(compiler.parent) + os.pathsep + os.environ['PATH']), \
                redirect_stderr(io.StringIO()):
            for _ in range(12):
                self.assertEqual(dev.cargo(self.layout, ["build"], 4096, 16_384), 0)
                self.assertEqual(dev.experiment(self.layout, command, True, 8192, 2, 16_384), 0)
                self.assertLessEqual(dev.size(self.root / "target/cargo-cache"), 4096)
                self.assertLessEqual(len(list(dev.runs(self.layout))), 2)
                sizes.append(dev.size(self.root / "target"))
        self.assertLess(max(sizes), 16_384)
        self.assertEqual(binary.read_bytes(), b"retained")

    def test_kept_experiments_have_provenance_and_return_failure_if_oversize(self):
        command = [sys.executable, "-c",
                   "import pathlib,sys; p=pathlib.Path(sys.argv[1]); p.mkdir(); (p/'data').write_text('x'*100)",
                   "{out}"]
        self.assertEqual(dev.experiment(self.layout, command, True, 10_000, 2), 0)
        path, record, _ = next(dev.runs(self.layout))
        self.assertEqual(record["returncode"], 0)
        self.assertIn(str(path / "out"), record["argv"])
        self.assertEqual(dev.experiment(self.layout, command, True, 10, 2), 1)
        self.assertEqual(list(dev.runs(self.layout)), [])

    def test_cargo_owns_paths_and_holds_lock_through_failed_child_cleanup(self):
        self.file("target/cargo-cache/data", b"old cache")

        def build(argv, env, guard):
            self.assertFalse((self.root / "target/cargo-cache").exists())
            self.assertEqual(env["CARGO_TARGET_DIR"], str(self.root / "target"))
            self.assertEqual(env["CARGO_BUILD_BUILD_DIR"], str(self.root / "target/cargo-cache"))
            self.assertIsNone(guard())
            with (self.layout.locks / "cargo.lock").open("a") as second:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(second, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.file("target/cargo-cache/data", b"new cache")
            return 42

        with patch.object(dev, "child", side_effect=build):
            self.assertEqual(dev.cargo(self.layout, ["test"], 1), 42)
        self.assertFalse((self.root / "target/cargo-cache").exists())
        for args in [["build", "--target-dir=elsewhere"], ["--config", "file", "build"], ["clean"]]:
            with self.assertRaises(ValueError):
                dev.cargo(self.layout, args, 1000)

    @unittest.skipUnless(shutil.which("cargo"), "requires Cargo")
    def test_actual_cargo_eviction_preserves_runnable_final_binary(self):
        manifest = self.file("probe/Cargo.toml", b'[package]\nname="storage-probe"\nversion="0.1.0"\nedition="2024"\n')
        self.file("probe/src/main.rs", b'fn main() { println!("storage-ok"); }')
        self.assertEqual(dev.cargo(self.layout, ["build", "--offline", "--manifest-path", str(manifest)], 1), 0)
        self.assertFalse((self.root / "target/cargo-cache").exists())
        binary = self.root / "target/debug/storage-probe"
        self.assertEqual(subprocess.check_output([binary], text=True).strip(), "storage-ok")

    @unittest.skipUnless(shutil.which("git"), "requires Git")
    def test_linked_worktrees_share_storage_and_lock(self):
        repo = self.root / "repo"
        repo.mkdir()

        def git(*args):
            subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)

        git("init", "--quiet")
        git("-c", "user.name=Storage test", "-c", "user.email=test@example.invalid",
            "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false",
            "commit", "--quiet", "--allow-empty", "-m", "fixture")
        linked = self.root / "linked"
        git("worktree", "add", "--detach", str(linked))
        self.assertEqual(dev.Layout.discover(repo), dev.Layout.discover(linked))


if __name__ == "__main__":
    unittest.main()
