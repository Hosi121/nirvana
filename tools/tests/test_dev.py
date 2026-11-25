"""Build storage stays disposable while source and final outputs survive."""
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import dev

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

        def build(argv, env):
            self.assertFalse((self.root / "target/cargo-cache").exists())
            self.assertEqual(env["CARGO_TARGET_DIR"], str(self.root / "target"))
            self.assertEqual(env["CARGO_BUILD_BUILD_DIR"], str(self.root / "target/cargo-cache"))
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
