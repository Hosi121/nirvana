#!/usr/bin/env python3
"""Shared Cargo cache and bounded, disposable experiment output (Linux)."""
import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

MIB = 1024 ** 2
CACHE_BYTES = 2048 * MIB
RUN_BYTES = 512 * MIB
RUN_COUNT = 2
RUN_SCHEMA = "nirvana-managed-run-v1"


@dataclass(frozen=True)
class Layout:
    root: Path
    locks: Path

    @classmethod
    def discover(cls, checkout):
        """All linked worktrees use the primary checkout's build storage."""
        checkout = checkout.resolve()
        try:
            entries = subprocess.check_output(
                ["git", "-C", str(checkout), "worktree", "list", "--porcelain", "-z"],
                stderr=subprocess.DEVNULL).decode().split("\0")
            root = Path(next(item[9:] for item in entries if item.startswith("worktree ")))
            common = subprocess.check_output(
                ["git", "-C", str(checkout), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                text=True, stderr=subprocess.DEVNULL).strip()
            return cls(root.resolve(), Path(common) / "nirvana-locks")
        except (subprocess.CalledProcessError, FileNotFoundError, StopIteration):
            return cls(checkout, checkout / "target/.locks")

    def path(self, relative):
        path = self.root / "target" / relative
        # Refuse a redirected storage root; rmtree itself also avoids following
        # symlinks inside a cache or run directory.
        for candidate in (path, *path.parents):
            if candidate == self.root:
                break
            if candidate.is_symlink():
                raise ValueError(f"storage directory is a symlink: {candidate}")
        return path


def size(path):
    """Count regular-file bytes once per inode, without following symlinks."""
    seen, total = set(), 0
    if not path.exists():
        return 0
    for directory, _, files in os.walk(path, followlinks=False):
        for name in files:
            item = Path(directory) / name
            if item.is_symlink():
                continue
            stat = item.stat()
            key = (stat.st_dev, stat.st_ino)
            if key not in seen:
                seen.add(key)
                total += stat.st_size
    return total


@contextmanager
def lock(layout, name):
    layout.locks.mkdir(parents=True, exist_ok=True)
    with (layout.locks / name).open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


def refresh_cache(layout, budget, force=False):
    cache = layout.path("cargo-cache")
    used = size(cache)
    if cache.exists() and (force or used > budget):
        shutil.rmtree(cache)
        print(f"Removed Cargo intermediates: {used / MIB:.1f} MiB", file=sys.stderr)


def child(argv, **kwargs):
    """Wait for all compiler children before deleting their output on interrupt."""
    with subprocess.Popen(argv, start_new_session=True, **kwargs) as process:
        try:
            result = process.wait()
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
    return result if result >= 0 else 128 - result


def cargo(layout, argv, budget):
    options = argv[:argv.index("--")] if "--" in argv else argv
    if not options:
        raise ValueError("cargo requires a subcommand, e.g. cargo test --locked --all-targets")
    if "clean" in options:
        raise ValueError("use dev.py clean to remove intermediates while keeping final binaries and evidence")
    if any(arg.split("=", 1)[0] in ("--target-dir", "--config") for arg in options):
        raise ValueError("managed Cargo owns its storage paths; use Cargo directly for custom configuration")
    with lock(layout, "cargo.lock"):
        refresh_cache(layout, budget)
        env = {**os.environ,
               "CARGO_TARGET_DIR": str(layout.path("")),
               "CARGO_BUILD_BUILD_DIR": str(layout.path("cargo-cache"))}
        try:
            return child(["cargo", *argv], env=env)
        finally:
            refresh_cache(layout, budget)


def runs(layout):
    root = layout.path("runs")
    if root.exists():
        for path in root.glob("run-*"):
            if not path.is_dir() or path.is_symlink():
                continue
            marker = path / "run.json"
            if marker.is_symlink():
                continue
            try:
                record = json.loads(marker.read_text())
            except (OSError, ValueError):
                continue
            if isinstance(record, dict) and record.get("schema") == RUN_SCHEMA:
                yield path, record, marker.stat().st_mtime_ns


def prune_runs(layout, budget, count, all_runs=False):
    kept, used = 0, 0
    for path, record, _ in sorted(runs(layout), key=lambda item: item[2], reverse=True):
        amount = size(path)
        if all_runs or not record.get("keep") or kept >= count or used + amount > budget:
            shutil.rmtree(path)
            print(f"Removed run: {path.name} ({amount / MIB:.1f} MiB)", file=sys.stderr)
        else:
            kept += 1
            used += amount


def experiment(layout, argv, keep, budget, count):
    if not argv or not any("{out}" in arg for arg in argv):
        raise ValueError("run requires a command with an {out} output path")
    with lock(layout, "runs.lock"):
        prune_runs(layout, budget, count)
        root = layout.path("runs")
        root.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="run-", dir=root))
        out = directory / "out"
        command = [arg.replace("{out}", str(out)) for arg in argv]
        record = {"schema": RUN_SCHEMA, "argv": command, "cwd": str(Path.cwd()), "keep": keep}
        (directory / "run.json").write_text(json.dumps(record, indent=2) + "\n")
        try:
            result = child(command)
            record["returncode"] = result
            (directory / "run.json").write_text(json.dumps(record, indent=2) + "\n")
        finally:
            if not keep:
                shutil.rmtree(directory)
            prune_runs(layout, budget, count)
        if keep:
            if not directory.exists():
                print("Run removed: retention budget exceeded. Use a larger --runs-mib to retain this run.",
                      file=sys.stderr)
                return result or 1
            print(f"Kept run: {out}", file=sys.stderr)
        return result


def positive(value):
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("require a positive integer")
    return parsed


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-mib", type=positive, default=CACHE_BYTES // MIB)
    parser.add_argument("--runs-mib", type=positive, default=RUN_BYTES // MIB)
    sub = parser.add_subparsers(dest="action", required=True)
    sub.add_parser("cargo", help="serialize builds and trim intermediate cache").add_argument(
        "argv", nargs=argparse.REMAINDER)
    run = sub.add_parser("run", help="run with disposable {out}; retain up to two runs with --keep")
    run.add_argument("--keep", action="store_true")
    run.add_argument("argv", nargs=argparse.REMAINDER)
    sub.add_parser("status", help="show shared build and experiment storage")
    sub.add_parser("clean", help="remove intermediate cache; --runs also removes retained runs").add_argument(
        "--runs", action="store_true")
    args = parser.parse_args(argv)
    layout = Layout.discover(Path(__file__).resolve().parents[1])
    budget, run_budget = args.cache_mib * MIB, args.runs_mib * MIB
    command = getattr(args, "argv", [])
    if command[:1] == ["--"]:
        command = command[1:]
    if args.action == "cargo":
        return cargo(layout, command, budget)
    if args.action == "run":
        return experiment(layout, command, args.keep, run_budget, RUN_COUNT)
    # Same lock order as a managed experiment that invokes managed Cargo.
    with lock(layout, "runs.lock"), lock(layout, "cargo.lock"):
        if args.action == "clean":
            refresh_cache(layout, budget, force=True)
            prune_runs(layout, run_budget, RUN_COUNT, all_runs=args.runs)
        print(f"Storage: {layout.root / 'target'}")
        print(f"Cargo intermediates: {size(layout.path('cargo-cache')) / MIB:.1f} MiB / {args.cache_mib} MiB")
        print(f"Managed runs: {size(layout.path('runs')) / MIB:.1f} MiB / {args.runs_mib} MiB; keep {RUN_COUNT}")
        print(f"All target files: {size(layout.path('')) / MIB:.1f} MiB")
    return 0


if __name__ == "__main__":
    def interrupted(*_):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f"dev: {error}", file=sys.stderr)
        sys.exit(1)
    except KeyboardInterrupt:
        sys.exit(130)
