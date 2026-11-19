"""Exercise real cross-module sockets and distinguish support gaps from tool failures."""

import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location(
    "http_server_benchmark", Path(__file__).resolve().parents[1] / "http_server_benchmark.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ProbeClassification(unittest.TestCase):
    def classify(self, stderr, returncode=1, **options):
        return MODULE.classify_probe({"returncode": returncode, "stderr": stderr, **options})

    def test_known_capability_rejection_is_unsupported(self):
        self.assertEqual(self.classify("Error: unsupported opcode 0f 28"), "unsupported")
        self.assertEqual(self.classify("call target is not proven external puts+0"), "unsupported")
        for reason in ["target 0x10 requires internal-call or PLT analysis",
                       'import "socket" requires an external effect model',
                       "indirect target requires value-flow evidence",
                       "slot 0x10 lacks dynamic import evidence"]:
            with self.subTest(reason=reason):
                self.assertEqual(self.classify("linked call at 0x20: " + reason), "unsupported")

    def test_panic_and_signal_cannot_count_as_unsupported(self):
        self.assertEqual(self.classify("thread 'main' panicked at unsupported call"), "tool-error")
        self.assertEqual(self.classify("unsupported", -11), "tool-error")

    def test_unknown_diagnostic_is_not_an_unsupported_count(self):
        self.assertEqual(self.classify("Error: failed allocation invariant"), "tool-error")

    def test_cli_incompatibility_and_timeouts_are_separate(self):
        self.assertEqual(self.classify("unknown emission format effects-readable-c"), "cli-incompatible")
        self.assertEqual(self.classify("unsupported", None, timeout=True), "timeout")
        self.assertEqual(self.classify("No such file", None, launch_error=True), "tool-error")

    def test_success_is_not_semantic_equivalence(self):
        self.assertEqual(self.classify("", 0), "accepted")


@unittest.skipUnless(shutil.which("cc") and shutil.which("readelf"), "requires cc and readelf")
class NativeModularServer(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="nirvana-http-test-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.build = MODULE.build_variant(Path(cls.directory.name), "O2", "pie")
        if cls.build["status"] != "passed":
            raise AssertionError(cls.build)
        cls.binary = Path(cls.build["binary"])

    def test_native_routes_and_bounded_parser_across_modules(self):
        for case in MODULE.native_cases():
            with self.subTest(case=case["name"]):
                result = MODULE.run_native_case(self.binary, case)
                self.assertEqual(result["status"], "passed", result)

    def test_linked_pie_has_relocated_route_table_and_no_copy(self):
        self.assertEqual(self.build["elf_type"], 3)
        self.assertEqual(self.build["copy_relocations"], 0)
        relocations = (self.binary.parent / "relocations.txt").read_text()
        self.assertGreaterEqual(relocations.count("R_X86_64_RELATIVE"), 4)

    def test_timeout_path_reaps_server_process(self):
        real_popen = subprocess.Popen
        processes = []

        def capture(*args, **kwargs):
            process = real_popen(*args, **kwargs)
            processes.append(process)
            return process

        with mock.patch.object(MODULE.subprocess, "Popen", side_effect=capture), \
                mock.patch.object(MODULE, "read_port", side_effect=TimeoutError("forced port timeout")):
            result = MODULE.run_native_case(self.binary, MODULE.native_cases()[0], timeout=0.1)
        self.assertEqual(result["status"], "failed")
        self.assertIn("forced port timeout", result["error"])
        self.assertEqual(len(processes), 1)
        self.assertIsNotNone(processes[0].poll())
        self.assertTrue(processes[0].stdout.closed)
        self.assertTrue(processes[0].stderr.closed)

    def test_truncated_response_cannot_pass_with_expected_body_prefix(self):
        with self.assertRaises(AssertionError):
            MODULE.check_response(b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n"
                                  b"Content-Length: 3\r\nConnection: close\r\n\r\nok",
                                  MODULE.native_cases()[0])


if __name__ == "__main__":
    unittest.main()
