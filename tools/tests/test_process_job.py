"""Each managed guardian owns and reaps only its job, across new sessions."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import process_job as jobs

LEAF = '''import json,os,pathlib,sys,time
p=pathlib.Path(sys.argv[1])
s=pathlib.Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()
(p/'leaf.json').write_text(json.dumps(dict(pid=os.getpid(),start=int(s[19]))))
with (p/'heartbeat').open('ab',buffering=0) as f:
 for _ in range(100): f.write(b'x'); time.sleep(.05)
'''
PARENT = '''import pathlib,subprocess,sys,time
p=pathlib.Path(sys.argv[1])
subprocess.Popen([sys.executable,'-c',sys.argv[2],str(p)],start_new_session=True,
 stdout=subprocess.DEVNULL if sys.argv[3]=='closed' else None,
 stderr=subprocess.DEVNULL if sys.argv[3]=='closed' else None)
deadline=time.monotonic()+3
while not (p/'release').exists() and time.monotonic()<deadline: time.sleep(.01)
print('leader',flush=True)
'''


class ProcessJob(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)

    def leaf_handle(self, root=None):
        root = self.root if root is None else root
        deadline = time.monotonic() + 3
        marker = root/'leaf.json'
        while not marker.exists() and time.monotonic() < deadline:
            time.sleep(.01)
        record = json.loads(marker.read_text())
        descriptor = os.pidfd_open(record['pid'], 0)
        self.assertEqual(jobs.identity(record['pid'])[1], record['start'])
        return record, descriptor

    def stop_handle(self, descriptor):
        try:
            signal.pidfd_send_signal(descriptor, signal.SIGKILL, None, 0)
        except ProcessLookupError:
            pass
        finally:
            os.close(descriptor)

    def assert_gone(self, record):
        current = jobs.identity(record['pid'])
        self.assertTrue(current is None or current[1] != record['start'],
                        f"owned process was not reaped: {record}")

    def test_return_codes_startup_errors_and_standard_streams(self):
        for code in [0, 17]:
            with jobs.Job([sys.executable, '-c', f'raise SystemExit({code})']) as job:
                self.assertEqual(job.wait(timeout=3), code)
                self.assertEqual(job.wait(timeout=0), code)
        with jobs.Job([sys.executable, '-c', 'import os,signal; os.kill(os.getpid(),signal.SIGTERM)']) as job:
            self.assertEqual(job.wait(timeout=3), -signal.SIGTERM)
        with self.assertRaises(FileNotFoundError):
            jobs.Job(['/no/such/nirvana-test-command'])
        with tempfile.TemporaryFile() as incoming, tempfile.TemporaryFile() as outgoing:
            incoming.write(b'preserved input')
            incoming.seek(0)
            with jobs.Job([sys.executable, '-c', 'import sys; print(sys.stdin.read(),end="")'],
                          stdin=incoming, stdout=outgoing) as job:
                self.assertEqual(job.wait(timeout=3), 0)
            outgoing.seek(0)
            self.assertEqual(outgoing.read(), b'preserved input')

    def test_normal_exit_drains_new_session_background_writer(self):
        job = jobs.Job([sys.executable, '-c', PARENT, str(self.root), LEAF, 'closed'],
                       stdout=subprocess.DEVNULL)
        record = descriptor = None
        try:
            record, descriptor = self.leaf_handle()
            (self.root/'release').touch()
            self.assertEqual(job.wait(timeout=3), 0)
            self.assert_gone(record)
            amount = (self.root/'heartbeat').stat().st_size
            time.sleep(.08)
            self.assertEqual((self.root/'heartbeat').stat().st_size, amount)
        finally:
            if descriptor is not None: self.stop_handle(descriptor)
            job.close()

    def test_double_fork_orphans_are_owned_even_before_the_first_poll(self):
        intermediate = ('import subprocess,sys; subprocess.Popen('
            '[sys.executable,"-c",sys.argv[1],sys.argv[2]],start_new_session=True,'
            'stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)')
        parent = '''import pathlib,subprocess,sys,time
subprocess.run([sys.executable,'-c',sys.argv[2],sys.argv[3],sys.argv[1]],check=True)
p=pathlib.Path(sys.argv[1]); deadline=time.monotonic()+3
while not (p/'release').exists() and time.monotonic()<deadline: time.sleep(.01)
'''
        job = jobs.Job([sys.executable, '-c', parent, str(self.root), intermediate, LEAF])
        descriptor = None
        try:
            record, descriptor = self.leaf_handle()
            self.assertEqual(jobs.identity(record['pid'])[0], job.process.pid)
            (self.root/'release').touch()
            self.assertEqual(job.wait(timeout=3), 0)
            self.assert_gone(record)
        finally:
            if descriptor is not None: self.stop_handle(descriptor)
            job.close()

    def test_cancellation_drains_capture_session_and_held_standard_output(self):
        capture = '''import sys
sys.path.insert(0,sys.argv[1])
import evaluate_structure
evaluate_structure.capture([sys.executable,'-c',sys.argv[3],sys.argv[2]],10)
'''
        job = jobs.Job([sys.executable, '-c', capture, str(Path(__file__).resolve().parents[1]),
                        str(self.root), LEAF], stdout=subprocess.PIPE)
        descriptor = None
        try:
            record, descriptor = self.leaf_handle()
            self.assertNotEqual(os.getpgid(record['pid']), job.process.pid)
            job.cancel()
            self.assertEqual(job.wait(timeout=3), -signal.SIGKILL)
            self.assert_gone(record)
            os.set_blocking(job.process.stdout.fileno(), False)
            self.assertEqual(job.process.stdout.read(), b'')
        finally:
            if descriptor is not None: self.stop_handle(descriptor)
            job.close()
            job.process.stdout.close()

    def test_normal_completion_closes_output_held_by_detached_child(self):
        job = jobs.Job([sys.executable, '-c', PARENT, str(self.root), LEAF, 'held'],
                       stdout=subprocess.PIPE)
        descriptor = None
        try:
            record, descriptor = self.leaf_handle()
            (self.root/'release').touch()
            self.assertEqual(job.wait(timeout=3), 0)
            self.assert_gone(record)
            os.set_blocking(job.process.stdout.fileno(), False)
            self.assertEqual(job.process.stdout.read(), b'leader\n')
        finally:
            if descriptor is not None: self.stop_handle(descriptor)
            job.close()
            job.process.stdout.close()

    def test_external_sibling_survives_owned_job_cleanup(self):
        outside = self.root/'outside'
        outside.mkdir()
        sibling = subprocess.Popen([sys.executable, '-c', LEAF, str(outside)], start_new_session=True)
        descriptor = None
        try:
            record, descriptor = self.leaf_handle(outside)
            with jobs.Job([sys.executable, '-c', 'pass']) as job:
                self.assertEqual(job.wait(timeout=3), 0)
            self.assertIsNone(sibling.poll())
            self.assertEqual(jobs.identity(record['pid'])[1], record['start'])
        finally:
            if descriptor is not None: self.stop_handle(descriptor)
            sibling.wait(timeout=3)

    def test_pid_reuse_and_foreign_parent_never_receive_a_signal(self):
        with patch.object(jobs, 'identity', side_effect=[(123, 100), (123, 101)]), \
                patch.object(jobs.os, 'pidfd_open', return_value=77), \
                patch.object(jobs.os, 'close') as close, \
                patch.object(jobs.signal, 'pidfd_send_signal') as send:
            jobs.kill_owned(456, 123)
            send.assert_not_called()
            close.assert_called_once_with(77)
        with patch.object(jobs, 'identity', return_value=(999, 100)), \
                patch.object(jobs.os, 'pidfd_open') as pin:
            jobs.kill_owned(456, 123)
            pin.assert_not_called()


if __name__ == '__main__':
    unittest.main()
