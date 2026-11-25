#!/usr/bin/env python3
"""Linux job-owned subreaper; sessions and process groups do not escape it.

The guardian is a separate, single-threaded process with exactly one job. Thus
all of its direct/adopted children belong to that job, unlike a global /proc
scan in a caller that may also own unrelated subprocesses. Linux procfs,
PR_SET_CHILD_SUBREAPER, and pidfds are required before starting the command.
Cleanup assumes SIGKILL can eventually terminate the command's processes; the
guardian is never killed to make an unconfirmed cleanup appear successful.
"""
import ctypes
import errno
import json
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import time


def identity(pid):
    try:
        fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
        return int(fields[1]), int(fields[19])  # parent PID, kernel start ticks
    except FileNotFoundError:
        return None


def kill_owned(pid, owner):
    """Pin first, verify parent/start identity again, then signal that pidfd."""
    before = identity(pid)
    if before is None or before[0] != owner:
        return
    try:
        descriptor = os.pidfd_open(pid, 0)
    except ProcessLookupError:
        return
    try:
        if identity(pid) != before:
            return
        try:
            signal.pidfd_send_signal(descriptor, signal.SIGKILL, None, 0)
        except ProcessLookupError:
            pass
    finally:
        os.close(descriptor)


def drain(leader):
    """Kill parents; their surviving children are adopted on the next pass."""
    owner = os.getpid()
    children = Path(f'/proc/self/task/{owner}/children')
    while True:
        for pid in map(int, children.read_text().split()):
            kill_owned(pid, owner)
        while True:
            try:
                pid, status = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                return
            if pid == 0:
                break
            if leader is not None and pid == leader.pid:
                leader.returncode = os.waitstatus_to_exitcode(status)
        time.sleep(.01)


def guardian(configuration, cancellation, status):
    libc = ctypes.CDLL(None, use_errno=True)
    if not hasattr(os, 'pidfd_open') or not hasattr(signal, 'pidfd_send_signal'):
        raise OSError(errno.ENOSYS, 'managed jobs require Linux pidfds')
    # prctl(int option, unsigned long, ...); this process owns only this job.
    libc.prctl.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong,
                          ctypes.c_ulong, ctypes.c_ulong]
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), 'cannot enable job subreaper')
    Path(f'/proc/self/task/{os.getpid()}/children').read_text()
    probe = os.pidfd_open(os.getpid(), 0)
    os.close(probe)
    cancelled = False

    def cancel(*_):
        nonlocal cancelled
        cancelled = True

    signal.signal(signal.SIGTERM, cancel)
    signal.signal(signal.SIGINT, cancel)
    leader = None
    try:
        leader = subprocess.Popen(configuration['argv'], start_new_session=True,
                                  pass_fds=configuration['pass_fds'],
                                  shell=configuration['shell'], executable=configuration['executable'])
        status.write(json.dumps({'started': True}) + '\n')
        status.flush()
        while leader.poll() is None and not cancelled:
            ready, _, _ = select.select([cancellation], [], [], .05)
            if ready:
                # EOF also cancels if the manager dies without running finally.
                os.read(cancellation, 1)
                cancelled = True
    finally:
        drain(leader)
    return leader.returncode


def main():
    config_fd, cancel_fd, status_fd = map(int, sys.argv[1:])
    with os.fdopen(config_fd) as stream:
        configuration = json.load(stream)
    with os.fdopen(status_fd, 'w') as status:
        try:
            result = guardian(configuration, cancel_fd, status)
            status.write(json.dumps({'returncode': result}) + '\n')
        except OSError as error:
            status.write(json.dumps({'errno': error.errno, 'error': error.strerror,
                                     'filename': error.filename}) + '\n')
        finally:
            os.close(cancel_fd)


class Job:
    """Popen-like wait/context interface used only by dev.child."""
    def __init__(self, argv, **kwargs):
        configuration = dict(argv=([os.fsdecode(arg) for arg in argv]
                                   if not isinstance(argv, (str, bytes)) else os.fsdecode(argv)),
                             pass_fds=list(kwargs.pop('pass_fds', ())),
                             shell=kwargs.pop('shell', False),
                             executable=kwargs.pop('executable', None))
        if configuration['executable'] is not None:
            configuration['executable'] = os.fsdecode(configuration['executable'])
        config_fd = os.memfd_create('nirvana-job', os.MFD_CLOEXEC)
        cancel_read, self.cancel_write = os.pipe()
        status_read, status_write = os.pipe()
        self.process = None
        self.status = os.fdopen(status_read)
        self.result = None
        try:
            with os.fdopen(config_fd, 'w', closefd=False) as config:
                json.dump(configuration, config)
            os.lseek(config_fd, 0, os.SEEK_SET)
            self.process = subprocess.Popen(
                [sys.executable, str(Path(__file__).resolve()), str(config_fd), str(cancel_read), str(status_write)],
                start_new_session=True,
                pass_fds=(*configuration['pass_fds'], config_fd, cancel_read, status_write), **kwargs)
            # Only the guardian owns these ends after Popen's exec handshake.
            os.close(config_fd)
            config_fd = None
            os.close(cancel_read)
            cancel_read = None
            os.close(status_write)
            status_write = None
            record = self._record()
            if record != {'started': True}:
                self._error(record)
        except BaseException:
            self.close()
            raise
        finally:
            for descriptor in [config_fd, cancel_read, status_write]:
                if descriptor is not None:
                    os.close(descriptor)

    def _record(self):
        line = self.status.readline(8192)
        if not line or not line.endswith('\n'):
            raise OSError(errno.EIO, 'job guardian did not confirm cleanup')
        return json.loads(line)

    @staticmethod
    def _error(record):
        raise OSError(record.get('errno') or errno.EIO,
                      record.get('error', 'job guardian protocol error'), record.get('filename'))

    def wait(self, timeout=None):
        if self.result is None:
            self.process.wait(timeout=timeout)
            record = self._record()
            if 'returncode' not in record or type(record['returncode']) is not int:
                self._error(record)
            self.result = record['returncode']
        return self.result

    def cancel(self):
        if self.cancel_write is not None:
            try:
                os.write(self.cancel_write, b'x')
            except BrokenPipeError:
                pass
            os.close(self.cancel_write)
            self.cancel_write = None

    def close(self):
        self.cancel()
        if self.process is not None:
            # A second terminal interrupt must not interrupt descendant drain.
            blocked = signal.pthread_sigmask(signal.SIG_BLOCK, [signal.SIGINT, signal.SIGTERM])
            try:
                self.process.wait()
            finally:
                self.status.close()
                signal.pthread_sigmask(signal.SIG_SETMASK, blocked)
        else:
            self.status.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()


if __name__ == '__main__':
    main()
