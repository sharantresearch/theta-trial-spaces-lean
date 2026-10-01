"""Run Lean through a four-slot, repository-local compiler semaphore.

Usage: python scripts/lean_check.py ThetaTrial/Module.lean [extra lean arguments]
Uses byte-range locks on Windows and POSIX; process exit releases its lock.
The verifier passes -j2 to each compiler process, separately from this limit.
"""
from contextlib import contextmanager
from pathlib import Path
import errno
import os
import shutil
import subprocess
import sys
import time

if os.name == "nt":
    import msvcrt
else:
    import fcntl

ROOT = Path(__file__).resolve().parents[1]
SLOTS = 4


def configure_output():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")


def try_lock(handle, slot):
    handle.seek(slot)
    try:
        if os.name == "nt":
            msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            fcntl.lockf(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB, 1, slot)
    except OSError as exc:
        if exc.errno in (errno.EACCES, errno.EAGAIN, errno.EDEADLK):
            return False
        raise
    return True


def unlock(handle, slot):
    handle.seek(slot)
    if os.name == "nt":
        msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
    else:
        fcntl.lockf(handle.fileno(), fcntl.LOCK_UN, 1, slot)


@contextmanager
def compiler_slot(lock_path):
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+b") as handle:
        # Concurrent initialization can append extra bytes; only the first four
        # are ever locked, so that does not change the semaphore's capacity.
        if lock_path.stat().st_size < SLOTS:
            handle.write(b"\0" * SLOTS)
            handle.flush()
        slot = None
        last_notice = time.monotonic()
        while slot is None:
            for candidate in range(SLOTS):
                if try_lock(handle, candidate):
                    slot = candidate
                    break
            if slot is None:
                if time.monotonic() - last_notice >= 30:
                    print("Waiting for a local Lean compiler slot...", flush=True)
                    last_notice = time.monotonic()
                time.sleep(0.5)
        try:
            yield slot
        finally:
            unlock(handle, slot)


def main():
    configure_output()
    if not sys.argv[1:]:
        raise SystemExit("Usage: lean_check.py ThetaTrial/Module.lean [lean arguments]")
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    lake = shutil.which("lake", path=env["PATH"])
    if lake is None:
        raise SystemExit("Lake not found; install elan and the pinned Lean toolchain first")
    with compiler_slot(ROOT / ".lake/compiler-slots.lock"):
        proc = subprocess.run([lake, "env", "lean", *sys.argv[1:]], cwd=ROOT, env=env,
                              encoding="utf-8", errors="replace")
    return proc.returncode


if __name__ == "__main__":
    sys.exit(main())
