#!/usr/bin/env python3
"""Single-writer build lock via fcntl (macOS has no flock(1)).

Usage: build_lock.py LOCKFILE -- cmd args...

Acquires an exclusive advisory lock on LOCKFILE, runs the command, releases.
Runs the child in its own session with SIGTERM ignored only in the wrapper sense:
we do NOT ignore signals; we just hold the lock so concurrent builds serialize.
Receipts: caller redirects stdout/stderr.
"""
import fcntl
import os
import subprocess
import sys
import time


def main():
    if len(sys.argv) < 4 or sys.argv[2] != "--":
        print("usage: build_lock.py LOCKFILE -- cmd args...", file=sys.stderr)
        return 2
    lockpath = sys.argv[1]
    cmd = sys.argv[3:]

    os.makedirs(os.path.dirname(lockpath) or ".", exist_ok=True)
    fd = os.open(lockpath, os.O_CREAT | os.O_RDWR, 0o644)
    waited = 0
    while True:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if waited % 60 == 0:
                print(f"[build_lock] waiting for {lockpath} ({waited}s)", file=sys.stderr, flush=True)
            time.sleep(5)
            waited += 5

    print(f"[build_lock] ACQUIRED {lockpath} (waited {waited}s); cmd={' '.join(cmd)}",
          file=sys.stderr, flush=True)
    t0 = time.time()
    try:
        rc = subprocess.call(cmd)
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)
    print(f"[build_lock] RELEASE rc={rc} elapsed={time.time()-t0:.0f}s", file=sys.stderr, flush=True)
    return rc


if __name__ == "__main__":
    sys.exit(main())
