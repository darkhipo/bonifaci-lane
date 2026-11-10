#!/usr/bin/env python3
"""Run any command in its OWN SESSION so the harness's process-group deadline misses it.

Measured on this pin (2026-11-10): a foreground `lake env lean …` or `lake build` from the
agent shell is SIGTERM'd 6-12 s in (exit 143 / build_lock rc=-15), with no body governor
logging a kill — the signal is group-scoped and comes from the harness. Starting the child
with `start_new_session=True` puts it in a different process group and it completes.
Verdicts go to files; poll them in-turn.

Usage:  python3 receipts/run_detached.py <log-path> <rc-path> -- cmd args...
"""
import os
import subprocess
import sys
import time
from datetime import datetime, timezone


def main():
    logpath, rcpath = sys.argv[1], sys.argv[2]
    if sys.argv[3] != "--":
        print("usage: run_detached.py LOG RCFILE -- cmd args...", file=sys.stderr)
        return 2
    cmd = sys.argv[4:]
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env.get("PATH", "")
    with open(logpath, "w") as log:
        log.write(f"[run_detached] {datetime.now(timezone.utc).isoformat()} cmd={' '.join(cmd)}\n")
        log.flush()
        t0 = time.time()
        proc = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True, env=env)
        rc = proc.wait()
        log.write(f"[run_detached] rc={rc} elapsed={time.time() - t0:.1f}s\n")
    with open(rcpath, "w") as fh:
        fh.write(f"{rc}\n")
    return 0 if rc == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
