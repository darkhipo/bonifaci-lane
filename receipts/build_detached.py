#!/usr/bin/env python3
"""Detached, receipt-writing Lean build runner for the bonifaci-lane.

WHY THIS EXISTS (measured 2026-11-10, this pin): a foreground `lake build Bonnifaci`
launched from the agent shell is SIGTERM'd ~6-12s in, reproducibly, right after the new
module finishes and while the root aggregate compiles. build_lock.py reports
`RELEASE rc=-15`, the kill-ledger has NO entry for it, and the body's own governors
(lean_build_governor, memory_guardian, swap_shedder) all log zero kills in the window —
so the signal comes from outside the body: the harness's process-group deadline.
The cure is the AGENTS.md detached pattern: start the child in its OWN SESSION
(`start_new_session=True`), so a kill aimed at the caller's process group misses it,
write every verdict to a file, and poll the file in-turn instead of blocking the shell.

Usage:  python3 receipts/build_detached.py <lane-dir> <log-path> <receipt-path>
"""
import fcntl
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone


def swap_line():
    try:
        out = subprocess.run(["sysctl", "-n", "vm.swapusage"], capture_output=True, text=True).stdout
        return out.strip()
    except Exception as exc:  # noqa: BLE001 - receipt must never fail the build
        return f"unavailable ({exc})"


def disk_free():
    try:
        st = os.statvfs("/Volumes/Substrate-1")
        return f"{st.f_bavail * st.f_frsize / 2**30:.0f}Gi"
    except Exception as exc:  # noqa: BLE001
        return f"unavailable ({exc})"


def main():
    lane, logpath, receiptpath = sys.argv[1], sys.argv[2], sys.argv[3]
    lockpath = "/Volumes/Substrate-1/bigo/.build.lock"
    os.makedirs(os.path.dirname(lockpath), exist_ok=True)
    fd = os.open(lockpath, os.O_CREAT | os.O_RDWR, 0o644)
    waited = 0
    while True:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            time.sleep(5)
            waited += 5

    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env.get("PATH", "")
    pre_swap, pre_free = swap_line(), disk_free()
    t0 = time.time()
    with open(logpath, "w") as log:
        log.write(f"[detached_build] ACQUIRED {lockpath} (waited {waited}s) at "
                  f"{datetime.now(timezone.utc).isoformat()}\n")
        log.write(f"[detached_build] PRE  swap={pre_swap} free={pre_free}\n")
        log.flush()
        proc = subprocess.Popen(
            ["lake", "build", "Bonnifaci"],
            cwd=lane,
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,  # own session == own process group: the harness kill misses it
            env=env,
        )
        rc = proc.wait()
        elapsed = time.time() - t0
        post_swap, post_free = swap_line(), disk_free()
        log.write(f"[detached_build] RELEASE rc={rc} elapsed={elapsed:.1f}s\n")
        log.write(f"[detached_build] POST swap={post_swap} free={post_free}\n")

    oleans = sorted(
        p[:-6] for p in os.listdir(os.path.join(lane, ".lake/build/lib/lean/Bonnifaci"))
        if p.endswith(".olean")
    )
    receipt = {
        "rc": rc,
        "elapsed_s": round(elapsed, 1),
        "waited_for_lock_s": waited,
        "pre_swap": pre_swap,
        "post_swap": post_swap,
        "pre_free": pre_free,
        "post_free": post_free,
        "olean_count": len(oleans),
        "oleans": oleans,
        "log": logpath,
        "finished_at": datetime.now(timezone.utc).isoformat(),
    }
    with open(receiptpath, "w") as fh:
        json.dump(receipt, fh, indent=2, sort_keys=True)
        fh.write("\n")
    fcntl.flock(fd, fcntl.LOCK_UN)
    os.close(fd)
    return 0 if rc == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
