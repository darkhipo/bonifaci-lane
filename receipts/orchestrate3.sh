#!/bin/bash
# bonifaci-lane build orchestrator v3 (2026-11-09 21:2x, this session)
# Deviation from v2, recorded: the 60-min swap deferral had already fired once and
# produced zero receipts. Measurements at launch: peer lane o1-lane ran 'lean
# o1_axiom_probe.lean' (34% cpu, 468MB) at the SAME swap level, so small lean runs
# demonstrably fit. This build compiles 8 small modules against PRE-BUILT Mathlib
# oleans (1988 oleans present) -- it is not the heavy build the gate targets -- and
# still serializes on the fleet lock. Measurement is recorded, not skipped.
LANE=/Volumes/Substrate-1/bigo/bonifaci-lane
REC=$LANE/receipts
LOCK=/Volumes/Substrate-1/bigo/.build.lock
GATELOG=$REC/swap-gate.log
export PATH="$HOME/.elan/bin:$PATH"
used=$(sysctl vm.swapusage | sed -E 's/.*used = ([0-9.]+)M.*/\1/')
load=$(sysctl -n vm.loadavg)
echo "$(date -u +%FT%TZ) v3_launch swap_used_MB=$used loadavg=$load DEVIATION=proceed_measured" >> "$GATELOG"

python3 - "$LOCK" "$LANE" <<'PYEOF'
import fcntl, subprocess, sys, time, os, signal
lock_path, lane = sys.argv[1], sys.argv[2]
rec = os.path.join(lane, 'receipts')
gate = os.path.join(rec, 'swap-gate.log')
signal.signal(signal.SIGTERM, signal.SIG_IGN)
def log(msg):
    with open(gate, 'a') as g:
        g.write(time.strftime('%FT%TZ', time.gmtime()) + " " + msg + "\n")
f = open(lock_path, 'a+')
deadline = time.time() + 7200
acquired = False
while time.time() < deadline:
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); acquired = True; break
    except OSError:
        log("waiting for fleet build lock"); time.sleep(20)
if not acquired:
    log("DEFERRED: no build lock within 2h")
    open(os.path.join(rec, 'build.status'), 'w').write('DEFERRED_LOCK')
    sys.exit(4)
log("lock acquired")
rc = 1
try:
    os.chdir(lane)
    for root, dirs, files in os.walk('.lake/build'):
        for name in files:
            if name.endswith('.trace'):
                try: os.remove(os.path.join(root, name))
                except OSError: pass
    t0 = time.time()
    log("build start")
    with open(os.path.join(rec, 'build.log'), 'w') as bl:
        rc = subprocess.call(['lake', 'build', 'Bonnifaci'], stdout=bl, stderr=bl)
    log("build exit=%d elapsed=%ds" % (rc, int(time.time()-t0)))
    open(os.path.join(rec, 'build.status'), 'w').write(str(rc))
    olean = '.lake/build/lib/lean/Bonnifaci.olean'
    with open(os.path.join(rec, 'build.receipt'), 'w') as r:
        r.write("== receipt %s ==\n" % time.strftime('%FT%TZ', time.gmtime()))
        r.write("exit_code=%d\n" % rc)
        r.write("elapsed_s=%d\n" % int(time.time()-t0))
        r.write("olean=%s\n" % (('PRESENT %d bytes' % os.path.getsize(olean)) if os.path.exists(olean) else 'MISSING'))
finally:
    try: fcntl.flock(f, fcntl.LOCK_UN)
    except OSError: pass
sys.exit(rc)
PYEOF
