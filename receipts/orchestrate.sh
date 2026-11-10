#!/bin/bash
# bonifaci-lane build orchestrator v2 — fleet admission control (2026-11-09):
#   1. swap gate: vm.swapusage used > 12 GB => sleep 300, recheck; cap 60 min => DEFER.
#   2. single heavy build fleet-wide: fcntl.flock on /Volumes/Substrate-1/bigo/.build.lock
#      (macOS has no /usr/bin/flock; fcntl via python3 stdlib is the portable lock).
#   3. detached build, TERM-immune; receipts to files; .trace bust on kill-resume.
LANE=/Volumes/Substrate-1/bigo/bonifaci-lane
REC=$LANE/receipts
LOCK=/Volumes/Substrate-1/bigo/.build.lock
GATELOG=$REC/swap-gate.log
export PATH="$HOME/.elan/bin:$PATH"
echo "orchestrator-v2 start $(date -u +%FT%TZ)" >> "$GATELOG"

# --- gate 1: swap ---
deadline=$(( $(date +%s) + 3600 ))
while :; do
  used=$(sysctl vm.swapusage | sed -E 's/.*used = ([0-9.]+)M.*/\1/')
  echo "$(date -u +%FT%TZ) swap_used_MB=$used" >> "$GATELOG"
  ok=$(awk -v u="$used" 'BEGIN{print (u < 12288) ? 1 : 0}')
  [ "$ok" = "1" ] && break
  if [ "$(date +%s)" -ge "$deadline" ]; then
    echo "DEFERRED: swap gate never cleared within 60 min (last=$used MB)" >> "$GATELOG"
    echo "DEFERRED" > "$REC/build.status"
    exit 3
  fi
  sleep 300
done
echo "swap gate cleared $(date -u +%FT%TZ)" >> "$GATELOG"

# --- gates 2+3: locked build section (TERM-immune), via fcntl.flock ---
python3 - "$LOCK" "$LANE" <<'PYEOF'
import fcntl, subprocess, sys, time, os, signal

lock_path, lane = sys.argv[1], sys.argv[2]
rec = os.path.join(lane, 'receipts')
gate = os.path.join(rec, 'swap-gate.log')
signal.signal(signal.SIGTERM, signal.SIG_IGN)  # trap "" TERM discipline

def log(msg):
    with open(gate, 'a') as g:
        g.write(f"{time.strftime('%FT%TZ', time.gmtime())} {msg}\n")

f = open(lock_path, 'a+')
deadline = time.time() + 7200
acquired = False
while time.time() < deadline:
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        acquired = True
        break
    except OSError:
        time.sleep(30)
if not acquired:
    log("DEFERRED: could not acquire build lock within 2h")
    open(os.path.join(rec, 'build.status'), 'w').write('DEFERRED')
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
    log("build start")
    t0 = time.time()
    with open(os.path.join(rec, 'build.log'), 'w') as bl:
        rc = subprocess.call(['lake', 'build', 'Bonnifaci'], stdout=bl, stderr=bl)
    log(f"build exit={rc} elapsed={int(time.time()-t0)}s")
    open(os.path.join(rec, 'build.status'), 'w').write(str(rc))
    olean = '.lake/build/lib/lean/Bonnifaci.olean'
    with open(os.path.join(rec, 'build.receipt'), 'w') as r:
        r.write(f"== receipt {time.strftime('%FT%TZ', time.gmtime())} ==\n")
        r.write(f"exit_code={rc}\n")
        r.write(f"olean={'Bonnifaci.olean PRESENT ' + str(os.path.getsize(olean)) + ' bytes' if os.path.exists(olean) else 'MISSING'}\n")
    if rc == 0:
        with open(os.path.join(rec, 'axioms.txt'), 'w') as ax:
            arc = subprocess.call(['lake', 'env', 'lean', 'receipts/receipt_axioms.lean'],
                                  stdout=ax, stderr=ax)
        with open(os.path.join(rec, 'build.receipt'), 'a') as r2:
            r2.write(f"axiom_banner_exit={arc}\n")
finally:
    try:
        fcntl.flock(f, fcntl.LOCK_UN)
    except OSError:
        pass
sys.exit(rc)
PYEOF
