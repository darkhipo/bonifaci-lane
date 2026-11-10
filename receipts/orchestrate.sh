#!/bin/bash
# bonifaci-lane build orchestrator — enforces fleet admission control (2026-11-09):
#   1. swap gate: vm.swapusage used > 12 GB => sleep 300, recheck; cap 60 min => DEFER.
#   2. single heavy build fleet-wide: flock -w 7200 /Volumes/Substrate-1/bigo/.build.lock
#   3. detached build with trap "" TERM; receipts to files; .trace bust on kill-resume.
LANE=/Volumes/Substrate-1/bigo/bonifaci-lane
REC=$LANE/receipts
LOCK=/Volumes/Substrate-1/bigo/.build.lock
GATELOG=$REC/swap-gate.log
echo "orchestrator start $(date -u +%FT%TZ)" >> "$GATELOG"

# --- gate 1: swap ---
deadline=$(( $(date +%s) + 3600 ))   # 60 min cap
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

# --- gate 2: fleet-wide single build ---
exec 9>"$LOCK"
if ! flock -w 7200 9; then
  echo "DEFERRED: could not acquire build lock within 2h" >> "$GATELOG"
  echo "DEFERRED" > "$REC/build.status"
  exit 4
fi
echo "lock acquired $(date -u +%FT%TZ)" >> "$GATELOG"

# --- build: detached-safe (this script itself is detached; TERM-immune) ---
trap "" TERM
cd "$LANE" || exit 5
# bust stale traces from any previously killed run
find .lake/build -name '*.trace' -delete 2>/dev/null
echo "build start $(date -u +%FT%TZ)" >> "$GATELOG"
start=$(date +%s)
lake build Bonnifaci > "$REC/build.log" 2>&1
rc=$?
end=$(date +%s)
echo "build exit=$rc elapsed=$((end-start))s $(date -u +%FT%TZ)" >> "$GATELOG"
echo "$rc" > "$REC/build.status"

# --- receipts ---
{
  echo "== receipt $(date -u +%FT%TZ) =="
  echo "exit_code=$rc"
  if [ $rc -eq 0 ] && [ -f .lake/build/lib/lean/Bonnifaci.olean ]; then
    echo "olean=Bonnifaci.olean PRESENT $(ls -la .lake/build/lib/lean/Bonnifaci.olean | awk '{print $5" bytes"}')"
  else
    echo "olean=MISSING"
  fi
} > "$REC/build.receipt"

if [ $rc -eq 0 ]; then
  lake env lean receipts/receipt_axioms.lean > "$REC/axioms.txt" 2>&1
  echo "axiom_banner_exit=$?" >> "$REC/build.receipt"
fi
exit $rc
