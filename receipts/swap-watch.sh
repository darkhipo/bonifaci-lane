#!/bin/bash
LOG=/Volumes/Substrate-1/bigo/bonifaci-lane/receipts/swap-watch.log
GATE=12000
for i in $(seq 1 90); do
  USED=$(sysctl -n vm.swapusage | sed -E 's/.*used = ([0-9.]+)M.*/\1/')
  STAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  echo "$STAMP swap_used_MB=$USED" >> "$LOG"
  INT=${USED%.*}
  if [ "$INT" -lt "$GATE" ]; then
    echo "$STAMP GATE_OPEN" >> "$LOG"
    exit 0
  fi
  sleep 60
done
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) GATE_STILL_CLOSED" >> "$LOG"
exit 1
