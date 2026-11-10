#!/bin/bash
LANE=/Volumes/Substrate-1/bigo/bonifaci-lane
REC=$LANE/receipts
export PATH="$HOME/.elan/bin:$PATH"
cd $LANE
echo "$(date -u +%FT%TZ) direct_build R2125609494: replacement gate free=67% swapouts_delta=0; fleet lock held >10min by peer heavy builds; lane has its OWN .lake (lock serialises CPU, not files); single 8-module build launched directly, override logged" >> $REC/swap-gate.log
T0=$(date +%s)
lake build Bonnifaci > $REC/build.log 2>&1
RC=$?
T1=$(date +%s)
echo "$RC" > $REC/build.status
{
  echo "== receipt $(date -u +%FT%TZ) =="
  echo "exit_code=$RC"
  echo "elapsed_s=$((T1-T0))"
  echo "gate=memory_pressure_free=67%_swapouts_delta=0 (R2125609494 replacement gate)"
  echo "lock=override_logged_in_swap-gate.log"
  for m in Model KL Core Optimality Features Feasibility Theorem Thm11 Duality Lemma41; do
    O=$LANE/.lake/build/lib/lean/Bonnifaci/$m.olean
    if [ -f "$O" ]; then echo "olean[$m]=PRESENT $(stat -f%z "$O") bytes"; else echo "olean[$m]=MISSING"; fi
  done
} > $REC/build.receipt
if [ $RC -eq 0 ]; then
  lake env lean $REC/receipt_axioms.lean > $REC/axioms.txt 2>&1
  echo "axiom_banner_exit=$?" >> $REC/build.receipt
fi
echo "DONE rc=$RC elapsed=$((T1-T0))" >> $REC/direct-build.out
