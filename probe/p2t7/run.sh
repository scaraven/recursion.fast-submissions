#!/usr/bin/env bash
# Stage P2 pass 7 (blueprint revision 4.1, `seq4`, S-F4's segment programs): segment and aggregate
# times on the runner through probe/p2t-prover/run.sh (build-asm, link as the runner does, rf-oracle).
# Every proof is also run by the dumped Lean programs (logs/S-F4/dump, shipped by the probe commit):
# `lean_seg` (prove-leaf: the kind's program on the file's trace) and `lean_acc` (prove-agg: V_A
# reconstructed over the segment programs, `ir::run_agg`).
#   probe/p2t7/run.sh OUTDIR     env: P2T_CASES, P2T_REPS (default 2)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
export FLOCK_IR_DUMP=$REPO/logs/S-F4/dump FLOCK_ITEMS_JSON=$REPO/logs/S-F4/dump/items.json
( cd "$FLOCK_IR_DUMP" && sha256sum ops-L30.txt ops-L31.txt ops-L32.txt items.json ) | tee "$OUT/dump-sha.txt"
export P2T_REPS=${P2T_REPS:-2}
export P2T_CASES=${P2T_CASES:-"leaf:32:262144:4 leaf:32:196608:4 leaf:32:131073:4 leaf:32:65536:4 leaf:32:1:4 leaf:31:131072:4 leaf:31:65536:4 leaf:31:1:4 leaf:30:65536:4 leaf:30:32768:4 leaf:30:1:4 agg:262145:4 agg:1048576:4"}
"$HERE/../p2t-prover/run.sh" "$OUT"; rc=$?
grep -h -o 'lean_[a-z]*=[A-Za-z]*\|canary_accept=[a-z]*\| acc=[a-z]*' "$OUT"/leaf-*.log "$OUT"/agg-*.log | sort | uniq -c
exit "$rc"
