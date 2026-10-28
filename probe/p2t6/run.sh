#!/usr/bin/env bash
# Stage P2 pass 6 (blueprint revision 4.1): the per-phase profile (FLOCK_PROF=1 sub-phase timers) of
# the segment prover and the kernel/memory throughput (`prover bench`) on the runner, through
# probe/p2t-prover/run.sh (build-asm, link as the runner does, rf-oracle).
#   probe/p2t6/run.sh OUTDIR     env: P2T_CASES, P2T_REPS (default 3), P2T6_BENCH (default "1 2 4"),
#   P2T6_SET (or the file probe/p2t6/set): profile | overlap | kern | kern2 | final (final.sh: base vs new)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
SET=${P2T6_SET:-$(cat "$HERE/set" 2>/dev/null || echo profile)}
[ "$SET" = final ] && exec "$HERE/final.sh" "$OUT"
export P2T_REPS=${P2T_REPS:-3}
# P2T6_SET picks the case list (the probe workflow passes no environment)
case "$SET" in
  profile) CASES0="leaf:32:262144:4:FLOCK_PROF=1 leaf:32:131072:4:FLOCK_PROF=1 leaf:31:131072:4:FLOCK_PROF=1" ;;
  overlap) CASES0="leaf:32:262144:4:FLOCK_PROF=1 leaf:32:131072:4 agg:524288:4 agg:524288:4:FLOCK_NO_OVERLAP=1 agg:1048576:4 agg:1048576:4:FLOCK_NO_OVERLAP=1 agg:262145:4 agg:262145:4:FLOCK_NO_OVERLAP=1"; P2T6_BENCH=${P2T6_BENCH-} ;;
  kern) CASES0="leaf:32:262144:4:FLOCK_PROF=1 leaf:32:131072:4:FLOCK_PROF=1 leaf:31:131072:4:FLOCK_PROF=1 agg:524288:3 agg:524288:4:FLOCK_NO_OVERLAP=1"; P2T6_BENCH=${P2T6_BENCH-4} ;;
  kern2) CASES0="leaf:32:262144:4:FLOCK_PROF=1 leaf:32:131072:4:FLOCK_PROF=1 leaf:31:131072:4:FLOCK_PROF=1"; P2T6_BENCH=${P2T6_BENCH-1 4} ;;
  *) CASES0="leaf:32:262144:4:FLOCK_PROF=1 leaf:32:131072:4:FLOCK_PROF=1 leaf:31:131072:4:FLOCK_PROF=1 leaf:31:1:4" ;;
esac
export P2T_CASES=${P2T_CASES:-$CASES0}
"$HERE/../p2t-prover/run.sh" "$OUT"; rc=$?
BIN=$OUT/asm/runner/prover
for t in ${P2T6_BENCH-1 2 4}; do FLOCK_THREADS=$t timeout 600 "$BIN" bench; done 2>&1 | tee "$OUT/bench.txt"
grep -h -o 'prof .*' "$OUT"/leaf-*.log | head -20
exit "$rc"
