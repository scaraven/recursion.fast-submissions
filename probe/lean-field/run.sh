#!/usr/bin/env bash
# Build and run the compiled-Lean field/BLAKE2s probe, pinned to one core.
#   probe/lean-field/run.sh [OUTDIR]     env: CPU (core to pin, default 1), REPS (default 7),
#                                         CHECKER_RUNS (default 3), R (default 6), N (default 262144)
# Prints: the machine, the known-answer check, `name median min max` in ns per operation, and the
# chain checker's ns at the season shape (2^R chains of N BLAKE2s steps, as `T_triv`).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
CPU=${CPU:-1}; REPS=${REPS:-7}; RUNS=${CHECKER_RUNS:-3}; R=${R:-6}; N=${N:-262144}
{ lscpu; echo; grep -m1 -o -w -E 'pclmulqdq|vpclmulqdq|gfni|avx2|avx512f|sha_ni' /proc/cpuinfo | sort -u | tr '\n' ' '; echo;
  nproc; uptime; lean --version 2>/dev/null || true; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)|Thread|MHz' "$OUT/machine.txt" || true
cd "$HERE"
( time timeout 1200 lake build ) > "$OUT/build.log" 2>&1 || { tail -30 "$OUT/build.log"; exit 1; }
tail -4 "$OUT/build.log"
BIN=$HERE/.lake/build/bin
"$BIN/gfbench" check 12345 > "$OUT/check-12345.txt"
"$BIN/gfbench" check 999 > "$OUT/check-999.txt"
cat "$OUT"/check-*.txt > "$OUT/check-all.txt"
python3 -I "$HERE/checkgf.py" "$OUT/check-all.txt" | tee "$OUT/check.log" | tail -3
echo "== gfbench (taskset -c $CPU), ns/op: name median min max"
timeout 1200 taskset -c "$CPU" "$BIN/gfbench" bench 7 "$REPS" | tee "$OUT/bench.txt"
echo "== chaincheck at r=$R n=$N (taskset -c $CPU), ns"
python3 -I "$HERE/gen_leaves.py" "$R" "$N" "$OUT/leaves.json"
for i in $(seq "$RUNS"); do timeout 300 taskset -c "$CPU" "$BIN/chaincheck" "$OUT/leaves.json" 00; done | tee "$OUT/chaincheck.txt"
