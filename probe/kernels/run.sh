#!/usr/bin/env bash
# Prover-kernel probe (FR-R5): build with -C target-cpu=znver3 (falls back to native if this CPU
# lacks a feature znver3 enables), print the machine, run the self-test and every kernel at 1 and 4
# threads.   probe/kernels/run.sh OUTDIR      env: KERNELS (default "all"), THREADS (default 1,4),
#                                                 QUICK=1 (tiny sizes), RUSTFLAGS_OVERRIDE
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
THREADS=${THREADS:-1,4}; KERNELS=${KERNELS:-all}
{ lscpu; echo; echo "flags of interest: $(grep -m1 -o -w -E 'pclmulqdq|vpclmulqdq|gfni|avx2|avx512f|avx512bw|avx512vl|sha_ni|vaes' /proc/cpuinfo | sort -u | tr '\n' ' ')";
  echo "nproc: $(nproc)"; free -m; uptime; echo "ImageVersion: ${ImageVersion:-?}"; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)|Thread|flags of interest' "$OUT/machine.txt"
export RUSTFLAGS="${RUSTFLAGS_OVERRIDE:--C target-cpu=znver3}"
TC=""; command -v rustup >/dev/null && rustup toolchain list 2>/dev/null | grep -q '^1.99.0' && TC="+1.99.0"
missing=$(comm -23 <(rustc $TC --print cfg $RUSTFLAGS | sed -n 's/^target_feature="\(.*\)"/\1/p' | sort -u) \
                   <(rustc $TC --print cfg -C target-cpu=native | sed -n 's/^target_feature="\(.*\)"/\1/p' | sort -u) | tr '\n' ' ')
if [ -n "$missing" ]; then
  echo "WARNING: RUSTFLAGS ($RUSTFLAGS) enables features this CPU lacks ($missing); using -C target-cpu=native" | tee -a "$OUT/machine.txt"
  export RUSTFLAGS="-C target-cpu=native"
fi
echo "RUSTFLAGS=$RUSTFLAGS; $(rustc $TC --version)" | tee -a "$OUT/machine.txt"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$OUT/target}
( cd "$HERE" && time timeout 900 cargo $TC build --release --offline ) > "$OUT/build.log" 2>&1 || { tail -40 "$OUT/build.log"; exit 1; }
tail -3 "$OUT/build.log"
BIN=$CARGO_TARGET_DIR/release/kernels
Q=""; [ -n "${QUICK:-}" ] && Q="--quick"
# shellcheck disable=SC2086
/usr/bin/time -v timeout 5400 "$BIN" $KERNELS --threads "$THREADS" $Q 2> "$OUT/time.txt" | tee "$OUT/kernels.log"
rc=${PIPESTATUS[0]}
grep -E 'Maximum resident|Elapsed' "$OUT/time.txt"
grep -h RESULT "$OUT/kernels.log" > "$OUT/results.tsv" || true
grep -E 'SELFTEST' "$OUT/kernels.log" | tail -1
# end-to-end leaf / node-shaped pipelines, one process each (own peak RSS)
for p in ${PIPES:-30 31 32 30:43008}; do
  th=4; [ "$p" = 30 ] && th=1,4
  /usr/bin/time -v timeout 900 "$BIN" "pipe:$p" --threads "$th" 2> "$OUT/time-pipe-${p/:/_}.txt" | tee "$OUT/pipe-${p/:/_}.log" | grep -E 'PIPE|phase'
  grep -E 'Maximum resident' "$OUT/time-pipe-${p/:/_}.txt"
done
rm -rf "$OUT/target"
exit "$rc"
