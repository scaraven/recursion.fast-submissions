#!/usr/bin/env bash
# probe/flock-bench/run.sh [WORK_DIR]
#
# Flock throughput probe for a GitHub runner (ubuntu-24.04, rustup present). Self-contained: clones
# github.com/succinctlabs/flock at the pinned commit, builds it with RUSTFLAGS=$FLOCK_RUSTFLAGS
# (default `-C target-cpu=znver3`: the evaluation runner is an AMD EPYC 7763, Zen 3, with AVX2,
# PCLMULQDQ, 256-bit VPCLMULQDQ, SHA-NI, no AVX-512, no GFNI; RUSTFLAGS overrides the repository's
# own `.cargo/config.toml` `-C target-cpu=native`). Flock selects its kernels at COMPILE time by
# `cfg(target_feature)`: on Zen 3 its AVX-512+VPCLMULQDQ kernels are compiled out and it runs the
# scalar-PCLMULQDQ GF(2^128) product with portable NTT / transpose / shift-reduce kernels (there is
# no ymm path). Set FLOCK_RUSTFLAGS="-C target-cpu=native" on an AVX-512 host for the fast path. Then:
#   1. the README's hash_throughput bench (BLAKE3 and SHA-256 compressions, best of 3 after a
#      verified warm-up) at batches 2^14 and 2^16, with 1 and 4 threads;
#   2. proof size / peak memory / verify time of one BLAKE3 batch proof at 2^16 under the Ligerito
#      profiles `secure` (120-bit unique decoding) and `fast` (strict 128), 4 threads;
#   3. the recursion tower: the per-stage online bench `tower::e2e_tests::tower_online_bench`
#      (leaf / FL / node / spine medians; prints node BLAKE rows, prove ms, proof KiB and the
#      per-shape circuit-build time) at CHAIN_BLOCKS=65536, then `examples/tower.rs` (8 leaves x
#      TOWER_BLOCKS, Chain128), each under a timeout (a timeout is reported, not fatal). On the
#      development VM (no clmul) one node shape's circuit build alone took ~106 s, serial.
# Everything is printed and also written to WORK_DIR/out/*.log. Knobs (env): LOG2S ("14 16"),
# THREADS ("1 4"), RUNS (3), PROOF_LOG2 (16), PROOF_PROFILES ("secure fast"), ONLINE_BLOCKS (65536),
# ONLINE_TIMEOUT (600), TOWER_BLOCKS (4096), TOWER_TIMEOUT (420), SKIP_TOWER, SKIP_EXAMPLE (unset).
set -uo pipefail

FLOCK_REPO=https://github.com/succinctlabs/flock
FLOCK_COMMIT=48f4bfe56af8c2b0ded19b8990622c4985c21d65   # main, 2026-10-26 (PR #65)
TOOLCHAIN=1.99.0                                        # the toolchain of the VM measurements
FLOCK_RUSTFLAGS=${FLOCK_RUSTFLAGS:-"-C target-cpu=znver3"}
LOG2S=${LOG2S:-"14 16"}
THREADS=${THREADS:-"1 4"}
RUNS=${RUNS:-3}
PROOF_LOG2=${PROOF_LOG2:-16}
PROOF_PROFILES=${PROOF_PROFILES:-"secure fast"}
TOWER_BLOCKS=${TOWER_BLOCKS:-4096}
ONLINE_BLOCKS=${ONLINE_BLOCKS:-65536}
TOWER_TIMEOUT=${TOWER_TIMEOUT:-420}
ONLINE_TIMEOUT=${ONLINE_TIMEOUT:-600}

WORK=$(mkdir -p "${1:-$PWD/flock-bench-work}" && cd "${1:-$PWD/flock-bench-work}" && pwd)
OUT=$WORK/out
mkdir -p "$OUT"
SRC=$WORK/flock
export CARGO_TARGET_DIR=$WORK/target
export RUSTUP_TOOLCHAIN=$TOOLCHAIN
export RUSTFLAGS=$FLOCK_RUSTFLAGS
TIME=/usr/bin/time; [ -x "$TIME" ] || TIME=""
tv() { if [ -n "$TIME" ]; then "$TIME" -v "$@"; else "$@"; fi; }

section() { echo; echo "=================== $* ==================="; }

section "machine"
{
  date -Is
  lscpu
  echo; echo "nproc: $(nproc)"; free -g
  echo "flags of interest: $(grep -o -w -E 'pclmulqdq|vpclmulqdq|gfni|avx512f|avx512bw|avx512vl|avx512vbmi|avx2|sha_ni|vaes' /proc/cpuinfo | sort -u | tr '\n' ' ')"
  [ -n "${ImageOS:-}" ] && echo "ImageOS=$ImageOS ImageVersion=${ImageVersion:-}"
} 2>&1 | tee "$OUT/machine.log"

section "toolchain + source"
{
  rustup toolchain install "$TOOLCHAIN" --profile minimal
  rustc --version; cargo --version
  if [ ! -d "$SRC/.git" ]; then
    git init -q "$SRC" && git -C "$SRC" remote add origin "$FLOCK_REPO"
  fi
  git -C "$SRC" fetch -q --depth 1 origin "$FLOCK_COMMIT" && git -C "$SRC" checkout -q --detach FETCH_HEAD
  echo "flock HEAD: $(git -C "$SRC" rev-parse HEAD)"
  [ "$(git -C "$SRC" rev-parse HEAD)" = "$FLOCK_COMMIT" ] || { echo "wrong commit" >&2; exit 1; }
  echo "repo rustflags (overridden by RUSTFLAGS): $(cat "$SRC/.cargo/config.toml" | tr '\n' ' ')"
  echo "RUSTFLAGS=$RUSTFLAGS; enabled target features:"; rustc --print cfg $RUSTFLAGS | grep target_feature | tr '\n' ' '; echo
  echo "host (target-cpu=native) features:"; rustc --print cfg -C target-cpu=native | grep target_feature | tr '\n' ' '; echo
} 2>&1 | tee "$OUT/toolchain.log"
[ "${PIPESTATUS[0]}" = 0 ] || exit 1
# refuse to run a build that would SIGILL: every feature RUSTFLAGS enables must be on the host
missing=$(comm -23 <(rustc --print cfg $RUSTFLAGS | sed -n 's/^target_feature="\(.*\)"/\1/p' | sort -u) \
                   <(rustc --print cfg -C target-cpu=native | sed -n 's/^target_feature="\(.*\)"/\1/p' | sort -u) | tr '\n' ' ')
if [ -n "$missing" ]; then
  echo "WARNING: RUSTFLAGS enables features this CPU lacks ($missing); using -C target-cpu=native" | tee -a "$OUT/toolchain.log"
  export RUSTFLAGS="-C target-cpu=native"
fi
for f in pclmulqdq vpclmulqdq avx512f gfni; do
  rustc --print cfg $RUSTFLAGS | grep -q "target_feature=\"$f\"" && echo "build has $f" || echo "build lacks $f"
done | tr '\n' ';' | tee -a "$OUT/toolchain.log"; echo
echo "Flock tier: AVX-512+VPCLMULQDQ kernels need avx512f+vpclmulqdq; scalar GF(2^128) mul needs pclmulqdq; else bit-serial portable" | tee -a "$OUT/toolchain.log"

section "build (cargo build --release --locked)"
( cd "$SRC" && tv timeout 1800 cargo build --release --locked ) 2>&1 | tail -30 | tee "$OUT/build.log"

section "build hash_throughput bench"
( cd "$SRC" && timeout 1800 cargo bench --locked --no-run --bench hash_throughput ) > "$OUT/bench-build.log" 2>&1
BIN=$(sed -n 's/.*Executable benches\/hash_throughput.rs (\(.*\))/\1/p' "$OUT/bench-build.log" | tail -1)
tail -3 "$OUT/bench-build.log"
[ -x "$BIN" ] || { echo "bench binary not found" >&2; exit 1; }

for t in $THREADS; do
  if [ "$t" = 1 ]; then PIN="taskset -c 0"; else PIN=""; fi
  for l in $LOG2S; do
    section "hash_throughput: $t thread(s), batch 2^$l"
    ( cd "$SRC" && RAYON_NUM_THREADS=$t HASH_BENCH_LOG2S=$l HASH_BENCH_RUNS=$RUNS tv timeout 1200 $PIN "$BIN" ) \
      2>&1 | tee "$OUT/hash-t$t-2e$l.log" | grep -E 'RESULT|thread\(s\)|run [0-9]|Maximum resident|Elapsed|Command exited'
  done
done

section "blake3_proof: proof size / peak memory / verify at 2^$PROOF_LOG2, 4 threads"
( cd "$SRC" && timeout 1800 cargo bench --locked --no-run --bench blake3_proof ) > "$OUT/proof-build.log" 2>&1
PBIN=$(sed -n 's/.*Executable benches\/blake3_proof.rs (\(.*\))/\1/p' "$OUT/proof-build.log" | tail -1)
if [ -x "$PBIN" ]; then
  for p in $PROOF_PROFILES; do
    echo "--- profile $p"
    ( cd "$SRC" && BLAKE3_PROFILE=$p BLAKE3_LOG2S=$PROOF_LOG2 BLAKE3_RUNS=1 RAYON_NUM_THREADS=4 timeout 900 "$PBIN" ) \
      2>&1 | tee "$OUT/proof-$p-2e$PROOF_LOG2.log" | grep -E '===|best prove_fast|peak memory|verify:|proof size'
  done
else
  echo "blake3_proof binary not found (see $OUT/proof-build.log)"
fi

if [ -z "${SKIP_TOWER:-}" ]; then
  section "tower_online_bench: CHAIN_BLOCKS=$ONLINE_BLOCKS, BENCH_RUNS=2 (timeout ${ONLINE_TIMEOUT}s)"
  # cargo test pulls the crate's dev-dependency feature `unsound-challenger` into the test build
  # (feature unification); the default challenger used by the bench is unchanged by it.
  ( cd "$SRC" && timeout 1800 cargo test --release --locked -p flock-prover --lib --no-run ) > "$OUT/online-build.log" 2>&1
  tail -2 "$OUT/online-build.log"
  ( cd "$SRC" && CHAIN_BLOCKS=$ONLINE_BLOCKS BENCH_RUNS=2 tv timeout "$ONLINE_TIMEOUT" \
      cargo test --release --locked -p flock-prover --lib tower::e2e_tests::tower_online_bench -- --ignored --exact --nocapture ) \
    2>&1 | tee "$OUT/tower-online.log" | grep -v -E '^\s*$|envelope rows' | tail -80
  [ "${PIPESTATUS[0]}" = 124 ] && echo "TOWER ONLINE BENCH: TIMEOUT after ${ONLINE_TIMEOUT}s (partial output above)"

  if [ -z "${SKIP_EXAMPLE:-}" ]; then
    section "tower example: 8 leaves x $TOWER_BLOCKS compressions, chain128 (timeout ${TOWER_TIMEOUT}s)"
    ( cd "$SRC" && timeout 1800 cargo build --release --locked --example tower ) > "$OUT/tower-build.log" 2>&1
    tail -2 "$OUT/tower-build.log"
    ( cd "$SRC" && tv timeout "$TOWER_TIMEOUT" "$CARGO_TARGET_DIR/release/examples/tower" 8 "$TOWER_BLOCKS" chain128 ) \
      2>&1 | tee "$OUT/tower-example.log" | grep -v -E '^\s*$|envelope rows' | tail -40
    [ "${PIPESTATUS[0]}" = 124 ] && echo "TOWER EXAMPLE: TIMEOUT after ${TOWER_TIMEOUT}s (partial output above)"
  fi
fi

section "summary"
echo "machine: $(lscpu | sed -n 's/^Model name: *//p') ; $(nproc) CPUs ; RUSTFLAGS=$RUSTFLAGS"
grep -h RESULT "$OUT"/hash-t*.log | awk -F'\t' '{printf "%-7s batch %7d  %2d thr  %9.3f s  %10.1f hashes/s\n", $2, $3, $4, $5, $6}'
for f in "$OUT"/hash-t*.log; do echo "$(basename "$f" .log): peak RSS $(sed -n 's/.*Maximum resident set size (kbytes): //p' "$f") kB"; done
grep -h -E "proof size|peak memory" "$OUT"/proof-*.log 2>/dev/null
grep -h -E "TOWER|ONE root proof|PER PROOF|SETUP|outer: BLAKE|amortized|amortised|median" "$OUT"/tower-*.log 2>/dev/null | head -40
echo "logs: $OUT"
