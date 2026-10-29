#!/usr/bin/env bash
# Stage P2 pass 11 (from pass 10's probe): the base prover (base.s: the branch HEAD's committed
# prover.s, put here by the probe commit) and the new one (built by build-asm.sh as the runner
# does), on one runner. The new one runs `prover setup` first (untimed in the harness; timed and
# sized here) and its streams see RF_SETUP. Streams alternate base / new through rf-oracle
# (`stream.sh`: the ready/go/done handshake, every output checked by `acc` and timed, canaries).
#   probe/p2t11/run.sh OUTDIR    env: P2T9_CHAINS, P2T9_REPS (default 2), P2T11_BASE=0 (skip the
#   base), P2T11_TRACE=1 (bench-trace N2/N4), P2T11_ENV (extra env for the new streams),
#   P2T11_ALT (env of a third stream per rep, the new prover again: an A/B on one runner)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
{ lscpu; echo "nproc: $(nproc)"; free -m; gcc --version | head -1; as --version | head -1; git -C "$REPO" log -1 --format='commit %H'; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)' "$OUT/machine.txt"
P=$REPO/submissions/flock-recursive/prover
W=$OUT/asm
( time timeout 1500 "$P/build-asm.sh" "$W" ) > "$OUT/build-asm.log" 2>&1 || { tail -30 "$OUT/build-asm.log"; exit 1; }
tail -3 "$OUT/build-asm.log"
link() {  # link SRC.s DIR
  mkdir -p "$2"; rm -f "$2"/*
  python3 -I "$REPO/.contract/harness/tools/asm-compat.py" "$1" "$2/prover.s" 2>&1 | tail -1 || true
  [ -s "$2/prover.s" ] || cp "$1" "$2/prover.s"
  ( cd "$2" && time gcc -static -O2 -pthread ./*.s -o prover -lm ) > "$2.link.log" 2>&1 || { tail -30 "$2.link.log"; exit 1; }
}
link "$P/prover.s" "$W/runner"; BIN=$W/runner/prover
echo "committed prover.s sha256 $(sha256sum "$P/prover.s" | cut -d' ' -f1); rebuilt $(sha256sum "$W/build/prover.s" 2>/dev/null | cut -d' ' -f1); binary $(sha256sum "$BIN" | cut -d' ' -f1)" | tee -a "$OUT/machine.txt"
BASE=""
if [ "${P2T11_BASE:-1}" != 0 ] && [ -s "$HERE/base.s" ]; then
  link "$HERE/base.s" "$W/base"; BASE=$W/base/prover
  echo "base prover.s sha256 $(sha256sum "$HERE/base.s" | cut -d' ' -f1)" | tee -a "$OUT/machine.txt"
fi
[ -f "$REPO/.contract/service/Cargo.toml" ] || git -C "$REPO" submodule update --init .contract > "$OUT/submodule.log" 2>&1
TC=""; command -v rustup >/dev/null && rustup toolchain list 2>/dev/null | grep -q '^1.99.0' && TC="+1.99.0"
( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release --offline --locked ) > "$OUT/build-service.log" 2>&1 \
  || ( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release ) >> "$OUT/build-service.log" 2>&1 || { tail -30 "$OUT/build-service.log"; exit 1; }
timeout 600 "$BIN" selftest 2>&1 | tee "$OUT/selftest.log"
[ "${P2T11_TRACE:-0}" != 1 ] || { timeout 300 "$BIN" bench-trace N2; timeout 300 "$BIN" bench-trace N4; } 2>&1 | tee "$OUT/bench-trace.log"
# prover setup (the harness: 240 s, 4 GiB, untimed)
S=$OUT/setup; mkdir -p "$S"
( cd "$S" && /usr/bin/time -v timeout 300 "$BIN" setup "$S" ) > "$OUT/setup.log" 2>&1; echo "setup exit $?" | tee -a "$OUT/setup.log"
grep -E '^setup|Elapsed|Maximum res' "$OUT/setup.log"; du -sb "$S" | tee -a "$OUT/setup.log"
export P2T11_ALT=${P2T11_ALT-}
export P2T9_CHAINS=${P2T9_CHAINS:-"262144 262144 131072 262144 311951 393216 786432 1048576 131072"}
rc=0
for r in $(seq 1 "${P2T9_REPS:-2}"); do
  if [ -n "$BASE" ]; then
    FLOCK_PROF=1 FLOCK_VERBOSE=1 "$HERE/stream.sh" "$BASE" "$OUT/target-svc/release/rf-oracle" "$OUT/base-$r" || rc=1
  fi
  env RF_SETUP="$S" FLOCK_PROF=1 FLOCK_VERBOSE=1 ${P2T11_ENV:-} "$HERE/stream.sh" "$BIN" "$OUT/target-svc/release/rf-oracle" "$OUT/new-$r" || rc=1
  if [ -n "${P2T11_ALT:-}" ]; then
    env RF_SETUP="$S" FLOCK_PROF=1 FLOCK_VERBOSE=1 $P2T11_ALT "$HERE/stream.sh" "$BIN" "$OUT/target-svc/release/rf-oracle" "$OUT/alt-$r" || rc=1
  fi
done
echo "alt env: ${P2T11_ALT:-none}" > "$OUT/alt.txt"
for f in "$OUT"/base-*/stream.txt "$OUT"/new-*/stream.txt "$OUT"/alt-*/stream.txt; do [ -f "$f" ] && { echo "== $f"; cat "$f"; }; done > "$OUT/results.txt"
rm -rf "$OUT/target-svc" "$W/target"
exit "$rc"
