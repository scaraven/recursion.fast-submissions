#!/usr/bin/env bash
# Stage P2 pass 9 (revision 4.1/4.3, the node prover): build prover.s as the runner does, then a
# stream through rf-oracle (`stream.sh`): `first` (two chains → N8), then `step`s (N2 for ≤ 2
# segments, N4 for 3–4), every output checked by the native `acc` (the node kinds' dumped programs,
# embedded in prover.s with the M rows in plan form) and its canary; node phase times (FLOCK_VERBOSE).
#   probe/p2t9/run.sh OUTDIR     env: P2T9_CHAINS (default below), P2T9_REPS (streams, default 1)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
{ lscpu; echo "nproc: $(nproc)"; free -m; gcc --version | head -1; as --version | head -1; git -C "$REPO" log -1 --format='commit %H'; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)' "$OUT/machine.txt"
TC=""; command -v rustup >/dev/null && rustup toolchain list 2>/dev/null | grep -q '^1.99.0' && TC="+1.99.0"
P=$REPO/submissions/flock-recursive/prover
W=$OUT/asm
( time timeout 1500 "$P/build-asm.sh" "$W" ) > "$OUT/build-asm.log" 2>&1 || { tail -30 "$OUT/build-asm.log"; exit 1; }
tail -3 "$OUT/build-asm.log"
mkdir -p "$W/runner"; rm -f "$W/runner"/*
python3 -I "$REPO/.contract/harness/tools/asm-compat.py" "$P/prover.s" "$W/runner/prover.s" 2>&1 | tail -1 || true
[ -s "$W/runner/prover.s" ] || cp "$P/prover.s" "$W/runner/prover.s"
( cd "$W/runner" && time gcc -static -O2 -pthread ./*.s -o prover -lm ) > "$OUT/link.log" 2>&1 || { tail -30 "$OUT/link.log"; exit 1; }
BIN=$W/runner/prover
echo "committed prover.s sha256 $(sha256sum "$P/prover.s" | cut -d' ' -f1); rebuilt $(sha256sum "$W/../asm/build/prover.s" 2>/dev/null | cut -d' ' -f1); runner copy $(sha256sum "$W/runner/prover.s" | cut -d' ' -f1); binary $(sha256sum "$BIN" | cut -d' ' -f1)" | tee -a "$OUT/machine.txt"
grep real "$OUT/link.log" | tee -a "$OUT/machine.txt"
[ -f "$REPO/.contract/service/Cargo.toml" ] || git -C "$REPO" submodule update --init .contract > "$OUT/submodule.log" 2>&1
( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release --offline --locked ) > "$OUT/build-service.log" 2>&1 \
  || ( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release ) >> "$OUT/build-service.log" 2>&1 || { tail -30 "$OUT/build-service.log"; exit 1; }
timeout 600 "$BIN" selftest 2>&1 | tee "$OUT/selftest.log"
export P2T9_CHAINS=${P2T9_CHAINS:-"262144 262144 131072 262144 393216 786432 1048576 131072"}
rc=0
for r in $(seq 1 "${P2T9_REPS:-1}"); do
  FLOCK_VERBOSE=1 "$HERE/stream.sh" "$BIN" "$OUT/target-svc/release/rf-oracle" "$OUT/stream-$r" || rc=1
done
cat "$OUT"/stream-*/stream.txt > "$OUT/results.txt"
rm -rf "$OUT/target-svc" "$W/target"
exit "$rc"
