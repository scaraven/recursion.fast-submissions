#!/usr/bin/env bash
# Stage P2 probe: build prover.s with build-asm.sh (rust 1.99.0), pass it through asm-compat.py,
# assemble and link it exactly as the runner does (gcc -static -O2 -pthread *.s -o prover -lm, the
# image's binutils), then: selftest; stream `leaf` requests (fresh process, ready/go/done) at
# n = 2^16 with the native acc and canary; prove-leaf at m = 30 with the node-shape surrogate;
# prove-leaf at m = 32. Every prover run uses the linked prover.s binary.
#   probe/p2-prover/run.sh OUTDIR     env: P2_LEAF_REQS (3), P2_M32 (2), RF_ORACLE_BIN
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
{ lscpu; echo "nproc: $(nproc)"; free -m; echo "ImageVersion: ${ImageVersion:-?}"; gcc --version | head -1; as --version | head -1; ld --version | head -1; ldd --version | head -1; git -C "$REPO" log -1 --format='commit %H'; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|GNU assembler|^gcc' "$OUT/machine.txt"
TC=""; command -v rustup >/dev/null && rustup toolchain list 2>/dev/null | grep -q '^1.99.0' && TC="+1.99.0"
P=$REPO/submissions/flock-recursive/prover
W=$OUT/asm
( time timeout 1500 "$P/build-asm.sh" "$W" ) > "$OUT/build-asm.log" 2>&1 || { tail -30 "$OUT/build-asm.log"; exit 1; }
tail -2 "$OUT/build-asm.log"
mkdir -p "$W/runner"; rm -f "$W/runner"/*
python3 -I "$REPO/.contract/harness/tools/asm-compat.py" "$P/prover.s" "$W/runner/prover.s" 2>&1 | tail -1 || cp "$P/prover.s" "$W/runner/prover.s"
[ -s "$W/runner/prover.s" ] || cp "$P/prover.s" "$W/runner/prover.s"
( cd "$W/runner" && time gcc -static -O2 -pthread ./*.s -o prover -lm ) > "$OUT/link.log" 2>&1 || { tail -30 "$OUT/link.log"; exit 1; }
BIN=$W/runner/prover
echo "prover.s sha256 $(sha256sum "$W/runner/prover.s" | cut -d' ' -f1); binary $(sha256sum "$BIN" | cut -d' ' -f1)" | tee -a "$OUT/machine.txt"
SVC=${RF_ORACLE_BIN:-}
if [ -z "$SVC" ]; then
  [ -f "$REPO/.contract/service/Cargo.toml" ] || git -C "$REPO" submodule update --init .contract > "$OUT/submodule.log" 2>&1
  ( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release --offline --locked ) > "$OUT/build-service.log" 2>&1 \
    || ( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release ) >> "$OUT/build-service.log" 2>&1 || { tail -30 "$OUT/build-service.log"; exit 1; }
  SVC=$OUT/target-svc/release/rf-oracle
fi
timeout 600 "$BIN" selftest 2>&1 | tee "$OUT/selftest.log"
D=$(mktemp -d /tmp/rfp2.XXXXXX); mkfifo "$D/in"
"$SVC" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
spid=$!; exec 3> "$D/in"
for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
rc=0
for i in $(seq "${P2_LEAF_REQS:-3}"); do
  timeout 300 python3 -I "$HERE/request.py" "$BIN" "$D/req$i" "$D/oracle.sock" 65536 "$(printf '%064x' $((i * 7919)))" 2>&1 | tee -a "$OUT/requests.log" || rc=1
done
( cd "$D" && FLOCK_VERBOSE=1 FLOCK_PREFAULT_MIB=1800 RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 600 "$BIN" prove-leaf 30 --reps 2 --out "$D/l30.bin" ) > "$OUT/leaf30.log" 2> "$OUT/time-leaf30.txt" || rc=1
( cd "$D" && FLOCK_VERBOSE=1 FLOCK_PREFAULT_MIB=6000 RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 900 "$BIN" prove-leaf 32 --reps "${P2_M32:-2}" --out "$D/l32.bin" ) > "$OUT/leaf32.log" 2> "$OUT/time-leaf32.txt" || rc=1
exec 3>&-; wait "$spid"; cp "$D/svc.log" "$OUT/svc.log"; rm -rf "$D"
grep -h -E 'PROVE-LEAF|LEAF-REQUEST|SELFTEST' "$OUT"/*.log | cut -c1-600 > "$OUT/results.txt"; cat "$OUT/results.txt" | cut -c1-300
grep -h -E 'Maximum resident' "$OUT"/time-*.txt
rm -rf "$OUT/target-svc" "$W/target"
exit "$rc"
