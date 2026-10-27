#!/usr/bin/env bash
# Stage P1 probe: build the flock-recursive prover (x86-64-v2, run-time tier dispatch) and the
# organiser's oracle service, run the kernel self-test and a small leaf with the in-process oracle,
# then leaves at m = 30 and m = 32 through a real `rf-oracle` (prove, record the verifier's trace,
# SIGN, native acc), with peak RSS from /usr/bin/time.
#   probe/p1-prover/run.sh OUTDIR     env: P1_RUNS ("30:3 32:2"), RF_ORACLE_BIN (skip the service build)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
{ lscpu; echo; echo "flags of interest: $(grep -m1 -o -w -E 'pclmulqdq|vpclmulqdq|gfni|avx2|avx512f|avx512bw|avx512vl|sha_ni|vaes' /proc/cpuinfo | sort -u | tr '\n' ' ')";
  echo "nproc: $(nproc)"; free -m; echo "ImageVersion: ${ImageVersion:-?}"; git -C "$REPO" log -1 --format='commit %H'; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)|flags of interest' "$OUT/machine.txt"
TC=""; command -v rustup >/dev/null && rustup toolchain list 2>/dev/null | grep -q '^1.99.0' && TC="+1.99.0"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$OUT/target}
# the prover: the submission's CPU baseline, kernels chosen at run time
( cd "$REPO/submissions/flock-recursive/prover" && time RUSTFLAGS="-C target-cpu=x86-64-v2" timeout 1200 cargo $TC build --release --offline ) > "$OUT/build-prover.log" 2>&1 || { tail -40 "$OUT/build-prover.log"; exit 1; }
BIN=$CARGO_TARGET_DIR/release/flock-prover
# the service (contract submodule at the pin)
SVC=${RF_ORACLE_BIN:-}
if [ -z "$SVC" ]; then
  [ -f "$REPO/.contract/service/Cargo.toml" ] || git -C "$REPO" submodule update --init .contract > "$OUT/submodule.log" 2>&1
  ( cd "$REPO/.contract/service" && time CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release --offline --locked ) > "$OUT/build-service.log" 2>&1 \
    || ( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release ) >> "$OUT/build-service.log" 2>&1 || { tail -40 "$OUT/build-service.log"; exit 1; }
  SVC=$OUT/target-svc/release/rf-oracle
fi
timeout 600 "$BIN" selftest 2>&1 | tee "$OUT/selftest.log"
timeout 600 "$BIN" test-leaf 25 2>&1 | tee "$OUT/test-leaf.log"
rc=0
for spec in ${P1_RUNS:-30:3 32:2}; do
  m=${spec%%:*}; reps=${spec##*:}
  D=$(mktemp -d /tmp/rfp1.XXXXXX)
  mkfifo "$D/in"
  "$SVC" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
  spid=$!
  exec 3> "$D/in"
  for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
  grep -E '^(simd|keygen_ms)' "$D/svc.log" | tr '\n' ' '; echo
  ( cd "$D" && FLOCK_VERBOSE=1 RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 1200 "$BIN" prove-leaf "$m" --reps "$reps" --out "$D/leaf$m.bin" ) \
      > "$OUT/leaf-$m.log" 2> "$OUT/time-leaf-$m.txt" || rc=1
  grep PROVE-LEAF "$OUT/leaf-$m.log"; grep -E 'Maximum resident|Elapsed' "$OUT/time-leaf-$m.txt"; tail -3 "$OUT/time-leaf-$m.txt" | grep -v '^\s' || true
  grep -i -E 'fatal|panic|error' "$OUT/time-leaf-$m.txt" | head -5
  exec 3>&-
  wait "$spid"
  cp "$D/svc.log" "$OUT/svc-$m.log"
  rm -rf "$D"
done
grep -h -E 'PROVE-LEAF|TEST-LEAF|SELFTEST' "$OUT"/*.log > "$OUT/results.txt"
rm -rf "$OUT/target" "$OUT/target-svc"
exit "$rc"
