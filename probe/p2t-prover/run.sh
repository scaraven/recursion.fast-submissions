#!/usr/bin/env bash
# Stage P2' probe (revision 4.0): the runner's CPUs, the segment prover's thread scaling, segments of
# variable length, the aggregate leaf (k segments, one trace, one SIGN) and its peak memory.
# Build prover.s with build-asm.sh (rust 1.99.0), asm-compat.py, link as the runner does
# (gcc -static -O2 -pthread *.s -o prover -lm); selftest; then `prove-leaf M --n N` through rf-oracle
# with FLOCK_THREADS = T for each case `M:N:T` of P2T_CASES (default below), P2T_REPS repetitions
# (default 2). Every prover run uses the linked prover.s binary.
#   probe/p2t-prover/run.sh OUTDIR     env: P2T_CASES, P2T_REPS, P2T_EXTRA (extra args)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
{ lscpu; echo "nproc: $(nproc)"; echo "affinity: $(python3 -c 'import os; print(sorted(os.sched_getaffinity(0)))')";
  grep -E 'Cpus_allowed_list' /proc/self/status; echo "cgroup: $(cat /proc/self/cgroup)";
  for f in cpu.max cpuset.cpus.effective memory.max; do echo "$f: $(cat /sys/fs/cgroup/$(sed -n 's/^0:://p' /proc/self/cgroup)/$f 2>/dev/null)"; done;
  free -m; echo "ImageVersion: ${ImageVersion:-?}"; gcc --version | head -1; as --version | head -1; ld --version | head -1; ldd --version | head -1;
  git -C "$REPO" log -1 --format='commit %H'; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)|nproc|affinity|Cpus_allowed|cpu.max|GNU assembler|^gcc' "$OUT/machine.txt"
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
D=$(mktemp -d /tmp/rfp2t.XXXXXX); mkfifo "$D/in"
"$SVC" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
spid=$!; exec 3> "$D/in"
for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
rc=0
# a case is `leaf:M:N:T[:ENV=V]` (prove-leaf M --n N) or `agg:N:T[:ENV=V]` (prove-agg N, the aggregate
# leaf of a chain of N steps: segments L32/L31, one trace, one SIGN)
CASES=${P2T_CASES:-"leaf:32:262144:4 leaf:32:196608:4 leaf:31:131072:4 leaf:31:1:4 agg:262145:4 agg:1048576:4 leaf:32:262144:2 leaf:32:262144:1"}
for cs in $CASES; do
  IFS=: read -r kind a b c d <<< "$cs"
  if [ "$kind" = leaf ]; then m=$a; n=$b; t=$c; ev=${d:-}; args=(prove-leaf "$m" --n "$n" --reps "${P2T_REPS:-2}");
  else m=32; n=$a; t=$b; ev=${c:-}; args=(prove-agg "$n" --reps 1); fi
  pf=6000; [ "$m" -le 31 ] && pf=3200
  tag="$kind-m$m-n$n-t$t${ev:+-${ev%%=*}}"
  ( cd "$D" && env ${ev:+"$ev"} FLOCK_THREADS=$t FLOCK_VERBOSE=1 FLOCK_PREFAULT_MIB=$pf RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 900 "$BIN" "${args[@]}" --out "$D/l.bin" ${P2T_EXTRA:-} ) > "$OUT/$tag.log" 2> "$OUT/time-$tag.txt" || rc=1
  echo "$tag: $(grep -o 'total_s=[0-9.]*\|segs=[^ ]*' "$OUT/$tag.log" | tr '\n' ' ') $(grep -o 'acc=[a-z]*' "$OUT/$tag.log" | head -1) $(grep -o 'prefault [0-9]* MiB [0-9.]*s' "$OUT/time-$tag.txt" | head -1) $(grep 'Maximum resident' "$OUT/time-$tag.txt")"
done
exec 3>&-; wait "$spid"; cp "$D/svc.log" "$OUT/svc.log"; rm -rf "$D"
grep -h -E 'PROVE-LEAF|PROVE-AGG|SELFTEST' "$OUT"/*.log | cut -c1-900 > "$OUT/results.txt"
rm -rf "$OUT/target-svc" "$W/target"
exit "$rc"
