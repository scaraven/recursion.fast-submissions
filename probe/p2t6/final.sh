#!/usr/bin/env bash
# Stage P2 pass 6, before/after on one runner: the base prover (probe/p2t6/base: the branch HEAD's
# prover/, added by the probe commit only) and this tree's prover, both built by build-asm.sh and linked as the runner does, run
# alternately through one rf-oracle on the same cases (prove-leaf M --n N, prove-agg N; 4 threads).
#   probe/p2t6/final.sh OUTDIR     env: P2T6_CASES, P2T6_REPS (default 2)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
{ lscpu; echo "nproc: $(nproc)"; git -C "$REPO" log -2 --format='commit %H'; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)' "$OUT/machine.txt"
TC=""; command -v rustup >/dev/null && rustup toolchain list 2>/dev/null | grep -q '^1.99.0' && TC="+1.99.0"
# the base sources: probe/p2t6/base (the branch HEAD's prover/, put there by the probe commit)
BASE=$HERE/base; [ -f "$BASE/Cargo.toml" ] || { echo "no base sources"; exit 1; }
build() { # build SRC_PROVER_DIR NAME
  local P=$1 W=$OUT/asm-$2
  ( timeout 1500 "$P/build-asm.sh" "$W" ) > "$OUT/build-asm-$2.log" 2>&1 || { tail -30 "$OUT/build-asm-$2.log"; exit 1; }
  mkdir -p "$W/runner"
  python3 -I "$REPO/.contract/harness/tools/asm-compat.py" "$P/prover.s" "$W/runner/prover.s" > /dev/null 2>&1 || cp "$P/prover.s" "$W/runner/prover.s"
  [ -s "$W/runner/prover.s" ] || cp "$P/prover.s" "$W/runner/prover.s"
  ( cd "$W/runner" && gcc -static -O2 -pthread ./*.s -o prover -lm ) > "$OUT/link-$2.log" 2>&1 || { tail -30 "$OUT/link-$2.log"; exit 1; }
  echo "$2: prover.s sha256 $(sha256sum "$P/prover.s" | cut -d' ' -f1)" | tee -a "$OUT/machine.txt"
  rm -rf "$W/target"
}
[ -f "$REPO/.contract/service/Cargo.toml" ] || git -C "$REPO" submodule update --init .contract > "$OUT/submodule.log" 2>&1
build "$BASE" base
build "$REPO/submissions/flock-recursive/prover" new
( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svc" timeout 1200 cargo $TC build --release ) > "$OUT/build-service.log" 2>&1 || { tail -30 "$OUT/build-service.log"; exit 1; }
SVC=$OUT/target-svc/release/rf-oracle
timeout 600 "$OUT/asm-new/runner/prover" selftest 2>&1 | tee "$OUT/selftest.log"
D=$(mktemp -d /tmp/rfp2t6.XXXXXX); mkfifo "$D/in"
"$SVC" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
spid=$!; exec 3> "$D/in"
for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
rc=0
CASES=${P2T6_CASES:-"leaf:32:262144 leaf:32:196608 leaf:32:131073 leaf:32:65536 leaf:32:1 leaf:31:131072 leaf:31:65536 leaf:31:1 agg:1048576"}
for cs in $CASES; do
  IFS=: read -r kind a b <<< "$cs"
  if [ "$kind" = leaf ]; then m=$a; n=$b; args=(prove-leaf "$m" --n "$n" --reps "${P2T6_REPS:-2}"); else m=32; n=$a; args=(prove-agg "$n" --reps 1); fi
  pf=6000; [ "$m" -le 31 ] && pf=3200
  for v in base new; do
    tag="$v-$kind-m$m-n$n"
    ( cd "$D" && env FLOCK_THREADS=4 FLOCK_VERBOSE=1 FLOCK_PROF=1 FLOCK_PREFAULT_MIB=$pf RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 900 "$OUT/asm-$v/runner/prover" "${args[@]}" --out "$D/l.bin" ) > "$OUT/$tag.log" 2> "$OUT/time-$tag.txt" || rc=1
    echo "$tag: $(grep -o 'total_s=[0-9.]*\|segs=[^ ]*' "$OUT/$tag.log" | tr '\n' ' ') $(grep -o 'acc=[a-z]*' "$OUT/$tag.log" | head -1) $(grep -o 'canary_accept=[a-z]*' "$OUT/$tag.log" | head -1) pi_sha=$(python3 -I -c 'import sys,hashlib;b=open(sys.argv[1],"rb").read();n=int.from_bytes(b[:8],"little");print(hashlib.sha256(b[8:8+n]).hexdigest()[:16])' "$D/l.bin") $(grep 'Maximum resident' "$OUT/time-$tag.txt")"
  done
done
exec 3>&-; wait "$spid"; cp "$D/svc.log" "$OUT/svc.log"; rm -rf "$D" "$OUT/target-svc"
exit "$rc"
