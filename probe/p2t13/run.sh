#!/usr/bin/env bash
# Stage P2 pass 13 (pass 12's, with p2t13/stream.sh, the N2-311951 KAT (a short replay), and
# P2T13_DET=1 (default): the service built a second time with `insecure-test-keys`, then three short
# streams of the new prover under fixed keys: det-1 and det-2 must give the same files at every step
# (the prover is deterministic given the oracle), det-3 re-runs every step on the same inputs under
# the same lifetime as the harness's re-timing does (each re-run accepted, its canary rejected).
# Pass 12 (pass 11's probe, plus P2T12_BENCH: `bench-r1 32` (round 1's kernels and the whole
# round 1, new vs pass 11's, checked equal) and `bench` before the streams; P2T12_STREAMS=0: benches only).
# Pass 12 also gives the base streams RF_SETUP (HEAD's base reads the same setup), and runs the KATs.
# Pass 11's text: the base prover (base.s: the branch HEAD's committed
# prover.s, put here by the probe commit) and the new one (built by build-asm.sh as the runner
# does), on one runner. The new one runs `prover setup` first (untimed in the harness; timed and
# sized here) and its streams see RF_SETUP. Streams alternate base / new through rf-oracle
# (`stream.sh`: the ready/go/done handshake, every output checked by `acc` and timed, canaries).
#   probe/p2t11/run.sh OUTDIR    env: P2T9_CHAINS, P2T9_REPS (default 2), P2T11_BASE=0 (skip the
#   base), P2T11_TRACE=1 (bench-trace N2/N4), P2T11_ENV (extra env for the new streams),
#   P2T11_ALT (env of a third stream per rep, the new prover again: an A/B on one runner)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
[ ! -f "$HERE/env" ] || . "$HERE/env"   # the probe commit's settings (the workflow passes no env)
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
[ "${P2T12_BENCH:-1}" != 1 ] || { timeout 900 "$BIN" bench-r1 32; timeout 300 "$BIN" bench-k; timeout 300 "$BIN" bench-nd "$OUT"; rm -f "$OUT/nodedata.bin"; timeout 600 "$BIN" bench; } 2>&1 | tee "$OUT/bench-r1.log"
# the KATs (P2T12_KAT=1, default): node-kat on S-E13a's data (pass 11's signed nodes in kat/) and
# test-leaf, with the base and the new binary; every pi_b2s must be equal (kat.txt, kat-check.txt)
if [ "${P2T12_KAT:-1}" = 1 ]; then
  K=$HERE/kat
  # B0's row layout (pass 13): the KAT nodes in kat/ are the new prover's; the base (another layout)
  # cannot replay them, so only the new prover runs, checked against kat-expected.txt (the VM's)
  for which in ${P2T13_KAT_WHO:-new}; do
    if [ "$which" = base ]; then b=$BASE; else b=$BIN; fi
    [ -n "$b" ] || continue
    for c in "N8 --m 32 --n 3" "N2 --prev $K/n8.signed --agg 262147" "N4 --prev $K/n8.signed --agg 524291" "N2 --prev $K/n2.signed --agg 131077" "N4 --prev $K/n4.signed --agg 1048576" "N2 --prev $K/n8.signed --agg 311951"; do
      t0=$(date +%s.%N); p=$(timeout 900 "$b" node-kat $c --prove 2>&1 | grep -o 'pi_b2s=[0-9a-f]*' | tail -1)
      echo "$which node-kat $c: $p $(awk "BEGIN{printf \"%.1f s\", $(date +%s.%N) - $t0}")"
    done
    for c in "30" "32" "31 --n 77777"; do
      echo "$which test-leaf $c: $(timeout 600 "$b" test-leaf $c 2>&1 | grep -o 'pi_b2s=[0-9a-f]*\|accept=[a-z]*' | head -2 | tr '\n' ' ')"
    done
  done 2>&1 | tee "$OUT/kat.txt"
  python3 -I - "$OUT/kat.txt" "$HERE/kat-expected.txt" <<'PY' | tee "$OUT/kat-check.txt"
import sys, collections
d = collections.defaultdict(dict)
for l in open(sys.argv[1]):
    w, rest = l.split(" ", 1); k, v = rest.split(":", 1); d[k][w] = v.split()[0] if v.split() else ""
bad = [k for k, v in d.items() if len(set(v.values())) != 1 or "" in v.values()]
print("KAT cases", len(d), "base=new" if not bad else "DIFFER " + "; ".join(bad))
if len(sys.argv) > 2:
    # the expected π (the VM's kat13.sh output: N8 N2 N4 N2N2 N4N4 N2-311951 leaf28 leaf30 leaf32 leaf31)
    e = [l.split("pi_b2s=")[1].split()[0] for l in open(sys.argv[2]) if "pi_b2s=" in l]
    ref = dict(zip(["N8", "N2", "N4", "N2N2", "N4N4", "N2-311951", "leaf28", "leaf30", "leaf32", "leaf31"], e))
    want = [ref[n] for n in ["N8", "N2", "N4", "N2N2", "N4N4", "N2-311951", "leaf30", "leaf32", "leaf31"]]
    got = [v.get("new", "").replace("pi_b2s=", "") for v in d.values()]
    print("KAT new vs expected (VM):", "EQUAL" if got == want else f"DIFFER got {got} want {want}")
PY
fi
# segment fits (P2T12_FIT=1, default; pass 6's final.sh cases): prove-leaf through one rf-oracle,
# base and new alternately, total_s = prove + trace + SIGN (fit.txt)
if [ "${P2T12_FIT:-1}" = 1 ]; then
  D=$(mktemp -d /tmp/rfp2t12.XXXXXX); mkfifo "$D/in"
  "$OUT/target-svc/release/rf-oracle" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
  fpid=$!; exec 6> "$D/in"
  for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
  CASES=${P2T12_CASES:-32:262144 32:196608 32:131073 32:65536 32:1 31:131072 31:65536 31:1 30:65536 30:32768 30:1}
  for cs in $CASES; do
    IFS=: read -r m n <<< "$cs"
    pf=6000; [ "$m" -le 31 ] && pf=3200; [ "$m" -le 30 ] && pf=1600
    for v in base new; do
      if [ "$v" = base ]; then b=$BASE; else b=$BIN; fi
      [ -n "$b" ] || continue
      ( cd "$D" && env FLOCK_VERBOSE=1 FLOCK_PROF=1 FLOCK_PREFAULT_MIB=$pf RF_ORACLE="$D/oracle.sock" timeout 900 "$b" prove-leaf "$m" --n "$n" --reps 2 --out "$D/l.bin" ) > "$OUT/fit-$v-m$m-n$n.log" 2>&1
      echo "$v-leaf-m$m-n$n: $(grep -o 'total_s=[0-9.]*' "$OUT/fit-$v-m$m-n$n.log" | tr '\n' ' ') pi_sha=$(python3 -I -c 'import sys,hashlib;b=open(sys.argv[1],"rb").read();n=int.from_bytes(b[:8],"little");print(hashlib.sha256(b[8:8+n]).hexdigest()[:16])' "$D/l.bin")"
    done
  done 2>&1 | tee "$OUT/fit.txt"
  exec 6>&-; wait "$fpid"; rm -rf "$D"
fi
[ "${P2T12_STREAMS:-1}" != 0 ] || { rm -rf "$W/target"; exit 0; }
[ "${P2T11_TRACE:-0}" != 1 ] || { timeout 300 "$BIN" bench-trace N2; timeout 300 "$BIN" bench-trace N4; } 2>&1 | tee "$OUT/bench-trace.log"
# prover setup (the harness: 240 s, 4 GiB, untimed)
S=$OUT/setup; mkdir -p "$S"
( cd "$S" && /usr/bin/time -v timeout 300 "$BIN" setup "$S" ) > "$OUT/setup.log" 2>&1; echo "setup exit $?" | tee -a "$OUT/setup.log"
grep -E '^setup|Elapsed|Maximum res' "$OUT/setup.log"; du -sb "$S" | tee -a "$OUT/setup.log"
# the base's own setup (pass 13: the node data image's format changed, FLNDIMG2)
SB=$OUT/setup-base; mkdir -p "$SB"
[ -z "$BASE" ] || { ( cd "$SB" && timeout 300 "$BASE" setup "$SB" ) > "$OUT/setup-base.log" 2>&1; echo "base setup exit $?"; du -sb "$SB"; }
if [ "${P2T13_DET:-1}" = 1 ]; then
  ( cd "$REPO/.contract/service" && CARGO_TARGET_DIR="$OUT/target-svck" timeout 1200 cargo $TC build --release --offline --features insecure-test-keys ) > "$OUT/build-service-k.log" 2>&1 || tail -5 "$OUT/build-service-k.log"
  KEYS="--insecure-test-keys $(printf '11%.0s' $(seq 32)) $(printf '22%.0s' $(seq 32))"
  for d in 1 2 3; do
    rr=0; [ "$d" = 3 ] && rr=1
    env RF_SETUP="$S" P2T9_CHAINS="131072 131072 131072 786432" RF_ORACLE_ARGS="$KEYS" P2T13_RERUN=$rr P2T13_KEEP=$([ "$d" != 2 ] && echo 1 || echo 0) FLOCK_VERBOSE=1 "$HERE/stream.sh" "$BIN" "$OUT/target-svck/release/rf-oracle" "$OUT/det-$d" || echo "det-$d: stream rc != 0"
  done
  for d in 1 2 3; do echo "det-$d: $(grep -o 'step [0-9]\|acc: [a-z]*\|canary: [a-z]*\|file_sha=[0-9a-f]*\|stmt_same=[a-z]*' "$OUT/det-$d/stream.txt" | tr '\n' ' ')"; done | tee "$OUT/det.txt"
  python3 -I - "$OUT" <<'PY' | tee -a "$OUT/det.txt"
import sys, re
f = lambda d: re.findall(r" file_sha=([0-9a-f]+)", open(f"{sys.argv[1]}/det-{d}/stream.txt").read())
a, b, c = f(1), f(2), f(3)
print("fixed keys, two streams:", "IDENTICAL" if a == b and a else "DIFFER", a, b)
print("re-run stream det-3, first outputs:", c, "step 1 equal to det-1:", bool(c) and bool(a) and c[0] == a[0])
PY
fi
export P2T11_ALT=${P2T11_ALT-}
export P2T9_CHAINS=${P2T9_CHAINS:-"262144 262144 131072 262144 311951 393216 786432 1048576 131072"}
rc=0
for r in $(seq 1 "${P2T9_REPS:-2}"); do
  if [ -n "$BASE" ]; then
    env RF_SETUP="$SB" FLOCK_PROF=1 FLOCK_VERBOSE=1 "$HERE/stream.sh" "$BASE" "$OUT/target-svc/release/rf-oracle" "$OUT/base-$r" || rc=1
  fi
  env RF_SETUP="$S" FLOCK_PROF=1 FLOCK_VERBOSE=1 P2T13_KEEP=$([ "$r" = 1 ] && echo 1 || echo 0) ${P2T11_ENV:-} "$HERE/stream.sh" "$BIN" "$OUT/target-svc/release/rf-oracle" "$OUT/new-$r" || rc=1
  if [ -n "${P2T11_ALT:-}" ]; then
    env RF_SETUP="$S" FLOCK_PROF=1 FLOCK_VERBOSE=1 $P2T11_ALT "$HERE/stream.sh" "$BIN" "$OUT/target-svc/release/rf-oracle" "$OUT/alt-$r" || rc=1
  fi
done
echo "alt env: ${P2T11_ALT:-none}" > "$OUT/alt.txt"
for f in "$OUT"/base-*/stream.txt "$OUT"/new-*/stream.txt "$OUT"/alt-*/stream.txt; do [ -f "$f" ] && { echo "== $f"; cat "$f"; }; done > "$OUT/results.txt"
rm -rf "$OUT/target-svc" "$OUT/target-svck" "$W/target"
exit "$rc"
