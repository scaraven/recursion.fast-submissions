#!/usr/bin/env bash
# Stage P2 pass 13 (pass 12's, plus):
#  * RF_ORACLE_ARGS: extra service arguments, e.g. `--insecure-test-keys K S` with a service built with
#    that feature (the determinism check: two streams under the same keys must give the same files);
#  * P2T13_RERUN=1: every step runs a second time, in a fresh process on the same inputs under the same
#    service lifetime, as the harness's re-timing does (rfh/bench.py `retime`); its output is checked
#    by `acc` and its canary too, and both file hashes are reported (`rerun_*`);
#  * `file_sha`: the first 16 hex digits of the sha256 of the whole proof.bin;
#  * P2T13_KEEP=1: every output (and re-run) kept as OUTDIR/step<i>[.rerun].bin, with the badge
#    `verify --batch` lists OUTDIR/verify.txt (`VK STMT FILE`) and OUTDIR/verify-canary.txt (the
#    statement with its last hex digit's low bit flipped).
# Pass 12's text: a short stream through rf-oracle (PROVER.md §3): `first` (two chains → N8), then
# `step`s (prev + one chain → N2 or N4), each a fresh process in its own work directory; every
# output checked by the native `acc` and its canary (the statement with one bit flipped); the
# request's time is from `go` to `done` (`req_s`); `pi_sha` the sha256 of the file's π part.
#   probe/p2t13/stream.sh BIN RF_ORACLE_BIN OUTDIR     env: P2T9_CHAINS ("nA nB n2 n3 …"), FLOCK_THREADS
set -uo pipefail
BIN=$1; SVC=$2; OUT=$3; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
CH=(${P2T9_CHAINS:-131077 70001 524295 150001})
D=$(mktemp -d /tmp/rfp2t13.XXXXXX); mkfifo "$D/in"
"$SVC" --socket "$D/oracle.sock" ${RF_ORACLE_ARGS:-} < "$D/in" > "$D/svc.log" 2>&1 &
spid=$!; exec 3> "$D/in"
for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
VK=$(sed -n 's/^vk //p' "$D/svc.log")
start() { printf '%064x' "$1"; }
pish() { python3 -I -c 'import sys,hashlib;b=open(sys.argv[1],"rb").read();n=int.from_bytes(b[:8],"little");print(hashlib.sha256(b[8:8+n]).hexdigest()[:16])' "$1"; }
# req MODE W S LOG: one request (the handshake), the inputs staged in S moved into W at `go`; sets REQ, STUP
req() {
  local mode=$1 W=$2 S=$3 log=$4 tag=$5
  mkfifo "$D/go$tag" "$D/out$tag"
  ( cd "$W" && RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 900 "$BIN" $mode "$W" < "$D/go$tag" > "$D/out$tag" ) 2> "$log" &
  local ppid=$!
  exec 4> "$D/go$tag" 5< "$D/out$tag"
  local t_s t_r t0 t1 l
  t_s=$(date +%s.%N); IFS= read -r l <&5; t_r=$(date +%s.%N)
  [ "$l" = ready ] || { echo "$tag: no ready line ($l)"; rc=1; }
  mv "$S"/* "$W"/; t0=$(date +%s.%N); echo go >&4
  IFS= read -r l <&5; t1=$(date +%s.%N)
  [ "$l" = done ] || { echo "$tag: no done line ($l)"; rc=1; }
  exec 4>&- 5<&-; wait "$ppid" || rc=1
  REQ=$(awk "BEGIN{printf \"%.3f\", $t1 - $t0}"); STUP=$(awk "BEGIN{printf \"%.3f\", $t_r - $t_s}")
}
rc=0; prev=""
for i in $(seq 1 $(( ${#CH[@]} - 1 ))); do
  W=$D/w$i; S=$D/s$i; mkdir -p "$W" "$S"
  if [ "$i" = 1 ]; then
    echo "{\"n\": ${CH[0]}, \"start\": \"$(start 17)\"}" > "$S/chainA.json"
    echo "{\"n\": ${CH[1]}, \"start\": \"$(start 29)\"}" > "$S/chainB.json"; mode=first
  else
    echo "{\"n\": ${CH[$i]}, \"start\": \"$(start $((40 + i)))\"}" > "$S/chain.json"
    cp "$prev/proof.bin" "$S/prev.bin"; cp "$prev/stmt" "$S/prev.stmt"; mode=step
  fi
  [ "${P2T13_RERUN:-0}" != 1 ] || { mkdir -p "$D/r$i" "$D/rs$i"; cp "$S"/* "$D/rs$i"/; }
  req "$mode" "$W" "$S" "$OUT/step$i.log" "$i"
  sed -n 's/.* stmt=\([0-9a-f]*\) .*/\1/p' "$OUT/step$i.log" > "$W/stmt"
  St=$(cat "$W/stmt"); F=$(printf '%x' $(( 0x${St:63:1} ^ 1 ))); S2=${St:0:63}$F
  ta=$(date +%s.%N)
  a=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$St" "$W/proof.bin" 2>&1 | tail -1)
  acc_s=$(awk "BEGIN{printf \"%.3f\", $(date +%s.%N) - $ta}")
  k=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$S2" "$W/proof.bin" 2>&1 | tail -1)
  line="step $i ($mode): req_s=$REQ startup_s=$STUP acc_s=$acc_s $(grep -o 'STREAM.*' "$OUT/step$i.log" | cut -c1-1500) | acc: $a | canary: $k | $(grep 'Maximum resident' "$OUT/step$i.log") | pi_sha=$(pish "$W/proof.bin") file_sha=$(sha256sum "$W/proof.bin" | cut -c1-16)"
  [ "$a" = accept ] && [ "$k" != accept ] || rc=1
  if [ "${P2T13_KEEP:-0}" = 1 ]; then
    cp "$W/proof.bin" "$OUT/step$i.bin"; echo "$VK $St $OUT/step$i.bin" >> "$OUT/verify.txt"; echo "$VK $S2 $OUT/step$i.bin" >> "$OUT/verify-canary.txt"
  fi
  if [ "${P2T13_RERUN:-0}" = 1 ]; then
    req "$mode" "$D/r$i" "$D/rs$i" "$OUT/step$i.rerun.log" "r$i"
    ra=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$St" "$D/r$i/proof.bin" 2>&1 | tail -1)
    rk=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$S2" "$D/r$i/proof.bin" 2>&1 | tail -1)
    rst=$(sed -n 's/.* stmt=\([0-9a-f]*\) .*/\1/p' "$OUT/step$i.rerun.log")
    line="$line | rerun: req_s=$REQ stmt_same=$([ "$rst" = "$St" ] && echo yes || echo no) acc: $ra | canary: $rk | rerun_pi_sha=$(pish "$D/r$i/proof.bin") rerun_file_sha=$(sha256sum "$D/r$i/proof.bin" | cut -c1-16)"
    [ "$ra" = accept ] && [ "$rk" != accept ] || rc=1
    if [ "${P2T13_KEEP:-0}" = 1 ]; then
      cp "$D/r$i/proof.bin" "$OUT/step$i.rerun.bin"; echo "$VK $St $OUT/step$i.rerun.bin" >> "$OUT/verify.txt"; echo "$VK $S2 $OUT/step$i.rerun.bin" >> "$OUT/verify-canary.txt"
    fi
  fi
  echo "$line" | tee -a "$OUT/stream.txt"
  prev=$W
done
exec 3>&-; wait "$spid"; cp "$D/svc.log" "$OUT/svc.log"; rm -rf "$D"
exit "$rc"
