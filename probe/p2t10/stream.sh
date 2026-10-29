#!/usr/bin/env bash
# Stage P2 pass 10 (from pass 9's): a short stream through rf-oracle (PROVER.md §3): `first` (two chains → N8), then
# `step`s (prev + one chain → N2 or N4), each a fresh process in its own work directory; every
# output checked by the native `acc` (a node: the kind's dumped program from the embedded node data,
# then `stmtOk4`) and its canary (the statement with one bit flipped).
# Each request follows PROVER.md §3's handshake: `ready` on stdout, then the inputs and `go`, then
# `done`; the request's time is from `go` to `done` (`req_s`; the prover's own `total_s` is inside it).
#   probe/p2t10/stream.sh BIN RF_ORACLE_BIN OUTDIR     env: P2T9_CHAINS ("nA nB n2 n3 …"), FLOCK_THREADS
set -uo pipefail
BIN=$1; SVC=$2; OUT=$3; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
CH=(${P2T9_CHAINS:-131077 70001 524295 150001})
D=$(mktemp -d /tmp/rfp2t10.XXXXXX); mkfifo "$D/in"
"$SVC" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
spid=$!; exec 3> "$D/in"
for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
VK=$(sed -n 's/^vk //p' "$D/svc.log")
start() { printf '%064x' "$1"; }
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
  mkfifo "$D/go$i" "$D/out$i"
  ( cd "$W" && RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 900 "$BIN" $mode "$W" < "$D/go$i" > "$D/out$i" ) 2> "$OUT/step$i.log" &
  ppid=$!
  exec 4> "$D/go$i" 5< "$D/out$i"
  t_s=$(date +%s.%N); IFS= read -r l <&5; t_r=$(date +%s.%N)
  [ "$l" = ready ] || { echo "step $i: no ready line ($l)"; rc=1; }
  mv "$S"/* "$W"/; t0=$(date +%s.%N); echo go >&4
  IFS= read -r l <&5; t1=$(date +%s.%N)
  [ "$l" = done ] || { echo "step $i: no done line ($l)"; rc=1; }
  exec 4>&- 5<&-; wait "$ppid" || rc=1
  req=$(awk "BEGIN{printf \"%.3f\", $t1 - $t0}"); stup=$(awk "BEGIN{printf \"%.3f\", $t_r - $t_s}")
  sed -n 's/.* stmt=\([0-9a-f]*\) .*/\1/p' "$OUT/step$i.log" > "$W/stmt"
  S=$(cat "$W/stmt"); F=$(printf '%x' $(( 0x${S:63:1} ^ 1 ))); S2=${S:0:63}$F
  a=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$S" "$W/proof.bin" 2>&1 | tail -1)
  k=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$S2" "$W/proof.bin" 2>&1 | tail -1)
  echo "step $i ($mode): req_s=$req startup_s=$stup $(grep -o 'STREAM.*' "$OUT/step$i.log" | cut -c1-1500) | acc: $a | canary: $k | $(grep 'Maximum resident' "$OUT/step$i.log")" | tee -a "$OUT/stream.txt"
  [ "$a" = accept ] && [ "$k" != accept ] || rc=1
  prev=$W
done
exec 3>&-; wait "$spid"; cp "$D/svc.log" "$OUT/svc.log"; rm -rf "$D"
exit "$rc"
