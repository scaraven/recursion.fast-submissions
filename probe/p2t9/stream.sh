#!/usr/bin/env bash
# Stage P2 pass 9: a short stream through rf-oracle (PROVER.md §3): `first` (two chains → N8), then
# `step`s (prev + one chain → N2 or N4), each a fresh process in its own work directory; every
# output checked by the native `acc` (a node: the kind's dumped program from the embedded node data,
# then `stmtOk4`) and its canary (the statement with one bit flipped).
#   probe/p2t9/stream.sh BIN RF_ORACLE_BIN OUTDIR     env: P2T9_CHAINS ("nA nB n2 n3 …"), FLOCK_THREADS
set -uo pipefail
BIN=$1; SVC=$2; OUT=$3; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
CH=(${P2T9_CHAINS:-131077 70001 524295 150001})
D=$(mktemp -d /tmp/rfp2t9.XXXXXX); mkfifo "$D/in"
"$SVC" --socket "$D/oracle.sock" < "$D/in" > "$D/svc.log" 2>&1 &
spid=$!; exec 3> "$D/in"
for _ in $(seq 600); do grep -q '^ready' "$D/svc.log" 2>/dev/null && break; sleep 0.1; done
VK=$(sed -n 's/^vk //p' "$D/svc.log")
start() { printf '%064x' "$1"; }
rc=0; prev=""
for i in $(seq 1 $(( ${#CH[@]} - 1 ))); do
  W=$D/w$i; mkdir -p "$W"
  if [ "$i" = 1 ]; then
    echo "{\"n\": ${CH[0]}, \"start\": \"$(start 17)\"}" > "$W/chainA.json"
    echo "{\"n\": ${CH[1]}, \"start\": \"$(start 29)\"}" > "$W/chainB.json"; mode=first
  else
    echo "{\"n\": ${CH[$i]}, \"start\": \"$(start $((40 + i)))\"}" > "$W/chain.json"
    cp "$prev/proof.bin" "$W/prev.bin"; cp "$prev/stmt" "$W/prev.stmt"; mode=step
  fi
  ( cd "$W" && RF_ORACLE="$D/oracle.sock" /usr/bin/time -v timeout 900 "$BIN" $mode "$W" ) > "$OUT/step$i.log" 2>&1 || rc=1
  sed -n 's/.* stmt=\([0-9a-f]*\) .*/\1/p' "$OUT/step$i.log" > "$W/stmt"
  S=$(cat "$W/stmt"); F=$(printf '%x' $(( 0x${S:63:1} ^ 1 ))); S2=${S:0:63}$F
  a=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$S" "$W/proof.bin" 2>&1 | tail -1)
  k=$(RF_ORACLE="$D/oracle.sock" timeout 900 "$BIN" acc --vk "$VK" --stmt "$S2" "$W/proof.bin" 2>&1 | tail -1)
  echo "step $i ($mode): $(grep -o 'STREAM.*' "$OUT/step$i.log" | cut -c1-400) | acc: $a | canary: $k | $(grep 'Maximum resident' "$OUT/step$i.log")" | tee -a "$OUT/stream.txt"
  [ "$a" = accept ] && [ "$k" != accept ] || rc=1
  prev=$W
done
exec 3>&-; wait "$spid"; cp "$D/svc.log" "$OUT/svc.log"; rm -rf "$D"
exit "$rc"
