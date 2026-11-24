#!/usr/bin/env bash
# svc-bench.sh PROVER RF_ORACLE WORKDIR CPUS THREADS [svcbench args…]
# WP-R0: start rf-oracle the way the harness does (rfh/service.py: its own memory scope, MemoryMax=2G, cwd = a fresh
# socket directory, `--socket oracle.sock --io-timeout 20`), both it and the client pinned to CPUS (e.g. 24-31, or
# `all`), then run `PROVER svcbench …` with LVM_THREADS=THREADS against it and close the service.
# WORKDIR must not exist. Extra env for the client (LVM6_BATCH_ITEMS, LVM6_BATCH_KIB, LVM6_CHUNK) passes through.
set -euo pipefail
prover=$1 oracle=$2 work=$3 cpus=$4 threads=$5; shift 5
mkdir "$work"
pin=(); [ "$cpus" = all ] || pin=(taskset -c "$cpus")
coproc SVC { cd "$work" && exec systemd-run --user --scope -q -p MemoryMax=2G -p MemorySwapMax=0 -- \
  timeout 1800 "${pin[@]}" "$oracle" --socket oracle.sock --io-timeout 20; }
while read -r line <&"${SVC[0]}"; do [ "$line" = ready ] && break; done
RF_ORACLE="$work/oracle.sock" LVM_THREADS=$threads systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  -E RF_ORACLE -E LVM_THREADS -E LVM6_BATCH_ITEMS -E LVM6_BATCH_KIB -E LVM6_CHUNK -- \
  timeout 600 "${pin[@]}" "$prover" svcbench "$@" || echo "svc-bench: client exit $?"
exec {SVC[1]}>&-
while read -r line <&"${SVC[0]}"; do case "$line" in stats*) echo "service: $line";; esac; done
wait 2>/dev/null || true
