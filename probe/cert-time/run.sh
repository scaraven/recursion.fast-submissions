#!/usr/bin/env bash
# H-cert: the certificate job's two capped Lean steps (season.toml [certificate]: build_s = 600,
# kernel_s = 600) for the whole Flock-recursive entry, on the runner.
#   probe/cert-time/run.sh [OUTDIR]
#   env: ORG/PKGS (a prebuilt core checkout and package tree; default: clone the core at the
#        `.contract` pin, `lake exe cache get` and the organiser build, as the setup job does),
#        KERNELS (a directory with the comparator built by the core's harness/ci/build-kernels.sh),
#        TREE (the build tree, default $RUNNER_TEMP/cert-tree), BUILD_MEM (12G, evaluate.py's
#        sandbox cap of the build), KERNEL_MEM (14G, its --cert-mem), BUILD_TIMEOUT/KERNEL_TIMEOUT
#        (2400 s each: past the caps, so that an over-cap step is measured, not cut), SKIP_BUILD=1
#        (reuse TREE's build).
# Proxy (there is no Solution.lean yet): step 3 is `lake build FR`, every module of the entry (the
# harness builds `+Challenge +Solution`, Solution's import closure); step 4 runs the pinned
# comparator with challenge = solution = FR, theorem_names = every theorem and definition_names =
# every definition declared in an FR* module (an upper bound of `certified`'s and `submission`'s
# dependency closure). It exports that closure (twice: the real challenge's export is a few
# constants, so the first export is reported apart) and replays it in the Lean kernel, single
# threaded, as the harness does. The sandbox (landrun / bwrap-landrun.sh) is replaced by a
# pass-through (landrun-pass.sh).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
TMP=${RUNNER_TEMP:-${TMPDIR:-/tmp}}
TREE=${TREE:-$TMP/cert-tree}
BUILD_MEM=${BUILD_MEM:-12G}; KERNEL_MEM=${KERNEL_MEM:-14G}
BUILD_TIMEOUT=${BUILD_TIMEOUT:-2400}; KERNEL_TIMEOUT=${KERNEL_TIMEOUT:-2400}
t0=$(date +%s); step() { echo "== $1 ($(( $(date +%s) - t0 )) s)"; }

{ lscpu; echo; nproc; free -g; uptime; df -h "$TMP" | tail -1
  echo "RUNNER_NAME=${RUNNER_NAME:-} ImageOS=${ImageOS:-} ImageVersion=${ImageVersion:-}"; } > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)' "$OUT/machine.txt" || true

# a memory-capped scope whose cgroup peak is recorded (as evaluate.py's memcap); on the runner the
# user manager needs lingering (core harness/ci/runner-setup.sh); without it, no cap and no peak
if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
  sudo loginctl enable-linger "$(id -un)" || true
  export XDG_RUNTIME_DIR=/run/user/$(id -u) DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus
  for _ in $(seq 1 50); do [[ -S /run/user/$(id -u)/bus ]] && break; sleep 0.2; done
fi
SCOPE=1; systemd-run --user --scope -q -p MemoryMax=64M true 2>/dev/null || { SCOPE=0; echo "no systemd user scope: no memory cap or cgroup peak"; }
# capped NAME MEM TIMEOUT CMD...: runs CMD in its own scope, writes $OUT/NAME.peak (cgroup memory.peak,
# bytes) and $OUT/NAME.time (/usr/bin/time -v: wall, the largest process's max RSS)
capped() {
  local name=$1 mem=$2 to=$3; shift 3
  local inner="/usr/bin/time -v -o $OUT/$name.time timeout $to \"\$@\"; rc=\$?; \
    cat /sys/fs/cgroup\$(cut -d: -f3 /proc/self/cgroup)/memory.peak > $OUT/$name.peak 2>/dev/null || true; exit \$rc"
  if [[ $SCOPE == 1 ]]; then
    systemd-run --user --scope -q -p MemoryMax="$mem" -p MemorySwapMax=0 -- bash -c "$inner" _ "$@"
  else
    bash -c "$inner" _ "$@"
  fi
}

# 1. the organiser's environment (the setup job; not timed against a cap)
if [[ -z "${ORG:-}" ]]; then
  PIN=$(git -C "$REPO" ls-tree HEAD .contract | awk '{print $3}')
  ORG=$TMP/rf-core
  step "core $PIN into $ORG"
  rm -rf "$ORG"; git clone -q https://github.com/scaraven/recursion.fast "$ORG"; git -C "$ORG" checkout -q "$PIN"
  for try in 1 2 3; do
    (cd "$ORG" && timeout 900 lake exe cache get) >> "$OUT/cache-get.log" 2>&1 && break
    [[ $try == 3 ]] && { tail -30 "$OUT/cache-get.log"; exit 1; }; echo "cache get: try $try failed"; sleep 30
  done
  tail -2 "$OUT/cache-get.log"
  step "organiser build (org-setup.sh step 1)"
  COMPPOLY="CompPoly.Fields.Binary.BF64.Ext3 CompPoly.Fields.Binary.BF64.Bytes"
  (cd "$ORG" && time timeout 1500 lake build RecursionFast $(printf '+%s ' $COMPPOLY)) > "$OUT/org-build.log" 2>&1 \
    || { tail -30 "$OUT/org-build.log"; exit 1; }
  tail -3 "$OUT/org-build.log"
fi
ORG=$(cd "$ORG" && pwd); export ORG PKGS=${PKGS:-$ORG/.lake/packages}
git -C "$ORG" rev-parse HEAD > "$OUT/core.txt" 2>/dev/null || true
git -C "$REPO" rev-parse HEAD > "$OUT/entry.txt" 2>/dev/null || true
if [[ -z "${KERNELS:-}" ]]; then
  step "comparator (core harness/ci/build-kernels.sh)"
  KERNELS=$TMP/kernels
  timeout 600 "$ORG/harness/ci/build-kernels.sh" "$KERNELS" > "$OUT/kernels.env" 2> "$OUT/kernels.log" \
    || { tail -30 "$OUT/kernels.log"; exit 1; }
fi
CMP=$KERNELS/comparator/.lake/build/bin/comparator
EXPORT=$KERNELS/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
[[ -x "$CMP" && -x "$EXPORT" ]] || { echo "comparator or lean4export missing under $KERNELS"; exit 1; }
(cd "$ORG" && lean --version) | tee -a "$OUT/machine.txt"

# 3. the build (build_s): every entry module, cold except for the organiser's environment
if [[ "${SKIP_BUILD:-0}" != 1 ]]; then
  step "tree $TREE"
  rm -rf "$TREE"; "$HERE/gen.sh" "$TREE"
  (cd "$TREE" && timeout 300 lake env true)       # the workspace loads (not timed)
  step "lake build FR (cap build_s = 600 s; scope $BUILD_MEM)"
  b0=$(date +%s.%N)
  (cd "$TREE" && capped build "$BUILD_MEM" "$BUILD_TIMEOUT" lake build FR) > "$OUT/build.log" 2>&1 || echo "build exit $?"
  b1=$(date +%s.%N)
  echo "build_wall_s $(echo "$b1 - $b0" | bc)" | tee "$OUT/build.wall"
  tail -3 "$OUT/build.log"
fi

# 4. the comparator (kernel_s): export and replay of the target sets' closures. SETS: `core`, every
# FR theorem and definition except the controls (filter-controls.py; the closest proxy of
# `certified`), `full`, all of them (an upper bound). KREPLAY: the sets replayed once more by
# KReplay.lean, which times each declaration in the kernel (the per-module breakdown).
SETS=${SETS-core full}; KREPLAY=${KREPLAY-core}
step "names"
mkdir -p "$OUT/names-full"
(cd "$TREE" && timeout 600 lake env lean --run "$HERE/ListConsts.lean" FR FR "$OUT/names-full") | tee "$OUT/names.txt"
python3 -I "$HERE/filter-controls.py" "$OUT/names-full" "$OUT/names-core" | tee -a "$OUT/names.txt"
for S in $SETS; do
  python3 -I - "$OUT/names-$S" "$TREE/config-$S.json" <<'PY'
import json, sys
d, out = sys.argv[1:]
rd = lambda f: [l.strip() for l in open(f"{d}/{f}") if l.strip()]
json.dump({"challenge_module": "FR", "solution_module": "FR", "theorem_names": rd("theorems.txt"),
           "definition_names": rd("definitions.txt"),
           "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "enable_nanoda": False}, open(out, "w"))
PY
  step "comparator, set $S (cap kernel_s = 600 s; scope $KERNEL_MEM)"
  # the comparator's stdout is block-buffered on a pipe, so its phases come from a process sampler:
  # each second, the time, lean4export's pid and RSS (kB) and the comparator's RSS (kB)
  ( set +e +o pipefail; while :; do
      e=$(ps -C lean4export -o pid=,rss= 2>/dev/null | head -1 || true)
      c=$(ps -C comparator -o rss= 2>/dev/null | head -1 || true)
      echo "$(date +%s.%N) ${e:-- -} ${c:--}"; sleep 1
    done ) > "$OUT/comparator-$S-ps.log" 2>/dev/null & SAMPLER=$!
  k0=$(date +%s.%N)
  (cd "$TREE" && COMPARATOR_LANDRUN=$HERE/landrun-pass.sh COMPARATOR_LEAN4EXPORT=$EXPORT \
     capped "comparator-$S" "$KERNEL_MEM" "$KERNEL_TIMEOUT" lake env "$CMP" "config-$S.json") 2>&1 \
    | while IFS= read -r l; do printf '%s %s\n' "$(date +%s.%N)" "${l:0:400}"; done > "$OUT/comparator-$S.log" || true
  k1=$(date +%s.%N); kill $SAMPLER 2>/dev/null || true
  echo "$k0 $k1" > "$OUT/comparator-$S.span"
  echo "comparator_wall_s $(echo "$k1 - $k0" | bc)" | tee "$OUT/comparator-$S.wall"
  grep -E ' (Lean default|Your solution|uncaught)' "$OUT/comparator-$S.log" | cut -c1-200 || tail -3 "$OUT/comparator-$S.log"
done
for S in $KREPLAY; do
  step "KReplay, set $S (per-declaration kernel time)"
  (cd "$TREE" && capped "kreplay-$S" "$KERNEL_MEM" "$KERNEL_TIMEOUT" lake env lean --run "$HERE/KReplay.lean" FR \
     "$OUT/names-$S" "$OUT/kreplay-$S.tsv") 2>&1 | tee "$OUT/kreplay-$S.log" || true
done

step "summary"
python3 -I "$HERE/summary.py" "$OUT" | tee "$OUT/summary.txt"
step "done"
