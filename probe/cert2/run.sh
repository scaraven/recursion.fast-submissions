#!/usr/bin/env bash
# H-cert2: the certificate job's kernel step (season.toml [certificate] kernel_s = 600) on the closure
# that is certified today: `Solution`'s `certified` and `submission`, the harness's own comparator
# targets (evaluate.py step 4). Adapted from probe/cert-time (H-cert), whose tools it reuses
# (ListConsts.lean, filter-controls.py, KReplay.lean, landrun-pass.sh).
#   probe/cert2/run.sh [OUTDIR]      env: as probe/cert-time/run.sh
# The harness's comparator rejects the PROVISIONAL `certified` (it states the hypothesis `Open4`) at
# the statement check, before the kernel. So here challenge = solution = Solution (the statements
# agree trivially) and the run reaches the export and the kernel replay. Step 3 is `lake build
# Solution` (a cross-check of probe/si-cert's build_s; the challenge is not rendered). Sets:
#   cert   theorem_names = [certified], definition_names = [submission]: the closure the harness
#          replays today (Open4 is a hypothesis, so its eventual proof is not in it);
#   upper  the two targets plus every non-control theorem and definition of the FR* modules in
#          Solution's import closure: an upper bound for when Open4 is proved.
# Export 1 (the challenge's) is full size here; in the real job it is a few constants, so the
# summary also reports the time without it.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
TMP=${RUNNER_TEMP:-${TMPDIR:-/tmp}}
TREE=${TREE:-$TMP/cert-tree}
CT=$(cd "$HERE/../cert-time" && pwd)
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
  step "lake build Solution (cap build_s = 1200 s; scope $BUILD_MEM)"
  b0=$(date +%s.%N)
  (cd "$TREE" && capped build "$BUILD_MEM" "$BUILD_TIMEOUT" lake build Solution) > "$OUT/build.log" 2>&1 || echo "build exit $?"
  b1=$(date +%s.%N)
  echo "build_wall_s $(echo "$b1 - $b0" | bc)" | tee "$OUT/build.wall"
  tail -3 "$OUT/build.log"
fi

# 4. the comparator (kernel_s), once per set (see the header); KREPLAY: the sets replayed once more
# by KReplay.lean, which times each declaration in the kernel (the per-module breakdown).
SETS=${SETS-cert upper}; KREPLAY=${KREPLAY-cert upper}
step "names"
mkdir -p "$OUT/names-all" "$OUT/names-cert"
(cd "$TREE" && timeout 600 lake env lean --run "$CT/ListConsts.lean" Solution FR "$OUT/names-all") | tee "$OUT/names.txt"
python3 -I "$CT/filter-controls.py" "$OUT/names-all" "$OUT/names-upper" | tee -a "$OUT/names.txt"
echo RecursionFast.Challenge.certified > "$OUT/names-cert/theorems.txt"
echo RecursionFast.Challenge.submission > "$OUT/names-cert/definitions.txt"
echo RecursionFast.Challenge.certified >> "$OUT/names-upper/theorems.txt"
echo RecursionFast.Challenge.submission >> "$OUT/names-upper/definitions.txt"
for S in $SETS; do
  python3 -I - "$OUT/names-$S" "$TREE/config-$S.json" <<'PY'
import json, sys
d, out = sys.argv[1:]
rd = lambda f: [l.strip() for l in open(f"{d}/{f}") if l.strip()]
json.dump({"challenge_module": "Solution", "solution_module": "Solution", "theorem_names": rd("theorems.txt"),
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
  (cd "$TREE" && COMPARATOR_LANDRUN=$CT/landrun-pass.sh COMPARATOR_LEAN4EXPORT=$EXPORT \
     capped "comparator-$S" "$KERNEL_MEM" "$KERNEL_TIMEOUT" lake env "$CMP" "config-$S.json") 2>&1 \
    | while IFS= read -r l; do printf '%s %s\n' "$(date +%s.%N)" "${l:0:400}"; done > "$OUT/comparator-$S.log" || true
  k1=$(date +%s.%N); kill $SAMPLER 2>/dev/null || true
  echo "$k0 $k1" > "$OUT/comparator-$S.span"
  echo "comparator_wall_s $(echo "$k1 - $k0" | bc)" | tee "$OUT/comparator-$S.wall"
  grep -E ' (Lean default|Your solution|uncaught)' "$OUT/comparator-$S.log" | cut -c1-200 || tail -3 "$OUT/comparator-$S.log"
done
for S in $KREPLAY; do
  step "KReplay, set $S (per-declaration kernel time)"
  (cd "$TREE" && capped "kreplay-$S" "$KERNEL_MEM" "$KERNEL_TIMEOUT" lake env lean --run "$CT/KReplay.lean" Solution \
     "$OUT/names-$S" "$OUT/kreplay-$S.tsv") 2>&1 | tee "$OUT/kreplay-$S.log" || true
done

step "summary"
BUILD_CAP=1200 python3 -I "$CT/summary.py" "$OUT" | tee "$OUT/summary.txt"
step "done"
