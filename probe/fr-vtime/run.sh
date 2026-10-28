#!/usr/bin/env bash
# H-V: the Flock-recursive verifier's time on the runner, beside the cap it must meet.
#   probe/fr-vtime/run.sh [OUTDIR]
#   env: CPU (core to pin, default 1), REPS (warm runSeq runs per process, default 21),
#        VRUNS (vtime N processes, default 3), KINDS (other kinds, one process each, default "L P"),
#        CHECKER_RUNS (default 3), R (default 6), N (default 262144),
#        ORG/PKGS (a prebuilt core checkout and package tree; default: clone the core at the pin
#        recorded for `.contract` and `lake exe cache get` there, as the evaluation's setup job does)
# Prints: the machine; `vtime v K REPS` (S-E8's method: a synthetic proof of kind K, its oracle trace
# recorded once, then REPS warm `runSeq` runs on one pinned core, best and median); the core's
# chain checker `chaincheck` at the season shape (2^R chains of N steps), CHECKER_RUNS runs on the
# same core: T_triv,best is their minimum and the cap T_V = T_triv,best / 10 (season.toml `R = 10`).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
CPU=${CPU:-1}; REPS=${REPS:-21}; VRUNS=${VRUNS:-3}; KINDS=${KINDS-L P}
RUNS=${CHECKER_RUNS:-3}; R=${R:-6}; N=${N:-262144}
t0=$(date +%s); step() { echo "== $1 ($(( $(date +%s) - t0 )) s)"; }

{ lscpu; echo; grep -m1 '^flags' /proc/cpuinfo | tr ' ' '\n' \
    | grep -x -E 'pclmulqdq|vpclmulqdq|gfni|avx2|avx512f|sha_ni|bmi2|adx' | sort | tr '\n' ' '; echo;
  nproc; free -g; uptime; echo "RUNNER_NAME=${RUNNER_NAME:-} ImageOS=${ImageOS:-} ImageVersion=${ImageVersion:-}"; } \
  > "$OUT/machine.txt" 2>&1
grep -E 'Model name|^CPU\(s\)|Thread|MHz' "$OUT/machine.txt" || true
sed -n '/^$/{n;p;q}' "$OUT/machine.txt"

# the core: a fresh clone at the pin, its package tree from Mathlib's cache (CompPoly from source)
if [[ -z "${ORG:-}" ]]; then
  PIN=$(git -C "$REPO" ls-tree HEAD .contract | awk '{print $3}')
  [[ -n "$PIN" ]] || { echo "no .contract pin"; exit 1; }
  ORG=${WORK:-$REPO/../rf-core}
  step "core $PIN into $ORG"
  rm -rf "$ORG"; git clone -q https://github.com/scaraven/recursion.fast "$ORG"; git -C "$ORG" checkout -q "$PIN"
  (cd "$ORG" && timeout 900 lake exe cache get) > "$OUT/cache-get.log" 2>&1 || { tail -30 "$OUT/cache-get.log"; exit 1; }
  tail -2 "$OUT/cache-get.log"
  PKGS=$ORG/.lake/packages
fi
ORG=$(cd "$ORG" && pwd); PKGS=${PKGS:-$ORG/.lake/packages}
git -C "$ORG" rev-parse HEAD > "$OUT/core.txt" 2>/dev/null || true
git -C "$REPO" rev-parse HEAD > "$OUT/entry.txt" 2>/dev/null || true

step "build vtime (entry modules from $REPO/submissions/flock-recursive/lean)"
ORG=$ORG PKGS=$PKGS "$HERE/gen.sh"
cd "$HERE"
lean --version | tee -a "$OUT/machine.txt"
( time timeout 5400 lake build vtime ) > "$OUT/build.log" 2>&1 || { tail -40 "$OUT/build.log"; exit 1; }
grep -E 'Build completed|^real' "$OUT/build.log" || true
step "build chaincheck (the core's harness/lean-tools)"
( cd "$ORG/harness/lean-tools" && time timeout 900 lake build chaincheck ) > "$OUT/build-chaincheck.log" 2>&1 \
  || { tail -20 "$OUT/build-chaincheck.log"; exit 1; }
VT=$HERE/.lake/build/bin/vtime; CC=$ORG/harness/lean-tools/.lake/build/bin/chaincheck
sha256sum "$VT" "$CC" > "$OUT/binaries.sha256"

step "vtime v N $REPS, $VRUNS processes (taskset -c $CPU)"
for i in $(seq "$VRUNS"); do
  timeout 900 taskset -c "$CPU" "$VT" v N "$REPS" > "$OUT/vtime-N-$i.log" 2>&1
  grep -E 'kind|collect|best|traceDigest' "$OUT/vtime-N-$i.log"
done
for k in $KINDS; do
  step "vtime v $k $REPS (taskset -c $CPU)"
  timeout 900 taskset -c "$CPU" "$VT" v "$k" "$REPS" > "$OUT/vtime-$k.log" 2>&1 || true
  grep -E 'kind|collect|best|traceDigest' "$OUT/vtime-$k.log" || tail -5 "$OUT/vtime-$k.log"
done

step "chaincheck at r=$R n=$N, $RUNS runs (taskset -c $CPU)"
python3 -I "$REPO/probe/lean-field/gen_leaves.py" "$R" "$N" "$OUT/leaves.json"
for i in $(seq "$RUNS"); do timeout 300 taskset -c "$CPU" "$CC" "$OUT/leaves.json" 00; done | tee "$OUT/chaincheck.txt"

# summary: V best/median per process, T_triv,best, the cap and the margin
python3 -I - "$OUT" <<'PY' | tee "$OUT/summary.txt"
import glob, os, re, sys
out = sys.argv[1]
ms = lambda s: float(s)
model = next((l.split(":", 1)[1].strip() for l in open(os.path.join(out, "machine.txt")) if l.startswith("Model name")), "?")
print(f"cpu: {model}")
best = {}
for f in sorted(glob.glob(os.path.join(out, "vtime-*.log"))):
    m = re.search(r"runSeq best ([\d.]+) ms, median ([\d.]+) ms over (\d+)", open(f).read())
    if m:
        k = os.path.basename(f)[6:-4]
        print(f"V {k}: best {m[1]} ms, median {m[2]} ms over {m[3]}")
        best.setdefault(k.split("-")[0], []).append((ms(m[1]), ms(m[2])))
cc = [int(l.split()[1]) for l in open(os.path.join(out, "chaincheck.txt")) if len(l.split()) == 2]
tb = min(cc) / 1e6
print(f"chaincheck ms: {[round(c / 1e6, 1) for c in cc]}; T_triv,best {tb:.1f} ms; cap T_V {tb / 10:.2f} ms")
if "N" in best:
    vb = min(b for b, _ in best["N"]); vm = sorted(m for _, m in best["N"])[len(best["N"]) // 2]
    print(f"V N30 best {vb:.2f} ms, median-of-medians {vm:.2f} ms; margin cap / V: best {tb / 10 / vb:.3f}x, median {tb / 10 / vm:.3f}x")
PY
step "done"
