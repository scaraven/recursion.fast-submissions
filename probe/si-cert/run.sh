#!/usr/bin/env bash
# S-I: the harness's own certificate job (`harness/evaluate.py cert` of the core at the `.contract`
# pin) on this commit's `submissions/flock-recursive`, with the season's [certificate] caps raised so
# that every step (build, comparator, gate, badge) runs to its end and is timed by evaluate.py
# itself. The organiser's environment is prepared as the evaluation's setup jobs do it (`lake exe
# cache get`, `org-setup.sh` with RF_ORG_SERVICE=0, `build-kernels.sh`), on this runner, untimed.
#   probe/si-cert/run.sh [OUTDIR]      env: CAP_BUILD (3000), CAP_KERNEL (1800), CAP_GATE (600),
#                                      CAP_BADGE (1800): the raised caps, in seconds
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/out}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
TMP=${RUNNER_TEMP:-${TMPDIR:-/tmp}}
t0=$(date +%s); step() { echo "== $1 ($(( $(date +%s) - t0 )) s)"; }
{ lscpu; nproc; free -g; echo "ImageOS=${ImageOS:-} ImageVersion=${ImageVersion:-}"; } > "$OUT/machine.txt" 2>&1
grep -m1 'Model name' "$OUT/machine.txt" || true
git -C "$REPO" rev-parse HEAD > "$OUT/entry.txt"

PIN=$(git -C "$REPO" ls-tree HEAD .contract | awk '{print $3}')
ORG=$TMP/core
step "core $PIN"
rm -rf "$ORG"; git clone -q https://github.com/scaraven/recursion.fast "$ORG"
git -C "$ORG" fetch -q origin "$PIN" || true
git -C "$ORG" checkout -q "$PIN"
"$ORG/harness/ci/runner-setup.sh" > "$OUT/runner-setup.log" 2>&1 || { cat "$OUT/runner-setup.log"; exit 1; }
export XDG_RUNTIME_DIR=/run/user/$(id -u) DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus
step "lake exe cache get"
for try in 1 2 3; do
  (cd "$ORG" && timeout 600 lake exe cache get) >> "$OUT/cache-get.log" 2>&1 && break
  [[ $try == 3 ]] && { tail -20 "$OUT/cache-get.log"; exit 1; }; sleep 30
done
step "org-setup.sh (RF_ORG_SERVICE=0)"
(cd "$ORG" && mkdir -p logs && RF_ORG_SERVICE=0 timeout 2400 harness/org-setup.sh "$ORG") > "$OUT/org-setup.log" 2>&1 \
  || { tail -30 "$OUT/org-setup.log"; exit 1; }
step "comparator (build-kernels.sh)"
K=$TMP/kernels
timeout 600 "$ORG/harness/ci/build-kernels.sh" "$K" > "$OUT/kernels.env" 2> "$OUT/kernels.log" || { tail -20 "$OUT/kernels.log"; exit 1; }
set -a; source "$OUT/kernels.env"; set +a

SEASON=$TMP/season-probe.toml
sed -e "s/^build_s = 600 /build_s = ${CAP_BUILD:-3000} /" -e "s/^kernel_s = 600 /kernel_s = ${CAP_KERNEL:-1800} /" \
    -e "s/^gate_s = 120 /gate_s = ${CAP_GATE:-600} /" -e "s/^badge_s = 180 /badge_s = ${CAP_BADGE:-1800} /" \
    "$ORG/harness/season.toml" > "$SEASON"
grep -A5 '^\[certificate\]' "$SEASON" | tee "$OUT/caps.txt"
step "evaluate.py cert"
rc=0
/usr/bin/time -v -o "$OUT/cert.time" python3 -I "$ORG/harness/evaluate.py" cert --entry "$REPO/submissions/flock-recursive" \
  --org "$ORG" --work "$TMP/cert" --season "$SEASON" --out "$OUT/cert.json" || rc=$?
echo "evaluate.py cert exit $rc"
for f in build gate badge manifest source-rule render comparator-lean; do
  [[ -f "$TMP/cert/$f.log" ]] && tail -c 2000000 "$TMP/cert/$f.log" > "$OUT/$f.log"
done
python3 -I - "$OUT/cert.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
for k in ("status", "reasons", "provisional_reasons", "build_s", "comparator_s", "gate_s", "badge_s", "gate", "built_modules"):
    v = c.get(k)
    print(k, "=", len(v) if k == "built_modules" and v else v)
lr = (c.get("kernel_runs") or {}).get("lean") or {}
print("kernel lean:", lr.get("outcome"), lr.get("seconds"), lr.get("peak_bytes"))
PY
step "done"
