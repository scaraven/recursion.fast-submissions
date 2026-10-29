#!/usr/bin/env bash
# H-cert2 probe (from cert-time/gen.sh, with Solution.lean): a build tree laid out as harness/evaluate.py's `mkfresh` does (the entry's modules as
# the library RFSubmission, the core `RecursionFast` as a path dependency, the core's package tree).
#   probe/cert-time/gen.sh TREE      env: SRC (default submissions/flock-recursive/lean), ORG, PKGS
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); R=$(cd "$HERE/../.." && pwd)
T=${1:?usage: gen.sh TREE}; mkdir -p "$T"; T=$(cd "$T" && pwd)
SRC=${SRC:-$R/submissions/flock-recursive/lean}
ORG=${ORG:?ORG}; PKGS=${PKGS:-$ORG/.lake/packages}
mkdir -p "$T/submission"; cp "$SRC"/*.lean "$T/submission/"
ROOTS=$(ls "$T/submission"/*.lean | xargs -n1 basename | sed 's/\.lean$//; s/.*/"&"/' | paste -sd, -)
cat > "$T/lakefile.toml" <<EOT
name = "rfentry"
packagesDir = "$PKGS"
[[require]]
name = "RecursionFast"
path = "$ORG"
[[lean_lib]]
name = "RFSubmission"
srcDir = "submission"
roots = [$ROOTS]
EOT
python3 -I - "$ORG/lake-manifest.json" "$ORG" "$PKGS" > "$T/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
m["packages"] = [dict(p, inherited=True) for p in m["packages"]]
m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                         "inherited": False, "dir": sys.argv[2], "configFile": "lakefile.toml"})
m["name"], m["packagesDir"] = "rfentry", sys.argv[3]
print(json.dumps(m, indent=1))
PY
cp "$ORG/lean-toolchain" "$T/lean-toolchain"
