#!/usr/bin/env bash
# Dev-only timing probe of the compiled verifier (outside the entry; S-F2, H-V). Writes this
# directory's lakefile.toml and lake-manifest.json: the entry's modules as a library, the probe
# `VTime.lean` as the executable `vtime`, the core `RecursionFast` as a path dependency.
#   env: SRC  the entry's modules   (default: submissions/flock-recursive/lean)
#        ORG  the core's checkout   (default: the private tree logs/org)
#        PKGS its package tree      (default: the private tree logs/pkgs)
# On the runner, run.sh sets ORG to a fresh clone of the core and PKGS to its .lake/packages.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); R=$(cd "$HERE/../.." && pwd)
SRC=${SRC:-$R/submissions/flock-recursive/lean}
ORG=${ORG:-$R/logs/org}
PKGS=${PKGS:-$R/logs/pkgs}
ROOTS=$(ls "$SRC"/FR*.lean | xargs -n1 basename | sed 's/\.lean$//; s/.*/"&"/' | paste -sd, -)
cat > "$HERE/lakefile.toml" <<EOT
name = "frvtime"
packagesDir = "$PKGS"
[[require]]
name = "RecursionFast"
path = "$ORG"
[[lean_lib]]
name = "RFSubmission"
srcDir = "$SRC"
roots = [$ROOTS]
[[lean_exe]]
name = "vtime"
root = "VTime"
EOT
# the manifest: the core's own (its pinned packages), plus the core as a path package
python3 -I - "$ORG/lake-manifest.json" "$ORG" "$PKGS" > "$HERE/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
pk = [{"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
       "inherited": False, "dir": sys.argv[2], "configFile": "lakefile.toml"}]
for p in m["packages"]:
    p = dict(p); p["inherited"] = True; pk.append(p)
print(json.dumps({"version": m["version"], "packages": pk, "name": "frvtime", "lakeDir": ".lake",
                  "fixedToolchain": False, "packagesDir": sys.argv[3]}, indent=1))
PY
cp "$ORG/lean-toolchain" "$HERE/lean-toolchain"
