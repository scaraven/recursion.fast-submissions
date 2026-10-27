#!/usr/bin/env bash
# S-E2 node dump (M rows, L rows, layout): lake project (dev-only, outside the entry): the entry's modules as a library, the
# dump as an executable. Packages from the private tree logs/pkgs via logs/org, as logs/fr-build.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); R=$(cd "$HERE/../.." && pwd)
# SRC: the entry's sources (default); a private view may be passed while a module is mid-edit.
SRC=${SRC:-../../submissions/flock-recursive/lean}
# every module of the entry (the finals import S-C/S-D modules)
ROOTS=$(cd "$HERE" && ls "$SRC"/*.lean | xargs -n1 basename | sed 's/\.lean$//; s/.*/"&"/' | paste -sd, -)
cat > "$HERE/lakefile.toml" <<EOT
name = "frnodedump"
packagesDir = "$R/logs/pkgs"
[[require]]
name = "RecursionFast"
path = "$R/logs/org"
[[lean_lib]]
name = "RFSubmission"
srcDir = "$SRC"
roots = [$ROOTS]
[[lean_exe]]
name = "nodedump"
root = "NodeDump"
EOT
