#!/usr/bin/env bash
# Dev-only timing probe of the compiled verifier (outside the entry; S-F2). The entry's modules as a
# library (default: L-cert's snapshot logs/fr-build-cert/src, HEAD plus L-cert's files), the probe as
# an executable. Packages from the private tree logs/pkgs via logs/org. S-F2 timed with
# SRC=logs/S-F2/src-fast: the snapshot with FRTranscriptDefs.bytesAt run as `q.get! (o + i)`
# (`implemented_by`, in that private copy only); see S-F2-RESULT §3.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); R=$(cd "$HERE/../.." && pwd)
SRC=${SRC:-$R/logs/fr-build-cert/src}
ROOTS=$(ls "$SRC"/*.lean | xargs -n1 basename | sed 's/\.lean$//; s/.*/"&"/' | paste -sd, -)
cat > "$HERE/lakefile.toml" <<EOT
name = "frvtime"
packagesDir = "$R/logs/pkgs"
[[require]]
name = "RecursionFast"
path = "$R/logs/org"
[[lean_lib]]
name = "RFSubmission"
srcDir = "$SRC"
roots = [$ROOTS]
[[lean_exe]]
name = "vtime"
root = "VTime"
EOT
