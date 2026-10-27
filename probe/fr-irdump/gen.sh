#!/usr/bin/env bash
# The dump tool's lake project (dev-only, outside the entry): the entry's modules as a library, the
# dump as an executable. Packages from the private tree logs/pkgs via logs/org, as logs/fr-build.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); R=$(cd "$HERE/../.." && pwd)
# SRC: the entry's sources (default); a private view may be passed while a module is mid-edit.
SRC=${SRC:-../../submissions/flock-recursive/lean}
cat > "$HERE/lakefile.toml" <<EOT
name = "frirdump"
packagesDir = "$R/logs/pkgs"
[[require]]
name = "RecursionFast"
path = "$R/logs/org"
[[lean_lib]]
name = "RFSubmission"
srcDir = "$SRC"
roots = ["FRFieldBase", "FRFieldBaseCorrect", "FRField128", "FRField256", "FRMerkle", "FRTranscriptDefs", "FRFormat", "FRVIR", "FRVIRSpec", "FRVIRFinals"]
[[lean_exe]]
name = "irdump"
root = "IRDump"
EOT
