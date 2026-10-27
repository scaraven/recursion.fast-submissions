#!/usr/bin/env bash
# build-asm.sh [WORK_DIR]
#
# Emit the prover crate in this directory as ONE x86-64 GNU-as file, `prover.s` (beside this
# script; the file the runner builds), and link it exactly as the v4 runner does
# (`harness/rfh/prover.py` `build`): `gcc -static -O2 -pthread /build/*.s -o /build/prover -lm`,
# here into WORK_DIR/build/prover (default: ${TMPDIR:-/tmp}/flock-recursive-asm). Cargo's target
# directory is WORK_DIR/target (outside the entry). Recipe of stage F0 (`stages/F0-probes-RESULT.md`
# §1), with the CPU pinned:
#   1. fat LTO, one codegen unit, panic=abort: core/alloc/std and the crate are one LLVM module, and
#      `--emit asm` on the final crate prints the whole program (rustc runs LTO only when it also
#      links, which cargo always asks for);
#   2. `-C target-cpu=x86-64-v2` (the runners have more; pclmulqdq is chosen at run time,
#      `field.rs`), `-C llvm-args=-align-all-functions=4` (no `.prefalign`, unknown to GNU as);
#   3. `sanitize-asm.py` drops DWARF directives and `.debug_*` sections (GNU as rejects LLVM's
#      DWARF-5 `.file N "dir" "file"` lines from std's bitcode) and refuses `.incbin`/`.include`.
# Paths are remapped so the `.s` holds no path of this machine (`--remap-path-prefix`), and the
# build is offline (no dependencies). Two clean builds give the same `prover.s` byte for byte.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
work=${1:-${TMPDIR:-/tmp}/flock-recursive-asm}
mkdir -p "$work"
work=$(cd "$work" && pwd)
export CARGO_TARGET_DIR="$work/target"
raw="$work/raw.s"
rm -f "$raw"
# run from this directory so that rustup takes the toolchain of `rust-toolchain.toml` (1.99.0)
(cd "$here" && cargo rustc --manifest-path "$here/Cargo.toml" --release --offline --locked --bin flock-prover \
  --config 'profile.release.lto="fat"' --config 'profile.release.codegen-units=1' \
  --config 'profile.release.panic="abort"' --config 'profile.release.debug=false' \
  --config 'profile.release.incremental=false' \
  -- --emit "asm=$raw" -C target-cpu=x86-64-v2 -C llvm-args=-align-all-functions=4 \
  --remap-path-prefix "$here=flock-recursive/prover" --remap-path-prefix "$HOME=~")
# cargo skips rustc when the crate is fresh: then rebuild from a clean target directory
if [ ! -s "$raw" ]; then
  [ -z "${BUILD_ASM_RETRY:-}" ] || { echo "build-asm: rustc wrote no assembly" >&2; exit 1; }
  (cd "$here" && cargo clean --release --manifest-path "$here/Cargo.toml")
  BUILD_ASM_RETRY=1 exec "$0" "$@"
fi
python3 -I "$here/sanitize-asm.py" "$raw" "$here/prover.s"
mkdir -p "$work/build"
rm -f "$work"/build/*.s "$work/build/prover"
cp "$here/prover.s" "$work/build/prover.s"
# the runner's link step, verbatim but for the directory (outside its sandbox)
(cd "$work/build" && /usr/bin/gcc -static -O2 -pthread "$work"/build/*.s -o "$work/build/prover" -lm)
echo "build-asm: prover.s $(wc -c < "$here/prover.s") bytes, sha256 $(sha256sum "$here/prover.s" | cut -d' ' -f1)"
echo "build-asm: $work/build/prover $(wc -c < "$work/build/prover") bytes, sha256 $(sha256sum "$work/build/prover" | cut -d' ' -f1)"
