#!/usr/bin/env bash
# build-asm.sh [--variants "v2 v4p v4"] [--install DIR] [--q QBIN] WORK_DIR
#
# Emit the `lvm6-prover` binary of this workspace as GNU-as files, one per CPU tier, and link them exactly as the
# runner does (PROVER.md §1): `gcc -static -O2 -pthread /build/*.s -o /build/prover -lm`, here in WORK_DIR/build.
# Adapted from season 1 (archive/season-1/wide-packs/prover/build-asm.sh); what differs:
#   - a Cargo workspace (leanVM's crates vendored as crates, not as modules): the tier's target flags and the path
#     remaps go to EVERY crate through RUSTFLAGS (leanVM selects kernels with `cfg(target_feature)` in primitives,
#     pcs, keccak_gkr and keccak256, resolved when each crate is compiled); only the final crate gets `--emit asm`
#     and `-align-all-functions` (`cargo rustc -- …`), and fat LTO makes its output the whole program;
#   - no `rm`/`cargo clean`: the binary crate is re-run by touching prover/src/main.rs, and the raw `.s` is checked
#     to be newer than a stamp written just before.
#
#   prover-v2.s   -C target-cpu=x86-64-v2                                           the portable fallback
#   prover-v4.s   -C target-cpu=x86-64-v4 +pclmulqdq,+vpclmulqdq,+gfni,+avx512vbmi   the evaluation machine (Zen 4)
#   prover-v4p.s  -C target-cpu=x86-64-v4 +pclmulqdq                                AVX-512 without GFNI/VPCLMUL
#   dispatch.s    the hand-written `main` (season 1's, unchanged): cpuid/XCR0, then `lvm_main_<v>`
#
# Per tier: tools/asm-compat.py (the core's harness/tools/asm-compat.py, byte-identical), then tools/suffix-asm.py
# (every defined symbol suffixed `_lvm_<v>`, `main` -> `lvm_main_<v>`, start-up code checked vector-free).
# Cargo's target directories are WORK_DIR/target-<v>; the build is offline (no crates.io dependency).
#
# R8: `--q QBIN` (the compact circuit `Q`, `lvm6-prover qpack BLOB QBIN`) builds every tier with the feature
# `embedded-q` and writes `qblob.s` (tools/qblob-asm.py: `.rodata` `.quad` lines, symbols `lvm6_qblob` /
# `lvm6_qblob_len`), one file shared by the tiers; the shipped binary then reads no blob file (`prover setup` writes
# its raw form to the setup directory). `GCC=…` replaces /usr/bin/gcc in the link (e.g. Ubuntu 24.04's gcc 13.3).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
variants="v2 v4p v4"; install=""; work=""; qbin=""
while [ $# -gt 0 ]; do
  case "$1" in
    --variants) variants=$2; shift 2 ;;
    --install) install=$2; shift 2 ;;
    --q) qbin=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    *) work=$1; shift ;;
  esac
done
[ -n "$work" ] || { echo "usage: build-asm.sh [--variants LIST] [--install DIR] WORK_DIR" >&2; exit 2; }
mkdir -p "$work"
work=$(cd "$work" && pwd)

flags_v2="-C target-cpu=x86-64-v2"
flags_v4="-C target-cpu=x86-64-v4 -C target-feature=+pclmulqdq,+vpclmulqdq,+gfni,+avx512vbmi"
flags_v4p="-C target-cpu=x86-64-v4 -C target-feature=+pclmulqdq"
remap="--remap-path-prefix=$here=lvm6/prover-src --remap-path-prefix=$HOME=~"
features=""; qlink=""
if [ -n "$qbin" ]; then
  # cargo links the final crate besides emitting its assembly: give that (discarded) link the data's object
  features="--features embedded-q"
  python3 -I "$here/tools/qblob-asm.py" "$qbin" "$work/qblob.s"
  as -o "$work/qblob.o" "$work/qblob.s"
  qlink="-C link-arg=$work/qblob.o"
fi
gcc=${GCC:-/usr/bin/gcc}

emit() {
  local v=$1 flags_var="flags_$1" raw="$work/raw-$1.s" stamp="$work/stamp-$1"
  : > "$stamp"
  sleep 1
  touch "$here/prover/src/main.rs"
  # run from this directory so that rustup takes the toolchain of `rust-toolchain.toml`
  (cd "$here" && CARGO_TARGET_DIR="$work/target-$v" LVM_VARIANT="$v" RUSTFLAGS="${!flags_var} $remap" \
    cargo rustc --manifest-path "$here/Cargo.toml" -p lvm6-prover --bin lvm6-prover \
    --release --offline --locked $features \
    --config 'profile.release.lto="fat"' --config 'profile.release.codegen-units=1' \
    --config 'profile.release.panic="abort"' --config 'profile.release.debug=false' \
    --config 'profile.release.incremental=false' \
    -- --emit "asm=$raw" -C llvm-args=-align-all-functions=4 $qlink)
  if [ ! -s "$raw" ] || [ ! "$raw" -nt "$stamp" ]; then
    echo "build-asm: rustc wrote no fresh assembly for $v" >&2; exit 1
  fi
  python3 -I "$here/tools/asm-compat.py" "$raw" "$work/compat-$v.s"
  python3 -I "$here/tools/suffix-asm.py" "$v" "$work/compat-$v.s" "$work/prover-$v.s"
}

for v in $variants; do emit "$v"; done

mkdir -p "$work/build"
for f in "$work"/build/*.s; do
  [ -e "$f" ] || continue
  case "$(basename "$f")" in
    dispatch.s) ;;
    qblob.s) [ -n "$qbin" ] || { echo "build-asm: $f is from an embedded-q build; move it away first" >&2; exit 1; } ;;
    prover-*.s) case " $variants " in *" $(basename "$f" .s | sed 's/^prover-//') "*) ;; *)
      echo "build-asm: $f is from another variant set; move it away first (this script deletes nothing)" >&2; exit 1 ;; esac ;;
    *) echo "build-asm: unexpected $f in the build directory" >&2; exit 1 ;;
  esac
done
cp "$here/dispatch.s" "$work/build/dispatch.s"
for v in $variants; do cp "$work/prover-$v.s" "$work/build/prover-$v.s"; done
[ -z "$qbin" ] || cp "$work/qblob.s" "$work/build/qblob.s"
# The runner's link step, verbatim but for the directory. The runner's glob sorts in C order (dispatch.s,
# prover-v2.s, prover-v4.s, prover-v4p.s); the link order changes the binary's layout, so sort in C order too.
(cd "$work/build" && LC_ALL=C $gcc -static -O2 -pthread $(LC_ALL=C ls -d -- "$work"/build/*.s) -o "$work/build/prover" -lm)
if [ -n "$install" ]; then
  mkdir -p "$install"
  cp "$here/dispatch.s" "$install/dispatch.s"
  for v in $variants; do cp "$work/prover-$v.s" "$install/prover-$v.s"; done
  [ -z "$qbin" ] || cp "$work/build/qblob.s" "$install/qblob.s"
fi
for f in $(LC_ALL=C ls -d -- "$work"/build/*.s); do
  echo "build-asm: $(basename "$f") $(wc -c < "$f") bytes, sha256 $(sha256sum "$f" | cut -d' ' -f1)"
done
echo "build-asm: $work/build/prover $(wc -c < "$work/build/prover") bytes, sha256 $(sha256sum "$work/build/prover" | cut -d' ' -f1)"
