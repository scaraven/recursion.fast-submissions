#!/usr/bin/env bash
# gcc2404-setup.sh DEBDIR TCDIR
# Builds the evaluation machine's toolchain (Ubuntu 24.04 "noble": gcc 13.3.0-6ubuntu2~24.04.1, binutils
# 2.42-4ubuntu2.10, libc6-dev 2.39-0ubuntu8.12) as a user-level sysroot in TCDIR. No install and no root needed.
#
# DEBDIR holds the 28 .deb files named in debs.sha256 (next to this script). On any machine with apt, fetch them with
# an apt configuration whose sources.list names noble, noble-updates and noble-security (main, amd64, signed by
# ubuntu-archive-keyring), e.g.
#   apt-get -c APTCONF update && cd DEBDIR && apt-get -c APTCONF download <package>=<version> ...
# with each <package>=<version> read off a file name in debs.sha256 (`%3a` is an escaped `:`), or download them from
# a noble mirror's pool/. The script checks every .deb against debs.sha256, unpacks each with `dpkg -x` into
# TCDIR/root, links noble's `as`/`ld` (TCDIR/bin) and the tools' own shared libraries (TCDIR/rtlib), and copies
# gcc2404.sh into TCDIR. Then build the prover's .s and link like the runner:
#   GCC=TCDIR/gcc2404.sh prover/build-asm.sh --variants "v2 v4p v4" --shape p17 --q q6-p17.qbin OUT
#   cd OUT/build && TCDIR/gcc2404.sh -static -O2 -pthread $(LC_ALL=C ls *.s) -o prover -lm
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: gcc2404-setup.sh DEBDIR TCDIR" >&2; exit 2; }
HERE=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd -P)
D=$(realpath -- "$1"); T=$(realpath -m -- "$2")
( cd "$D" && sha256sum -c --strict --quiet "$HERE/debs.sha256" )
mkdir -p "$T/root" "$T/bin" "$T/rtlib"
while read -r _ f; do dpkg -x "$D/$f" "$T/root"; done < "$HERE/debs.sha256"
ln -sfn ../root/usr/bin/x86_64-linux-gnu-as "$T/bin/as"
ln -sfn ../root/usr/bin/x86_64-linux-gnu-ld.bfd "$T/bin/ld"
for l in libbfd-2.42-system.so libctf-nobfd.so.0 libctf.so.0 libgmp.so.10 libgprofng.so.0 libisl.so.23 \
         libjansson.so.4 libmpc.so.3 libmpfr.so.6 libopcodes-2.42-system.so libsframe.so.1 libz.so.1 libzstd.so.1; do
  [ -e "$T/root/usr/lib/x86_64-linux-gnu/$l" ] || { echo "gcc2404-setup: $l missing from the unpacked .debs" >&2; exit 1; }
  ln -sfn "../root/usr/lib/x86_64-linux-gnu/$l" "$T/rtlib/$l"
done
install -m 755 "$HERE/gcc2404.sh" "$T/gcc2404.sh"
"$T/gcc2404.sh" --version | head -n 1
