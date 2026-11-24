#!/usr/bin/env bash
# gcc2404.sh <gcc args...>
# Runs Ubuntu 24.04 (noble) gcc 13.3.0-6ubuntu2~24.04.1 + binutils 2.42-4ubuntu2.10 + glibc 2.39-0ubuntu8.12
# (libc6-dev), all extracted with dpkg -x into ./root, never the host toolchain.
#  - driver:       root/usr/bin/x86_64-linux-gnu-gcc-13 (cc1/collect2 found relative to it in root/usr/libexec/gcc)
#  - as / ld:      bin/as, bin/ld -> root/usr/bin/x86_64-linux-gnu-{as,ld.bfd}, selected with -B and PATH
#  - crt/libs:     --sysroot=root (crt1.o/crti.o/crtn.o/libc.a/libm.a from root/usr/lib/x86_64-linux-gnu,
#                  crtbeginT.o/libgcc.a/libgcc_eh.a from root/usr/lib/gcc/x86_64-linux-gnu/13)
#  - tool runtime: noble's non-glibc shared libs (libbfd, libctf, libisl, libmpc, ...) via rtlib/;
#                  the tools themselves run on the host's ld.so/libc.so.6 (does not affect their output).
set -u
TC=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd -P)
R=$TC/root
unset GCC_EXEC_PREFIX COMPILER_PATH LIBRARY_PATH CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH OBJC_INCLUDE_PATH \
      DEPENDENCIES_OUTPUT SUNPRO_DEPENDENCIES GCC_COMPARE_DEBUG LD_PRELOAD LD_RUN_PATH LDEMULATION
export PATH="$TC/bin:$R/usr/bin"
export LD_LIBRARY_PATH="$TC/rtlib"
exec "$R/usr/bin/x86_64-linux-gnu-gcc-13" --sysroot="$R" -B"$TC/bin/" "$@"
