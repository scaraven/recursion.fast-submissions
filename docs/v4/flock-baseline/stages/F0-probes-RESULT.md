# F0: probes (assembly route, spartan-chain sizes under v4, Flock on this VM), 2026-10-22

Status: the probe agent's report, lightly edited for layout. All logs under the worktree's
`logs/probes/` (gitignored; `P` below). Toolchain: rustc 1.99.0 (LLVM 23.1.1), gcc 15.2.0,
binutils `as`/`ld` 2.46, glibc 2.43. The VM (32 vCPU QEMU, AVX2 and AVX-512F, **no pclmulqdq**)
had load average 10–16 from other agents: every timing is a relative indication only.

## 1. The assembly route: works, with one sanitising step

**Verdict.** A `std` Rust program with dependencies can be emitted as one `.s` file that the
harness's exact command `gcc -static -O2 -pthread *.s -o prover -lm` links into a working static
binary.

- **Recipe** (`P/asm/build-asm.sh`, filter `P/asm/sanitize-asm.py`, sample crates
  `P/asm/sample-std`, `P/asm/sample-rayon`):
  `cargo rustc --release --bin B --config 'profile.release.lto="fat"' --config profile.release.codegen-units=1 --config 'profile.release.panic="abort"' -- --emit asm=raw.s -C llvm-args=-align-all-functions=4`,
  then `python3 -I sanitize-asm.py raw.s prover.s`, then the harness's `gcc` command.
- **The raw `.s` does not assemble with GNU `as`** (`P/asm/t1/link.log`, `P/asm/t2/link.log`):
  `Error: unknown pseudo-op: '.prefalign'` ×428 (new in LLVM 23; `-C llvm-args=-align-all-functions=4`
  removes it, the filter also rewrites it), and `Error: junk at end of line, first unrecognized
  character is '"'` ×284 on DWARF-5 `.file 1 "/rustc/<hash>" "library/alloc/..."` lines carried in
  from std's precompiled bitcode; `-C dwarf-version=4` does not help and no stable flag strips them.
  The filter drops `.file N`, `.loc` and `.debug_*` sections and refuses `.incbin`/`.include`.
- **LTO runs only when rustc links**: cargo passes `link`; with bare rustc use
  `--emit asm=X,link` (plain `--emit asm` gives the pre-LTO crate, and `gcc` then reports undefined
  std symbols).
- **Sample program** (8 threads with TLS, Unix-socket echo, file I/O, formatting, an AVX2 function
  chosen at run time by `is_x86_feature_detected!`, inline asm): assembles, links, runs, takes the
  AVX2 path; `#[target_feature(enable="avx2")]` keeps its ymm code; panic prints and aborts
  (exit 134); `panic="unwind"` also links; `relocation-model` default PIC and `static` both work;
  `-C target-cpu=x86-64-v3` works.
- **Symbols.** `main`, `lang_start`, `rust_eh_personality`, `__rust_alloc` are inside the `.s`; of
  76 external symbols, `_Unwind_*` come from libgcc_eh and the rest from static glibc (pthread,
  socket, `dlsym`, `dl_iterate_phdr`); `compiler_builtins` is not in the `.s` but libgcc supplies
  `__udivti3`, `__divti3`, `__floattisf`.
- **Sizes**: sample-std raw `.s` 7.70 MB → 2.87 MB after the filter, binary 1.47 MB;
  sample-rayon (a crates.io dependency) 2.96 MB / 1.48 MB; **the v3 spartan-chain prover: 8.05 MB of
  `.s`, binary 2.61 MB**, emitted in 1 min 40 s (`P/asm/build-asm-sc.log`); its `prove-leaf n=16`
  proof is byte-identical to the cargo-built binary's and verifies (`P/asm/sc-cmp`).
- **Through the harness's own sandboxed build** (`rfh.prover.build`): sample-std and spartan-chain
  link (`P/asm/harness-build/harness-build.log`); same binary hash as the local link.
- **Deterministic**: the same filtered `.s` SHA-256 across two clean builds, another target dir and
  a copy of the crate in another directory; identical binaries.
- **Paths**: no `/home`, no `.incbin`; 57 `"/rustc/<hash>/library/..."` strings remain as panic
  location data (data only).
- `no_std` + `no_main` on libc also works (111 KB `.s`, 924 KB binary; needs the same filter).
  C: `gcc -S -O3` with pthreads, AVX2 and `__builtin_cpu_supports` gives a 7.6 KB `.s` that links.
- **Caveat**: Flock and leanVM select clmul/AVX-512 at compile time (`target-cpu=native` in
  `.cargo/config`); an assembly entry must pin its target CPU when it emits the `.s` and dispatch at
  run time, or the build host's ISA is baked in.
- **Not tested**: Ubuntu 24.04's binutils 2.42 (the runner's).

## 2. spartan-chain's proof and v4 trace sizes

Instrumented copy (per-tag oracle counters, `P/sc-instrumentation.diff`), `SPARTAN_THREADS=16`,
`P/sc-runs/n<N>.log`. "v4 trace" = Σ over the verifier's queries of `8 + |q| + 32` (FORMAT.md),
`q` without v3's internal `0x52` prefix.

| n | proof B | prove s | peak RSS | V queries | V Σ\|q\| B | **v4 trace B** | prover oracle calls (Merkle leaf / node / FS) | prover Σ\|q\| |
|---|---|---|---|---|---|---|---|---|
| 16 | 143,711 | 0.16 | 8 MB | 3,533 | 248,875 | 390,195 | 8,344 (4,096 / 4,095 / 153) | 0.56 MB |
| 1024 | 457,843 | 0.92 | 255 MB | 4,414 | 591,318 | 767,878 | 65,789 (32,768 / 32,767 / 254) | 19.1 MB |
| 4096 | 796,111 | 3.40 | 995 MB | 4,753 | 940,519 | 1,130,639 | 131,404 (65,536 / 65,535 / 333) | 71.7 MB |
| 16384 | 1,464,107 | 11.24 | 3.95 GB | 5,156 | 1,621,560 | 1,827,800 | 262,619 (131,072 / 131,071 / 476) | 277.6 MB |
| 65536 | 2,791,559 | 45.43 | 15.8 GB | 5,687 | 2,966,281 | 3,193,761 | 525,034 (262,144 / 262,143 / 747) | 1.09 GB |

The verifier's 260 column-leaf queries carry the opened columns again (1.07 MB at n = 65536), so
the v4 trace is about the size of `π` or larger (2.7× at n = 16). Under v4 the prover pushes about
525k calls and 1.1 GB through the service at n = 65536, almost all Merkle leaves hashing whole
columns. Proofs at n ≥ 16384 exceed `proofCap`.

## 3. Flock (succinctlabs, BLAKE3) on this VM

Commit `b684b12` (2026-09-11), `P/flock-src`. BLAKE3 and SHA-256 only (no BLAKE2s). The fast path
needs AVX-512F + VPCLMULQDQ chosen at compile time; without them GF(2^128) multiplication falls
back to a bit-by-bit clmul. Builds here (2 min 48 s, crates over the network, `P/flock-build.log`).
`RAYON_NUM_THREADS=16`:

| BLAKE3 compressions | best prove | throughput | proof | verify | peak heap | max RSS |
|---|---|---|---|---|---|---|
| 2^14 | 5.36 s | 3,058 /s | 283,104 B | 53.9 ms | 1,079 MB | 1.44 GB |
| 2^16 | 13.94 s | 4,701 /s | 416,368 B | 63.9 ms | 2,629 MB | 3.64 GB |

At 2^14: commit 2.42 s, Ligerito opening 2.33 s, zerocheck + lincheck 0.31 s (`P/flock-bench-2e14-trace.log`);
CPU use 235–270 %. About 100–135× below the README's Threadripper + VPCLMULQDQ figures.

## 4. leanVM's Flock (BLAKE2s, WHIR, GF(2^64)/GF(2^192)) on this VM

HEAD `a386121`, copied to `P/leanvm`, builds offline. `LEANVM_NUM_THREADS=16`.

| Independent compressions (`crates/flock/tests/batch_proving_hashes.rs`) | prove (mean of 3) | throughput | proof | verify | RSS |
|---|---|---|---|---|---|
| 2^12 | 5.60 s | 732 /s | 235,552 B | 462 ms | 175 MB |
| 2^14 | 19.50 s | 840 /s | 259,320 B | 495 ms | 687 MB |

Zerocheck is 55–60 % of proving (GF(2^64) multiplication without pclmulqdq). Through the VM
(`rec_aggregation hash_chain::blake2s_hash_chain`, unroll 4): 4096 steps 16.04 s / 255.2 KiB;
16384 steps 40.70 s / 258.5 KiB (its chain is `compress(d, d)` over 4 F64 words, not the
competition's chain format). Witness: `K_LOG = 14`, 16,384 bits per compression (16,000 used),
2 KiB packed.
