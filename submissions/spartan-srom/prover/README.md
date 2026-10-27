# `spartan-srom` native prover

The efficient prover of the entry (blueprint `docs/v4/flock-baseline/BLUEPRINT.md` §7): v3's
`spartan-chain` prover (std Rust, no dependencies) with every Merkle and Fiat–Shamir hash sent to
the v4 oracle service, the verifier's trace written by the prover and signed, and the bundles
(`B`) of §1.4 for inner nodes. The execution-time golf (`stages/F2-golf-RESULT.md`) changed how
the bytes are computed, not the bytes. The runner builds only **`prover.s`**; the Rust sources
beside it are what it is generated from, byte for byte, by `build-asm.sh`.

## Files

| File | What |
|---|---|
| `main.rs` | the modes: `setup`, `tree`, `leaf`, `node` (`harness/PROVER.md`) and the development modes (`verify-native`, `extract-check`, `info`, `prove-leaf`, `check-leaf`, `prove-signed`, `bench-leaf`, `selftest-field`, v3's `dump-*`) |
| `oracle.rs` | the `Oracle` trait; in-process oracles (keyed BLAKE2s-256 = the service's `PRF_k`, and v3's `blake2s256(0x52 ‖ q)`); `Recorder` (counts; for the replay check, the prover's answers by query fingerprint), `Replay` (the verifier against those answers), `Seq` (`runSeq`) |
| `service.rs` | the service client (`service/PROTOCOL.md`): `QUERY` batches on one connection per thread, the sequential Fiat–Shamir queries on their own polled connection, `SIGN` (also split in send / finish, to work while the service signs), `VK`; any refusal aborts with the service's message |
| `format.rs` | `encode`/`decode` of witnesses (`witWords`, `decodeWit`), the signed-proof file (`harness/FORMAT.md`), `traceDigest`, `SigOk` |
| `acc.rs` | the native `acc` with the verifier `V` (branches `L`, `C`, `N`, `B`, blueprint §2): the trace cap `qV = 2^16` of the core's `acc` (`ea2e8ab`) and the clear and bundled leaves' cap `n ≤ 2^12` (D-6) |
| `make.rs` | signed proofs: leaf (prove with the trace, `SIGN`), bundle, plain node (when a child cannot be bundled: a leaf with `n = 0` or `n > 2^12`, or two bundles under different σ0); the stream's node file built in place from its children's files |
| `prover.rs`, `verifier.rs`, `transcript.rs`, `sumcheck.rs`, `chain.rs`, `circuit.rs`, `field.rs`, `mle.rs`, `rs.rs`, `ringswitch.rs`, `blake2s.rs`, `kat.rs` | v3's SNARK with the oracle parameter, batched Merkle levels, keyed BLAKE2s and the run-time `pclmulqdq` dispatch in `field.rs`; the same bytes as v3's, computed faster (stage F2-golf: the sumcheck provers, the bit-sliced witness, the FFT's factors, the trace from the transcript); `circuit.rs` is from leanerVM (Apache-2.0, `../LICENSE-leanerVM`) |
| `par.rs` | a persistent pool of worker threads shared by every parallel call (the tree's leaves are proved at once on it) |
| `build-asm.sh`, `sanitize-asm.py`, `rust-toolchain.toml` | the assembly build (stage F0's recipe) and its pinned toolchain |
| `selftest.py` | end-to-end tests against the real service (`tree`, `stream`, `sizes`, `bench`, `keyed-kat`) |
| `prover.s` | the generated assembly: the submission |

## Rebuilding `prover.s` byte for byte

Toolchain: rustc 1.99.0 (b940084d7 2026-09-28), LLVM 23.1.1, cargo 1.99.0, pinned by
`rust-toolchain.toml` (rustup then refuses another toolchain rather than emitting a different
`.s`; `build-asm.sh` runs cargo from this directory so that the pin applies), and Python 3 for the
filter. The link test uses gcc 15.2.0, GNU as/ld 2.46 and glibc 2.43 (Ubuntu). The build is
offline, with no dependencies.

```sh
./build-asm.sh /some/work/dir      # writes ./prover.s and /some/work/dir/build/prover
sha256sum prover.s                 # see stages/F2-prover-RESULT.md, "Fix pass", for the committed hash
```

It runs `cargo rustc --release --offline --locked` with fat LTO, one codegen unit, `panic=abort`,
`-C target-cpu=x86-64-v2 -C llvm-args=-align-all-functions=4` and path remapping, emits the whole
program as one `.s` (`--emit asm=…`), filters it (`sanitize-asm.py`: drops DWARF directives and
`.debug_*` sections, refuses `.incbin`/`.include`), and links it with the runner's command
`gcc -static -O2 -pthread *.s -o prover -lm`. Two clean builds give the same `prover.s`.

The CPU target is pinned to `x86-64-v2`; the GF(2^64) products use `pclmulqdq` when
`is_x86_feature_detected!` finds it (`SPARTAN_NO_CLMUL=1` forces the portable product), and no
other instruction above the baseline is used. (A binary linked against this VM's static glibc 2.43
needs AVX2 at start-up, from glibc's own `init_cpu_features`; the runner links with its own glibc.)

## Tests

```sh
CARGO_TARGET_DIR=/elsewhere cargo test --release --offline     # unit tests (toy signatures, no service)
# (cargo compiles them with codegen-units = 4 and no LTO: not the submission's binary; the
#  selftests below run the linked prover.s)
python3 -I selftest.py --prover /some/work/dir/build/prover --service PATH/rf-oracle --work DIR \
    [tree stream sizes keyed-kat bench]
```

Environment: `RF_ORACLE` (the service socket, set by the runner), `SPARTAN_THREADS` (threads;
default all CPUs), `SPARTAN_VERBOSE=1` (timings on stderr; `2`: per sumcheck round too),
`SPARTAN_REPLAY=1` (replay the native verifier on every leaf and check the trace the prover wrote),
`SPARTAN_TREE_WIDTH` (leaves of a tree proved at once; default: the threads, within 8 GiB).
An output above a cap that `acc` or the runner checks (`proofCap`, `qV`, `queryCap`, the 64 MiB
file cap) is still written, with a line on stderr saying which cap. The pool keeps at most 32
connections to the service (16 opened before `ready`).
The stream requests (`leaf`, `node`) prepare before `ready`: the circuit, the connections, the
worker threads, and 64 MiB of heap (glibc `mallopt`: freed memory is kept, so the request's
allocations do not fault pages in).
