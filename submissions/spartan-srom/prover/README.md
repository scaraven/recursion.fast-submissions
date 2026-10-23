# `spartan-srom` native prover

The efficient prover of the entry (blueprint `docs/v4/flock-baseline/BLUEPRINT.md` §7): v3's
`spartan-chain` prover (std Rust, no dependencies) with every Merkle and Fiat–Shamir hash sent to
the v4 oracle service, the verifier's trace replayed and signed, and the bundles (`B`) of §1.4 for
inner nodes. The runner builds only **`prover.s`**; the Rust sources beside it are what it is
generated from, byte for byte, by `build-asm.sh`.

## Files

| File | What |
|---|---|
| `main.rs` | the modes: `setup`, `tree`, `leaf`, `node` (`harness/PROVER.md`) and the development modes (`verify-native`, `extract-check`, `info`, `prove-leaf`, `check-leaf`, `prove-signed`, `bench-leaf`, `selftest-field`, v3's `dump-*`) |
| `oracle.rs` | the `Oracle` trait; in-process oracles (keyed BLAKE2s-256 = the service's `PRF_k`, and v3's `blake2s256(0x52 ‖ q)`); `Recorder` (the prover's answers by query fingerprint), `Replay` (the verifier against those answers), `Seq` (`runSeq`) |
| `service.rs` | the service client (`service/PROTOCOL.md`): `QUERY` batches on one connection per thread, `SIGN`, `VK`; any refusal aborts with the service's message |
| `format.rs` | `encode`/`decode` of witnesses (`witWords`, `decodeWit`), the signed-proof file (`harness/FORMAT.md`), `traceDigest`, `SigOk` |
| `acc.rs` | the native `acc` with the verifier `V` (branches `L`, `C`, `N`, `B`, blueprint §2) |
| `make.rs` | signed proofs: leaf (prove, replay, `SIGN`), bundle, plain node |
| `prover.rs`, `verifier.rs`, `transcript.rs`, `sumcheck.rs`, `chain.rs`, `circuit.rs`, `field.rs`, `mle.rs`, `rs.rs`, `ringswitch.rs`, `blake2s.rs`, `par.rs`, `kat.rs` | v3's SNARK, unchanged but for the oracle parameter, batched Merkle levels, keyed BLAKE2s and the run-time `pclmulqdq` dispatch in `field.rs`; `circuit.rs` is from leanerVM (Apache-2.0, `../LICENSE-leanerVM`) |
| `build-asm.sh`, `sanitize-asm.py` | the assembly build (stage F0's recipe) |
| `selftest.py` | end-to-end tests against the real service (`tree`, `stream`, `sizes`, `bench`, `keyed-kat`) |
| `prover.s` | the generated assembly: the submission |

## Rebuilding `prover.s` byte for byte

Toolchain: rustc 1.99.0 (b940084d7 2026-09-28), LLVM 23.1.1, cargo 1.99.0, Python 3 (the filter);
the link test uses gcc 15.2.0, GNU as/ld 2.46, glibc 2.43 (Ubuntu). Offline, no dependencies.

```sh
./build-asm.sh /some/work/dir      # writes ./prover.s and /some/work/dir/build/prover
sha256sum prover.s                 # see stages/F2-prover-RESULT.md for the committed hash
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
python3 -I selftest.py --prover /some/work/dir/build/prover --service PATH/rf-oracle --work DIR \
    [tree stream sizes keyed-kat bench]
```

Environment: `RF_ORACLE` (the service socket, set by the runner), `SPARTAN_THREADS` (threads;
default all CPUs), `SPARTAN_VERBOSE=1` (timings on stderr).
