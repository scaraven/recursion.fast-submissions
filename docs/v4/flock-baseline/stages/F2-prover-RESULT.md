# F2: the native prover of `spartan-srom` — RESULT, 2026-10-22

Status: **built and tested; not committed** (the orchestrator commits). Two checks against F1's
**compiled Lean code** were run with a snapshot of F1's scratch runner `srom-run` (§3.5), taken
before F1 finished:

- F1's Lean prover `P` gives the **same leaf bytes** as this prover at `n = 1` and `n = 16`;
- F1's compiled `acc` **accepts** this prover's service-signed leaf and bundle proofs and rejects
  their canaries.

The harness smoke (`run-benchmark.py` with `smoke.toml`, every part) passed end to end, but with a
**native stand-in badge** (§3.4). The run with the real badge is still open, because the harness
builds that badge (`evaluate.py`) from F1's finished entry.

Logs are under the worktree's `logs/f2/` (gitignored; written `F/` below). `F/run-all.sh` reruns
the final build and every test of §2–§4 in one go (`F/run-all.log`). The journal is
`F2-prover-JOURNAL.md`. The machine is the shared 32-vCPU QEMU VM (AVX2, AVX-512F, **no
pclmulqdq**), with a load average of 8–10 from other agents during every run, so every time below
is a relative indication. Every run used at most 16 threads (`SPARTAN_THREADS=16`; the harness under
`taskset -c 0-15`) and ran under a `timeout`.

## 1. What was built

`submissions/spartan-srom/prover/` (flat): crate `spartan-srom-prover`, `[[bin]] path = "main.rs"`,
no dependencies, `Cargo.lock` committed, 5,683 lines of Rust.

| File | Lines | Origin |
|---|---|---|
| `main.rs` | 772 | new: the modes and 4 end-to-end unit tests (toy signatures) |
| `oracle.rs` | 322 | new: `Oracle` (`ask`, batched `ask_many`), `Local::Keyed`/`Local::V3`, `Recorder`, `Replay`, `Seq` |
| `service.rs` | 264 | new: the service client |
| `format.rs` | 396 | new: `encode`/`decode` (`witWords`/`decodeWit`), the FORMAT.md file, `traceDigest`, `SigOk`, a test-only signer |
| `acc.rs` | 167 | new: the native `acc` and `V` (branches L, C, N, B), `qBound` |
| `make.rs` | 177 | new: signed leaf (prove, replay, SIGN), bundle, plain node |
| `field.rs` | 565 | v3 + run-time `pclmulqdq` dispatch (202 changed lines) |
| `transcript.rs`, `verifier.rs`, `prover.rs`, `blake2s.rs`, `kat.rs` | 156, 165, 229, 237, 287 | v3 with the oracle as a parameter, batched Merkle levels, keyed BLAKE2s; v3's node code removed from `verifier.rs` |
| `chain.rs`, `circuit.rs`, `mle.rs`, `par.rs`, `ringswitch.rs`, `rs.rs`, `sumcheck.rs` | 2,346 | v3, unchanged (0 changed lines) |

`build-asm.sh`, `sanitize-asm.py` (F0's filter, unchanged), `selftest.py` (end-to-end tests),
`README.md` and the generated `prover.s` sit beside them. The leanerVM licence is the entry root's
`LICENSE-leanerVM` (F1 put it there; `circuit.rs` names it).

**Oracle (§7).** Every Merkle and Fiat–Shamir hash goes through `Oracle::ask` and
`Oracle::ask_many`. The Merkle leaves (one query `0x00 ‖ column` per column) form one batch, and
so does each Merkle level. Through the service a batch is split into `QUERY` requests of at most
4,096 queries or 4 MiB, each sent on a connection the worker thread takes from a pool and keeps for
its chunk. At most 60 connections are opened. Start-up opens one per thread, untimed. The
transcript is sequential: each Fiat–Shamir step is one `QUERY` round trip. Every refusal or I/O
error aborts the process (exit 3) with the service's message. The in-process `Local::Keyed(k)` is
keyed BLAKE2s-256 (RFC 7693, the key block compressed once), selected by `--oracle keyed:HEX`
(default: 32 zero bytes). `Local::V3` is v3's `blake2s256(0x52 ‖ q)`.

**Traces.** The prover's oracle is wrapped in a `Recorder`, which keeps a 128-bit fingerprint of
every query with its answer. After proving, v3's native leaf verifier is run against `Replay`.
`Replay` answers each query from that table and records `(q, a)` in order. A query missing from the
table is never sent to the service; it fails the proof. One `SIGN` then carries the recorded
queries, and the service's answers must equal the replayed ones. This comparison also covers a
fingerprint collision: such a collision would abort the proof, never produce a wrong one. A leaf's
trace has exactly `qBound (kap n)` entries (3,533 at `n = 16`). σ0 is one `SIGN` with count 0, made
once per tree and once per stream, at its first node; later nodes take it from the `B` child.

**Bundles (§1.4).** A child of a node gives:

- its statement;
- its clear form: `C = π[..48]` of an `L`, or `encode W` of a `B`, the strict prefix that `decode`
  reads;
- its part of `T`: `π[48..]` of an `L`, `π[|encode W|..]` of a `B`;
- its trace.

The node is `π = encode (.node c₁ c₂ (clear₁, [], σ0) (clear₂, [], σ0)) ‖ T₁ ‖ T₂` with the trace
`tr₁ ‖ tr₂`. It asks no `QUERY` and makes one `SIGN`. In `tree` every inner node and the root is
built this way, level by level, from its two children. The result is identical to the bundle of
the subtree's leaves in §1.4.

**Modes.**

- `setup`: does nothing and exits 0.
- `tree`: reads `leaves.json`, checks `vk.hex` against `VK`, and writes `proofs/L<i>.bin`,
  `proofs/N<l>_<j>.bin` and `root.bin` (for `r = 0`, `root.bin` is `L0`).
- `leaf` and `node`: print `ready` after the circuit is built, the connections are opened and the
  key is checked; then wait for `go`, write `proof.bin`, print `done`.

The development modes are listed in `main.rs` and `README.md`. The main ones:

- `verify-native VK STMT FILE`: the native `acc`. It parses the file strictly, checks the caps,
  checks `SigOk` with the contract's WOTS layout, and runs `runSeq` against `V`.
- `extract-check`: the copy extractor's witness of a file is in `Rel (acc vk)`.
- `prove-leaf`, `check-leaf`, `prove-signed`, `bench-leaf`, `selftest-field`, `info`, and v3's
  `dump-*` known-answer dumps (`--oracle`).

**The native `V` and F1's `V`.** The native `V` is written from blueprint §2. It was then compared,
by reading, with F1's `SpartanSromNode.V`, `clearLeaves`, `bundleOK` and `runBundle`. The two have
the same branch conditions, the same clear-tree conditions, the same static checks and the same
order of the per-leaf statement check and the SNARK run. The order in which the native code makes
the no-query checks differs in places, which changes no decision.

## 2. The assembly

| | |
|---|---|
| Command | `prover/build-asm.sh WORK`: `cargo rustc --release --offline --locked --bin spartan-srom-prover` with `lto="fat"`, `codegen-units=1`, `panic="abort"`, `debug=false`, then `-- --emit asm=WORK/raw.s -C target-cpu=x86-64-v2 -C llvm-args=-align-all-functions=4 --remap-path-prefix …`; `python3 -I sanitize-asm.py raw.s prover.s`; link `gcc -static -O2 -pthread WORK/build/*.s -o WORK/build/prover -lm` |
| Toolchain | rustc 1.99.0 (b940084d7 2026-09-28), LLVM 23.1.1, cargo 1.99.0, Python 3.14.4; gcc 15.2.0 (Ubuntu 15.2.0-16ubuntu1), GNU as/ld 2.46, glibc 2.43 (Ubuntu 2.43-2ubuntu2.4) |
| `prover.s` | **8,699,228 bytes, SHA-256 `1354401796ea99c47f44b6db75bd7199601213fc308b163faf68100e22017ba3`**; 273,664 debug lines dropped by the filter |
| Binary | 2,698,536 bytes, SHA-256 `30b46975f03a97c06b54bac487ea40e6b757c22c3299b3f95a9cd84ef66f6ffc` |
| Times | rustc emit with LTO 58.3 s (cargo "Finished"); `build-asm.sh` wall 61.3 s, 61.8 s, 60.3 s for the three builds; link 1.06 s (`F/build-asm-{a,b,c}.log`) |
| Determinism | three clean builds (two target directories, plus a copy of the crate in another directory): the same `prover.s` and the same binary (`F/determinism.log`) |
| Harness build | `rfh.prover.build` inside its sandbox (through `run-benchmark.py`): the same binary SHA-256 (`F/harness-smoke.log`) |
| Content | no host path (`grep -c /home` = 0); 57 `/rustc/<hash>/library/…` strings (std's panic locations, data); no `.incbin`/`.include`; 13 `pclmulqdq` instructions (`field::hw`); no `ymm`/`zmm` register |

**Run-time dispatch.** `field.rs` checks `is_x86_feature_detected!("pclmulqdq")` and `sse4.1`
once, and caches the answer in an atomic. `K × K`, `E × E` and `E × K` products then call
`#[target_feature(enable = "pclmulqdq,sse4.1")]` functions that each do a whole product, so the
dispatch costs one call per product. `SPARTAN_NO_CLMUL=1` forces the portable path. AVX2 is not
used. The tests:

- the unit test `clmul_dispatch_matches_portable` compares both paths when the CPU has the
  instruction; this VM has none, so here it skips;
- `prover selftest-field` compares both paths on 50,000 random and 16 edge inputs. Run with the
  linked binary under `qemu-x86_64` TCG with `-cpu Haswell` and `-cpu max`, the products are equal;
- with v3's oracle, the leaf proofs at `n = 1, 16, 64` equal v3's under `-cpu Haswell` (the
  pclmulqdq path), `-cpu Haswell,pclmulqdq=off` (the portable path) and `-cpu max`
  (`F/qemu-asm.log`);
- native runs on this VM take the portable path.

**Toolchain finding.** A static binary linked against this VM's glibc 2.43 needs AVX2 at start-up:
glibc's own `init_cpu_features` executes `vmovd`. Even a static C hello-world raises SIGILL under
`qemu -cpu Nehalem`, `Westmere` or `SandyBridge`, and runs under `Haswell`. So the `x86-64-v2` pin
could not be tested on a pre-AVX2 CPU. The runner links with its own glibc (Ubuntu 24.04), so this
does not affect the entry.

## 3. Tests (all with the linked assembly binary `F/prover-asm`, SHA-256 `30b46975…`)

### 3.1 (a) Leaf SNARK bytes against v3's cargo-built prover, v3's oracle (`F/kat-asm.log`)

The v3 prover was built with cargo from `spartan-chain` at the submissions repository's `main`
(`F/v3-target`, `F/v3-build.log`).

- `prove-leaf` at `n = 1, 16, 64` (`--oracle v3`): identical bytes (95,719, 143,711 and 193,467) and
  identical statements.
- v3's `dump-proof` (`n = 1, 2, 16, 64`): identical.
- `dump-field`, `-circuit`, `-walk`, `-encode`, `-transcript`, `-mle`, `-transcript-ops`, `-phi`,
  `-sumcheck` and `-leaf-trace`: identical.

F1's KAT oracle `katOracle q = BLAKE2s-256(0x52 ‖ q)` is `--oracle v3`, so these dumps are the ones
to compare with F1's Lean `P` once it runs.

### 3.2 (b) Against the real service (`rf-oracle`, copied to `F/rf-oracle`, SHA-256 `d6003237…`)

Results are in `F/selftest-asm.log`; the driver is `prover/selftest.py`.

- **Smoke tree `r = 2, n = 16`.** The driver writes `leaves.json` and `vk.hex` and runs
  `prover tree` (0.89 s). The 4 `L`, 2 `N1_j` and the `root.bin` are all accepted by
  `verify-native` against statements recomputed in Python. The runner's canaries
  (`rfh/checks.py`) of every output are rejected: file ±1 byte, π ±1 byte, statement bit,
  swapped sibling, trace answer changed (first entry and middle entry), extra trace entry, OTS
  value, signature index. That is 11 canaries for each of the 6 non-root outputs and 10 for the
  root.
- **Stream, `M = 4`.** The handshake is driven as `rfh/prover.py` `request` does it: start the
  process, wait for `ready`, write the inputs atomically, send `go`, wait for `done`. All 5 `leaf`
  and 4 `node` outputs are accepted, and the canaries of leaf 0 and node 1 are rejected.
- **`keyed-kat`.** With a service started with `--insecure-test-keys K SEED`, `--oracle service` and
  `--oracle keyed:K` give identical proofs at `n = 1, 16, 64`: the in-process oracle is the
  service's `PRF_k`.
- **`n = 0`.** Tree and stream (`F/selftest-asm-n0.log`): 80-byte leaves, plain `N` nodes, all
  accepted, canaries rejected.
- **Unit tests** (cargo, `F/cargo-test.log`): 27 pass. They cover keyed-BLAKE2s vectors (checked
  with `hashlib`), the encode/decode round trip, the strict file format, the toy signer against
  `SigOk`, `qBound` equal to F0's query counts and to v3's `7 774` at κ = 20, leaf canaries (also a
  changed answer that is re-signed), bundles `r = 2, n = 16` with swapped children and a foreign
  σ0, the plain node above `proofCap` at `n = 16`, and the plain node at `n = 1`.

### 3.3 (c) Sizes (bytes; `F/selftest-asm.log`)

| Proof | kind | π | trace entries | Σ\|q\| | trace in file (8 + Σ(8+\|q\|+32)) | file |
|---|---|---|---|---|---|---|
| leaf `n = 16` | L | 143,711 | 3,533 | 248,875 | 390,203 | 538,698 |
| `N1_j` (2 leaves) | B | 297,078 | 7,066 | 497,750 | 780,398 | 1,082,260 |
| root `r = 2` (4 leaves) | B | 603,812 | 14,132 | 995,500 | 1,560,788 | 2,169,384 |
| stream node 2 (3 leaves) | B | 450,445 | 10,599 | 746,625 | 1,170,593 | 1,625,822 |
| stream node 4 (5 leaves) | B | 757,179 | 17,665 | 1,244,375 | 1,950,983 | 2,712,946 |
| leaf `n = 1024` | L | 457,843 | 4,414 | 591,318 | 767,886 | 1,230,513 |
| leaf `n = 4096` | L | 796,111 | 4,753 | 940,519 | 1,130,647 | 1,931,542 |
| leaf `n = 16384` (above `proofCap`) | L | 1,464,107 | 5,156 | 1,621,560 | — | 3,296,699 |
| leaf `n = 65536` (above `proofCap`) | L | 2,791,559 | 5,687 | 2,966,281 | — | 5,990,112 |
| leaf/node `n = 0` | L / N | 80 / 9,816 (2 leaves) | 0 | 0 | 8 | 4,872 / 14,608 |

Each extra leaf in a bundle adds 153,367 bytes to π at `n = 16`: 143,663 of `T` and 9,704 of `W`.
**Stream links that fit `proofCap`**, measured with `selftest.py stream` and `verify-native`
(`F/links-n{16,1024,4096}.log`):

| `n_f` | links accepted | first rejection |
|---|---|---|
| 16 | 5 | link 6: `|π| = 1063913 > proofCap` |
| 1,024 | 1 | link 2: `1392841 > proofCap` |
| 4,096 | 0 | link 1: `1601878 > proofCap` |
| ≥ 16,384 | 0 | the leaf itself is above `proofCap` |

In the tree at `n = 16`, `r = 2` fits; the level-3 root would hold 8 leaves, more than 1 MiB.

### 3.4 (d) The harness smoke (`F/harness-smoke.{log,json}`)

`taskset -c 0-15 python3 -I -B harness/run-benchmark.py --season harness/smoke.toml --entry
submissions/spartan-srom --badge F/badge-native --service F/rf-oracle --bench F/rf-bench …`, all
parts: **`benchmark: pass`**.

- The prover is built in the sandbox, with the same binary hash.
- `setup`: 0.08 s.
- Tree: T = 0.917 s, root and 6 samples accepted, 69 canaries rejected.
- DoS column: 64 inputs rejected.
- Stream `M = 4`: leaf requests 0.214–0.238 s, merges 0.019, 0.026, 0.042 and 0.055 s; 18 canaries
  rejected. The harness reports `t_leaf` = 0.280, `t_merge` = 0.036, `t_link` = 0.316.
- Liveness: ok.
- Provisional `S` = 7.23.

**The badge is a native stand-in, not the Lean `acc`.** It has three parts:

- `verify` runs `prover verify-native` once per line;
- `liveness` runs `prover extract-check`. The entry's extractor is the copy extractor, which ignores
  the log;
- `chaincheck` is 15 lines of Python with `hashlib`.

The run therefore exercises the runner, the sandbox, the service, the build, the handshake and the
canaries with this prover, but **not** F1's verifier. That run is still to do, once F1's
`Run`/badge exists. When it is done, also check that the compiled `acc` accepts the outputs and
compare the KAT with F1's Lean `P` (§3.1).

### 3.5 Against F1's compiled Lean code (snapshot `F/lean-badge/srom-run`)

The snapshot is F1's scratch runner (`logs/lean/core/.lake/build/bin/srom-run`, built 19:28, its
`.hash` `dd75522ac8cced7e`; copy SHA-256 `0fac852b…`, source `F/lean-badge/SromRun.lean`). It is
not the harness badge.

**F1's Lean `P` against this prover** (`srom-run prove-leaf-kat`, under `katOracle` =
`BLAKE2s(0x52 ‖ q)`, against `prover prove-leaf --oracle v3`; `F/lean-kat/run.log`):

| n | result | Lean `P` time |
|---|---|---|
| 1 | identical, 95,719 bytes | 15.6 s |
| 16 | identical, 143,711 bytes | 37.0 s |

This is blueprint §7's known-answer test.

**F1's compiled `acc`** (`srom-run verify VK STMT FILE` = `Submission.acc SpartanSrom.submission`)
on this prover's outputs, all signed by the real service (`F/lean-check/*.out`):

| File | verdict | `acc` | process wall |
|---|---|---|---|
| tree `L0.bin` (538,698 B) | accept | 0.217 s | 87.8 s |
| tree `N1_0.bin`, bundle of 2 leaves (1,082,260 B) | accept | 0.575 s | 579 s |
| `L0.bin` canary `pi+1` | reject (`V = none`) | 0.005 s | 88.6 s |
| ROOT_RESULT |
| STREAM_RESULT |
| CANARY_RESULT |

**What the wall times mean.** Almost all of the process wall time is outside `acc`; it is spent
before `acc` runs, presumably in the runner's parsing of the file (`parseSigned`). It grows faster
than the file: 87.8 s for 538 KB, 579 s for 1.08 MB. The harness counts the parse in the badge's
time (`rfh/checks.py`: "NS the nanoseconds of parsing the file's bytes and evaluating `acc`") and
caps one check at `verify_s = 60 s`. A badge with this parse would therefore fail every proof of
this entry, including the smallest leaf. This is reported to F1 and the orchestrator; it is not a
property of the proofs.

## 4. Measurements (blueprint §8)

**Setup.** `selftest.py bench` runs `prover bench-leaf N REPS` with the in-process keyed oracle,
then through a fresh service. Each run uses 16 threads, takes the median over its repetitions, and
records the peak RSS from `/usr/bin/time -v` (`F/bench-asm-n{16,1024,4096,16384,65536}.log`).

**What each timing measures.**

- *prove*: proving with every hash through the oracle.
- *replay*: running the native verifier against the answer table.
- *SIGN*: the round trip, with the service re-hashing the trace.
- *oracle*: the wall time inside oracle calls, that is the Fiat–Shamir round trips plus the Merkle
  batches including the building of the column queries, as a share of *prove*.

| n | oracle | reps | prove s | replay s | SIGN s | leaf total s | oracle s (share) | of which FS s | peak RSS |
|---|---|---|---|---|---|---|---|---|---|
| 16 | keyed | 5 | 0.137 | 0.044 | — | 0.185 | 0.007 (4.7 %) | 0.0003 | 9.2 MB |
| 16 | service | 5 | 0.142 | 0.046 | 0.004 | 0.193 | 0.014 (10.0 %) | 0.0087 | 9.4 MB |
| 1,024 | keyed | 3 | 0.897 | 0.222 | — | 1.117 | 0.024 (2.8 %) | 0.0010 | 265 MB |
| 1,024 | service | 3 | 0.879 | 0.225 | 0.013 | 1.122 | 0.034 (3.9 %) | 0.0147 | 267 MB |
| 4,096 | keyed | 3 | 2.975 | 0.441 | — | 3.463 | 0.071 (2.4 %) | 0.0018 | 1.02 GB |
| 4,096 | service | 3 | 3.114 | 0.441 | 0.011 | 3.554 | 0.074 (2.4 %) | 0.0179 | 1.03 GB |
| 16,384 | keyed | 2 | 12.245 | 0.866 | — | 13.113 | 0.228 (2.0 %) | 0.0076 | 3.97 GB |
| 16,384 | service | 2 | 11.944 | 0.901 | 0.023 | 12.876 | 0.191 (1.6 %) | 0.0280 | 4.03 GB |
| 65,536 | keyed | 1 | 47.110 | 1.727 | — | 48.840 | 0.778 (1.7 %) | 0.0107 | 15.79 GB |
| 65,536 | service | 1 | 46.575 | 1.944 | 0.033 | 48.555 | 0.653 (1.4 %) | 0.0584 | 15.85 GB |

**Service traffic per leaf proof** (the service's `stats` line divided by the repetitions;
prover `QUERY`s plus the one `SIGN`):

| n | requests | queries | query bytes |
|---|---|---|---|
| 16 | 193 | 11,877 | 808,515 |
| 1,024 | 454 | 70,203 | 19,677,861 |
| 4,096 | 597 | 136,157 | 72,655,563 |
| 16,384 | 868 | 267,775 | 279,255,921 |
| 65,536 | 1,395 | 530,721 | 1,095,091,479 |

At `n = 65536` the Merkle batches pushed 525,034 queries (1.09 GB) through the service in 0.594 s
of wall time on 16 connections, about 1.8 GB/s. Each Fiat–Shamir round trip costs about 57–78 µs
here (153 steps in 8.7 ms at `n = 16`, 747 in 58 ms at `n = 65536`). The harness's calibration
measured the service at 4.87 M calls/s on 1 thread and 74.8 M calls/s on 32 threads, with 1,024
queries of 64 bytes per request (`F/harness-smoke.json`).

**Findings.**

- Going through the service costs no measurable prover time at any `n`; the differences are within
  the noise of this VM.
- The oracle is 1.4–10 % of proving, most at `n = 16`, where the 153 sequential Fiat–Shamir round
  trips dominate it.
- Proving itself is v3's sumchecks: the outer sumcheck is 55–60 % of proving at large `n`.
- The replay, the native verifier run, adds 4–24 % to a leaf request.
- At `n_f = 65536` a leaf needs 15.8 GB, above the season's 11 GiB prover cap, so a stream at
  `n_f = 2^16` would be stopped by memory before `proofCap`.

**A merge (`node`) request** in the stream at `n = 16` (`F/selftest-asm.log`, `SPARTAN_VERBOSE`
lines; the wall time is from `go` to `done`):

| node (leaves) | wall | read+parse the 2 files | build π and trace | SIGN | write file |
|---|---|---|---|---|---|
| 1 (2) | 0.019 s | 0.003 | 0.003 (incl. `SIGN []` 0.0003) | 0.011 (7,066 queries, 498 KB) | 0.003 |
| 2 (3) | 0.028 s | 0.005 | 0.004 | 0.016 (10,599, 747 KB) | 0.004 |
| 3 (4) | 0.032 s | 0.006 | 0.005 | 0.015 (14,132, 996 KB) | 0.005 |
| 4 (5) | 0.042 s | 0.008 | 0.007 | 0.021 (17,665, 1.24 MB) | 0.006 |

A merge asks no `QUERY`. Its cost grows linearly in the bundled leaves: the `SIGN` re-hashes the
whole concatenated trace (C-m4), and the running proof's file grows by 543 KB per link. The harness
measured merges of 0.019–0.055 s.

## 5. Deviations from the blueprint

1. **`n = 0`.** A bundle needs every bundled leaf to have `n ≥ 1` (§1.4), so with `n = 0`, and
   whenever a child cannot be bundled, the node is the plain node `N` of the two signed children
   (§1.3), with an empty trace and one `SIGN []`. §7 says nothing about this case; such a node is
   accepted (§3.2).
2. **Two `B` children with different σ0** (not produced by this prover, nor by the runner's stream)
   also fall back to `N`.
3. **The answer table** keeps 128-bit fingerprints of the queries rather than the queries. The
   replay never sends a query; the `SIGN` comparison guards against collisions (§1).
4. **Leaves in `tree` are proved one after another**, each with all threads. At `n = 16` that is
   0.15–0.2 s per leaf at low parallel efficiency; proving them concurrently would shorten
   `T_tree` at small `n` only.
5. **The KAT against the Lean `P`** (§7, last bullet) was run at `n = 1` and `n = 16` only (§3.5),
   with an unfinished snapshot of F1's runner; Lean's `P` takes 37 s at `n = 16`. The comparison
   with v3's cargo-built prover covers `n = 1, 2, 16, 64` (§3.1).
6. `setup` does nothing: building the circuit takes milliseconds, and it happens before `ready`.

## 6. Friction with the v4 interfaces (evidence for the rules' feedback)

1. **The trace restates the opened columns.** A leaf's file is 3.7× its π at `n = 16` (538,698 vs
   143,711) and 2.1× at `n = 65536`. A bundle's file grows by 543 KB per leaf at `n = 16`, the
   stream node 4 file is 2.7 MB, and the node request reads and parses it inside the timed merge
   (0.008 s at 5 leaves).
2. **`proofCap` bounds the recursion.** Bundles carry the leaves' SNARKs, so the stream completes 5
   links at `n_f = 16`, 1 at `1024`, 0 at `4096`, and none at `n_f ≥ 16384`, where the leaf itself
   is too large. The exact `verify-native` messages are in §3.3; the harness's own message on this
   failure is still to be recorded with the real badge. At the season shape the T run fails at the
   first leaf: π at `n = 2^18` is above `proofCap`, and the memory, extrapolated from 15.8 GB at
   `2^16`, is far above 11 GiB. The stream at `n_f = 2^16` is stopped by memory (§4).
3. **`SIGN` re-hashes the whole trace** (C-m4). A merge's cost is dominated by it (§4), and it grows
   with the bundle.
4. **The Unix socket path limit.** Rust's `UnixStream::connect` fails on a path of 108 bytes or more
   with `path must be shorter than SUN_LEN`; this was hit with a 109-byte test path under `logs/f2/`.
   The runner's `/run/rf/oracle.sock` is short, but local tests with deep directories fail. The
   client now connects through `/proc/self/fd/<dir fd>/<name>` when the path has 100 bytes or more.
   PROTOCOL.md could say that `RF_ORACLE` is always short, or recommend this trick.
5. **`run-benchmark.py`'s `T_tree` has a 50 ms resolution.** `Run.tree` times the prover with
   `subprocess.Popen.wait(timeout=…)`, which polls with sleeps of up to 50 ms. Three runs measured
   0.917036, 0.917041 and 0.917063 s for a prover that takes 0.83–0.89 s outside the sandbox.
   Python 3.14.4 on this VM shows the same: `Popen(["sleep", "0.83"]).wait(timeout=100)` returns
   after 0.869 s, and `wait()` after 0.838 s. The stream requests use `select` and are not
   affected.
6. **`t_leaf` counts `M + 1` leaves over `M` links.** `bench.py` computes
   `t_leaf = sum(leaf_s) / M` with `len(leaf_s) = M + 1`, so `t_leaf` reads 0.280 s where the mean
   leaf request is 0.224 s.
7. **The calibration ignores the CPU affinity.** It uses `os.cpu_count()` (32) threads even when the
   runner runs under `taskset -c 0-15`; the result labels it `threads_32`.
8. **Stage B's mock badge is not self-contained.** `tests/harness/mock_badge/mock_acc.py` imports
   `wots_ref` from `tests/service/`, so a copied mock `chaincheck` fails in the badge sandbox with
   `ModuleNotFoundError: No module named 'wots_ref'`. The stand-in here uses its own `hashlib`
   chain checker.
9. **Static glibc 2.43 on this VM needs AVX2** (§2). This does not affect the runner, but a binary
   linked here cannot run on pre-AVX2 CPUs.

## 7. Open problems

- Run the smoke through `run-benchmark.py` with the real badge built from F1's entry (`verify`,
  `liveness`), and record the harness's own messages for the `proofCap` failures of §3.3.
- The superlinear file parse of F1's runner (§3.5) must not reach the badge: `verify_s = 60 s`
  includes the parse.
- The memory at `n ≥ 2^16`: v3's prover keeps 15.8 GB at `2^16`, above the season's 11 GiB. The
  stream at the season's `n_f` needs a leaf prover with less memory before anything else matters,
  and `proofCap` stops it anyway.
- Optional speed-ups that were not made: proving tree leaves concurrently at small `n`, a lighter
  replay (only the transcript and the openings), and using `pclmulqdq` for the Merkle hashing as
  well.
