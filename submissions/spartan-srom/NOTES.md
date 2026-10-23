# `spartan-srom`: notes for the next solver

This is the entry's journal (`AGENTS.md` §8). It is untrusted text, published whatever the verdict,
and written for whoever builds the next v4 entry. It says what was tried, what it cost, what
stopped it, and what we would do next. The entry itself is described in `README.md`. Its records,
which hold the full evidence, are under `docs/v4/flock-baseline/` (repository root), and the report
to the rules' authors is `docs/v4/FLOCK-BASELINE-FEEDBACK.md`.

Dated 2026-10-23. Evidence is tagged as in the core:

- **kernel**: a kernel-checked theorem;
- **measured**: a number with its log;
- **estimate**: arithmetic on measured or published inputs;
- **paper**: an argument.

Logs are under `logs/` at the repository root (gitignored, kept on the development VM). Every
measurement is from that VM: 32 vCPU under QEMU, AVX2 and AVX-512F, **no `pclmulqdq`**, shared with
other agents, so read times as relative. Stage records are cited as F0 … F3:
`docs/v4/flock-baseline/stages/F<n>-…-RESULT.md`.

## 0. In short

- **The idea.** Port v3's certified Spartan+Ligero leaf SNARK to v4, because it is the only route
  that is certified and exercises the ranked path end to end. Since a plain v4 node cannot hold two
  signed SNARK leaves within `proofCap`, make every node a **σ0-bundle**: the subtree as a clear
  witness signed once on the empty trace, followed by the leaves' SNARKs.
- **The result.**
  - The Lean is certified for every key: ε = 2^-129, δ = 0, qV = 2^16.
  - The harness ACCEPTed the entry at the smoke shape (F3, core `a874f87`).
  - It is ACCEPTed only where `2^r · n ≤ 4,096` chain steps; the season needs `2^24`.
  - `T_V` is unmeetable at every shape it runs.
  - The season shape REJECTs it: the tree on `queryCap`, the stream on memory (the pre-golf
    prover). `proofCap` would stop both anyway.
- **The lesson.** Under v4 a non-recursive entry cannot run the season shape: the next entry must
  recurse, and its leaf needs a polylogarithmic commitment. §7 says what such a node must verify.

## 1. The idea and the route

The route analysis is `docs/v4/flock-baseline/reviews/F0-route-ideation.md`, and the decisions
taken from it are BLUEPRINT D-1 … D-6. Three routes were weighed.

- **(a) Flock's own protocol with a new Lean verifier.** It needs a zerocheck with univariate
  skip, a lincheck through the circuit walk, pinned challenges, skipping `c`, the shift argument,
  and the PCS's soundness in Lean: Ligerito or WHIR, with an MCA theorem for RS codes and OOD
  binding. The ideation put that at about 25–40k Lean lines, research-scale (**estimate**,
  F0-ideation Q1). As published, Flock also works over GF(2^128), whose sumcheck rounds cannot meet
  `errorCap = 2^-128` per fresh query: a degree-2 round errs with `2/2^128 = 2^-127`, the
  univariate-skip round with `126/2^128 ≈ 2^-121` (**estimate**, Q4). A certified Flock needs
  GF(2^192), or grinding (FB-9).
- **(b) Port `spartan-chain`** (v3's honest entry: Spartan R1CS sumchecks over GF(2^64)/GF(2^192),
  ring switching, Ligero with unique-decoding proximity; 61 modules, 16,766 code lines,
  knowledge-sound against the v3 contract in the kernel). Its pins are v4's (Lean and Mathlib
  v4.34.1, CompPoly `572f997`), so most of it carries over. **Chosen (D-1)**, because:
  - it is the only route that is **certified**, so it exercises the ranked path end to end
    (C-m10);
  - the ideation expected about 13–14k of its 16.8k lines to carry over (**estimate**); in the
    event 15,209 lines in 47 modules did, unchanged (§3.1);
  - its native prover is dependency-free std Rust, and F0 found a way to emit std Rust as one
    `.s` (D-4, §3.2).
- **(c) Route (b), plus leanVM's BLAKE2s Flock as a PROVISIONAL prover-only study.** Not done: it
  was to follow only if budget remained, and it did not.

The ideation also predicted, before any code, what would stop route (b): smoke only, because
Ligero's `√`-size proofs cross `proofCap` near `n = 2^12`. That is what F3 measured.

## 2. The node: why plain witness-sending fails, and the σ0-bundle

**A signed child restates every byte its verifier hashed.** Under v4 a node's witness holds each
child as a signed proof `(π, tr, σ)`. The trace `tr` holds every oracle query with its answer, and
this leaf's verifier hashes whole prover messages (the Ligero rows `ū` and `v`), whole Merkle
columns (`0x00 ‖ column`) and every Merkle node preimage. So (**measured**, F0 §2, F2 §3.3, F1 §5):

- an `n = 16` leaf has a `π` of 143,711 B; its trace has 3,533 entries and 390,203 B; its signed
  file is 538,698 B, **3.7× `π`** (2.1× at `n = 2^16`);
- the library's plain node of two such leaves is **1,089,384 B, above `proofCap` = 1,048,576**. It
  dies at the first node of the smoke tree.

Only query-free children (clear leaves, the toy entry) survive plain witness-sending.

**The σ0-bundle** (D-2; format `B`, BLUEPRINT §1.4).

- `π = encode W ‖ T`. `W` is a clear tree: every slot has an **empty trace** and the same
  signature σ0, one `SIGN` of the empty trace (count 0 is allowed; 0.3 ms). `T` is the leaves'
  `h_j ‖ π_S,j`, left to right.
- `V` checks, with no query: the clear tree, `SigOk vk (traceDigest []) σ0` once, `|T|` exactly,
  `1 ≤ n_j ≤ 2^12` (D-6), `Σ qBound ≤ 2^16` (a static bound, since `KS` bounds queries on every
  input), and `c = nodeStmt c₁ c₂`. Then it runs each leaf's SNARK with fresh queries. The node's
  trace is the leaves' traces, concatenated.
- **Why it is sound** (**kernel**, F1 §3; the F1 review §3.2 found no gap). The extractor is the
  library's copy extractor, unchanged, because `decodeWit` ignores trailing words: a bundle extracts
  to `W`. `final` holds because v3's potential already covers every chain in the log: under
  `μ L < 1`, each accepted SNARK run gives `chainEnd s_j n_j = h_j`, and then every clear slot of
  `W` is accepted by `acc` (strong induction on the slot's size: no query, empty trace, the checked
  σ0). A bundle of `k` SNARKs costs no extra error.
- **Why C-m1 does not bite.** C-m1 says a certified `V` cannot trust a signature. Here σ0 is checked
  only to make the extracted `W` a member of `Rel`. It holds for every key the adversary picks, and
  it never substitutes for a witness.
- **The Lean `P` cannot sign**, so its node proofs are plain (`N`, D-5). Completeness is about `V`,
  not `acc`, so those over-cap proofs still count. Only the native prover makes bundles.
- **What a bundle costs.** It grows by 153,367 B per leaf at `n = 16`: 143,663 B of SNARK and
  9,704 B of `W`, of which 9,552 B are two copies of σ0. `decodeWit` reads a full signature
  (597 words, 4,776 B) in every slot (F2 §3.3).

## 3. What was built

### 3.1 The Lean (stage F1)

Measured at F1 with v3's `scripts/loc.py` rule (code lines are neither blank nor comment;
`logs/lean/loc/`):

| | modules | code lines |
|---|---|---|
| v3 `spartan-chain` | 61 | 16,766 |
| v4 `spartan-srom` | 65 | 17,252 (24,037 lines in all) |
| carried unchanged after the rename | 47 whole modules | 15,209 (16,056 with the unchanged lines of ported modules) |
| changed or added inside 13 ported modules | | 310 |
| new: `Node` 288, `NodeControls` 431, `Queries` 62, `SnarkQueries` 88, `Solution` 17 | 5 | 886 |
| v3 lines dropped (`Decode` 227, `VerifierTop` 255, `Submission` 84, `Solution` 23, others 121) | | 710 |

- The 47 unchanged modules are the field, the BLAKE2s circuit and R1CS, MLE, sumcheck, RS,
  proximity, ring switching, the transcript and Merkle tree, Ligero, Spartan, the PCS bounds, the
  chain R1CS and every soundness module up to `SoundnessKS`.
- The new work is the v4 verifier with its four branches (`Node`), the path-uniform query bound
  `OProg.AtMost` (`Queries`, `SnarkQueries`), and the format controls.
- A clean build takes 2 min 38 s on 8 cores, peak RSS 4.12 GB (`logs/lean/build-full-3.log`).
- **The F1 golf** (`F1-golf-RESULT.md`; delivered as `logs/golf-lean/golf.patch`, merged in the fix
  pass) speeds up the compiled verifier without changing a statement:
  - `F.mul` is now Karatsuba over 32-bit halves through `clmul32`: 25 ns against 85 ns per product,
    with 343 more proof lines in `FieldBaseCorrect`;
  - `decodeFront` decodes a node from a prefix, so that a bundle no longer packs `T`;
  - `bundleProg` is `@[inline]`.

<!-- TODO(orchestrator): the F1 fix pass (review F1-M1 … F1-m6, D-6, ea2e8ab's acc conjunct and wordBytes, the golf merged, the byte-level node reader `SpartanSromNodeBytes`): module count and line counts after it; the Lean golf and D-6 badge timings; the re-run of the F1-M2 attack; the build at the final pin 81e1ebf (time, peak RSS, log) -->

### 3.2 The native prover (stage F2, its golf and its fix pass)

- **The source.** std Rust, no dependencies: v3's prover with every Merkle and Fiat–Shamir hash sent
  to the service, a recorded and signed trace, and the bundles. At F2 it was 5,683 lines of Rust.
  After the golf and the fix pass it is 6,775 (`wc -l prover/*.rs`, 2026-10-23), plus
  `selftest.py` (435 lines), `build-asm.sh` (47) and `sanitize-asm.py` (58).
- **The assembly recipe** (F0 §1; `prover/build-asm.sh`; `AGENTS.md` §4.5):
  - `cargo rustc --release` with fat LTO, one codegen unit and `panic=abort`, then
    `--emit asm -C target-cpu=x86-64-v2 -C llvm-args=-align-all-functions=4` with the paths
    remapped;
  - `sanitize-asm.py`, which drops LLVM 23's DWARF-5 `.file N` lines and `.debug_*` sections, which
    GNU `as` rejects, and refuses `.incbin` and `.include`;
  - the runner's `gcc -static -O2 -pthread *.s -o prover -lm`.
- **The pieces that matter.** CPU dispatch happens at run time: `pclmulqdq` through
  `is_x86_feature_detected!`, whole products under `#[target_feature]`, validated under QEMU only.
  The prover writes the verifier's trace itself; since the golf it no longer replays the verifier,
  and `SPARTAN_REPLAY=1` checks the trace. The tree's leaves are proved at once on a persistent
  thread pool, and a node request is built from its children's files in place while the service
  signs.
- **The submitted file** (F2 RESULT, fix pass). `prover.s` is 9,238,056 B, SHA-256 `7a30e654…`. The
  binary is 2,818,664 B, SHA-256 `fecda6a0…`. Three clean builds were identical; `build-asm.sh`
  took 57.8–65.3 s (`logs/f2/fix/build-{a,b,c}.log`, `determinism.log`). `cargo test`: 32 pass.

## 4. Measurements

### 4.1 Probes (F0; `logs/probes/`)

**v3's leaf prover, instrumented** (`logs/probes/sc-runs/n<N>.log`, 16 threads). The "v4 trace" is
`Σ (8 + |q| + 32)` over the verifier's queries:

| `n` | `π` (B) | prove | peak RSS | `V` queries | v4 trace (B) |
|---|---|---|---|---|---|
| 16 | 143,711 | 0.16 s | 8 MB | 3,533 | 390,195 |
| 1,024 | 457,843 | 0.92 s | 255 MB | 4,414 | 767,878 |
| 4,096 | 796,111 | 3.40 s | 995 MB | 4,753 | 1,130,639 |
| 16,384 | 1,464,107 | 11.24 s | 3.95 GB | 5,156 | 1,827,800 |
| 65,536 | 2,791,559 | 45.43 s | 15.8 GB | 5,687 | 3,193,761 |

**The neighbours, on this VM** (F0 §3–§4):

- Flock (BLAKE3; `logs/probes/flock-bench-2e1{4,6}.log`): at `2^14` compressions, 5.36 s,
  283,104 B, verify 53.9 ms, 1.44 GB; at `2^16`, 13.94 s, 416,368 B, 63.9 ms, 3.64 GB. That is
  about 100–135× below Flock's published figures, without VPCLMULQDQ.
- leanVM's BLAKE2s Flock (WHIR; `logs/probes/leanvm-flock-batch-2e1{2,4}.log`): at `2^12`
  compressions, 5.60 s, 235,552 B, verify 462 ms; at `2^14`, 19.50 s, 259,320 B, verify 495 ms,
  687 MB.

### 4.2 The leaf prover (F2 and its golf)

Interleaved runs of the base binary and the golfed binary, in-process keyed oracle, 16 threads
(F2 golf §4.2–§4.3; `logs/golf/ab/final-n{16,1024,4096,16384}-t16.log`; `logs/golf/ref-65536.log`,
`final-65536.log`). Every output was byte-identical between the two (F2 golf §3):

| `n` | base total | golfed total | × | base peak RSS | golfed peak RSS |
|---|---|---|---|---|---|
| 16 | 0.1760 s | **0.0390 s** | 4.5 | 8.9 MB | 67 MB (64 MiB premapped heap) |
| 1,024 | 1.068 s | **0.292 s** | 3.7 | 265 MB | 67 MB (premapped) |
| 4,096 | 3.480 s | **0.980 s** | 3.6 | 1,008 MB | 181 MB |
| 16,384 | 13.678 s | **5.343 s** | 2.6 | 3,961 MB | 656 MB |
| 65,536 (single runs, `prove-leaf`) | 41.16 s | **16.49 s** | 2.5 | 15,765,352 kB | **2,585,312 kB (2.47 GiB)** |

- **Where the time went**, and what the golf changed (F2 golf §2):
  - the outer sumcheck was 55–60 % of proving: `h(1)` is now taken from the claim, round 0 is a
    zerocheck round, tables are made after round 6, and the lookup rounds are bucketed;
  - the inner sumcheck now sums over the blocks first (Flock §4.1, prover-only);
  - the witness is bit-sliced, and the FFT's factors are computed once per leaf.
- **Memory.** The `2^16` leaf fell from about 15 GiB to 2.47 GiB because the outer sumcheck's tables
  are made late (`LATE = 7`) and the bit tables are freed early. At `2^18` it is about 10 GB
  (**estimate**, F2 golf §6).
- **What remains in an `n = 16` leaf** (`logs/golf/st-final-verbose.log`): proving takes 49–56 ms,
  including 153 sequential Fiat–Shamir round trips (5.1–7.2 ms), then the `SIGN` takes 4–9 ms.

### 4.3 The service and the merges

**Through the service** (F2 §4; `logs/f2/bench-asm-n{16,1024,4096,16384,65536}.log`; pre-golf
prover, 16 threads):

- **The tax.** The oracle was 1.4–10 % of proving, most at `n = 16`, where the sequential
  Fiat–Shamir round trips (57–78 µs each) dominate it. The service itself, against in-process
  hashing, added about 4 % at `n = 16` and was within the noise from `n = 1,024` up.
- **Traffic per leaf proof:**

  | `n` | requests | queries | query bytes |
  |---|---|---|---|
  | 16 | 193 | 11,877 | 808,515 |
  | 1,024 | 454 | 70,203 | 19,677,861 |
  | 4,096 | 597 | 136,157 | 72,655,563 |
  | 16,384 | 868 | 267,775 | 279,255,921 |
  | 65,536 | 1,395 | 530,721 | 1,095,091,479 |

- **Merkle throughput.** At `n = 2^16` the Merkle batches pushed 525,034 queries (1.09 GB) in
  0.594 s on 16 connections, about 1.8 GB/s.
- **Merges** at `n = 16`: a merge asks no `QUERY`; it concatenates and makes one `SIGN`, which
  re-hashes the whole trace.
  - Before the golf (`logs/f2/selftest-asm.log`): 0.019, 0.028, 0.032 and 0.042 s for bundles of 2,
    3, 4 and 5 leaves, of which the `SIGN` took 11–21 ms (7,066–17,665 queries).
  - After it: a median of 21.1 ms on 16 threads and 17.1 ms on 4
    (`logs/golf/ab/final-shapes-t{16,4}.log`), of which waiting for the `SIGN` is 6–18 ms.
- **The smoke shapes after the golf** (`r = 2, n = 16, M = 4`, the golf's own driver, medians):
  - `T_tree` fell from 0.879 to **0.131 s** on 16 threads, and from 0.807 to 0.184 s on 4;
  - a leaf request fell from 0.194 to **0.055 s** on 16 threads, and from 0.191 to 0.061 s on 4.

  The harness has not been run with the golfed prover.

### 4.4 The compiled Lean verifier (what `T_V` times)

The badge's parse plus `accF`, on one core:

| Proof | F1 (`logs/lean/run/verify-final.log`) | after the F1 golf (`logs/golf-lean/verify-abab.log`) |
|---|---|---|
| `L`, `n = 16` | 204–218 ms | 91–136 ms |
| `B` of two `n = 16` leaves | 0.45–0.50 s | 193–207 ms |
| `C` | 0.3 ms | 0.3 ms |
| `N` of two signed leaves (rejected, `> proofCap`) | 0.69–0.83 ms | — |

**With the real badge in F3**, pre-golf Lean (`logs/f3/bench-smoke-reverify.log`,
`logs/f3/frontier-table.txt`):

- the smoke root, a bundle of 4, takes 931–979 ms;
- the bundles of 2 take 456–481 ms, and the leaves 203–229 ms;
- the stream nodes (bundles of 2–5) take 455, 800, 921 and 1,311 ms;
- one leaf at `n = 4,096` takes 1,771 ms; the `r = 1, n = 1,024` root takes 2,000 ms.

The Lean `P` takes 15.6 s at `n = 1` and 37.0 s at `n = 16` (F2 §3.5). It is only used for the
known-answer test.

<!-- TODO(orchestrator): the badge times after the F1 fix pass (golf merged with D-6, ea2e8ab and the byte-level node reader) -->

### 4.5 Through the real harness (F3: frozen entry `8111b71`, core `a874f87`; `logs/f3/`)

**The organiser's set-up and the certificate job.** The successful run needed `Solution` importing
every module (variant V) and CompPoly among the organiser's roots
(`cert-closure.{log,json,rsmon.json}`, F3 §2.3):

| Step | Wall | Peak |
|---|---|---|
| `org-setup.sh`, default roots (`org-setup.log`) | 5 min 56 s | 6.0 GB RSS |
| comparator: build and export `Challenge` and `Solution`, then the Lean kernel | 8 min 33 s (the kernel about 192 s) | 4.11 GB (`lean`); 3.62 GB (the kernel); scope 4.37 GB |
| gate-tree rebuild and byte comparison | 3 min 30 s | 4.11 GB |
| gate | 21.8 s | 2.47 GB, mostly mapped `.olean` |
| badge build (986 package objects outside the prebuilt closure: 952 Mathlib, 28 CompPoly, 6 Batteries) | 73.7 s | 0.99 GB |
| **the whole job** | **14 min 22 s** | **4.11 GB** |

- The badge executables are 142.7 MB each, and the job's work directory is 926 MB.
- **nanoda.** Through the harness it was OOM-killed at 13.65 GB in the 14 GiB scope, 375 s after it
  started (`cert-nanoda.{log,curve}`). Run alone under a 20 GB cap, it was OOM-killed after
  10 min 1 s, its last RSS sample 20.93 GB and still growing about 2.1 GB per minute
  (`nanoda-standalone/`). The export it
  checks is 226 MB.

**The smoke benchmark: ACCEPT** (`bench-smoke.{log,json}`, F3 §3; the pre-golf prover, binary
`30b46975…`):

| | |
|---|---|
| `T_tree` | 0.896 s |
| `t_leaf` | 0.2512 s (the harness's `Σ` of `M + 1` leaves over `M`; the mean leaf request was 0.201 s) |
| `t_merge` | 0.0373 s |
| `t_link` | 0.2885 s |
| `S` | 6.666 (`o_est` 0.065) |
| canaries rejected | 69 (tree), 18 (stream), 29 (liveness tree) |
| DoS column | 64 inputs rejected; maximum 443 ms |
| liveness | 3 witnesses from a log of 30,820 entries, in 24.1 s and 121 MB |
| `T_V` (reported only) | `T_triv,best` 103,479 ns, so a cap of 10.3 µs; all 19 capped checks above it |

**The frontier** (F3 §4.3, `frontier-table.txt`, `fr-*.log`). Each tree shape had one repeat:

| `r` | largest `n` accepted | its root `π` (B) | first `n` rejected | its root `π` (B) |
|---|---|---|---|---|
| 0 | 4,096 | 796,111 | 8,192 | 1,062,591 |
| 1 | 1,024 | 925,342 | 2,048 | 1,192,062 |
| 2 | 128 | 936,916 | 256 | 1,166,724 |
| 3 | 4 | 984,096 | 8 | 1,052,576 |
| 4 | none | — | 1 | 1,676,344 |

- Every rejection is `|π| > proofCap`, and the harness reported each as "rejected by acc".
- The stream accepts 5 links at `n_f = 16` (link 6: 1,063,913 B) and 1 at `n_f = 1,024` (link 2:
  1,392,841 B), the same counts as F2's native check (`logs/f2/fix/links-n{16,1024,4096}.log`).

**The season shape** (F3 §4.1–§4.2):

- **The tree** (`bench-season.log`, `diag/tree-r6-n2p18.log`): "prover tree exit 3", 46 s after the
  start. The service refused a 1,572,898-byte query (`CAP`, `queryCap = 2^20`) 27.6 s into leaf 0.
  It was the absorb `0x20 ‖ st ‖ kind ‖ ū` of the Ligero row `ū`: 2^16 elements of 24 B. By then the
  prover had sent 1,049,601 queries (4.33 GB) and was at 6.48 GB RSS. `T_triv,best` was 2.668 s, a
  `T_V` cap of 266.8 ms.
- **The stream** (`bench-season-stream.log`): "proof.bin: missing; stderr:", 33 s after the start.
  The 11 GiB cgroup OOM-killed leaf 0 at 11.14 GB RSS after 25 s (the pre-golf prover).

**`T_V` enforced** (`fr-tv-r2-n16.log`, `fr-tv-r1-n1024.log`): REJECT at both shapes. At
`r = 2, n = 16` the root took 945.9 ms against a cap of 0.015 ms; at `r = 1, n = 1,024`, 1,776 ms
against 0.194 ms.

## 5. What is proved, and what is not

**Proved** (**kernel**; F1 §3, review F1 §0: "pass on the Lean content").

- `SpartanSrom.certificate : Certificate SpartanSrom.submission`, for every `vk`: KS with
  ε = 2^-129 and qV = 2^16 against `Rel (acc vk)`; completeness with δ = 0; `Computes` with the
  library's copy extractor (fuel `8 t`); the caps.
- `RecursionFast.Challenge.certified : CertificateR declared submission` against the rendered
  challenge.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`. The audit of every declaration of the entry,
  controls included, passed on 3,508 declarations (`logs/lean/axioms-2.log`).
- The controls: v3's, and the format controls of `SpartanSromNodeControls`.
  - Positive: a clear tree under the reference signer is accepted by `acc`.
  - Negative: every bundle check rejects with no query.
  - Canaries: one byte added or removed is rejected in `L`, `C`, `N` and `B`.
  - Claims: `ε = 2^-130`, `qV = 2^16 − 1` and fuel `7 t` are not certified.

**Not proved**:

- the native prover, and its native `acc` (`acc.rs`). These are checked by the compiled Lean `acc`
  in the harness, by known-answer tests (the Lean `P` at `n = 1, 16`; v3 at `n = 1, 2, 16, 64`) and
  by selftests against the service;
- that the compiled code matches the kernel terms (O-12);
- any bound on `V`'s time. D-6 bounds the clear-leaf recomputation; the nesting cost is §6, item 6;
- `acc` on the Lean `P`'s node proofs, which exceed `proofCap` (D-5);
- the composition across the tree, which uses unforgeability, outside every certificate (design
  §2.4).

Observation (review F1-m5): the static `Σ qBound ≤ 2^16` check is never reached within `proofCap`.
The cheapest bundle carries at most 10 leaves of `n = 1`, which is `Σ qBound ≤ 29,770`. It is still
needed, because `KS` bounds queries on every input.

## 6. What did not work, and why

1. **The frontier `2^r · n ≤ 4,096`** (§4.5). A bundle carries every leaf's SNARK, so a root grows
   by about one leaf `π` per leaf. Ligero's `π` is `√`-sized: 796,111 B at `n = 4,096` and
   1,062,591 B at 8,192. The largest accepted tree is 4,096 times smaller than the season's `2^24`
   steps. No `r ≥ 4` fits, even at `n = 1`. The stream stops at link 6 (`n_f = 16`), link 2
   (`1,024`) or link 0 (`≥ 16,384`, where the leaf alone is over the cap). Bundling cannot reach the
   season's `M = 512`.
2. **`T_V`** (§4.4, §4.5).
   - At the shapes the entry can run, the trivial checker takes microseconds, so the cap is
     microseconds: 10.3–15.4 µs at the smoke shape, against a root of 0.9–1 s.
   - At the season scale the cap is 266.8 ms on the VM (F3) and about 178 ms on a GitHub runner
     (design §3.5). One `n = 4,096` leaf alone takes 1,771 ms.
   - After the Lean golf, one `n = 16` leaf takes 91–136 ms and a two-leaf bundle 193–207 ms, on the
     VM. So a node checking two Spartan children would sit at about the runner's cap (**estimate**,
     FB-2).
   - Compiled Lean has no carry-less multiply, and GF(2^64) products were 64 % of the badge's time
     before the golf (F1 golf §2, Q11).
3. **`queryCap` against a large absorb at `n = 2^18`** (§4.5). The transcript absorbs `ū` whole, and
   at `2^18` that is 1.57 MB, above the service's `2^20`-byte cap. The fix is a chunked absorb (§7).
   Since the F2 fix pass the client refuses such a query itself, with an explicit message (F2-m5).
4. **Memory before the golf.** v3's leaf prover needed about 15 GiB at `2^16`, and the season
   stream's leaf was OOM-killed at 11.14 GB. The golf's late tables and early frees brought it to
   2.47 GiB (§4.2). Memory no longer stops this prover below `2^18`; `proofCap` does.
5. **The quadratic `.data` trap.** Compiled Lean turns `ByteArray.data` into a boxed copy of the
   whole array on every call. v3's `digestFrom` read `π.data.getD`, 32 times per digest, so F1's
   scratch runner took 87.8 s to parse a 539 KB file and 579 s for 1.08 MB, outside `acc`
   (`logs/f2/lean-check/`; F2 §3.5). The fix reads bytes in place (`byteAt`, equal by `rfl`). The
   harness's own badge parser was always linear. The same trap was in `tagWord`/`leafN`; F1's
   attempt to read those in place made `split_ifs` time out at `whnf` (F1 journal), and the review
   suggests a bridge lemma, proved once.
6. **The crafted-proof DoS and D-6** (review F1-M2; FB-5).
   - σ0 is public in every bundle, so anyone can sign every query-free slot. The review built a
     depth-100 chain of plain nodes over clear leaves, 970,448 B, on which the compiled `acc` takes
     **68.5 s** with `n = 1` leaves and **183 s** with `n = 2^20` leaves. The honest root takes
     0.43 s and `verify_s` is 60 s.
   - There are two causes. `N` re-decodes each child from scratch at every level, which is
     `O(|π| · depth)`; and `C` recomputed up to `2^20` chain steps per clear leaf.
   - D-6 caps clear and bundled leaves at `n ≤ 2^12`. No `acc`-acceptable proof is lost, because
     `leafSize 4096 = 796,111 ≤ 2^20 < leafSize 8192 = 1,062,591`.
   - The harness's DoS column, which uses random mutations, never reaches such inputs.

   <!-- TODO(orchestrator): the post-fix-pass attack timing (depth-100 chains after D-6, decodeFront and the byte-level node reader) -->
7. **Harness frictions at `a874f87`**, all fixed at the pin `81e1ebf` (B-RESULT §9). They are listed
   so that nobody chases them again:
   - the rebuild binding rejected modules outside `Solution`'s closure (Q7);
   - CompPoly was not an organiser root, so its `@[csimp]` lemma rejected the entry (Q2;
     `RF_ORG_ROOTS` is no longer needed);
   - a nanoda OOM kill read as "the certificate does not check" (Q12);
   - a service refusal and an OOM kill were invisible in the result (Q13, Q14).
8. **A false alarm.** Review F1-m4 said that `Batteries.Data.BitVec.Lemmas` was outside the
   allowlist. It is in the default allowlist (`logs/f3/allowlist-default.txt`, line 171).
9. **Golf attempts that did not pay** (F2 golf §2.15):
   - writing the leaf file during its `SIGN`;
   - splitting the transposed walk over two threads;
   - lookup rounds without buckets;
   - `LATE = 6` or `8` instead of 7.
10. **Kernel-time traps in the Lean** (F1 golf §3).
    - The kernel evaluated a BLAKE2s signature inside casts: computing the size generically took the
      check from 3.6–4.8 s to under 0.1 s.
    - A `split_ifs` on an `AtMost` goal made `whnf` evaluate the header parser.
    - The 45 `decide +kernel` are v3's, on small terms; `TranscriptControls` is the slowest module,
      at 75–144 s.

## 7. What to try next

1. **Recursion.** It is the only way to the season shape (FB-1). A node must verify each child
   `(π, tr, σ)` completely, because `acc` is all or nothing (F0-ideation Q3; design §4.2):
   - **`V`'s algebra under `runSeq`.** For this leaf that is the outer and inner sumchecks over
     GF(2^192), the ring switch, Ligero's column checks and about 3.5–5.7k transcript and Merkle
     queries. Inside a GF(2) circuit this is the open cost.
   - **`traceDigest tr`.** The node hashes every byte of the child's trace: about `|trace| / 64`
     compressions. For this leaf that is about 6.1k at `n = 16` and about 50k at `2^16`, from the v4
     trace sizes of §4.1 (**estimate**). The design's figure is 1.6 compressions per 64-byte query.
     A Ligero child is a bad child: its trace restates its opened columns.
   - **One WOTS `SigOk`.** About 300 compressions on average and 495 at most (design §4.2).
   - **The total.** For a Flock-class child the hashing alone is about 16–17k compressions, about
     one `2^14` leaf. leanVM's whole step is 18.4k compression-equivalents (v3 §5.2).
   - **And the node's own proof.** It must stay bounded over `M = 512` links, its `acc` must stay
     within `T_V` (about 178 ms on a runner), and its extractor must output the children's signed
     proofs within `outCap = 2^24` words, at 4,776 B per signature slot (C-m11).
2. **A smaller-proof PCS for the leaf.** Ligero's `√`-size is what sets the frontier, and it makes
   the trace a recursive node must hash large.
   - WHIR-class proofs are about 250 KB: leanVM's BLAKE2s Flock gives 259,320 B at `2^14` (F0 §4).
   - Under `errorCap` that needs GF(2^192) (F0-ideation Q4: about 261–309 queries per level at
     rate ½, **estimate**).
   - It also needs a proximity theorem in Lean. Unique decoding is the admissible first step (v3
     §5.3); the list-decoding MCA is research-scale.
3. **A chunked absorb.** Absorb long messages as a hash chain over pieces of at most `2^20` bytes.
   This changes the transcript, so the Lean `V`, its soundness proof and the prover all change. Any
   Ligero leaf needs it at `n ≥ 2^18`.
4. **Flock's optimisations that change `V`** (F0-ideation Q1; each changes `V` and the KS proof):
   - the univariate skip (Flock §4.2), with a degree-126 round, which GF(2^192) admits;
   - pinned or "friendly" challenges (§4.3), which need an F₂-independence lemma;
   - skipping `c` (§4.4);
   - the shift argument (§4.6).

   The block-diagonal collapse (§4.1) is already used on the prover's side without changing `V`
   (F2 golf §2.4), and so could the circuit walk (§4.5).
5. **The compiled verifier** (F1 golf §2, "proposed next"):
   - Spartan's `chainMats` without `Finset`/`Multiset` in compiled code (31 % after the golf);
   - fewer `reduce`s in `EF.mul`/`dotE`;
   - `natLE` without `Nat` bignums.

   Measure on a runner (FB-2 (3)): the badge's `acc` on one leaf and on a bundle of two, against
   that runner's own `T_V`.
6. **The prover** (F2 golf §4.1, §6):
   - the serial transposed walk, about 1.6 ms per `n = 16` leaf;
   - the 153 sequential Fiat–Shamir round trips, 5.1–7.2 ms per leaf;
   - the `pclmulqdq` path, which has never been timed on hardware that has it;
   - whether the runner's binutils 2.42 assembles `prover.s` (untested; by reading, yes).
7. **If the rules change** (`docs/v4/FLOCK-BASELINE-FEEDBACK.md`):
   - a vacuous `SigOk` on empty traces (FB-10) would drop 4,776 B per clear slot, worth one more
     frontier notch (`r = 3, n = 8`; a sixth link at `n_f = 16`);
   - a Library bundle (FB-3) would save the next entrant about 870 Lean lines;
   - documented grinding (FB-9) would admit GF(2^128).

## 8. Where things are

| What | Where |
|---|---|
| decisions, formats, the verifier branch by branch | `docs/v4/flock-baseline/BLUEPRINT.md` (D-1 … D-6) |
| the route analysis | `docs/v4/flock-baseline/reviews/F0-route-ideation.md` |
| probes: the assembly route, sizes, Flock on the VM | `stages/F0-probes-RESULT.md` |
| the Lean port, its golf, journal and review | `stages/F1-lean-RESULT.md`, `F1-golf-RESULT.md`, `F1-lean-JOURNAL.md`, `reviews/F1-lean-review.md` |
| the prover, its golf, journal and review | `stages/F2-prover-RESULT.md` (with its fix pass), `F2-golf-RESULT.md`, `F2-prover-JOURNAL.md`, `reviews/F2-prover-review.md` |
| the harness run | `stages/F3-harness-RESULT.md` |
| the report on the rules | `docs/v4/FLOCK-BASELINE-FEEDBACK.md` |
| logs | `logs/probes/`, `logs/lean/`, `logs/golf-lean/`, `logs/f2/`, `logs/golf/`, `logs/f3/` (gitignored) |
