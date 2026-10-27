# Stage P1 (track P, prover core): RESULT

Status: implementation report, 2026-10-27, for the orchestrator. Blueprint: `BLUEPRINT.md` at
revision 2 (`de0d708`) for the values adopted, revision 3 (`0d513c9`) read for §5 below. Running notes
are in `P1-JOURNAL.md`. Evidence tags as in the blueprint: **measured** (a GitHub-runner run, with its
run id and log under `logs/P1/run-<id>/`, gitignored) and **estimate** (arithmetic on measured
inputs, derivation shown). Nothing is committed; the probe branches `probe/p1-1` … `p1-7` are one
commit each on `v4/flock-recursive` adding the files below and `.github/probe.conf = p1-prover`.

## 0. Summary

- **Built:** a std-only Rust prover crate (`submissions/flock-recursive/prover/`, 6,678 lines,
  no dependencies) that proves a leaf `chainEnd s n = h` end to end: the BLAKE2s witness, the
  Ligerito commitment through the oracle service, the zerocheck with the 64-point univariate
  skip, the lincheck by the transpose circuit walk, the chain shift argument with both endpoints,
  ring switching for three claims, and the five-level Ligerito opening. A native verifier `V`
  and the native `acc` (caps, `SigOk` on the trace digest, `runSeq`) check every proof.
- **Correctness:** every proof made on the VM and on the runners was accepted by the native
  `acc`, and the flipped statement (the runner's canary) was rejected. Mutated proof bytes are
  rejected (`test-leaf`). Every vector kernel is checked against the portable reference on every
  run (`selftest`). The unit tests pass, including the 8 + 8 F/K known answers that S-A
  kernel-checked (§3).
- **Tiers (B-9):** tier 1 is AVX2 + VPCLMULQDQ-256, verified on the EPYC 7763. Tier 2 is scalar
  `pclmulqdq` or portable. A `ymm-sim` tier runs the tier-1 kernel bodies with the 256-bit
  carry-less product emulated, so they are tested on this VM under `qemu-x86_64 -cpu max`.
  Dispatch is at run time; the crate builds at `-C target-cpu=x86-64-v2`.
- **Measured on the EPYC 7763** (4 vCPU, tier ymm, through a real `rf-oracle`; times are the whole
  request: prove, record the trace, SIGN, write the file):

  | shape | total | compressions/s | peak RSS | `|π|` | `|tr|` |
  |---|---:|---:|---:|---:|---:|
  | leaf m = 30 (2^16) | **1.75–1.81 s** | 36.2–37.5 k | 1.42 GB | 691,744 | 6,981 |
  | leaf m = 32 (2^18) | **6.55–6.67 s** | 39.3–40.0 k | 5.49 GB | 750,944 | 8,744 |

  Run 40515354434 (probe/p1-6), peak RSS from `/usr/bin/time -v`. §2 has every run and CPU,
  including an EPYC 9V74 (7.55–7.61 s and 1.95–2.04 s on the ymm tier).
- **Against the caps:** the m = 32 leaf is 1.7× K's pipeline (3.73–3.86 s). The tree estimate is
  64 × 6.6 + 63 × ≈ 1.9 ≈ 545 s against `tree_s` = 600 s: inside, with 9 % margin. The
  stream link estimate is ≈ 1.8 + ≈ 1.9 ≈ 3.7 s against ≈ 3.1 s: **not yet met** (§2.3).
  Where the remaining time goes is in §2.2, and what to do about it is in §6.
- **Protocol:** constants and layouts follow rev. 2's Appendix A where it gives a value (§4). Where
  rev. 2/3 is still open or would cost throughput, P1 made its own choices, listed in §4.2.
  The item sequence and byte layout are **not** rev. 3's yet (§5).

## 1. What was built (file by file; lines by `wc -l`)

| File | Lines | What |
|---|---:|---|
| `params.rs` | 147 | every protocol constant in one place: block layout (A.6), ladder (5 levels, rates 1/2…1/32, rows 64/16, caps 9,8,8,8,7, queries 290/178/145/132/126, checked against rev. 2's formula), tags (7-byte seed), `qV = 10,240` |
| `field.rs` | 602 | BF64 / F = BF64[y]/(y²+y+β) / K = F[u]/(u²+u+α) with β = x^63, α = βy (A.1); Karatsuba products, unreduced accumulators (`FAcc`, `KAcc`), inverses by the norm; portable and `pclmulqdq` carry-less products; ζ = x^((2^64−1)/255), its minimal polynomial, GF(2^8) arithmetic |
| `simd.rs` | 980 | tier dispatch (`FLOCK_TIER`); tier-1 kernels generated twice by one macro (VPCLMULQDQ and `ymm-sim`): F product, MAC, NTT butterfly, folds, zerocheck inner loops, K folds and K×K / K×F / F×F round messages, consistency-weight MAC, axpy; the AVX2 round-1 window (port of the probe's `x_hi_avx2`); `selftest` |
| `ntt.rs` | 258 | additive NTT on the basis `x^0 … x^19` (A.1's `D`), LCH novel basis (BF64 twiddles), radix-4 top passes, rate `1/2^r` by replication; `Ŵᵥ(D[j])`, the tensor rows `X_x(D[j])` and their multilinear extension `Π(1 + c + c Ŵᵥ)` |
| `skipdom.rs` | 268 | `S`, `Λ` from ζ (A.1), the compressed LDE byte table, the convert table, the pinned point (§4.2), Lagrange weights |
| `circuit.rs` | 596 | leanerVM's BLAKE2s product circuit (from spartan-srom, Apache-2.0) on A.6's layout: tape, bit trace, transpose walk |
| `witness.rs` | 249 | the chain, the bit-sliced witness by the tape, and the word-level witness `block_fast` (equal to the tape, unit test) |
| `zerocheck.rs` | 219 | round 1 (skip) with the two C banks, `P^z` on Λ, the x₆ round from bits, tail rounds in Gruen's form |
| `lincheck.rs` | 89 | partial fold of z over blocks (8×8 transposes, sum tables), row weights, η by the walk |
| `ringswitch.rs` | 245 | partials `s_v` (four Russians), the 128 × 128 recombination, the batched target, the prover's weight table `W(y)`, the verifier's width-128 MBP over K ⊗ F (unit test against the table's MLE) |
| `ligerito.rs` | 469 | level-0 commit, the five-level opening (fused fold + next message, coordinate split, consistency weights), the final rounds; the verifier with the recursive weight evaluation |
| `merkle.rs` | 60 | Merkle trees through the oracle (column and node queries, caps) |
| `leaf.rs` | 457 | the leaf prover and native verifier, phase by phase |
| `transcript.rs` | 163 | seed/absorb/squeeze, F/K challenges, positions; the proof writer and reader |
| `sumcheck.rs`, `mle.rs` | 66, 188 | degree-2 rounds; eq tables, MLE folds, the shift MLE |
| `main.rs` | 233 | modes `selftest`, `test-leaf M`, `prove-leaf M` (service, SIGN, `acc`), `acc`; the native `acc` |
| `par.rs`, `oracle.rs`, `service.rs`, `blake2s.rs`, `format.rs` | 251, 342, 374, 237, 185 | reused from spartan-srom (pool, oracle wrappers incl. `Recorder`/`Replay`/`Seq`, the service client with the 31-connection cap, BLAKE2s, the signed-proof file and `SigOk`) |
| `../LICENSE-flock`, `../LICENSE-leanerVM` | | Flock's MIT/Apache-2.0 (code marked as a port of Flock via the phase-0 probe), leanerVM's Apache-2.0 |
| `probe/p1-prover/run.sh` | 51 | the runner probe: builds the prover (x86-64-v2) and `rf-oracle` (`.contract/service`), `selftest`, `test-leaf 25`, `prove-leaf 30 ×3`, `prove-leaf 32 ×2` under `/usr/bin/time -v` |

Not built in P1 (P2's scope): `setup`/`tree`/`leaf`/`node` runner modes, `prover.s` (the crate
reuses `sanitize-asm.py`; `build-asm.sh` is not yet adapted), the node prover and the IR generator.

## 2. Measurements

### 2.1 Runs (all `ubuntu-24.04`, 4 vCPU, the probe workflow)

| Run | Branch | CPU | Build | m = 30 total (s) | m = 32 total (s) | peak RSS m = 30 / 32 |
|---|---|---|---|---:|---:|---|
| 40512899416 | p1-1 | EPYC 7763 | tier pclmul only (portable round 1) | 8.09–8.16 | 32.30–32.38 | 1.26 / 4.92 GB |
| 40513625501 | p1-2 | EPYC 7763 | + ymm kernels, AVX2 round 1 | 2.61–2.72 | 10.35–10.44 | 1.26 / 4.92 GB |
| 40514255970 | p1-3 | EPYC 7763 | + K kernels, vector x₆ round | 2.04–2.08 | 8.02–8.11 | 1.26 / 4.92 GB |
| 40514779510 | p1-4 | EPYC 7763 | + word-level witness, vector scaling | 1.91–1.96 | 7.12–7.17 | 1.26 / 4.96 GB |
| **40514984183** | **p1-5** | **EPYC 7763** | + fused Ligerito rounds, vector consistency weights | **1.82–1.88** | **6.73–6.81** | **1.36 / 5.36 GB** |
| **40515354434** | **p1-6** | **EPYC 7763** | + radix-4 NTT passes | **1.75–1.81** | **6.55–6.67** | **1.42 / 5.49 GB** |
| 40515361052 | p1-7 | EPYC 9V74 (Zen 4; AVX-512 present, tier 0 not built) | same as p1-6 | 1.95–2.04 | 7.55–7.61 | 1.42 / 5.49 GB |

Every run: `SELFTEST pass` (ymm, pclmul and ymm-sim checked against portable on the runner),
`TEST-LEAF m=25 accept`, every `PROVE-LEAF` line `acc=accept canary_accept=false`.

### 2.2 Where the time goes (EPYC 7763, run 40514984183 = p1-5; p1-6 differs only in the commit, 0.30 / 1.27–1.35 s)

| phase | m = 30 | m = 32 | K's pipeline m = 32 (K §3) |
|---|---:|---:|---:|
| witness (chain + word-level z, a, b) | 0.21 | 0.43 | 0.12 |
| commit: NTT level 0 + Merkle through the service | 0.34 | 1.45 | 0.64 (NTT only) |
| zerocheck round 1 (skip) | 0.31 | 1.23–1.27 | 1.15 |
| zerocheck x₆ round + fold | 0.16 | 0.59 | 0.25 |
| zerocheck tail | 0.09 | 0.34 | 0.22 |
| lincheck | 0.08 | 0.30 | 0.20 |
| shift + IO | 0.02 | 0.08 | — |
| ring switching | 0.25 | 0.98–1.00 | 0.86 |
| Ligerito opening | 0.29 | 1.07 | 0.31 |
| trace recording (replay of `V`) + SIGN | 0.07 | 0.26 | — |
| **total** | **1.82–1.88** | **6.73–6.81** | 3.73–3.86 (compute only) |

The oracle's share (`oracle_s`: Merkle batches and the ≈ 300 sequential Fiat–Shamir queries) is
0.18 s at m = 30 and 0.66 s at m = 32. The service hashes 2.79 M queries (1.27 GB) per m = 32 leaf.
The Fiat–Shamir round trips cost 5–6 ms in total.

### 2.3 Against the caps (**estimate** from §2.2)

- **Tree** (64 × m = 32 leaves + 63 nodes at m = 30): 64 × 6.6 s + 63 × (1.8 + ≈ 0.1) s ≈ 422 +
  120 ≈ **545 s** against 600 s. The node's extra phases are E1/E2 over `N_M ≈ 2^19.86` rows and Lr
  over `2^15` rows; at the measured tail and round rates they cost ≈ 0.1 s.
- **The m = 30 node at 53,792 of 65,536 blocks** (rev. 3): this prover does the same work for every
  block (zero blocks are not skipped). The m = 30 leaf is therefore the measured cost of the
  node's commitment and bit-level PIOP: **1.75–1.81 s on the 7763** (run 40515354434). The E/Lr phases add ≈ 0.1 s
  (estimate). A node-mode prover (P2) can skip the 11,744 unused blocks in the witness, round 1
  and the lincheck fold, about 18 % of those phases.
- **Stream link** (an m = 30 leaf + a node, start-ups included): ≈ 1.8 + 1.9 ≈ **3.7 s against
  ≈ 3.1 s: over by about 20 %**. Process start-up and the arena are not counted here; the prover
  allocates per phase. Remaining gaps against K's kernels, all at m = 32: Ligerito 0.76 s,
  commit 0.2 s plus Merkle 0.6 s, the x₆ round 0.34 s, the witness 0.31 s, the trace replay
  0.26 s. Closing them is P2's work (§6).
- **Memory:** 5.49 GB peak at m = 32 against 11 GiB.

## 3. Correctness checks

- `cargo test` (21 unit tests): `field_laws`, the S-A KATs (`kat_products`: the 8 F and 8 K
  triples of `probe/fr-field/kat.out`, `FRFieldControls.katF/katK`, on the portable and
  `pclmulqdq` paths), the NTT against the novel-basis evaluation (radix-2 and radix-4 paths), the
  tensor identity, the LDE table against Lagrange, the 128-weight rank of the pinned point, the
  circuit (chain step, rows `a ∧ b = z ⊕ e`, transpose = adjoint of walk), the word-level witness
  against the tape, the MBP against the weight table's MLE, the ring-switch identity.
- `selftest` (every run): each tier-1 / sim kernel against portable on random inputs.
- `test-leaf M` (VM: m = 25…30, portable; under qemu: m = 25, pclmul and ymm-sim; runners: m = 25):
  prove, native verify (accept). It also flips the statement and three proof bytes; each is
  rejected. A build with debug assertions also checks every sumcheck invariant inside the prover.
- `prove-leaf` (VM with the organiser's `rf-oracle` binary: m = 26, 30; runners: m = 30, 32). The
  steps are prove; replay `V` on the recorded answers to obtain the trace (0 missing queries);
  `SIGN`; check the answers equal the QUERY answers; write the FORMAT.md file; run the native
  `acc` (accept); run the canary `acc` on the flipped statement (reject).

## 4. The protocol as implemented, and deviations

### 4.1 Adopted from the blueprint (rev. 2 Appendix A)

β = x^63, α = βy (the S-A KATs pass); `D[j] = j` on the basis `x^0…x^19`; the novel-basis Enc
(message = LCH coefficients); ζ, `S = span(ζ^0…ζ^5)`, `Λ = S + ζ^6`; A.6's block layout (`one` at
1152, natural message order, `d` at 520…775); the five-level ladder and query counts; the 7-byte
seed tag and the absorb/squeeze/Merkle tags; F challenges from bytes 0…15, the second F of a
phase from bytes 16…31, K from all 32; positions as `idxOf`, `⌊256/b⌋` per answer, repeats
allowed; caps at depth `depth − cap` in index order; `qV = 10,240`. Header `hdr` (48 bytes,
§1.1) and the leaf statement fields `enc64 n ‖ h ‖ 0^8`.

### 4.2 P1 choices where the blueprint differs or was open (each kept in `params.rs` or its phase module)

| # | P1 | Blueprint | Reason |
|---|---|---|---|
| P1-D1 | pinned point = the paper's two-level progression: `gᵢ = ζ^(2^(i−1))` (i ≤ 3), `y^(2^(i−4))` (i ≥ 4), `ρᵢ = gᵢ/(1+gᵢ)` | rev. 2: `x^(2^(j+3))`; rev. 3: `ρⱼ = y^(2^j)` | round 1 accumulates `Σ_k ζ^k (â·b̂)` in GF(2^8) and lifts once per 8 rows (the paper's §4.3 kernel). Rev. 3's point is a one-level progression in F (`eq = C·(y/(1+y))^(2·int(b))`), so all 7 coordinates are in F. Round 1 would then lift every row: 8× the convert-table work, about +0.3 s per m = 32 leaf (**estimate**). Recommend a two-level choice. |
| P1-D2 | `one` forced by the constraint `(Az)∘(Bz) = z + e` (`e` = position 1152 in every block; the verifier adds `P^e` on S) | public-pattern claim | one term in the skip check instead of a pattern sumcheck |
| P1-D3 | constants (`h0`, tag, zero bytes, `t`, `f`) as constant rows of the block | public-pattern claims | spartan-srom's block; the rows are free in the zerocheck |
| P1-D4 | lincheck: 14 multilinear rounds (skip bits as Boolean variables); a plain multilinear z-claim | 9 rounds + a univariate round L3 | simpler, same error per round |
| P1-D5 | shift: `θ` (8 coordinates), `τ`, `κ_s` in one phase; one block sumcheck of `eq(τ,·)·Out + (shift(τ,·) + κ_s·eq(0,·))·In` with `h` and `s` in the target; then `μ` and a 10-round collapse over positions `< 1024` with the verifier-computed weight of the two digest slots | range-restricted degree-3 round + univariate S3/I2 | both endpoints without extra claims; the misaligned `d` slot (520…775) is handled by the slot weight |
| P1-D6 | ring switching for the three z-claims at once. The prover sends `3 × 128` partials; `r″` and `κ` come from one phase. The batched claim `Σ_y W(y) f(y)` is Ligerito's input directly. The verifier evaluates `Ŵ` once, by the MBP, at Ligerito's final point. | B: an `m`-round batching sumcheck; R: `m − 7` rounds to `f̂(r_f)` | the B sumcheck over `2^m` bits has no efficient prover as written (its first fold makes an F table of `2^(m−1)` entries). This also saves `m − 7` rounds and a pass over `f`. |
| P1-D7 | Ligerito's last level: the verifier checks `Enc₄(final)[j]` directly. Then `log k₄` (5 or 7) final rounds reduce `Σ_c Ŵ(s, c) final(c)`, and every weight is evaluated once (recursion `weight_eval`). The final message is the level-4 fold, `2^5` / `2^7` K elements. | final message `k₅ = 4 / 16` K, no final rounds | the claim needs `Ŵ` on every point of the final hypercube unless it is reduced to one point |
| P1-D8 | `π` = the prover's messages in reading order (caps, rounds, columns, siblings interleaved per position) | A.3 field order, `piSize = 754,896` | P1's sizes: 691,744 (m = 30), 750,944 (m = 32); within `proofCap` |

## 5. Open questions and needed blueprint changes

1. **Rev. 3's interface** (one item sequence for both kinds, dummy Merkle-node queries, every
   index opened, `piSize = 754,896` with padding, `reassemble` from item 1, the pattern sumcheck)
   is not implemented. It changes the item sequence and the byte layout, not the kernels. The S-0
   dump tools (`gen` op sequence, `items` as JSON) are what P2 must match byte for byte. P2 should
   start from them once they exist.
2. **Pinned point (P1-D1):** see the table. The kernel needs the 3 + 4 split, with the low 3
   coordinates in GF(2^8). A two-level set keeps `pinned_rank` (the test `pinned_rank` checks
   rank 128 for P1's set).
3. **B, the batching sumcheck over `m` variables (rev. 2 §2.3 B2):** as written its prover is
   infeasible (above). P1-D6 batches inside ring switching instead. Please confirm, or specify B's
   variable order so that its prover stays on packed data.
4. **Final message size:** rev. 2/3 list `k₅ = 4 / 16` K elements (128 / 512 bytes). A level-4
   fold of 4 row variables yields `k₄ = 32 / 128` K elements. Which object is sent?
5. **Lincheck L2 "9 rounds":** the block's high position bits are 8 (`14 − 6`). Which variable is
   the ninth?

## 6. Next (P2)

The `setup`/`tree`/`leaf`/`node` modes; `prover.s` with `build-asm.sh` (binutils 2.42); and the
rev. 3 item sequence with the S-0 KAT. Throughput work for the stream link, the binding cap, with
each gap measured against K in §2.2:

- Ligerito: K×K Karatsuba with paired lanes and a fused level-0 F→K pass (−0.5 s at m = 32,
  −0.15 s at m = 30, **estimate** from K's 3.71 / 5.0 ns per element);
- a pre-faulted arena reused across phases (K §5.2);
- the Merkle leaves hashed while the NTT's deep phase runs;
- trace recording without the full replay table;
- zero-block skipping in node mode;
- the GF(16)² round-1 kernel (K §5.3);
- an AVX-512 tier 0 for the dominant kernels.
