# Phase 0 K: prover-kernel kill test (FR-R5)

Status: measurement memo, 2026-10-27. It answers FR-R5 (`PLAN.md` §5): can a std-Rust prover on
the slowest evaluation runner reach the throughput the season shape needs? The season needs:

- the tree: 2^24 BLAKE2s compressions plus 63 node proofs within `tree_s` = 600 s;
- the stream: about 3.1 s per link, which is one 2^16-compression leaf and one node merge, with
  their start-ups (`.contract/harness/PROVER.md` §3);
- `memory.prover` = 11 GiB.

**Evidence tags.** **measured**: a GitHub-runner run, with its CPU, run id and log path.
**estimate**: arithmetic on measured inputs, with the derivation shown. The VM numbers are not of
record (the VM has no carry-less multiply). Logs live under
`logs/phase0-K/run-<id>/probe-kernels/out/` (gitignored): `machine.txt` (lscpu), `kernels.log`,
`results.tsv`, `pipe-*.log`, `time-pipe-*.txt`.

## 0. Verdict

**FR-R5: feasible as designed.** The protocol needs no change: rate 1/2 at level 0, the Secure UD
ladder, GF(2^128) with GF(2^256) fold challenges, the 64-point univariate skip.

The verdict depends on three conditions:

1. **The prover's implementation.** It needs an **AVX2 + VPCLMULQDQ-256 kernel tier**, written
   here, and run-time dispatch.
   - Flock's own x86 code has no such tier. On a CPU without AVX-512 it falls back to scalar
     PCLMULQDQ and scalar byte kernels.
   - With Flock's Zen-3 path the leaf work alone is about 36 µs per compression, about 600 s for
     2^24 compressions (**estimate** from measured kernels, §4.5): **infeasible**.
   - With the ymm tier the whole leaf computation measures **14.2–14.7 µs per compression** on
     the EPYC 7763 (§3).
2. **The tree's leaf segmentation is 64 leaves of 2^18 (m = 32), not T's suggested 128 × 2^17.**
   - 2^18 leaves are faster (fewer nodes): about 330–365 s for the tree against 385–430 s.
   - They fit in memory with a large margin: **3.81 GB peak measured** at m = 32, against 11 GiB.
     T's 11 GB worry (T §3.4) came from Flock's 8.5 GB figure, which this buffer plan does not
     reproduce.
   - This is a parameter choice T already allows (T §1.1, §3.2), not a protocol change.
3. **The node circuit has T's size.** That is about 43k BLAKE2s compressions and an M region of
   about 2·10^5 GF(2^128) product rows (2^26.2 *bits*, T §3.2), committed at m = 30.
   - If "2^26 GF(2^128)-product constraints" in the task prompt meant 2^26 product *rows*, the
     node would commit about 2^34.6 bits. That gives about 16 s per node and about 30 GB (§4.6),
     which is **infeasible**.

Key numbers on the **EPYC 7763** (Zen 3, 2 cores × SMT, AVX2, 256-bit VPCLMULQDQ, no AVX-512, no
GFNI). It is the slowest of the four models seen.

| Cap | Need | Measured part | Estimate (all in) | Margin |
|---|---|---|---|---|
| tree ≤ 600 s | 64 × 2^18 leaves + 63 nodes | leaf compute 3.73–3.86 s; node compute 0.81–0.83 s | **≈ 330–365 s** | 1.65–1.8× |
| stream link ≈ 3.1 s | 2^16 leaf + node, start-ups included | leaf 0.97–1.01 s; node 0.81–0.83 s; arena 0.04–0.14 s each | **≈ 2.1–2.7 s** | ≥ 13 % (the tightest cap) |
| memory ≤ 11 GiB | one m = 32 leaf on 4 threads | **3.81 GB** peak RSS | ≤ 4.5 GB | 2.4× |

On the AVX-512 runners every figure is lower. Leaf compute at m = 32 measures 3.58 s on the Xeon
8573C, 3.02 s on the EPYC 9V74 and 2.11–2.28 s on the EPYC 9V45. Only the dominant kernels have a
zmm path here (§1); the rest run the ymm code.

## 1. The probe

The probe is `probe/kernels/`:

- 3,426 lines of std-only Rust with no dependencies, plus `run.sh`;
- `run.sh OUTDIR` builds with `-C target-cpu=znver3`. It falls back to `native` if the host lacks
  a feature (the 8573C lacks `sse4a`) and prints `lscpu`;
- every hot loop is a `#[target_feature]` function chosen at run time with
  `is_x86_feature_detected!`, with a portable fallback, so it also runs on the VM.

It ran through `.github/workflows/probe.yml` on branches `probe/kernels-1` … `-12`, each one
commit on `v4/flock-recursive` at `c9bd4d3` that adds `probe/kernels/` and
`.github/probe.conf = kernels`.

**Fidelity.** Each kernel is a port of the Flock code it names (repository `48f4bfe`, copy in
`logs/ref/flock`). A "flock-zen3" variant is what Flock compiles to on a CPU without AVX-512/GFNI.
The ymm and zmm variants are the rewrite.

| Item | Port of (Flock) | Variants |
|---|---|---|
| 1. GF(2^128) product, MAC | `flock-field/src/gf2_128{,/x86_64}.rs`: `ghash_mul_karatsuba_barrett`, `ghash_mul_unreduced_x86`, `ghash_mul_x4`, `WideGhashX4` | portable, scalar PCLMULQDQ (Flock), xmm, ymm (schoolbook / Karatsuba / by-constant), zmm (Flock's AVX-512); K = GF(2^256) = F[u]/(u²+u+x⁻¹) K×F and K×K |
| 2. F × packed GF(2), eq table | `pcs/ring_switch.rs`: `fold_1b_rows_{1,2}way_method_of_four_russians`, `fold_b128_elems`; `build_eq` | scalar (Flock's code is scalar on every x86); eq: pclmul, ymm |
| 3. additive NTT, RS rate 1/2 | `ntt/additive_ntt_f128.rs` + `kernels/` (LCH novel basis {1, x, …}, interleaved SoA, replicate + start at layer 1) | scalar PCLMULQDQ radix-4 (Flock's Zen-3 path), ymm radix-4/8, zmm radix-8 (Flock's AVX-512 kernel shape) |
| 4. zerocheck rounds 1, 2, 3.. | `zerocheck/univariate_skip_optimized.rs` + `kernels/` (`apply_x86_unchecked`, `shift_reduce_inner_ab_scalar`, `bit_transpose_64bytes_scalar`, `accumulate_convert_with_s_hat_v`), `ntt/inv_table.rs`, `zerocheck/multilinear.rs` (`fold_pair_run`, `fold_and_message_x86_avx512`) | flock-zen3; AVX2: ymm table apply, bit-serial GF(2^8) product in ymm (no GFNI on Zen 3), unpack transpose, VPCLMULQDQ-256 convert/eq products |
| 5. BLAKE2s witness | Flock's "Option F" carry encoding carried to BLAKE2s (F-flock §3): 6 product words per G, z = product, a, b = its two linear operands | scalar |
| lincheck | `lincheck.rs`: `pack_z_lincheck`, `partial_fold_packed_z_fast` | scalar |
| Ligerito sumcheck rounds | the F→K and K→K fold + message of the opening (not a Flock port; written to the T protocol) | ymm |

**Synthetic tables.** The round-1 tables (inverse-NTT byte table, convert table, fold table) are
random. They keep Flock's sizes, layouts and F2-linear structure. The kernels' cost does not depend
on the values.

**Self-test** (`kernels selftest`). It **passed on every runner run**: 7763 ×4, 8573C ×2,
9V74 ×1, 9V45 ×4. It checks:

- every product tier against the portable reference, and the portable reference against field
  identities;
- every NTT tier against Flock's reference loop, including the replicate-from-layer-1 identity;
- the AVX2 round 1 against the Flock-path port on the same inputs;
- round 2, the zerocheck tail and the Ligerito rounds against portable versions;
- the four-Russians folds against naive sums;
- the lincheck fold against a direct sum;
- BLAKE2s("abc") and the witness rows (`z = a & b`).

**Runs** (all `ubuntu-24.04`, 4 vCPU = 2 cores × SMT; probe workflow):

| Run | Branch | CPU | Probe version |
|---|---|---|---|
| 40499891632 | probe/kernels-1 | AMD EPYC 7763 (Zen 3) | v1, kernels only |
| 40501050042 | probe/kernels-2 | AMD EPYC 7763 | v2, first pipeline (allocation inside phases) |
| 40501057608 | probe/kernels-3 | Intel Xeon Platinum 8573C | v2 |
| 40501685601, 40501699666, 40502058070, 40502436136 | -4, -6, -7, -12 | AMD EPYC 9V45 (Zen 5) | v3 |
| 40501692242, 40502064046, 40502422451 | -5, -8, -10 | AMD EPYC 7763 | v3 |
| 40502071172 | -9 | AMD EPYC 9V74 (Zen 4) | v3 |
| 40502428767 | -11 | Intel Xeon Platinum 8573C | v3 |

v3 is the version of record. It has the arena pipeline (§3), warm witness buffers and the 1-way
`s_hat_v`. Its kernel numbers repeat v1/v2's within a few per cent.

## 2. Measured kernel costs

Best of 3, wall time; 4T means 4 threads on the 4 vCPUs. Columns: 7763 = run 40502064046,
8573C = 40502428767, 9V74 = 40502071172, 9V45 = 40501685601. The source is each run's
`results.tsv`. A dash means the tier is absent on that CPU.

| Kernel | unit | 7763 1T | 7763 4T | 8573C 1T | 8573C 4T | 9V74 1T | 9V74 4T | 9V45 1T | 9V45 4T |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| GF(2^128) product, scalar PCLMULQDQ (Flock x86 `Mul`) | ns/product | 5.09 | 2.49 | 4.63 | 2.32 | 4.19 | 1.99 | 2.65 | 1.4 |
| GF(2^128) product, xmm-resident PCLMULQDQ | ns/product | 3.77 | 1.85 | 2.29 | 1.2 | 3.29 | 1.57 | 2.84 | 1.36 |
| GF(2^128) product, ymm VPCLMULQDQ, 2 per insn (schoolbook) | ns/product | 1.89 | 0.853 | 0.997 | 0.447 | 1.65 | 0.762 | 1.43 | 0.655 |
| same, Karatsuba | ns/product | 1.58 | 0.739 | 1.02 | 0.433 | 1.41 | 0.607 | 1.19 | 0.58 |
| same, by a constant (NTT twiddle / fold challenge) | ns/product | 1.57 | 0.786 | 0.83 | 0.34 | 1.38 | 0.6 | 1.19 | 0.555 |
| GF(2^128) product, zmm, 4 per insn (Flock `ghash_mul_x4`) | ns/product | — | — | 0.742 | 0.317 | 0.917 | 0.358 | 0.715 | 0.289 |
| multiply-accumulate, delayed reduction, scalar (Flock) | ns/product | 2.82 | 1.44 | 1.99 | 0.916 | 2.48 | 1.14 | 1.92 | 0.882 |
| multiply-accumulate, delayed reduction, ymm | ns/product | 1.26 | 0.562 | 0.652 | 0.233 | 1.1 | 0.5 | 0.955 | 0.43 |
| multiply-accumulate, delayed reduction, zmm (Flock `WideGhashX4`) | ns/product | — | — | 0.428 | 0.135 | 0.552 | 0.2 | 0.482 | 0.207 |
| K x F product, K = GF(2^256), ymm | ns/product | 3.77 | 1.74 | 1.96 | 0.836 | 3.33 | 1.48 | 2.85 | 1.27 |
| K x K product, ymm | ns/product | 6.43 | 3.19 | 5.31 | 2.51 | 5.76 | 2.63 | 4.64 | 2.32 |
| eq table, 2^22 entries, ymm | ns/entry | 1.65 | 1.14 | 1.53 | 0.876 | 1.44 | 0.895 | 1.21 | 0.769 |
| ring switch s_hat_v, F x packed-GF(2) (1 claim, four Russians) | ns/packed elem | 33.4 | 13.3 | 51.8 | 21.7 | 28.9 | 11.8 | 17.8 | 8.32 |
| same, 2 claims | ns/packed elem | 39.3 | 17.4 | 109 | 44.1 | 34.1 | 15 | 22.3 | 10.5 |
| ring switch rs_eq_ind (16 byte tables) | ns/packed elem | 7.07 | 4.13 | 6.87 | 3.44 | 6.83 | 3.67 | 4.68 | 2.41 |
| additive NTT, RS rate 1/2, 64 lanes x 2^20: scalar PCLMULQDQ (Flock on Zen 3) | ns/butterfly | 4.84 | 2.41 | 4.52 | 1.98 | 4.12 | 2.07 | 3.18 | 1.68 |
| same, ymm radix-4 | ns/butterfly | 2.02 | 1.01 | 1.67 | 0.76 | 1.77 | 0.869 | 1.42 | 0.746 |
| same, zmm radix-8 (Flock AVX-512 kernel shape) | ns/butterfly | — | — | 1.4 | 0.637 | 1.41 | 0.694 | 0.967 | 0.495 |
| same, ymm, 64 x 2^16 | ns/butterfly | 1.95 | 1.02 | 1.36 | 0.678 | 1.69 | 0.866 | 1.47 | 0.762 |
| same, ymm, 16 lanes x 2^22 | ns/butterfly | 2.13 | 1.1 | 1.73 | 0.811 | 1.85 | 0.978 | 1.44 | 0.77 |
| zerocheck round 1 (64-pt univariate skip), Flock Zen-3 path | ns/compression | 64,635 | 19,801 | 74,202 | 26,434 | 54,478 | 17,009 | 57,464 | 16,605 |
| same, AVX2 + VPCLMULQDQ-256 port | ns/compression | 8,776 | 4,354 | 8,867 | 4,139 | 7,024 | 3,621 | 5,698 | 2,577 |
| zerocheck round 2 (fold at z + message), Flock Zen-3 path | ns/compression | 3,293 | 1,535 | 2,096 | 1,014 | 2,617 | 1,207 | 2,021 | 1,023 |
| same, ymm | ns/compression | 2,009 | 1,043 | 1,269 | 719 | 1,748 | 765 | 1,289 | 621 |
| zerocheck rounds 3.. (fold + message), Flock Zen-3 path | ns/index | 12.9 | 6.46 | 11.9 | 5.62 | 11.3 | 5.58 | 7.99 | 4.24 |
| same, ymm fused | ns/index | 3.61 | 1.82 | 5.76 | 1.95 | 3.14 | 1.54 | 2.68 | 1.35 |
| Ligerito sumcheck round F -> K (fold + message), ymm | ns/input elem | 7.24 | 3.71 | 8.7 | 3.52 | 6.38 | 3.04 | 5.22 | 2.72 |
| Ligerito sumcheck round K -> K, ymm | ns/input elem | 10.4 | 5 | 15.5 | 6.18 | 8.52 | 4.02 | 6.94 | 3.56 |
| lincheck: pack z into stripes | ns/compression | 275 | 186 | 275 | 167 | 248 | 153 | 196 | 130 |
| lincheck: partial fold of z over the batch (sum tables) | ns/compression | 1,133 | 672 | 954 | 601 | 920 | 506 | 713 | 388 |
| sparse matrix fold (gather-XOR) | ns/nnz | 0.788 | 0.45 | 0.762 | 0.435 | 0.702 | 0.365 | 0.653 | 0.267 |
| BLAKE2s compression (chain) | ns/compression | 161 | 65.8 | 165 | 55.8 | 141 | 55.4 | 99.2 | 36 |
| BLAKE2s witness z, a, b (warm buffers) | ns/compression | 561 | 870 | 850 | 371 | 482 | 854 | 339 | 141 |
| same, fresh buffers (page faults inside) | ns/compression | 3,970 | 483 | 2,928 | 1,216 | 1,453 | 538 | 683 | 343 |
| memory copy, 256 MiB | ns/byte | 0.036 | 0.029 | 0.076 | 0.029 | 0.03 | 0.025 | 0.024 | 0.023 |

How to read the table:

- **4 vCPU are 2 cores.** 4T is 2–2.5× 1T on clmul-bound kernels.
- **The ymm tier on Zen 3 is 2.4–3.5× Flock's scalar PCLMULQDQ path.** Products: 0.74–0.79 ns
  against 2.49. NTT: 1.01 against 2.41 ns per butterfly. The zerocheck tail: 1.82 against 6.46.
- **Round 1 gains 4.5×** (4.35 µs against 19.8 µs per compression at 4T). Most of the gain comes
  from the byte-level kernels (table apply, transpose, GF(2^8) products), not the GF(2^128) ones.
- **The NTT** runs at about 1.0 ns per butterfly at every size from 2^22 to 2^26 elements. Rate
  1/2 at level 0 costs 128·(m − 13) butterflies per compression, 2,432 at m = 32.
- **zmm.** On the AVX-512 machines it halves the product and NTT costs against ymm (0.32 against
  0.79 ns per product, 0.64 against 0.76 ns per butterfly on the 8573C).
- **Noisy rows.** The witness rows with warm buffers are noisy at 4T. Their buffers are allocated
  by the main thread. The pipeline (§3) measures the witness at 280 ns per compression on the 7763
  at 4T. Use that figure.

## 3. End-to-end leaf pipeline (measured)

`kernels pipe:M[:USEFUL]` (`src/pipe.rs`) runs every per-witness-bit kernel above in protocol
order, on one set of buffers, with the best tier on the machine:

1. sequential chain;
2. parallel witness of z, a, b;
3. lincheck pack and partial fold;
4. round 1 (its C banks are the c-claim's `s_hat_v`);
5. round 2;
6. zerocheck tail rounds;
7. RS encode of level 0 (64 lanes, rate 1/2);
8. ring switch: two m − 7 eq tensors, the lincheck claim's `s_hat_v` (1-way), and `rs_eq_ind`
   for both claims;
9. the Ligerito sumcheck (one F→K round, then K→K to the end);
10. the level-1 encode (16 lanes; rate 1/4 approximated by a rate-1/2 encode of twice the message).

All buffers come from one arena of 7·2^(m−3) bytes, first-touched by 4 threads before the clock
starts. The time for that is reported separately: in the tree the arena is reused from leaf to
leaf; in the stream it is paid by each process. Challenges and tables are random.

**Not in the pipeline:** the service's Merkle and Fiat–Shamir hashing, the transcript, the
lincheck's per-proof matrix evaluation, queries and serialisation. They are costed in §4.

**Compute seconds per proof, 4 threads** (from `pipe-*.log`; three 7763 runs, one 8573C, one
9V74, four 9V45):

| Shape | 7763 | 8573C | 9V74 | 9V45 |
|---|---:|---:|---:|---:|
| leaf 2^18 (m = 32) | **3.73 / 3.76 / 3.86** | 3.58 | 3.02 | 2.11–2.28 |
| leaf 2^17 (m = 31) | 1.83 / 1.84 / 1.90 | 1.78 | 1.49 | 1.05–1.14 |
| leaf 2^16 (m = 30) | **0.97 / 0.98 / 1.01** | 0.88 | 0.80 | 0.52–0.58 |
| leaf 2^16, **1 thread** | 2.20 / 2.20 / 2.31 | 1.94 | 1.90 | 1.07–1.14 |
| node-shaped: m = 30, 43,008 useful compressions | **0.81 / 0.81 / 0.83** | 0.75 | 0.67 | 0.44–0.48 |
| arena alloc + first touch, m = 32 / m = 30 | 0.17–0.55 / 0.04–0.14 | 0.52 / 0.13 | 0.15 / 0.04 | 0.11–0.38 / 0.03–0.09 |
| peak RSS (`/usr/bin/time`), m = 32 / 31 / 30 | **3.81 / 1.91 / 0.96 GB** | same | same | same |

Throughput on the 7763 is 67.8k–70.4k compressions per second at m = 32 (14.2–14.7 µs per
compression).

**Per-compression breakdown, 7763, m = 32** (run 40502064046, `pipe-32.log`; ns per statement
compression = phase seconds / 2^18):

| Phase | ns / compression | share | Matches §2 (estimate check) |
|---|---:|---:|---|
| chain (sequential BLAKE2s) | 166 | 1 % | 161 ns × 1 |
| witness z, a, b | 283 | 2 % | — |
| lincheck pack + partial fold | 766 | 5 % | 186 + 672 |
| zerocheck round 1 | **4,390** | 31 % | 4,354 |
| zerocheck round 2 | 960 | 7 % | 1,043 |
| zerocheck tail | 840 | 6 % | (256 + 128 + …) indices × 1.82 ≈ 930 |
| NTT level 0 | 2,450 | 17 % | 2,432 butterflies × 1.01 |
| ring switch | **3,296** | 23 % | eq 2 × 128 × 1.14 + `s_hat_v` 128 × 13.3 + rs 2 × 128 × 4.13 = 3,051 |
| Ligerito sumcheck | 978 | 7 % | 128 × 3.71 (F→K) + (64 + 32 + …) × 5.0 (K→K) ≈ 1,110 |
| NTT level 1 | 200 | 1 % | — |
| **total** | **14,332** | | |

The additive model of §2 reproduces the pipeline within about 10 %. Memory and cache effects at
m = 32 do not change the picture.

## 4. The cost model against the caps

### 4.1 Per proof (EPYC 7763, 4 threads)

| Component | m = 32 leaf | m = 30 leaf (stream) | node (m = 30, 43k useful) | Tag |
|---|---:|---:|---:|---|
| compute (§3) | 3.73–3.86 s | 0.97–1.01 s | 0.81–0.83 s | measured |
| Merkle hashing in the service | 0.37 s | 0.09 s | 0.09 s | estimate (a) |
| moving codeword bytes to the service | 0.14–0.29 s | 0.04–0.07 s | 0.04–0.07 s | estimate (b) |
| Fiat–Shamir round trips, lincheck matrix walk, queries, serialisation, SIGN | ≤ 0.06 s | ≤ 0.06 s | ≤ 0.06 s | estimate (c) |
| node only: native child checks, trace parsing, M-region element zerocheck, T/L bits | — | — | ≤ 0.05 s | estimate (d) |
| **total per proof** | **4.24–4.58 s** | **1.10–1.23 s** | **0.94–1.10 s** | |

Derivations:

- **(a) Service hashing.** Level 0 commits 4 KiB of codeword per statement compression (rate 1/2,
  2^14 bits). That is 4 Merkle leaves of 1 KiB (64 lanes × 16 B). Each leaf query is about 1,072 B
  (with its envelope), which is 18 keyed compressions (key block + 17). Add about 4 parent
  queries of 2 compressions, and about 7 % for levels ≥ 1. Total: about 85 BLAKE2s compressions
  per statement compression.
  - The service's throughput was measured on this 7763: 30.1M 64-byte calls/s on 4 threads
    (`logs/gh/40493470932/result-1/result-1.json`, `calls_per_s`), i.e. at least 60M
    compressions/s, about 16.6 ns each.
  - So 85 × 16.6 ns = 1.4 µs per statement compression.
  - The service shares the same 4 vCPUs, so this time is added, not overlapped.
- **(b) Transfer.** 4.3 KiB per statement compression through the socket, at an assumed 4–8 GB/s
  for large batches.
- **(c) Per-proof extras.**
  - about 200 sequential Fiat–Shamir queries at 20–50 µs each (4–10 ms);
  - the lincheck's matrix MLE by a circuit walk, O(10^5–10^6) XOR; the O(nnz) alternative is
    about 7·10^7 nnz × 0.45 ns = 32 ms at the measured gather rate;
  - about 1 MB of answers.
- **(d) Node only.**
  - 2 native child verifications of 1–3·10^5 products each (about 1 ms);
  - an element-row zerocheck over about 2^17.6 rows at about 30 products each (about 4 ms);
  - the T and L regions' 2^24.4 bits of GF(2) rows, about 1.3k compression-equivalents (about
    20 ms).

### 4.2 The tree (cap 600 s)

**64 × 2^18 leaves:** 64 × 4.24–4.58 s + 63 × 0.94–1.10 s + one arena (≤ 0.55 s) ≈ **330–365 s**.
The headroom is 1.65–1.8×.

Two alternative shapes:

- **128 × 2^17 leaves:** 128 × 2.08–2.28 s + 127 × 0.94–1.10 s ≈ 385–430 s. This is slower, and
  the leaf memory saving is not needed (§4.4).
- **On the AVX-512 runners**, with the same service and transfer estimates:
  - 8573C: 64 × (3.58 + 0.51–0.72) + 63 × (0.75 + 0.13–0.27) ≈ 320–340 s;
  - 9V74: about 290 s;
  - 9V45: about 215–240 s.

Nodes are about 20 % of the tree. Leaves are 80 %. Of the leaf time, round 1 and ring switching
are more than half (§3).

### 4.3 The stream link (about 3.1 s per link, start-ups included)

| Request | 7763 | 8573C | 9V74 | 9V45 |
|---|---:|---:|---:|---:|
| leaf 2^16: start-up and setup load (≤ 0.05, estimate) + arena (0.04–0.14) + compute + service and transfer + extras | 1.14–1.42 s | 1.31 s | 1.10 s | 0.80–0.92 s |
| node merge: the same + node extras | 0.98–1.29 s | 1.22 s | 0.97 s | 0.72–0.84 s |
| **link** | **2.1–2.7 s** | **2.5 s** | **2.1 s** | **1.5–1.8 s** |

The cap is met on every model. **On the 7763 the margin is at least 13 %** (at the pessimistic
end of every estimate). This is the binding cap of FR-R5. The arena's page-fault time varies threefold between 7763 hosts: 0.04–0.14 s at m = 30.
Setup objects (tables, twiddles) cost 3–8 ms to build (`setup` line of `pipe-*.log`), so they can
also be rebuilt per process.

### 4.4 Memory (cap 11 GiB)

- **Measured.** The m = 32 pipeline's peak RSS is 3.81 GB: the arena of 7·2^29 B = 3.5 GiB plus
  small buffers. At m = 31 it is 1.91 GB, and at m = 30 0.96 GB.
- **Not in the pipeline** (estimate): the Merkle digests (2^(m−12) × 2 × 32 B = 64 MiB at m = 32),
  query answers and socket buffers, about 0.2 GB. The service has its own 2 GiB cgroup.
- **Estimate for a full m = 32 prover:** ≤ 4.5 GB, a 2.4× margin.
- **Larger leaves.** An m = 33 leaf (2^19 compressions) would also fit (about 7.6 GB). It would
  cut the node count to 31, but it moves the extractor's fuel the wrong way (T §4.3), so it is not
  proposed.

### 4.5 Contrast: Flock's own kernels on Zen 3 (estimate from measured kernels)

This replaces in §3's breakdown the phases where Flock's Zen-3 path differs from the ymm path, at
the measured flock-zen3 rates (7763, 4T):

| Phase | Flock Zen-3 path | Instead of (ymm) |
|---|---:|---:|
| round 1 | 19.8 µs | 4.4 µs |
| round 2 | 1.5 µs | 0.96 µs |
| tail | 6.46 ns × 256 = 1.65 µs | 0.84 µs |
| NTT | 2,432 × 2.41 ns = 5.85 µs | 2.45 µs |
| Ligerito | about 2.4 µs (scalar products at 2.5× the ymm cost) | 0.98 µs |

The ring switch, the lincheck and the witness use the same code in both.

Total: **about 36 µs per compression, about 28k compressions/s.** The tree's leaves alone take
2^24 × 36 µs ≈ 600 s, before nodes and service hashing: **infeasible**. This agrees with
F-flock's estimate of 21–42k/s (F §6.3). **The ymm tier is the difference between infeasible and
feasible on the 7763.**

### 4.6 Sensitivity

- **Node size.** Each extra 10k useful compressions in the node adds about 0.065 s of PIOP work
  (about 6.4 µs per compression for witness, lincheck and zerocheck, §3).
  - While the node commits at most 2^30 bits (about 60k compressions with T's other regions,
    +40 % over T), it stays at m = 30 and the link stays within about 2.4–2.8 s.
  - Past that, the node becomes m = 31: its PCS roughly doubles. A node of twice T's size, about
    86k compressions, takes about 1.9 s. That gives about 400 s for the tree (still within the
    cap) and **about 3.1–3.4 s per link, at or over the stream cap**.
  - So the stream needs the node to fit m = 30.
- **"2^26 GF(2^128)-product constraints" read as rows.** That is 2^26 rows × 3 elements × 128 bits
  = 2^34.6 committed bits.
  - Commitment: 2^20.6 compression-equivalents × the about 9 µs of commitment work (NTT, ring
    switch, Ligerito, service hashing) per 2^14 committed bits ≈ 15 s.
  - Element zerocheck: about 1 s.
  - About 16 s per node; arena about 30 GB.
  - **Infeasible** on time and memory. T's count (M ≈ 2·10^5 rows, 2^26.2 bits) is the one this
    verdict assumes.
- **Service hashing.** If the service ran at the 1-thread rate only (10.2–11.2M calls/s), (a)
  would be about 3× larger: +0.7 s per m = 32 leaf, +45 s per tree, +0.18 s per link. That still
  fits the tree but **not the stream on the 7763**.

## 5. What to do with it (recommendations for B and P)

1. **The prover needs three dispatch tiers:**
   - AVX-512 + VPCLMULQDQ (+ GFNI): Flock's x86 kernels, behind `#[target_feature]`;
   - **AVX2 + VPCLMULQDQ-256: this probe's kernels**, the tier of record for the 7763;
   - portable, for development only.

   Size every budget on the 7763.
2. **Use 64 leaves of 2^18 in the tree** (§4.2, §4.4), and pre-fault one arena reused across
   leaves.
3. **Widen the stream margin.** These are implementation changes; none touches the protocol, and
   all savings are estimates:
   - **Round 1, about 31 % of the leaf.** Move GF(2^8) into a GF(16)² tower basis and multiply
     by `vpshufb` log/exp. The basis change folds into the round-1 byte table and the convert
     table, so it is free. This replaces about 56 ymm ops of bit-serial multiply per 32 products
     with about 35. Estimate: −20 to −35 % of round 1.
   - **`s_hat_v`, 13 ns per packed element.** The scalar four-Russians loop could get a
     transposed SIMD form.
   - **The witness.** Multi-buffer (8-lane AVX2) BLAKE2s, since the chain values are known after
     the cheap sequential pass.
   - **On AVX-512 runners**, Flock's GFNI round-1 kernels.
4. **Keep the node circuit at m = 30**: about 60k compressions with T's other regions, +40 % over
   T's 43k, and about 2·10^5 product rows (§4.6). Measure B's exact node count against this
   budget.
5. **Re-measure the service.** A real prover with a service in the loop is the next measurement.
   It replaces estimates (a)–(c).

## 6. Limits of the probe

- **Partial kernels.** The probe measures kernels and a pipeline skeleton, not a prover.
  - The zerocheck and the Ligerito sumcheck do not draw challenges from a transcript; their
    challenges are random.
  - Ligerito's levels ≥ 1 are approximated by continuing the K→K rounds and one 16-lane encode.
  - No query phase is run.
- **The node** is modelled as an m = 30 commitment carrying 43,008 BLAKE2s compressions of
  witness. Its element-row and trace regions are estimated (§4.1 (d)).
- **zmm coverage.** The zmm tier covers products, MAC and the NTT. On AVX-512 runners the other
  kernels run the ymm code, so the AVX-512 columns are upper bounds for a full AVX-512 tier.
- **Round 2 and the tail** process only the useful prefix (Flock's padding skip). The ring switch
  and the PCS run at full size.
- **Untimed builds.** The build is `-C target-cpu=znver3` on AMD, with the kernels behind run-time
  checks (`native` on the 8573C, which lacks `sse4a`). A `prover.s` at `x86-64-v3` with the same
  `#[target_feature]` kernels compiles the same hot loops. That claim is not measured.
- **Branches.** `probe/kernels-1` … `-12` remain on origin (probe workflow only). They can be
  deleted.
