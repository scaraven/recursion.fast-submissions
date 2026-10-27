# F2-golf: execution-time golf of the `spartan-srom` native prover — RESULT, 2026-10-23

Status: **done; not committed** (the orchestrator commits). Base: commit `f8f7c1e` (stage F2,
before review). Files changed: `submissions/spartan-srom/prover/*` only (no Lean, no format, no
verifier change). Every output of the golfed prover is **byte for byte** the pre-golf prover's
(§3): the leaf `π` under v3's and the keyed oracle at 12 sizes up to `n = 65536`, the v3 KAT dumps,
and every file of the smoke tree and stream **including the signatures** (against a service with
fixed test keys, so the `SIGN` order is checked too).

Logs are under the worktree's `logs/golf/` (gitignored; written `G/` below). The machine is the
shared 32-vCPU QEMU VM without `pclmulqdq`, with a load average of 6–22 from other agents during the
runs; every timing is a median of interleaved (ABAB…) runs of the binaries compared, at most 16
threads, every run under a `timeout`. **All timings are of the portable field product**: the
runners multiply with `pclmulqdq`, which cannot be timed here (QEMU TCG checks its correctness
only, §3 item 5). §4.4 gives a cost model of the runner's case (a profiling-only build whose field
product is an integer multiply).

**Result** (final binary against the base, interleaved; §4):

| | base | golfed | |
|---|---|---|---|
| smoke tree `T_tree` (`r = 2, n = 16`), 16 / 4 threads | 0.879 / 0.807 s | **0.131 / 0.184 s** | 6.7× / 4.4× |
| stream `t_leaf` (`n_f = 16`), 16 / 4 threads | 0.194 / 0.191 s | **0.055 / 0.061 s** | 3.5× / 3.1× |
| stream `t_merge` (`M = 4`), 16 / 4 threads | 29.8 / 29.2 ms | **21.1 / 17.1 ms** | 1.4× / 1.7× |
| leaf `n = 1024 … 16384`, 16 threads (prove + trace) | 1.07 … 13.7 s | **0.29 … 5.3 s** | 3.7× … 2.6× |
| leaf `n = 1024 / 4096`, 4 threads | 2.49 / 9.37 s | **0.73 / 2.75 s** | 3.4× |
| peak RSS of a leaf at `n = 2^16` | 15.77 GB | **2.59 GB** | under the 11 GiB cap |

The harness run of stage F3 measured the pre-golf prover at the smoke shape through the real
badge at **T_tree 0.896 s, t_leaf 0.251 s, t_merge 0.037 s** (its `t_leaf` divides `M + 1` leaves
by `M`, F2 RESULT §6 item 6); the harness has not been rerun with the golfed prover. With this
document's driver, `S = T_tree + 20·(t_leaf + t_merge)` goes from 5.36 to 1.65 at 16 threads.

The changes, in the order they were made (§2): a persistent thread pool; the trace written by the
prover instead of a verifier replay; the tree's leaves proved at once; the inner sumcheck summed
over the blocks first (Flock §4.1); the outer sumcheck with `h(1)` from the claim, a zerocheck round
0, tables made after round 6 instead of 3, bucketed lookup rounds and a bit-sliced round 1; the
node request built from the files in place while the service signs; a polled connection for the
Fiat–Shamir queries; a bit-sliced witness; a premapped heap; the FFT's factors once per leaf;
memory freed early; the tree's width by a memory budget.

## 1. Method

- Base binary rebuilt from `f8f7c1e` with `build-asm.sh` (`G/base/`, same `prover.s` SHA-256
  `13544017…` and binary `30b46975…` as F2's RESULT §2).
- Each change was built as its own assembly binary (`G/mk.sh NAME` → `G/steps/NAME/`, the
  submission's recipe) and measured against the previous step with `G/ableaf.py` (leaf: `bench-leaf
  --oracle keyed`), `G/absvc.py` (leaf through the service), `G/abshapes.py` (the smoke tree and
  stream, ready/go/done as the runner drives them) and `G/abtree.py` (`tree` only), all
  interleaved. Ablations (`LATE`, buckets, the split transpose) were built from the same tree with
  one edit (`PATCH=` in `mk.sh`).
- Proof bytes were compared after every change (`G/eq-leaf.sh` + `G/cmp.sh` against `G/ref/`, the
  base binary's outputs), and `abshapes.py` compares every output file of every binary with the
  first binary's (base) in every round.
- A change that did not pay measurably was dropped (§2.15).

## 2. The changes

Lines are added/removed against `f8f7c1e` (`git diff --numstat`); the per-change measurements are
each against the previous step (`G/ab/*.log`). `n = 16` is the smoke shape (`r = 2`, `M = 4`).

### 2.1 `pool`: a persistent thread pool (`par.rs`, +195 −44 with 2.3)

v3's `par.rs` spawned threads (`std::thread::scope`) for every parallel call; a leaf makes a few
hundred such calls, so at `n = 16` sixteen threads were no faster than one. Now one pool of
`threads() − 1` workers is started once; a call posts a job of chunks, the caller works on it too,
idle workers take chunks of any posted job (so concurrent leaves share the workers, and a chunk may
itself call in parallel). Results are unchanged by construction: every sum is an XOR.
Leaf `n = 16`, 16 threads: prove **0.146 → 0.106 s** (`G/ab/c1-n16-t16.log`).

### 2.2 `trace`: the prover writes the verifier's trace (`prover.rs`, `transcript.rs`, `make.rs`, `oracle.rs`)

The trace of a leaf is the verifier's queries in order: the transcript's queries (the verifier
repeats them from `π`), then per opened column its leaf query and its `ℓ_N` path queries. The
transcript now records each query with its answer (`Transcript::traced`), the Merkle tree keeps the
whole answers of every level (it kept their 31-byte labels), and `Merkle::open_trace` writes a
column's queries. The native verifier is no longer replayed per leaf (0.04 s at `n = 16`, 0.22 s at
`n = 1024`); `SPARTAN_REPLAY=1` still replays it and fails unless its trace equals the prover's
(§3.3), and the unit tests do so for `n = 1, 2, 3, 16`. The `Recorder` then only counts (no
fingerprints, no table). Leaf `n = 16`, 16 threads: total **0.139 → 0.100 s** (`G/ab/c2-n16-t16.log`).

### 2.3 `tree`: the tree's leaves proved at once (`main.rs`)

`tree` proves `w` leaves at a time on the shared pool and signs them **in leaf order** on the main
thread while later leaves are still proved, then the nodes as before, so the `SIGN` calls come in
the base's order (and the files, signatures included, are the base's; §3.2). `w` is the threads,
within 8 GiB at `32 MiB + 64 KiB·n` per leaf (2.14); `SPARTAN_TREE_WIDTH` overrides.
Smoke tree, 16 threads: **T_tree 0.684 → 0.261 s** (`G/ab/c3-shapes.log`, base 0.908 s).

### 2.4 `inner`: the inner sumcheck sums over `t'` first (`sumcheck.rs`)

Flock §4.1's block-diagonal collapse, in the order this protocol binds variables (`j` first): on
`top = 0` the table is `Σ_i P_i(j)·γ_i(t')`, so with `Z_i(j) = Σ_{t'} γ_i(t')·z(j, t')` the first 14
rounds are a sumcheck of `Σ_i P_i·Z_i` over `2^14` entries, whatever `n`. `Z_i` is one pass of
additions over the bits of `w` (`fold_blocks`); `z̃(r_{<14}, t')` for the last `κ + 1` rounds is
another (sums of `eq(r_{<14}, ·)` over each block's bits). Before, every round touched all `2^{14+κ}`
entries. `P_1`, `P_2` and the public tables are folded only on their supports (`fold_range`).
A round polynomial is unique, so the bytes cannot change. Inner sumcheck, 16 threads:
**38 → 20 ms** at `n = 16`, **166 → 24 ms** at `n = 1024` (`G/ab/c4-n{16,1024}-t16.log`).
Later (2.10) the four dense tables sit side by side and each round is one parallel pass that folds
them and sums the next round.

### 2.5 `outer`: the outer sumcheck rewritten (`sumcheck.rs`, `field.rs` `E::inv`)

Four independent ideas, measured together (`G/ab/c5-n{16,1024,4096}-t16.log`):

- **`h(1)` from the claim.** `g(0) + g(1)` is the claim, so only `h(0)` and `h(∞)` are summed and
  `h(1) = (claim + (1 + τ_l)·prefix·h(0)) / (τ_l·prefix)` (`τ_l^{-1}` by one batch inversion). If some
  `τ_l = 0` that round sums `h(1)` too (unit test `outer_with_zero_tau`). The same in the inner and
  the product sumchecks (no inversion there: `g(1) = claim − g(0)`).
- **Zerocheck round 0.** `A·B = C` on the cube (the honest witness), so `h(0) = h(1) = 0` in round
  0, and `h(∞) = Σ eq·[(a₀⊕a₁)(b₀⊕b₁)]` is a sum of `eq` over the set bits of one word expression.
- **Late tables.** v3 materialised the three tables over `E` after round 3 (`3·2^{ℓ−4}` entries,
  9.7 GB at `n = 2^16`) and folded them with byte tables of the challenge (24 lookups per entry).
  Now rounds 3…6 read `A(r_{<l}, X, y)` from the bit tables through byte tables of the linear map
  `p ↦ Σ_b p_b eq(r_{<l}, b)` (`lin`), and the tables are made after round 6 (`LATE = 7`,
  `3·2^{ℓ−7}` entries). `LATE = 6` and `8` are slower (§2.15).
- **Parallel by ranges of `y`**, not by blocks of the high `eq` table (at `n = 16` rounds ≥ 6 ran on
  one thread), and the `eq` split balanced so a round builds `O(2^{rem/2})` entries.

Outer sumcheck, 16 threads: **44 → 15 ms** (`n = 16`), **463 → 263 ms** (`1024`), **1.64 → 1.01 s**
(`4096`); peak RSS of a leaf **266 → 62 MB** (`1024`), **1.06 GB → 226 MB** (`4096`).

### 2.6 `rounds`: bucketed lookup rounds; `g(1)` in the product sumcheck (`sumcheck.rs`)

In rounds 3…6, `Σ_y e·A·B = Σ_{g,p} T_g[p]·Σ_{y: A's byte g = p} e·B`: the bytes of `A`'s pattern
index buckets of `e·B`, `C`'s bytes buckets of `e`, and the buckets are combined once per range of
`y` (2 products per `y` instead of 4). Per-round times at `n = 4096`, 16 threads: round 3
**494 → 215 ms**, round 4 **222 → 130 ms**, round 5 **116 → 74 ms** (`SPARTAN_VERBOSE=2`).
The product sumcheck (ring switch, inner phase 2) drops `g(1)` as in 2.5.
Measured on its own (16 threads, `G/ab/c6-n{1024,4096}-t16.log`): leaf **0.435 → 0.397 s** at
`n = 1024` (outer 255 → 198 ms, ring switch 43 → 37 ms), **1.624 → 1.341 s** at `n = 4096` (outer
1.008 → 0.710 s).

### 2.7 `merge`: the node request built from the files in place (`make.rs` `view`, `node_files`; `service.rs`)

The `node` request no longer parses the two files into vectors of entries, clones the traces and
re-serialises: `view` reads a file in place (strictly, as `from_file`), the `SIGN` body is built
from the entries' bytes and sent (`Service::sign_start`), and the output file (`π = encode W ‖ T₁ ‖
T₂`, the entries copied) is built while the service hashes (`sign_finish`). The plain node
(`n = 0`, mixed `σ0`) keeps the old path. Smoke stream, 16 threads: **t_merge 36.1 → 24.5 ms**
(`G/ab/c7-shapes.log`).

### 2.8 `pieces`: the file written during `SIGN`; large `eq` blocks for bucketed rounds

The node's file up to the signature is also written while the service signs, the signature
appended after. The bucketed rounds (1, 2, 3…6) combine their buckets once per block of the low
`eq` table, so they use the largest low table (12 variables) instead of the balanced split, and a
range too short for the buckets to pay is summed directly. Smoke stream, 16 threads: **t_merge 24.8
→ 19.7 ms**, t_leaf 73.4 → 68.9 ms (`G/ab/c8-shapes.log`).

### 2.9 `fs`: the Fiat–Shamir queries on their own polled connection (`service.rs` `ask`)

The 153 sequential transcript queries of an `n = 16` leaf each waited for a wake-up after the
service's answer. `ask` now has its own non-blocking connection and polls it (a short spin, then
`yield_now`), reading header and answer in one call. Fiat–Shamir time per leaf, 4 threads:
**9.6 → 5.6 ms**, leaf total 74.3 → 65.6 ms (`G/ab/c9-fs-n16-t4.log`); at 16 threads 7.9 → 5.8 ms
with the total unchanged within noise (`…-t16.log`). Smoke stream at 4 threads: t_leaf **76.9 →
69.7 ms** (`G/ab/c11-shapes-t4.log`). The poll uses one CPU while a leaf waits; on the 4-vCPU
runners nothing else of the prover runs then (the transcript is sequential).

### 2.10 `cpu`: bit-sliced witness, one pass per inner round, pool before `ready`

- `Circuit::trace64` runs the gadget program on 64 blocks at once (`u64` lanes) and transposes the
  results with 64 × 64 bit transposes; the witness at `n = 4096` takes **0.165 → 0.032 s**
  (`G/ab/c5-n4096-t16.log`, `G/ab/c12-n4096-t16.log`). Unit test `trace64_equals_trace`.
- The inner sumcheck's dense tables `(P_0, Z_0, Z_1, Z_2)` side by side; one parallel pass per round
  folds them and sums the next round (`sum_pairs`, `par::map_chunks_mut`).
- `leaf` and `node` start the pool's workers before `ready`.
Leaf `n = 16`, 4 threads: **53.7 → 51.2 ms** (`G/ab/c10-n16-t4.log`).

### 2.11 `heap`: no page faults in a request (`main.rs` `heap_setup`)

A fresh `leaf` process faulted in about 2,100 pages per `n = 16` proof. Before `ready`, `leaf` and
`node` set glibc's `mallopt` (one arena, no trimming, the 32 MiB `mmap` threshold) and map 64 MiB
of heap; the request's allocations then reuse mapped pages (30 faults per leaf). `tree` and
`bench-leaf` set the options (no premapping in `tree`, which is timed from its start). Leaf `n = 16`,
4 threads: **51.2 → 46.9 ms** (`G/ab/c10-n16-t4.log`); smoke stream at 4 threads: t_leaf **69.7 →
63.2 ms** (`G/ab/c11-shapes-t4.log`).

### 2.12 `rounds1`: round 1 bit-sliced; two copies of the round-1/2 buckets; the FFT's factors once

- Round 1: with `r = r_0`, `A(r, 0, y) = a₀₀ + r·δa` etc., so (with `A·B = C` on the cube) `h(0)`
  and `h(∞)` are `r`- and `r²`-weighted sums of `eq` over five bit masks of each word.
- Round 2 keeps buckets, two copies for even and odd `y` (independent updates).
- `Code::twiddles`: the factors `W_i(ω_{off+s})` of the additive FFT were recomputed for each of
  the `m` rows; now once per leaf.
Leaf, 4 threads, `n = 1024`: **0.906 → 0.813 s** (encode 176 → 120 ms); 16 threads, `n = 4096`:
**1.193 → 1.133 s** (`G/ab/c12-*.log`; the `n = 16` run of that log, 72 → 48 ms, had a noisy base).
Round 1 alone, cost model of §4.4 at `n = 1024`: **32–48 → 6–7 ms**; encode there **76 → 33 ms**
(`G/ab/fakemul2-n1024-t4.log`).

### 2.13 `mem`: bit tables freed after the outer sumcheck made its tables; `eq(r_hi)` after `Φ`

The bit tables `A`, `B`, `C` (768 MB at `2^16`) are freed one by one as their `E` tables are made,
and `eq(r_hi)` once `Φ` of it is taken. Peak RSS at `n = 65536`: **3.02 → 2.59 GB**
(`G/out-65536/c12.log`, `c13.log`).

### 2.14 `width`: tree width by a memory budget

With the leaves' memory down, proving 4 leaves at once beats one at a time at every `n` measured
(`G/ab/width-*.log`, `r = 2`, 16 threads): T_tree **0.262 → 0.145 s** (`n = 16`), **1.37 → 0.96 s**
(`1024`), **4.16 → 3.09 s** (`4096`), **16.5 → 13.9 s** (`16384`); at 4 threads, `n = 16`: **0.286
→ 0.185 s**. The width rule of 2.3 replaces F2-era thresholds (which proved one leaf at a time
above `n = 4096`).

### 2.15 Tried and dropped

| Change | Result | Log |
|---|---|---|
| leaf file written during its `SIGN` (as 2.8 for the node) | stream t_leaf 61.3 vs 63.8 ms, within noise | `G/ab/c14-shapes-t4.log` |
| the transposed walk split in its `A` and `B` halves on two threads | inner set-up 3.7 → 4.1–4.4 ms (slower) | (profiling run) |
| rounds 3…6 without buckets (4 products per `y`) | round 3: 48 → 82 ms, round 4: 29 → 55 ms (cost model of §4.4) | (profiling run) |
| `LATE = 6` / `8` | `n = 16384` outer 2.63 / 2.49 s vs 2.30 s at `LATE = 7` | `G/ab/late-n{4096,16384}-t16.log` |

## 3. Equality checks (the final linked binary `G/final-prover`, SHA-256 `d6aaa228…`)

1. **Leaf `π` and statement** (`prove-leaf`) under v3's oracle and under the keyed oracle, at
   `n = 1, 2, 3, 5, 16, 17, 64, 100, 1024, 4096, 16384`, and keyed at `65536`: identical to the base
   binary's (`G/ref/`). With the 11 KAT dumps (`dump-field`, `-circuit`, `-walk`, `-encode`, `-mle`,
   `-phi`, `-sumcheck`, `-transcript`, `-transcript-ops`, `-proof`, `-leaf-trace`): **59 of 59
   identical** (`G/eq-final.log`).
2. **Signed files.** `abshapes.py` runs the smoke tree (`r = 2, n = 16`) and stream (`M = 4`)
   against a service started with `--insecure-test-keys` for every binary, and compares all 24
   output files (4 `L`, 2 `N1_j`, `root.bin`, 5 stream leaves, 4 stream nodes, and the copies) with
   the base's in every round: identical, **signatures included**, so the `SIGN` calls are made in
   the same order. The base's tree outputs are accepted by `verify-native`.
3. **Replay.** With `SPARTAN_REPLAY=1`, `bench-leaf --oracle service` replays the native verifier
   against the prover's answers and fails unless its trace equals the one the prover wrote:
   passes at `n = 1, 2, 3, 16, 17, 64, 1024` (`G/replay-final.log`).
4. **Selftest against the real service** (`selftest.py tree stream keyed-kat sizes`, `G/selftest-final.log`;
   `--n 0 tree stream`, `G/selftest-final-n0.log`): every output accepted by `verify-native`,
   every canary rejected (9 canary sets), the keyed oracle equal to the service at `n = 1, 16, 64`,
   `selftest: pass`.
5. **The `pclmulqdq` path** under `qemu-x86_64` TCG (`G/qemu-final.log`): `selftest-field 50000`
   passes with `-cpu Haswell` and `-cpu max`; the leaf proofs at `n = 1, 16, 64` (v3 oracle) are
   identical to the base's with `-cpu Haswell`, `-cpu Haswell,pclmulqdq=off` and `-cpu max`.
6. `cargo test --release`: **31 pass** (27 of F2, plus `nested_and_concurrent_calls`,
   `outer_with_zero_tau`, `transpose64_is_the_transpose`, `trace64_equals_trace`; `E::inv` in
   `e_field_laws`) (`G/cargo-test.log`).

## 4. Measurements (final binary `G/steps/final/prover` = `G/final-prover` against `G/base/prover`)

All interleaved; loads 9–20 (`G/ab/final-*.log`, `G/final-timings.log`).

### 4.1 The runnable shapes (`G/abshapes.py`, 5 rounds, `r = 2, n = 16, M = 4`)

| | 16 threads base | 16 threads golfed | 4 threads base | 4 threads golfed |
|---|---|---|---|---|
| `T_tree` (spawn to exit of `prover tree`) | 0.8794 s | **0.1305 s** | 0.8074 s | **0.1835 s** |
| `t_leaf` (median of the 25 leaf requests, go → done) | 0.1939 s | **0.0552 s** | 0.1912 s | **0.0612 s** |
| `t_merge` (median of the 20 node requests) | 29.8 ms | **21.1 ms** | 29.2 ms | **17.1 ms** |

`G/ab/final-shapes-t16.log`, `G/ab/final-shapes-t4.log`; every output file identical to the base's
in every round. What is left (one verbose stream run, 16 threads, `G/st-final-verbose.log`): a
leaf request is proving 49–56 ms (one outlier 95 ms) including the 153 sequential Fiat–Shamir
round trips (5.1–7.2 ms), then `SIGN` 4–9 ms; a merge is reading the files 0.4–1.1 ms, building
and writing 3–6 ms, and waiting for the service's `SIGN` of the concatenated trace 6–18 ms of
10–26 ms.

### 4.2 The leaf (`bench-leaf --oracle keyed`; the base's total includes its verifier replay)

| `n` | threads | base total (replay) | golfed total | × | outer | inner | witness | encode | peak RSS |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 16 | 0.1760 s (0.040) | **0.0390 s** | 4.5 | 56.5 → 14.0 ms | 54.0 → 15.0 ms | 4.0 → 1.0 ms | 3 → 2 ms | 8.9 → 67 MB¹ |
| 1,024 | 16 | 1.068 s (0.228) | **0.292 s** | 3.7 | 459 → 160 ms | 190 → 20 ms | 43 → 8 ms | 46 → 39 ms | 265 → 67 MB¹ |
| 4,096 | 16 | 3.480 s (0.442) | **0.980 s** | 3.6 | 1.768 → 0.606 s | 0.593 → 0.038 s | 0.159 → 0.032 s | 0.217 → 0.148 s | 1,008 → 181 MB |
| 16,384 | 16 | 13.678 s (1.026) | **5.343 s** | 2.6 | 7.26 → 3.34 s | 2.50 → 0.10 s | 0.80 → 0.16 s | 1.18 → 0.95 s | 3,961 → 656 MB |
| 16 | 4 | 0.1692 s (0.038) | **0.0446 s** | 3.8 | 59 → 18 ms | 50 → 16 ms | 4 → 1 ms | 3 → 2 ms | |
| 1,024 | 4 | 2.490 s (0.221) | **0.733 s** | 3.4 | 1.348 → 0.480 s | 0.493 → 0.027 s | 105 → 11 ms | 138 → 113 ms | |
| 4,096 | 4 | 9.373 s (0.443) | **2.752 s** | 3.4 | 5.60 → 1.86 s | 1.78 → 0.06 s | 0.44 → 0.05 s | 0.59 → 0.47 s | |

¹ `bench-leaf` premaps 64 MiB of heap (2.11); the leaf itself needs less.
Medians of 4 × 5 (`n = 16`), 3 × 3 (`1024`), 3 × 2 (`4096`), 2 × 1 (`16384`) runs
(`G/ab/final-n{16,1024,4096,16384}-t{16,4}.log`).

### 4.3 Memory at `n = 2^16` (`prove-leaf --oracle keyed:…`, 16 threads, `/usr/bin/time -v`)

| | wall | peak RSS | log |
|---|---|---|---|
| base | 41.16 s | 15,765,352 kB | `G/ref-65536.log` |
| golfed | 16.49 s | **2,585,312 kB** | `G/final-65536.log` |

Single runs, not interleaved (the base needs 15.8 GB). Where it goes now: the encoded rows (`m·N`
words, 1 GB), the outer sumcheck's tables made after round 6 (`3·2^{ℓ−7}` elements of `E`, 1.2 GB,
while the bit tables are freed one by one) and the witness bits.

### 4.4 A cost model of the runners (`pclmulqdq`): integer-multiply field product

The runners multiply in `GF(2^64)` with `pclmulqdq`, about ten times cheaper than this VM's
portable product, so the share of everything else grows. A **profiling-only** build replaces the
portable carry-less product by an integer multiply (`(a·b) ⊕ a`, wrong values, similar cost to
`pclmulqdq`); the base's copy of it ignores its (failing) replay. Leaf, 4 threads (`G/ab/fakemul-*`,
`G/ab/fakemul2-*`; the golfed side is the state after 2.11, then after 2.12):

| `n` | base | after 2.11 | after 2.12 |
|---|---|---|---|
| 16 | 52.4 ms | 19.3 ms (17.0 in the second run) | 16.1 ms |
| 1,024 | 1.093 s | 0.353 s (0.327) | 0.262 s |

So the speed-ups hold, a little larger, in this model. What dominates there at `n = 16` (4
threads): the inner sumcheck about 7 ms (the serial transposed walk about 2 ms), the outer about
4 ms, Merkle 2 ms.


## 5. The assembly

| | |
|---|---|
| Command | `prover/build-asm.sh WORK` (unchanged recipe) |
| `prover.s` | **9,217,197 bytes, SHA-256 `ae9d7e5bb10768ba2f6b5121df9b6137b077f6ea8d55d97a2c0d974c438be6e9`** (base 8,699,228, `13544017…`) |
| Binary | 2,814,232 bytes, SHA-256 `d6aaa228998d24b8a0ea4de82f02621654b37dc518e3259a859dd68b1e4bd800` |
| Determinism | two clean builds (`G/final-a`, `G/final-b`): the same `prover.s` and the same binary (`G/determinism.log`) |
| Times | `build-asm.sh` wall 58.4 s and 57.1 s (`G/build-final-{a,b}.log`) |
| Content | no host path (`grep -c /home` = 0), no `.incbin`/`.include`, no `ymm`/`zmm`; 13 `pclmulqdq` (`field::hw`, unchanged) |

New in the binary: a call to glibc's `mallopt` (`extern "C"`, the binary is linked `-static` with
glibc as before) and non-blocking sockets (`std`).

## 6. Notes and open items

- **The runners' field product was not timed.** The changes cut multiplications (`h(1)` from the
  claim, buckets, the inner collapse), lookups (late tables replace the byte-table folds) and
  passes; §4.4's cost model suggests they carry over. Not tried, because not measurable here: the
  folds and `eq_table` multiply by a fixed challenge through 24 byte lookups (`ETab`) whatever the
  CPU; with `pclmulqdq` a plain product may be as fast.
- **16 vs 4 threads.** The polled Fiat–Shamir connection (2.9) pays at 4 threads and is neutral at
  16; on a loaded machine the spinning thread competes with the service.
- Memory at `n = 2^18` (the season's tree shape, above `proofCap` anyway) would be about 10 GB with
  `LATE = 7`; `LATE = 8` halves the outer tables.
- The serial transposed walk (about 1.6 ms of compute per leaf, 100,503 nodes) and the 153
  sequential Fiat–Shamir round trips are now a large part of an `n = 16` leaf.
- `circuit.rs` (leanerVM's circuit) gained `trace64` and `transpose64` beside the unchanged `trace`;
  `rs.rs` gained `twiddles`/`encode_k_tw` (`encode_k` is now a call of them).
