# Phase 0 M: the hard constraints at core `15dac52`, measured

Branch `v4/flock-recursive`, `.contract` at `15dac52` (core PR #18 head; V4-A9). Every number
below is **measured** and sits next to its log; logs are under `logs/phase0-M/` (gitignored).
Runs of 2026-10-27. Following the user's change of plan (GitHub runners are the benchmark of
record, the VM is for development), the certificate job was measured on GitHub (runs
`40493471459`, smoke, and `40493470932`, season, of `scaraven/recursion.fast-submissions`, both
through `eval-push.yml` → the pinned `evaluate.yml`), and the VM certificate run was not made.

**Machines.**

| Where | CPU | vCPUs | Notes |
|---|---|---|---|
| development VM | QEMU Virtual CPU 2.5+ (Intel host, AVX-512, **no** PCLMULQDQ/VPCLMULQDQ/GFNI), KVM | 32 | shared with other agents (load 2–7 during the runs); `logs/phase0-M/probe-vm-run1/machine.txt` |
| smoke run: `setup` | AMD EPYC 9V74 | 4 | `gh/smoke-setup.log` |
| smoke run: `certificate` | Intel Xeon Platinum 8370C @ 2.80 GHz | 4 | `gh/smoke-cert.log` |
| smoke run: `benchmark` | AMD EPYC 7763 | 4 | pclmulqdq, vpclmulqdq, sha_ni, avx2 (no avx512); `gh/smoke-result0/result-0.json` |
| season run: `setup`, `certificate` | AMD EPYC 7763 | 4 | `gh/season-setup.log`, `gh/season-cert.log` |

**GitHub's 4-vCPU runners are not one machine**: three CPU models appeared in two runs (Zen 3,
Zen 4, Ice Lake). The certificate caps are absolute seconds, so an entry's margin depends on the
draw; `T_V` is recalibrated per benchmark job, so it does not.

## 1. Organiser setup at `15dac52`

| Step | VM (private copy, 32 vCPU) | Runner, smoke (EPYC 9V74, cold) | Runner, season (EPYC 7763, cold) |
|---|---|---|---|
| package tree | `rsync` of `recursion.fast-v4/.lake/pkgs-local` (9.2 GB, revisions match the manifest at `15dac52`; it also holds an unused `Clean`): 1 min 40 s (`rsync-pkgs.log`) | `lake exe cache get` (restore + get): about 2 min 19 s | about 2 min 12 s |
| `lake build` (contract, library, controls; 45 modules built, Mathlib from the tree) | 1 min 57 s, 1,264 jobs (`org-lake-build.log`) | in step 1 below | in step 1 below |
| `org-setup.sh` step 1, organiser build | 4 s (already built) | 102 s | 131 s |
| step 2, harness tools | 11 s | 10 s | 10 s |
| step 3, allowlist (10,816 modules) and olean manifest (34,374 entries) | 74 s | 8 s | 8 s |
| step 4, badge objects (`RecursionFast`, CompPoly roots, `Mathlib.Tactic` closure) | 130 s | **345 s** | **473 s** |
| step 5, service (`cargo build`) | 17 s | not in `setup` (`setup-tools`, 51 s job) | not in `setup` (63 s job) |
| `org-setup.sh` total | **236 s** (`org-setup.log`) | **465 s** | **622 s** |
| whole `setup` job (cold cache, incl. save) | — | 10 min 45 s | 13 min 19 s |

Against the design's nesting (`org-setup.sh` steps 1–4 timeouts 300 + 60 + 90 + 90 + 540 = 1,080 s,
the `setup` job ≤ 30 min): step 4 used 473 of its 540 s on the EPYC 7763 (88 %), the tightest
organiser margin seen. On a cache hit the `setup` job does nothing.

## 2. The certificate job under the new caps (spartan-srom, 17,901 code lines)

The entry builds against `15dac52` unchanged: its only use of the cap, `εR1_le_errorCap`, is a
generic `pow_le_pow_of_le_one … (by norm_num)` that proves `2^-129 ≤ 2^-120` as it proved
`2^-129 ≤ 2^-128` (`submissions/spartan-srom/lean/SpartanSromSubmission.lean:210`); confirmed by
the VM build of §2.2 and by both runner runs (`certificate: ok`, gate PASS). No fix needed.

### 2.1 On GitHub (4 vCPUs; the harness's own parallelism: `lake build` uses all CPUs of the job, the comparator's kernel replay is one process)

| Phase | Cap (`season.toml`) | Smoke run, Xeon 8370C | Season run, EPYC 7763 |
|---|---|---|---|
| the one build (`lake build +Challenge +Solution`, 67 modules) | `build_s` 600 | **163.0 s** (27 %) | **179.8 s** (30 %) |
| comparator: exports + Lean kernel replay | `kernel_s` 600 | **93.7 s** (16 %) | **105.1 s** (18 %) |
| gate + badge build + two manifest checks + render + source rule | `gate_s` 120, `badge_s` 180 | ≤ 31 s together (step 288 s − build − kernel) | ≤ 34 s together (319 s − build − kernel) |
| certificate step (wall) | — | 4 min 48 s | 5 min 19 s |
| certificate job (wall, incl. restores 53 s / 36 s) | 30 min | 6 min 19 s | 6 min 47 s |
| outcome | | ok, gate PASS, kernels `[lean]` | ok, gate PASS, kernels `[lean]` |
| the run's verdict | | smoke ACCEPT, S = 0.560 | season REJECT (`queryCap`; §4) |

Logs: `gh/smoke-artifact/cert.json`, `gh/season-artifact/cert.json` (the harness's own timings),
`gh/smoke-cert.log`, `gh/season-cert.log` (step times). The harness records no separate gate and
badge times; their sum is bounded by the step's wall time minus the recorded build and kernel times.
The kernel's memory peak is not recorded (`peak_bytes: null`).

The 4-vCPU runner is much faster than the VM at this job: F4's VM run at `81e1ebf` took 354 s in
the comparator alone (on 32 vCPUs; the replay is single-threaded), against 94–105 s here.

### 2.2 Where the Lean time goes, by kind of proof (VM, profiler)

The entry was built at the pin in a fresh tree mirroring `evaluate.py`'s `mkfresh`, with
`-Dprofiler=true -Dprofiler.threshold=50` (`entry-prof/tree`, `entry-prof/build-profile.log`;
2 min 27 s wall, 12 min 21 s user on the VM's 32 vCPUs). `type checking` is the kernel's time on
each declaration as it is added, the same work the comparator replays. Table:
`entry-prof/profile-table.txt` (script `scripts/profile_table.py`; code lines by the core's
`loc.py`, `spartan-srom-loc.log`).

| Kind (modules) | code lines | module build s (sum) | kernel s (sum) | build s / kLoC | kernel s / kLoC |
|---|---|---|---|---|---|
| controls and known answers by `decide +kernel` (10) | 1,230 | 119.1 | **72.5** | 96.8 | **59.0** |
| protocol soundness: algebra, probability, KS (20) | 8,548 | 161.1 | 33.7 | 18.8 | 3.9 |
| BLAKE2s/chain circuit, R1CS, witness (15) | 4,622 | 110.1 | 26.5 | 23.8 | 5.7 |
| field arithmetic and its correctness (6) | 1,374 | 43.4 | 13.7 | 31.6 | 9.9 |
| verifier, bytes, decoding, glue (15) | 2,127 | 64.0 | 4.3 | 30.1 | 2.0 |
| **total** (66) | **17,901** | 497.7 | **150.6** | 27.8 | **8.4** |

Module build seconds include about 2–3 s of imports each. The single largest item is
`SpartanSromTranscriptControls`: **83 code lines, 68.1 s of kernel time**, ten `decide +kernel`
known-answer tests that run BLAKE2s-based transcripts and Merkle paths in the kernel. Next:
`SoundnessKSBase` (1,651 lines, 19.4 s), `FieldBaseCorrect` (812 lines, 12.4 s; word-level
`decide`/`bv_decide`-style field facts), `Blake2sWitness` (215 lines, 6.5 s).

## 3. Compiled-Lean binary-field arithmetic (the `T_V` currency)

A Lean-core-only project (no Mathlib, Lean v4.34.1), now also the runner probe
`probe/lean-field/` (§6). Sources: `GF.lean` (variants), `GFU.lean` (generated by
`gen_gfu.py`: unrolled variants), `Main.lean` (benchmark and known-answer dump),
`Blake2sProbe.lean` (a copy of the core library's `compressF` definitions, no proofs),
`ChainCheck.lean` (a copy of the core's chain checker).

**Fields.** GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1), two `UInt64` limbs; GF(2^64) =
GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), CompPoly's `BF64` modulus, one `UInt64`.

**Variants of the 64×64→128 carry-less product** (GF(2^128) is Karatsuba over three of them,
then a two-fold reduction):

- `naive`: GF(2^128) shift-and-xor directly, 128 branch-free steps (`naive` a 16-round loop,
  `naiveU` fully unrolled);
- `comb`: 64 branch-free steps per 64-bit product (`comb` a loop returning a structure,
  `combU` unrolled);
- `win4a`: 4-bit windows, the 16-entry table in an `Array UInt64` built per product (boxed);
  `win4m`/`win4mU`: the table in 16 locals and the lookup a `match` on the nibble (loop /
  unrolled); `fixed-win4`: three tables for a fixed multiplicand, built once (Shoup-style);
- `h32`: integer multiplication with holes on 32-bit halves (16 `imul` give the exact 64-bit
  carry-less product of two 32-bit words; spartan-srom's `clmul32`), Karatsuba twice: 9 × 16 =
  144 `imul` per GF(2^128) product;
- `h64`: BearSSL's `ghash_ctmul64`: 16 `imul` give the low 64 bits of a 64×64 carry-less
  product; the high half from the bit-reversed operands: six `bmul64` (96 `imul`) and seven
  bit reversals per GF(2^128) product.

**Correctness.** Every variant's output was compared with an independent Python-integer
reference on 372 pairs per variant (three seeds; structured inputs x^127·x, x^64·x^64, all ones,
1·a; then pseudo-random): **8,556 of 8,556 agree** (`gf-check.log`, `gf-check-all.txt`,
`scripts/checkgf.py`). The reference itself reproduces the GCM specification's test case 2
(`C·H = X1` in GHASH's reflected bit order). The BLAKE2s copy gives RFC 7693's
`BLAKE2s-256("abc") = 508c5e8c…86675982` (`probe-vm-run1/check-all.txt`).

**Allocation.** The generated C was inspected: the hot loops of `naiveU`, `combU`, `win4mU`, `h32`,
`h64` (latency and throughput) contain no `lean_alloc_*`, `lean_box*` or `lean_apply*`;
`naive`/`comb` allocate one structure per loop call, `win4a` and `fixed-win4` read boxed
`UInt64`s from an array, `win4m` allocates the 16-field table per product.

**Results** (VM; three processes pinned to one core each, `taskset -c 29`, `30`, `28` — core 2
was busy with another agent's benchmark; 7 repetitions per process; ns per multiplication,
median of the three per-process medians, with the best single repetition;
`probe-vm-run1/summary.txt`, raw `bench.txt`, `bench-cpu30.txt`, `bench-cpu28.txt`). "lat" chains
`x := x·y` (latency); "thr" runs four independent chains (throughput).

| Operation | lat ns | thr ns | best |
|---|---|---|---|
| GF(2^128) naive (loop) | 256 | 249 | 230 |
| GF(2^128) naiveU (unrolled) | 174 | 174 | 166 |
| GF(2^128) comb (loop) | 607 | 601 | 574 |
| GF(2^128) combU (unrolled) | 168 | 173 | 164 |
| GF(2^128) win4a (array table per product) | 783 | 789 | 770 |
| GF(2^128) win4m (locals, loop) | 234 | 252 | 228 |
| GF(2^128) win4mU (locals, unrolled) | 133 | 178 | 123 |
| GF(2^128) fixed-win4 (tables for a fixed `y`, built once) | 208 | — | 205 |
| **GF(2^128) h32** | **63.4** | **65.1** | 60.8 |
| **GF(2^128) h64** | **60.7** | **56.8** | 55.1 |
| GF(2^128) h64 as a real call returning a fresh structure (`@[noinline]`) | 79.4 | — | 76.2 |
| GF(2^128) inner product of two `Array` of 1,024 boxed elements, per term, boxed call | 83.9 | — | 82.2 |
| the same, multiplication inlined | 70.8 | — | 65.4 |
| GF(2^128) squaring (bit spread + reduce) | 13.2 | — | 12.5 |
| GF(2^64) comb (loop) | 215 | 202 | 189 |
| GF(2^64) combU | 57.6 | 58.4 | 54.2 |
| **GF(2^64) h32** (spartan-srom's `F.mul`) | **25.2** | **24.5** | 23.9 |
| **GF(2^64) h64** (lo by `bmul64`, hi reversed) | **23.7** | **22.1** | 21.3 |
| BLAKE2s compression, `compressF` (core library fast path), chained | 201.7 | — | 194.8 |

So in compiled Lean on this VM a GF(2^128) product costs about **60 ns inline** (h64 or h32, the
two within 5 %), about **80 ns** when elements live in structures or arrays, i.e. about
**0.3–0.4 BLAKE2s compressions**. Table methods lose in Lean: an indexable unboxed table does not
exist in core Lean (`Array UInt64` boxes), and a `match` on the nibble is a branch. The clean
probe build took 1 min 8 s on the VM.

Not measured: GF(2^192) (CompPoly `Ext3` over `BF64`, spartan-srom's `EF.mul`; the import needs
Mathlib) and GF(2^256) as a quadratic extension of GF(2^128) (about three GF(2^128) products and a
constant multiplication, **estimate**).

## 4. The chain checker `T_triv,best`

| Where | Shape | Runs | `T_triv` | Log |
|---|---|---|---|---|
| VM, the core's `chaincheck` (copied, built in the probe), one core (28, 29, 30) | r = 6, n = 2^18 (2^24 compressions, 8 chains interleaved) | 9 | best **2.63 s**, median 2.77 s, worst 3.54 s | `probe-vm-run1/chaincheck*.txt` |
| design §3.5 (earlier) | season | — | 3.10 s on the VM, 1.78 s on a runner | design |
| GitHub, EPYC 7763, smoke shape | r = 2, n = 16 | 2 | 68.7 µs (meaningless at n = 16) | `gh/smoke-result0/result-0.json` |
| GitHub, EPYC 7763, season shape (tree part) | r = 6, n = 2^18 | 3 | best **2.0594 s** (2.0594, 2.0644, 2.0618); `T_V` cap **205.9 ms** | `gh/season-result-0/result-0.json` |
| GitHub, EPYC 7763, season shape (stream part, another runner) | r = 6, n = 2^18 | 3 | best 2.0583 s (2.0590, 2.0583, 2.0617) | `gh/season-result-1/result-1.json` |

On the VM `chaincheck` spends 157 ns per compression (8 chains interleaved), against 195–202 ns
for one chained `compressF`; on the EPYC 7763 it spends 123 ns. **VM/runner ratio of the chain
checker: 2.63 s / 2.059 s = 1.28** (VM best against runner best; 1.35 with the VM's median). The
design's 1.78 s was another runner; on today's EPYC 7763 `T_V` is 205.9 ms, not 178 ms.

The season benchmark of spartan-srom was REJECTed, as expected for a √-size PCS past its frontier:
the tree's prover made a Fiat–Shamir query of 1,572,898 bytes, above the service's
`queryCap = 1048576`, and the stream's leaf 0 was rejected by `acc`
(`gh/season-result/result.json`). The calibration above ran before either and is unaffected.

The smoke benchmark also shows what spartan-srom's verifier costs on a runner: the root check took
**292.6 ms** (`root_check_ns`, EPYC 7763, smoke shape; not enforced there), above the season's
`T_V` of 205.9 ms measured on the same CPU model.

## 5. The season files at the pin (relevant parts)

`.contract/harness/season.toml`:

```toml
K = 20.0          # S = T_tree + K * t_link
R = 10            # T_V = T_triv,best / R
[certificate]     # on a 4-vCPU runner; a breach is the entry's REJECT, except the kernel's (unchecked)
build_s = 600     # the entry's `lake build` of the challenge and Solution's import closure
kernel_s = 600    # the comparator: the exports and the Lean kernel's replay
gate_s = 120
badge_s = 180
[tree]
r = 6
n = 262144        # 2^18
tree_s = 600
[stream]
M = 256
n_f = 65536       # 2^16
step_s = 60
stream_s = 960    # 900 s for the entry, 60 s organiser overhead
check_every = 32
[canaries]
per_kind = 2
[dos]
proofs = 100
item_factor = 10  # an input may take at most 10 · T_V
total_s = 180
[caps]
proof_cap = 1048576   # |π| ≤ 2^20
file_cap = 67108864
verify_s = 10
setup_s = 300
build_s = 300         # the prover's build
[memory]
prover = "11G"
service = "2G"
badge = "4G"
[tv]
enforce = true
checker_runs = 3
service_calibration_s = 2
```

`.contract/harness/smoke.toml` differs in: `r = 2`, `n = 16`, `tree_s = 120`; `M = 4`,
`n_f = 16`, `stream_s = 300`, `check_every = 2`; `dos.proofs = 64`; `tv.enforce = false`,
`checker_runs = 2`, `service_calibration_s = 1`. The `[certificate]` caps, `[caps]` and `[memory]`
are the season's.

## 6. The runner probe

`probe/lean-field/` (committable; `.lake/` and `out/` ignored): `lakefile.toml` (Lean core only,
exes `gfbench` and `chaincheck`), `lean-toolchain` (v4.34.1), and `run.sh [OUTDIR]`, which builds,
runs the known-answer check (`checkgf.py`), runs `gfbench bench` pinned to one core
(`CPU`, default 1; `REPS`, default 7) and runs `chaincheck` `CHECKER_RUNS` times (default 3) at
`R`/`N` (default the season's 6 and 2^18) on starts from `gen_leaves.py`. It prints
`name median min max` in ns per operation and `mismatch NS` for the checker (the root is not
computed; NS is the time of the full recomputation, as the harness measures it). It needs
`python3`, `taskset` and elan. A clean copy builds and runs end to end
(`logs/phase0-M/probe-clean-out/`). VM run: `CPU=29 probe/lean-field/run.sh logs/phase0-M/probe-vm-run1`.

## 7. What this means

### 7.1 The Lean budget of a certificate

- **Neither cap binds spartan-srom on a runner.** Build 163–180 s of 600, kernel 94–105 s of 600,
  gate and badge together about 30 s of 300: about 30 % of the build cap and 18 % of the kernel
  cap. The 30-minute job finished in under 7 minutes.
- **Per 1,000 code lines, on a runner**: build about **9–10 s** and kernel about **5.2–5.9 s**
  at spartan-srom's mix (17,901 lines; 163–180 s and 94–105 s). Linear scaling (an
  **estimate**: the build is parallel on 4 vCPUs and limited by the import chain's critical path,
  the kernel replay is serial) gives about 60 kLoC before the build cap and about 100 kLoC before
  the kernel cap; the build cap binds first, and both leave room for a recursive entry several
  times spartan-srom's size **if its proofs are of the same kinds**.
- **By kind** (VM kernel seconds per kLoC from §2.2; on a runner the comparator's whole replay
  was 0.62–0.70 of the VM's summed `type checking`, so divide by about 1.5, **estimate**):
  `decide +kernel` evaluation **59 s/kLoC** (about 40 on a runner), field-arithmetic correctness
  10, circuit/R1CS 5.7, protocol soundness 3.9, verifier/bytes/glue 2.0. Kernel evaluation is
  15–30× the cost of a proof by rewriting. A kernel budget of 600 s on a runner buys about
  15 kLoC of `decide +kernel` known-answer tests, or over 100 kLoC of algebraic proof. Every kernel
  KAT of a BLAKE2s transcript costs seconds (spartan-srom: ten of them, 68 s on the VM); keep
  them few, small, or compiled-side (a badge test) where the rules allow.
- The runners differ (Xeon 8370C, EPYC 7763 and 9V74 seen): the two certificate runs differ by
  10 % in build and 12 % in kernel. Keep a margin of at least 1.5× on both caps.

### 7.2 The `T_V` budget in GF(2^128) multiplications per root check

`T_V = T_triv,best / R` with `R = 10`, recalibrated per benchmark job on its own runner: on the
EPYC 7763 today **`T_V` = 205.9 ms** (§4). The VM/runner ratio of the chain checker is **1.28**.
Since the cap itself is a chain-checker time, the number of operations that fit in `T_V` does not
depend on the ratio, provided field arithmetic and BLAKE2s scale alike between the two machines
(an **estimate**: integer multiplication against add-rotate-xor; the probe of §6 run on a runner
settles it). Runner nanoseconds below are VM nanoseconds ÷ 1.28:

| Cost model of one operation | VM ns | runner ns (÷ 1.28) | operations in `T_V` = 205.9 ms |
|---|---|---|---|
| GF(2^128) product, inline, allocation-free (`h64`) | 60.7 | 47 | **≈ 4.3 million** |
| GF(2^128) product, boxed (elements in structures, a real call) | 79.4 | 62 | ≈ 3.3 million |
| GF(2^128) inner-product term over `Array` of boxed elements | 83.9 | 66 | ≈ 3.1 million |
| GF(2^128) squaring | 13.2 | 10 | ≈ 20 million |
| GF(2^64) product, inline (`h64`/`h32`) | 22–25 | 17–20 | ≈ 10–12 million |
| BLAKE2s compression (`compressF`) | 202 | 158 | ≈ 1.3 million |

The whole of `acc` is charged, not just the arithmetic: the node's trace digest (about 1.6
compressions per 100-byte query, so `2^16` queries ≈ 105 k compressions ≈ 17 ms on a runner,
**estimate**), the WOTS signature (300–500 compressions, under 0.1 ms) and the proof parsing. The
DoS column allows 10 · `T_V` per input. As a rule of thumb, **a root check of Flock over
GF(2^128) may spend about 3 million field multiplications (boxed), or about 1.3 million BLAKE2s
compressions, on a runner, less the trace digest**; inline allocation-free arithmetic stretches
that to about 4 million. For scale: spartan-srom's verifier took 292.6 ms on an EPYC 7763 at the
smoke shape (`gh/smoke-result0/result-0.json`), 1.4 × the season's `T_V`.
