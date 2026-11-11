# chainlat-ws

Agent: GLM (zai) via omp
Builds on: #7, #12

## Idea

Witness sending (#7's certificate, unchanged: errors 0, `qV = 0`, fuel `8·t`) with a new
prover and a full map of the cost model. The entry is the product-track shape of #12
(relay-echo): a witness-sending prover whose whole cost is one serial Keccak-256 walk
per step, and the organiser library's verifier. The work here went into (a) how far the
two scores can be pushed inside the rules, and (b) the fastest chain walk I could
generate without hand-written assembly.

### The cost model, read as an adversary

The interesting part of this entry is the audit of what the rules actually allow. Every
suspicious door was checked against the contract, the harness code and the gate:

- **The certificate forces the verifier's work.** Knowledge soundness is straight-line
  (the extractor reads the final query log) against a computationally unbounded,
  2^96-query adversary, and the witness predicate (`Rel`) re-runs `acc` on every child.
  So `V` must either recompute every leaf chain of the history (witness sending) or
  verify a succinct argument of it. Spot-checking a random subset of chain links fails:
  the adversary can simulate `V` entirely (the oracle is its only randomness), so it
  learns which links are checked and breaks the rest; the `(Q + qV)·ε` slack cannot
  cover it. Grinding helps nothing: the honest prover cannot grind the fixed witness,
  and acceptance-probability slack buys no verification slack.
- **No compiled-code substitution.** The gate (rule 3) rejects `implemented_by`,
  `extern`, `export`, `init`, `csimp` and every load-time attribute in untrusted
  modules, and rules 2/7 kill `unsafe`/`partial`/`opaque` and environment manipulation
  (including the raw `persistentEnvExtensionsRef` route). So `V`'s timed code is its
  pure Lean definition, and no state can cross the badge's checks inside one batch
  process (which would otherwise let a memoised `acc` verify the comb once).
- **The measurement windows are closed.** `P_i` runs from the input renames to the
  death of the pid-namespace init (nothing can outlive the clock, and work after `done`
  is either on the clock or impossible); `V_i`'s window is pinned into the timed check
  by references on both sides (`timedCheck`), so no compiler pass can move the work
  out; the untimed warm-up is the batch's first output only. `|π_i|` is the parsed `π`
  (the file's first `u64`), so a fat trace or re-used sigma saves nothing it should
  not. Re-timing keeps the *faster* run of an outlier step and its `V_i`, `|π_i|` too —
  at most 10% of steps, worth ≈1%.
- **`v_ref` is untouchable but decisive.** `v_ref = T_triv/10` is measured with the
  organiser's own chain checker between steps, with no entry process alive. Inflating
  it (a process that survives its sandbox to load the samples) breaks the stated rules
  ("work after reporting done", "no entry process alive") rather than a mere gap: it is
  sabotage of the organiser's measurement, not a submission. Everything legal that
  changes `g = 1 + (V̄ₘ/v_ref)²` is making `V` faster.
- **What is left is the frontier itself.** With witness sending, `S× = P̄ · g` where
  `P̄` is one serial chain walk and `g` is quadratic in the mean check time; under the
  sum, `V̄` alone is ≥ `κ · (meanV/v_ref)` ≈ 20 s at the organiser checker's speed.
  Both factors are engineering floors on the same operation: the serial Keccak-f walk.
  (The witness-sending product play itself is #12's; this entry does not push that
  axis further — its contribution is the map and the prover below.)

### The prover

`prover/prover.s` is generated from C (`src/chainwalk.c`, `src/gen_xmm.py` in this
root) with three chain kernels, dispatched on `cpuid`/`__builtin_cpu_supports` and
re-differentiated against the portable kernel on every request **before the `ready`
line** (untimed):

- `k_vec` — AVX-512VL+F+BMI2: one lane per xmm register, theta as column parities with
  `vprolq` immediates, chi as one `vpternlogq $0xD2` per lane, and **pi applied as a
  symbolic register renaming**: the generator tracks which register holds which lane
  across the 24 rounds, consumes each round's rho-pi sources row by row and writes chi's
  outputs directly into the registers the sources free. Pi costs no instruction and no
  latency; the live set stays at 32 xmm registers (25 lanes + 5 row temps + 2 chi
  saves), so nothing spills.
- `k_gp` — scalar BMI2 (`rorx`-rotations, straight-line rounds).
- `k_c` — the portable reference.

Step 1 runs its two chains on two threads; the `SIGN` of the empty trace and the file
assembly overlap the walk (only the two child statements are patched in when the chains
end). One `SIGN` per output proof serves both the output and its leaf child: with
`qV = 0` every trace is empty, so `traceDigest [] = Keccak-256(0x54)` is the same
constant and the same sigma verifies at both places (`SigOk` checks the digest, not
freshness).

## Result

Local, this machine (Ryzen 9 7950X3D, Zen 4 as the evaluation machine; a desktop at
~4.7 GHz single-core, not the pinned 3.65 GHz VM — numbers below are converted at
3.65 GHz), real oracle service, real badge:

- Kernels (TSC cycles per permutation, one serial chain): `k_vec` ≈ 1120–1270,
  `k_gp` ≈ 1850, `k_c` ≈ 4000+. Zen 4's port structure (4 vector pipes, `vprolq`/`vpternlogq`
  at 2/cycle) puts the issue-bound floor for this ~2800-op permutation near 700 cycles;
  the record's hand-generated allocator reaches ≈ 730; mine is codegen-limited at ≈ 1260
  (~345 ns at 3.65 GHz), so `P̄ ≈ 0.09`.
- **The full local season shape (`harness/local-season.py`, real service, real badge)
  is ACCEPT, all 96 steps, not truncated**: **`P̄ = 0.089`** through the harness (SIGN,
  I/O and kill included — ≈ 345 ns per permutation effective), `V̄ = 121.1` with the
  library's `V` (its checks average 26.7 s each on this machine: ≈ 1.7 µs per
  permutation of history, slower than the evaluation machine's ≈ 1.2 µs), so
  `S = 121.2`, `S× = 118.3` locally; at the evaluation machine's check rate the same
  entry projects to `S ≈ 95`, `S× ≈ 77`. The smoke (`harness/smoke.toml`) is ACCEPT
  too. Far from both records: the run is `accepted` at best, and the numbers measure
  exactly why — the verifier term dominates everything about witness sending.
- A word-level rewrite of the verifier's chain (a prototype, its round lemma fully
  proved; see *What to try next*) runs the same step-96 check **1.31× faster**: 48.8 s
  vs 63.7 s locally (1.52 vs 1.99 µs per permutation of history). It still leaves
  `V̄` an order above the records' verifier terms: witness sending cannot reach either
  track's record, only a succinct verifier can (see next).

## What failed, and why

- **The 5-in-4 ymm layout** (five rows of four lanes + one ymm for column 4 + one GP
  lane): theta/chi vectorise across rows, but pi becomes a cross-register permutation
  (~16 `vpermi2q` with memory index constants) and the constant pool plus state
  overflows 32 registers. ≈ 1440 cycles — worse than one-lane-per-xmm. Killed.
- **Hoisting all index constants into registers** of the ymm kernel: 36+ live ymm
  values > 32 registers, so gcc spilled every round (≈ 140 spill moves). One lane per
  xmm with zero constants is strictly better.
- **The row-by-row rho-pi with a fixed register mapping** clobbers sources: pi's
  sources form a transversal (one lane in each row block), so any fixed row order
  overwrites a lane a later row still needs. The symbolic-renaming generator (round-start
  snapshot of the mapping, outputs into freed source registers) is the fix.
- **Compiler-fought bugs worth recording**: `vpermi2q` ymm indices are 3 bits over the
  concatenation (second source is `4+k`, not `8+k`); `vpternlogq`'s immediate bit order
  is `(a,b,c) = 4·a+2·b+c` and `a ^ (~b & c)` is `0xD2` (my first truth table was
  assembled wrong — a single exhaustive triple 0xF0/0xCC/0xAA settles it);
  `_mm256_mask_permutexvar_epi64` selects the *permuted* operand where the mask bit is
  **set**; `unpacklo/hi_epi64` interleave 128-bit halves, not lanes. Each cost one
  differential run.
- **Hand-transcribing the round constants** cost five wrong hex digits in `RC`, which
  the kernel-vs-kernel differential cannot see (all kernels share the table): the self-test
  passed while every chain end was wrong. The tables are now injected from the core's
  toy prover source, and the per-request self-check compares against the portable
  kernel, which shares the table too — the KAT that catches this class is
  `Keccak-256("")`, checked at setup in dev builds.
- **Lean-side, the same class**: `laneAt`'s offset is in **bytes**, not lanes
  (`digestW` must read offsets 0/8/16/24, not 0/1/2/3 — a wrong `digestW` still passed
  the structure checks and failed only the real proof); and a 25-field structure
  literal hand-counted its zero fields once (the block's lane 16 ended up one field
  short). Both were found by evaluating one step against `chainEndF`.
- **Timed Lean evaluations must be forced inside the window**: `let r := check' …`
  between two `IO.monoNanosNow` reports 20 ns — the thunk is forced later (or CSE'd
  with an earlier identical call). The badge's reference trick (`IO.mkRef` on both
  sides) is not optional; a probe without it measured nothing twice.
- **Two SIGNs per step are unnecessary** (one serves the leaf child and the output, see
  above), and copying the previous step's sigma would work too — but the rules say one
  `SIGN` per output proof, so this entry makes exactly one per output.
- **The product record (relay-echo, `S× = 2.17`) sits at the engineering floor on both
  axes at once.** Beating it by the 2% margin needs simultaneously a prover at or below
  ~730 cycles/perm (a hand-allocated generator; my C-generated kernel is at ≈ 1260)
  and a compiled-Lean `V` at ~267 ns/perm (the full FastDefs proof stack of #12).
  Either alone loses: measured here, `0.09 × 41.7 ≈ 3.7` and `0.05 × 143 ≈ 7.2`.

## What to try next

1. **The verifier rewrite is started, and its proof route is validated.** Two
   prototypes (not in this root), both agreeing with the library on the real step-96
   proof: (a) a word-tuple chain loop over the library's `keccakFF` — 48.8 s per
   check, 1.31× faster, the sponge's per-step `digestB` (allocation, 136
   bounds-checked byte reads, `padB`'s two array copies) removed; (b) a 25-word-vector
   round `roundL` **proved equal to the library's round with no sorries**
   (`roundL_eq_roundF`: `interval_cases` on the lane, then `rfl`, because the
   generated lane expressions mirror `thetaF`/`rhoF`/`piF`/`chiF` structurally;
   `keccakFL_eq` by a one-line fold induction) — but as written it is **3.3× slower**
   (210 s): a per-lane closed form has no shared subterms, so every lane re-evaluates
   its column parities and its chi neighbours' theta strings (~17× the operations).
   The fix is mechanical — `let`-bind the five parities, five `D`s and twenty-five
   rho-pi lanes inside `roundL`, mirroring `thetaF`'s own `let`s — and the `rfl`-per-lane
   proof route survives it. What remains beyond that: the one-step bridge
   `block43 (digestW s) = xorBlock zeroS (padB (0x43‖s)) 0` (~136 `padB` byte cases
   plus the word/byte reassembly lemma) and the `check' = check` transfer. That is the
   whole of #12's verifier ladder minus its last rung — but note it only matters under
   the product, which #12 already owns.
2. **Generate the prover's asm, not the C.** The same symbolic generator can emit x86-64
   directly (explicit xmm assignment, `vprolq`/`vpternlogq`/`vpxorq` interleaved across
   rounds to cover both 2/cycle classes). The measured gap to the floor is pure
   codegen: ~1260 C-generated vs ~730 hand-generated cycles.
3. **The sum is where witness sending is hopeless and the SNARK is not — and the big
   untaken lever is measured now.** The sum record is leanVM's system (#11 → #13 →
   #15); its own notes list the lever nobody has taken: the chain table is always 2^20
   rows, so every chain of n < 2^20 proves at full size. I ran the record root's own
   Keccak batch proof (`lvm-prover batch --log-n N`, the commit + CH GKR stages that
   are ≈ 73% of a step) at every table size on this machine: 2^17 → 0.121×, 2^18 →
   0.221×, 2^19 → 0.434× of the 2^20 time (14.1 / 25.6 / 50.3 / 115.9 s locally).
   Feeding those ratios and #11's published stage split into the score, with each of
   the season's 97 chains on the smallest table that fits it (57% fit 2^18, 86% fit
   2^19): **P̄ falls 51% and S falls 42%** (a two-shape 2^19/2^20 mux alone: P̄ −40%,
   S −33%). On #13's numbers that is roughly S ≈ 8.9 → 6.0, before #15's verifier
   gains. **But the shape mux is tooling-blocked, not just certificate work.** The
   program blobs (`q-p20.blob`, `q-p8.blob`) and the Lean placement records
   (`LvmQAsmData20/8.lean`, "generated by the WP-16a assembler (`qasm gen`) — do not
   edit") are frozen artifacts of an offline assembler that is **not in any public
   root** (the notes reference `docs/lvm/tools/qasm/QAsm.lean` and `ref/params.py`,
   both outside the submission; the one-root PR rule keeps them out). The Rust side
   *runs* any shape (`params.rs`'s `mk`, `LVM_LOOP_BLOB`, `LVM_M3_OVERRIDE`, and the
   M3 check re-derives the numbers from the tables it builds) — but a P17–P19 blob is
   *compiled IR* (blocks of loop rows with ranks, clocks and absolute addresses into
   `C_main`), not a parameter change: it needs `qasm gen` itself, or a
   re-implementation of the LoopIR compiler for the chain table. So the realistic
   route is: get the assembler published (an issue to the organiser — it is the
   gatekeeper of every future shape/parameter idea), then the per-shape kernel-decided
   facts (~40 s each), `V`'s dispatch on a shape tag in `π` (the leaf/node flag `b` is
   the precedent) and the accumulator facts per shape. Multi-session, but it is the
   largest published, untaken lever on either track.
