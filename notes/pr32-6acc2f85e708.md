# tableless

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #11, #7, #12, #13, #15, #17, #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30, #31

This root continues #31 (`trimmed-phi`, blob U′ and the GOLF kernel diets), #30 (`timed-spin`, prover-only),
#29 (`planned-phi`, prover-only), #28 (`brisk-tape`, prover-only) and #27 (`single-tape`, stage `S2GU`), which continued
#26 (`halved-phi`), #25, #22, #21, #20, #19 and PR #11. This root is stage `S2GL` ("MB-LIN"): the mini-bus's table
phase is gone and each of its three grand-product trees ends in one linear claim on `C_main`. "Changes since #31" is
relative to #31; the sections from "Changes in #31" on describe the earlier rolls.

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, ring switching and
stacked WHIR. It is reshaped for the contract in four ways:
- an extractor that decodes only the child's stream block (8 lanes of `C_main`: from 40 for big steps, from 32 for
  small ones), with unique-decoding programs on advice;
- a hash-chain transcript over the signed oracle;
- an in-circuit verifier written as loop tables instead of a VM guest;
- a typed backend for those tables. The node program commits only its row results. A Spartan-style zerocheck and
  a wiring sumcheck tie them to the program's wiring polynomial `Φ_Q`, which `V` evaluates once per proof through
  the self-fold accumulator.

From #7 it takes the core library's `WitnessSending` relation, unchanged: that relation is the right leaf of every
node and the completeness route. The prover can run relay-echo's (#12) AVX-512VL chain kernel, and its v4 tier runs
leanvm-gkr-fast's (#13) Keccak GKR with leanvm-fast-verify's (#15) round storage. Its root leaves carry only their
occupied lanes, as in relay-slim (#17).

Notation:
- `K = GF(2^64)` (`x^64+x^4+x^3+x+1`, CompPoly `BF64`), `E = E3 = K[y]/(y^3+y+1)` (CompPoly `BF64.Ext3`) and
  `E2 = K[X]/(X² + xX + 1)` (`LvmFieldE2`; `|E2| = 2^128`); `g = x` generates `K^×`.
- `Ex` is the extractor; UD means unique decoding. P20 is the production parameter set and P8 the test set.
- `Q` is the node program. `T` is `C_main`'s typed table region. `Φ_Q` is the multilinear extension of `Q`'s
  wiring matrices, in 44 variables at `S2GF` (43 in #21).
- Shapes: big for `n > 2^18` (stride 1); small for `n ≤ 2^18` (the even words, stride 2).
- dev means the QEMU dev VM. Labels: [measured], [exact] (schedule arithmetic or a Lean `decide`), [model] (a model
  on measured inputs), [estimate].

## Changes since #31 (trimmed-phi)

**Conclusion.** Stage `S2GL` deletes the mini-bus's table phase (the challenge `ξ`, six `E3` sumcheck rounds and 633
`E3` column evaluations). The mini-bus has 211 tables (187 seeds of 16 rows, 24 read tables of 16/32/64 rows), none
with a constraint, and every flush coordinate is a constant, a column or `g^k` times a column. So each leaf of its three
product trees (push, pull, count) is an affine function of one table row. The multilinear extension of an affine map of
columns is the same affine map of their extensions. `V` therefore turns each tree's final GKR claim into one `K`-linear
claim on `C_main`:

  `v_s = (1 + Σ_b eq(ζ_hi, sel_b)) + Σ_b eq(ζ_hi, sel_b)·(β_s + Σ_i w_i·coord_i~(ζ[..τ_b]))`.

Here `w = eq(α⃗, ·)` (count side: `w = [1, 0, …]`, `β = 0`), committed columns are the unknowns, and the seeds' fixed
address columns `g^(base + 17x)` are evaluated in closed form, `g^base·Π_k((1 + ζ_k) + ζ_k·g^(17·2^k))`. The three
claims (259, 446 and 24 column terms) join the opening batch where the 633 table claims stood. No bytes are sent for
them. The proof shrinks to **268,336 B** (−15,624 B) [exact], `qS` 3,649 → 3,642, the hashed trace 538,656 → 522,528 B
and the sponge blocks 3,961 → 3,843. The claim, the contract theorem's form and `εFS ≤ 2^-128` are unchanged. The
table phase's groups leave and no group is added. The certificate is `certificateL20S` with the standard three axioms.

- **The identity, checked natively [measured].** An independent Rust evaluation of the formula above from the mini-bus
  spec and the `C_main` words equals the GKR's three leaf values on 12 honest `S2GU` proofs (small and big shapes, `S,0`
  and `S,1`: 36/36) and on every `S2GL` proof made since.
- **Lean.** `mbLeafLin` (a degree-≤ 1 row polynomial commutes with the column extensions), `mbClaimsL_iff` (on the
  mini-bus's tables, the bus seam's form condition holds iff the three claims hold on `C_main`), `midSpecP_GL` (the
  pinned middle phases with the mini-bus ending in the three claims; the table phase's `ξ` leaves the error list,
  `errsL_at`: every group ≤ 7·2^-131), the schedule `P20L` (`sizes_P20L` by `decide`: `|π|` 268,336, `qS` 3,642, trace
  522,528, 3,843 blocks), `refinesL20` (`V_S` at `S2GL` refines the compiled program), `nodeL20`/`harithL20` (the node
  program verifies an `S2GL` child) and the certificate chain `certificateSL20`/`certificateL20S`. Re-used: ACW's
  generalisation of the wire's sponge intervals to a block-count parameter (the shorter trace moves them to [1, 3842]
  and [8080, 8110]), and ACW's generic node-soundness pair lemmas (ported onto GOLF3). New modules: `LvmS2GL{Sched,
  Lin,Mid,Plan,StmtV,StmtC,Har,Cert}`, `LvmE2QTypedL`, `LvmE2QTypedLSem`, `LvmE2QInstL`, `LvmE2QAsmDataL20`, `LvmE2LDec`,
  `LvmE2LRef` (993 files in `lean/`).
- **The circuit (blob L).** The node program drops the child's table gadget (its 187 in-circuit `powColG` checks,
  rounds, the 633-term final) and the 443 extra opening claims, and gains `mbLinG`: block selectors, coefficients
  `eq(ζ_hi, sel)·w_i·g^k` and the closed-form constants. `Φ_Q` has **217,507 products** (blob U′: 230,349, −5.6 %)
  [exact]; `T` dense 682,410, padded 754,561 ≤ 0.95·2^20 [exact]. The guard `staticOkBL20` (with the new conjunct
  `mbLinB`: no constraints, affine flushes, every column on `C_main`) holds natively on blob L.
- **`V`.** `V_S` computes the three values and their weights at the opening's final point as sums over the sorted column
  runs, with one `eq(ζ[..τ], ρ[..τ])` table per `τ ∈ {4, 5, 6}`. The fast weights are proved equal to the
  specification's (`linWS_eq`, `mbValsF_eq`). **`V` badge** [measured, dev, timing lock, CPU 8, 3 rounds × 2 files per
  shape, medians, big / small]: mini-bus 3.45 / 3.51 → 2.34 / 2.36 ms, opening 14.80 / 19.99 → 13.83 / 17.88 ms,
  `Φ_Q` and the rest 29.25 / 29.44 → 28.52 / 28.40 ms; **full `V_S` 61.00 / 67.10 → 57.86 / 61.82 ms (−3.1 / −5.3)**.
- **The prover** is #31's (#29's code with blob L embedded) plus #30's timed spin. `m3::prove_lin` runs the bus and
  its trailing zero only, then pushes the three claims. The opening merges terms that sit on the same block at the same
  point (prover-only, same weight), so it opens the same 446 blocks as before. [measured, dev, timing lock, CPUs 8–15,
  5 interleaved pairs at 2^17]: open main 257 → 244 ms (`S,0`), 300 → 273 ms (`S,1`); mini-bus 16 → 10 ms, 14 → 9 ms.
  The `.s` are regenerated.
- **Projected [model]** from #31's evaluation (S 1.5739, `V` 44.5 ms): `|π|` −0.0246 [exact rate], `V` −2.6 to −2.9 ms
  eval (dev ×0.62–0.7) ≈ −0.013 to −0.015, #30's spin ≈ −0.004 (#30 against #29), the prover's open main and mini-bus 0 to
  −0.015: **S ≈ 1.515–1.531** against the record #29's 1.5873 (bar 1.5556).
- **Checked locally** [measured]:
  - harness cert **ok** (fresh, timing lock first, CPUs 8–15): Lean kernel **541.4 s** (stop rule 560, cap 600), `build_s`
    905.1 s, 578 modules, peak 4.88 GB; axioms `propext`, `Classical.choice`, `Quot.sound`. The kernel is +87 s over
    #31's 454.0 s: `certified`'s closure now holds both the `S2GL` chain and the `S2GU` chain it imports (30 modules
    more). Dropping the `S2GU` certificate from the closure is the next kernel lever.
  - axioms of `certified` and `certificateL20S`: exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorry`,
    `native_decide` or axiom declaration in `lean/` (checkall: source rule 0 findings over 993 files).
  - statement gate against #31's Lean (GOLF3-PHI d34b3284): no theorem statement of the entry changed; the only type
    change is `Params`' new field `mbLin` (its constructor and recursors). The value changes are the intended ones: the
    parameter records (`P20U`, `P20T`, `P20F`, …, one more field), `phases` (the `S2GL` dispatch), `S2GU`'s front
    definitions rewritten as instances of the block-count-generic ones (`contIvU`, `tapeProgU`, `wireProgU`, `GkU`,
    `midGU`), and `Solution.submission`. Every changed axiom set stays within the three.
  - NGATE-L (the `S2GL` native gate): `staticOkBL20` true; `V_S` accepts the 10 honest files made by the shipped linked
    `.s` (a 5-step stream over both shapes, `S,0` at 1, 2^17, 2^18, 2^18 + 1, 2^20) and rejects all 42 tampers (the
    32 `S2GU` modes, and on the new claims: a flipped last-layer read of the bus GKR, one coefficient + 1, one term moved
    to the next block), accepting the 3 byte-identical controls; blob L regenerates byte-identically. The decision fuzz
    (byte 32 of every bus-phase entry and every 7th entry) rejects 248/249; the one accepted entry is the opening's
    batching nonce, which the decision does not read, as at `S2GU` (249/250).
  - Byte identity of the prover: the linked `.s` reproduces the dev build's `S2GL` streams on v4p and v2 (a 5-step
    stream, `S,0` at 2^17 and 2^20) and on v4 under Intel SDE (n = 1, three steps at 2^14, `S,0` at 2^17).
  - quick bench (24 steps): ACCEPT, S 2.745 (P̄ 2.093, V̄ 0.652), S× 2.103, mean `V` 72.0 ms, `|π|` 268,336 B; `c_P`
    drift 0.095 (host loaded: P̄ reads high). #31's quick run: S 2.663 (P̄ 1.978, V̄ 0.685), mean `V` 74.3 ms, drift 0.034.

## Changes in #31 (trimmed-phi), since #29 (planned-phi)

**Conclusion.** A `V`-side roll on #27's stage, with #29's prover. The node program evaluates the wire target's `ω` with
five convolution loops instead of 260 unrolled lane forms (blob U′), and `V`'s fused `Φ_Q` code keeps its accumulator
in two machine words. `Φ_Q` has **230,349 products** (blob U: 249,188, −7.6 %) [exact], and `V`'s `Φ_Q` falls by
**3.9 / 4.4 ms** on dev (small / big) [measured]. The certificate is also cheaper to check (GOLF2's import closure,
GOLF3's proofs; Lean kernel 454 s locally against #29's 563 s). The transcript, `|π|` = 283,960 B, `qS`, `εFS`, the
claim and the theorem's statement are unchanged; the proof bytes differ from #29's (different node program, same
lengths). Projected from #29's evaluation (`V` 47.3 ms, S 1.5873): **`V` −2 to −3 ms, S ≈ 1.571–1.577, S× ≈ 0.908**
[model; eval `V` ≈ 0.6 × dev `V`, ΔS = κ·ΔV/v_ref ≈ 0.005 per ms].

- **`Φ_Q` remainder, lever 1: `runF2` without state allocation** (`LvmE2VPhiT`, `LvmE2VPhiTEq`). `Φ_Q`'s fused code at
  `E2` ran one state record per instruction; `runF2` is now `runF2Go`, tail-recursive on fuel, with the accumulator
  as two words. `runF2_fold` is re-proved (`runF2Go_succ`, `runF2Go_eq`); no statement changes and the blob is unchanged.
- **`Φ_Q` remainder, lever 2: the wire target's `ω` as loops (blob U′)** (`LvmE2QWU`, `LvmE2QWUSem`). `preWU` computed
  `ω_j` for the 260 wire positions `j < 320` as 260 unrolled lane forms (`g2Omega`). It now copies `eq(a, ·)` twice
  (128 twin-pair rows) and runs five loops of 11-term convolution chains (`convInsO` on `laneOffs`/`laneCoefs`), one
  per lane class; `ω_1087` stays unrolled. `hs_preWU` is re-proved (`hs_convLoopO`, `hs_omLoops`, `lane_sum`,
  `omCell_val`) with its statement unchanged. `f.wire.preWU` costs 4,596 products instead of 22,012 [exact, census of
  the compiled cache]. The guard `staticOkBU20` holds natively on blob U′, and `LvmE2QAsmDataU20` is regenerated
  from the source.
- **The prover** is #29's code (the planned `Φ_Q` batch, the chunked zerocheck). Its embedded P20 program
  (`q-p20.blob`, `qb-p20.lay`, `qb-p20.mb`) is blob U′'s, as #25 did for blob v4; the `.s` are regenerated.
- **`V` badge** [measured, dev, timing lock, CPU 8, 3 rounds × 2 reps of a 4-step stream, both arms in the same runs,
  host load 24 → 12]: `Φ_Q` 29.1 / 29.9 → **25.2 / 25.5 ms** (small / big); `V_S` 71.1 / 68.5 → 67.9 / 61.5 ms.
  The wire phase is unchanged, as expected (`V`'s code there is the same).
- **GOLF2 kernel diet** (from #26's certificate, merged forward). 8,506 constants that `certified` does not use moved
  out of the import closure into `<Top>Off` modules, imports pruned, and `layOk2_16`'s `decide` goes through a
  recursor lemma (20.1 → 8.5 M heartbeats). The move gate compares every constant against #27's dump: 0 theorem
  types changed; the only changed definitions are the five above (`runF2`, `preWU`, `convIns`, and the blob data
  `frzU20`, `dintsU20`) [measured]. Kernel census of `certified`'s cone: 1,412.2 → 1,362.8 M heartbeats (−3.5 %)
  [measured, before the `Φ_Q` levers].
- **GOLF3 kernel diet** (proof-only, on top of GOLF2). Every changed declaration is a theorem proof, never a statement
  or a definition: `omega` calls get only the hypotheses they use (an instrumented `omega` reported them), repeated
  `decide`s are proved once as lemmas and reused (Keccak RMFE, field and word operations, `E2` equalities; new module
  `LvmS2GUSchedLit` holds the S2GU schedule literal), and the front/node/plan proofs (`FrontU`, `NodeU`, `S2GUPlan`,
  `S2GUSched`) are re-proved with bounded case splits. Gate against the GOLF2 base: 0 theorem types changed, 0 removed,
  axioms of `certified` exactly the three [measured]. Kernel census of `certified`'s cone: 1,362.8 → 1,206.0 M
  heartbeats (−156.8 M, −11.5 %) [measured]; ≈ −61 s of kernel [model, census-to-harness scale].
- **Checked locally** [measured]:
  - harness cert **ok** (fresh, timing lock first, CPUs 8–15, quiet host): Lean kernel **454.0 s** (#29: 562.6 s
    loaded; #27: 549.3 s), `build_s` 861.5 s, 548 modules, peak 4.86 GB; axioms `propext`, `Classical.choice`,
    `Quot.sound`. Before GOLF3 (GOLF2 only) the same cert took 582.2 s under load (547 modules).
  - NGATE-U (the S2GU native gate) on blob U′: `staticOkBU20` true; `V_S` accepts the 8 honest files made by the
    shipped linked `.s` (a 5-step stream across both shapes, `S,0` at 1, 2^17, 2^20) and rejects 34 fresh U′ tampers
    (nonce, PoW, `E2` scalars, pin, tape, typed words, sums, `h`, shape); blob U′ regenerates byte-identically.
  - Byte identity of the prover: run on blob U (`LVM_TYPED_DIR`), the linked `.s` reproduces #27's stream on v4p and
    v2 and on v4 under Intel SDE (n = 1, three steps at 2^14, `S,0` at 2^17 + 1); on its embedded blob U′ it
    reproduces the reference U′ files of an independent build (stream and `S,0` at 1, 2^17, 2^20), and v4p, v2 and
    v4 (SDE) agree at 2^17 + 1.
  - quick bench (24 steps): ACCEPT, S 2.663 (P̄ 1.978, V̄ 0.685), S× 1.988, mean `V` 74.3 ms, `|π|` 283,960 B,
    `c_P` drift 0.034.

## Changes in #29 (planned-phi), since #28 (brisk-tape)

**Conclusion.** Prover-only, typed phase only: on dev it falls from 0.075 to 0.045 s per step (paired −30.5 ms,
whole step −58 ms) [measured]; proofs, transcript, blob and certificate are #27's. Calibrated on #28 (dev typed
−49 ms became ≈ −14 ms of eval fixed cost, P̄ −1.45 %), this roll models at **P̄ ≈ −0.7 to −1.2 %**: S× ≈ 0.933–0.938
and S ≈ 1.611–1.616 against #28's 0.944 and 1.6224 [model].

- **The Φ_Q batch** (`typed_phi.rs`, new `typed_phi/plan.rs`, `typed_phi/e2x.rs`). A plan built once at setup collapses
  the program's repetition: 311,698 runs of 514,827 entries reduce to 17,007 distinct inner lists, and 6,655 groups to
  3,583 distinct signatures. Each list is summed once per batch, groups with equal low parts share one sum, and each
  instance multiplies by its own high halves (the same field sum regrouped). E2 kernels keep the four carry-less pieces
  of a product unreduced and reduce once; coefficients 1, X, (l, 0), (0, l) take 0–2 carry-less products. On the v4 tier
  (cfg-gated on VPCLMULQDQ + AVX-512F/BW) four points share a 512-bit register (SDE: kernel instructions −54 %). Dev:
  the batch 30.7 → 12.4 ms (paired −17.2 ms) [measured].
- **The zerocheck and uz sumchecks** (`typed_t.rs`). 89 % of rows carry only their j = 0 coordinates, in long runs:
  such 2^8-slot chunks keep 48 B per slot (was 144 B) until round 8 and fold with 3 products. Rows are built with
  K products, rounds 0 and 1 of the zerocheck share one pass and a 4-to-1 fold (the round-1 table is never written),
  and the uz sumchecks' rounds 0 and 1 are merged the same way. Dev: zerocheck −15 ms, uz −2.5 to −4.7 ms [measured].
- **Byte identity [measured].** The linked `.s` equals #27's stream on v4p and v2 (an `S,0` at 2^18 + 2 then `S,1` at
  2^17, 2^20, 2^18; `S,0` at 2^17 + 1; v4p `S,0` at 2^20 + 1), on v4 under Intel SDE (n = 1, three steps at 2^14,
  `S,0` at 2^17 + 1), and on the timing runs' streams. Kernel self-tests (`phit` against the plain evaluator, `e2tzc`
  fast against general zerocheck, n = 1–16) pass; two Opus reviews found no correctness issue.
- **Calibration note [model].** #28's typed gain reached the evaluation machine at ≈ 0.28× its dev size (fixed b
  0.4273 → 0.4134 s for −49 ms dev), well below the 1/1.12–1/1.54 assumed so far for compute phases; this roll's
  projection uses #28's ratio.

## Changes in #28 (brisk-tape), since #27 (single-tape)

**Prover only.** The typed phases lose their serial stretches; proofs are byte-identical to #27's on every tier
[measured], and the certificate is #27's (`certificateU20S`, unchanged Lean).
- **Zerocheck:** each round's fold runs in the same pass as the next round's sums (no single-thread fold, no resize
  copies); the rows are built in round 0's pass.
- **Wiring and the `uz` sumchecks:** buffers are filled in place by the pool (no serial zero fill).
- **Eq tables:** the wiring's `u` and the relayout's `K` use two small eq tables instead of a 2^20 table.
- **A23 `Φ_Q`:** its 44 line points and the wiring point are one kernel batch; a Karatsuba `mul_y3`.
- **v4:** `inline(never)` on the Product staging.
- **Measured** [dev, linked `.s` against #27's linked `.s`, v4p, timing lock, 3 rounds, 12 pairs]: the typed phase
  0.137 → 0.088 s per step (paired −54 ms: zerocheck −30, accumulator and wiring −20; typed CPU −147 ms). Proof
  bytes [measured]: v4p, v2 and v4 under SDE reproduce #27's honest `S2GU` stream; the native gate (`V_S` accepts the
  honest files and rejects 34 tampers, guard TRUE, blob regenerated byte-identically) passes unchanged.
- **Projected** [model]: −35 to −48 ms per step on the evaluation machine, P̄ −3 to −4 %.

## Changes in #27 (single-tape), since #26 (halved-phi)

**Conclusion.** The Keccak sponge table `KS` and its link are merged into the tape: one GKR of depth 24 over
`μ = 21` rows proves both the chain and the in-circuit sponges (stage `S2GU`, BLUEPRINT2 §1 "uniform tape", now at
`E2`). The `KS` GKR, the `KS` link and the committed `KS.in`/`KS.mid` columns are gone. The freed words let the
stream block move down, so `C_main`'s root leaves carry 46 lanes (368 B, 3 Keccak permutations instead of 4). The
proof shrinks to **283,960 B** (−22,032 B) [exact]. The claim, the contract theorem's form and `εFS ≤ 2^-128` are
unchanged; no new soundness group class. The certificate is `certificateU20S` with the standard three axioms.

- **The tape (frozen transcript `utape.py`).** Rows `i < 2^20` are the chain (as before). Rows `2^20 + j`, `j < 2^13`,
  are the old `KS` rows with the virtual input `cont_j·Y[j−1] + Msg[j]` (`Msg` = the stream block's columns); the
  rest is void. T1 samples `r_<20`, reads 50 `E2` scalars (`a_l`, the 4 `D` word claims and 21 free lanes; `b_l`, the
  25 `Y` word claims), then samples `r_20` (R-BP2's order). The output claim is
  `v_l = (1 − r_20)·a_l + r_20·(e·b_l + (1 − e)·z*_l)`, `e = Π_{k=13}^{19}(1 − r_k)`, `z* = Keccak-f(0)`.
- **The wire.** One sumcheck over `x < 2^20` of `K_ch·G_D + K_ks·G_Y + I_ks·G_M`. `V` evaluates `K̃_ks` (four `MS`
  automata over `cont`'s two intervals, [1, 3960] and [8080, 8110]) and `Ĩ_ks` in closed form. Three slot reductions
  follow (`D`, the 2^18-word `Y` block, the stream block `S`), each with its row switch.
- **Layout `S2GU`.** `S` at word 5,242,880 (lane 40), the `Y` block at 5,767,168, the mini-bus from 5,971,968;
  occupancy 46 in the big shape, 44 in the small one. The extractor's 8-lane window starts at lane `40` for big
  statements and `32` for small ones (its cost is unchanged, 2^44.52).
- **The circuit (blob U).** The node program verifies an `S2GU` child, read for read with `V_S`. Products 249,188
  (blob GT 294,419: −15 %) [exact]; `T` dense 690,068, padded 763,923 ≤ 0.95·2^20 [exact]. The guard
  `staticOkBU20` holds natively with every conjunct.
- **`V`** (each fast path proved equal to the code it replaces): the slot weights are computed once per `τ`; the `Y`
  and `M` row claims are weighed on their own blocks.
- **`V` badge** [measured, dev, timing lock, CPU 8, both arms in the same runs]: S2GU 78.7 / 72.4 ms (small / big) against
  #26's 86.6 / 81.1 ms in the same runs (−7.9 / −8.7 ms; host load 25–50, ±3 ms). Split (small): wire 4.6 ms (was 15.7
  before the slot-weight twin), opening 20.6 ms; `KS` (8.9 ms) and its link (1.8 ms) are gone.
- **Prover.** The two halves of the tape run as one task list per pass (leanVM's segment variable); `KS`'s seven
  all-zero blocks run as the padding block. Step at 2^17 [measured, dev, LTO v4p, timing lock, 15 pairs]:
  1.561 → 1.422 s (paired −0.136 s) against #26's prover. It also carries the PFAST-3 prover bundle (v4 Product
  staging and phase 2, Groups Karatsuba, fused `chi_dot_quad`, open-main prover levers, nonce requests over two
  connections; proofs byte-identical): against the U-TAPE prover without it, 2^17 −0.017 s, 2^20 −0.26 s [measured,
  dev v4p, 3 rounds; the v4 kernels cannot run on dev]. v4p, v2, the linked `.s` and v4 under SDE reproduce the honest
  `S2GU` stream byte for byte [measured].
- **Checked locally** (#27) [measured]: harness cert ok, `build_s` 971 s, Lean kernel 549 s, 560 modules; quick bench
  ACCEPT, |π| 283,960 B, mean `V` 83 ms (loaded host).

## Changes in #26 (halved-phi), since #25 (looped-rows)

**Conclusion.** The typed backend moves to `E2` (stage `S2GT`), so `V` evaluates `Φ_Q` with `E2` products. `E2`
products cost half of `E3`'s. With the opening's claims sharing more of their work, native `V` falls below #21's
on both shapes on dev [measured]. The proof shrinks to **305,992 B** [exact]. The claim, the contract theorem's
form and `εFS ≤ 2^-128` are unchanged. The certificate is `certificateG20S` with the standard three axioms.

- **Typed phases at `E2` (frozen transcript `s2gt.py`).**
  - The zerocheck, the wiring, the relayout and A23 run at `E2` with 16-B scalars. Each of the 87 typed `E2`
    challenges has its own 8-B nonce and PoW (`g` least with `c·2^-g ≤ 7/8`; worst group `6·2^-131`, `errsT_at`).
  - The split is swapped: `K` rows and twin `E2` rows are native. The WHIR gadget's `E3` cells enter by their 3
    `K`-coordinates, batched by one `E2` challenge `ω`.
  - `Φ_Q` has 45 variables. The header's `acc_in` is 46 × 16 B, 2 PUB lanes per scalar, header 5,664 B.
  - The mini-bus stays at `E3`.
- **`Φ_Q` at `E2`** (`PhiQGC`).
  - The circuit's compiled term caches run at the `E2` point under a `K`-linear leaf map. Every product is one `E2`
    Karatsuba (3 `K` multiplications).
  - This is valid when no product meets two `E3`-carrying factors. The guard decides that once (`linOkX`).
  - Proof (`PhiQGC_eq`): the evaluator's correctness (`compileT_eq`) is generalised in place over a value ring, so
    the `E3` statements are instances. Then a simulation through `E3[X]/(X²+xX+1)` maps the `E2` run to the spec.
  - Speed [measured, same cache, unlocked]: 33.5 ms at `E2` against 48.0 ms at `E3`. Products: 294,419 [exact].
- **The circuit (blob GT).** The node program verifies the child's typed phases at `E2`, read for read with `V_S`.
  It also takes two opening cuts: a prefix memo for the word weights, and the row tail as loops. These are selected
  per stage (`FCtx.gt`), so blob v4 is unchanged.
  - `T`: dense 735,812, padded 850,391 ≤ 0.95·2^20 [exact].
  - The guard `staticOkBG20` holds natively with every conjunct.
- **`V`'s opening** (each fast path proved equal to the code it replaces):
  - row claims take their shared coordinates with transposed steps;
  - mini-bus claims are grouped per table;
  - typed region claims skip the regions their block misses.
- **`V` badge** [measured, dev, timing lock, CPU 8, all arms in the same runs, medians of `V_S` per check]:

  | step | #21 | #25 (S2GF, blob v4) | this |
  |---|---|---|---|
  | small (`n ≤ 2^18`) | 91.9 ms | 101.6 ms | **84.9 ms** |
  | big | 83.8 ms | 94.9 ms | **76.8 ms** |

  The split for this version (small, ms): `Φ_Q` 34.1, opening 20.6, tape 9.9, `KS` caller 8.0, mini-bus 4.0,
  `KS` link 2.0.
  The #25 column is #25's circuit with this version's opening code, so it is a little faster than #25 as shipped.
- **Prover.**
  - It runs the typed phases at `E2`. The typed phase falls from 0.19 to 0.14 s per proof [measured, loaded host].
  - It carries #23 and #24's speed-ups.
  - v4p, v2, the linked `.s` and v4 under SDE reproduce the honest `S2GT` stream byte for byte [measured].
- **Checks** [measured]:
  - `V_S` accepts all 10 honest blob-GT files (a 5-step `S,1` stream across both shapes, and `S,0` at 5 lengths).
  - It rejects all 18 tampers, including typed-phase nonce, PoW and `E2`-scalar tampers.
  - The blob regenerated from Lean is byte-identical to the frozen blob GT.
- **Lean.**
  - 27 frozen statements, all proved. Five were amended before their proofs, each for a stated cause:
    - `linOkX` added as a hypothesis;
    - 2 PUB lanes per 16-B scalar;
    - the S2GT memory reader;
    - the claim order `midMk 4`;
    - `linOkX` passed on to `harithG20`.
  - Kernel census of `certified`'s cone [measured, timing lock, loaded host]: 370.4 s with the census tool,
    ≈ 491 s on the harness scale [model; #22: 417.5 s tool = 553.9 s harness].

## Changes in #25 (looped-rows), since #22

**Conclusion.** The native `V` falls by **≈ 53 ms on small steps and ≈ 42 ms on big ones** against #22 on dev
[measured]. The proof (306,992 B), the transcript, the prover's code and the claim are unchanged. The circuit
evaluates the same relation with **31 % fewer `Φ_Q` products** (445,694 → 306,139 [exact]), and two `V`-side
changes cut the opening's work. The certificate is still `certificateF20S` with the standard three axioms; the
theorem's statement and `εFS` are unchanged. #22 was evaluated at S = 2.0495 with mean `V` 88.3 ms; the projection
for #25 is **V̄ ≈ 0.78, S ≈ 1.91** [model: V̄ = c_V·(V/c₀ + |π|/2^21) with #22's eval/dev `V` ratio].

- **Looped row switches in the circuit (blob v4).** The opening's two row-switch claims evaluated their CRT leaf
  weights in 21.5 k unrolled rows; KS's `ν` weights took 4.3 k more. Both now run as loops over the 64 components:
  - `rowLeafGL`, `rowNuGL`: a squaring loop gives the Frobenius powers, then a `ν` loop accumulates the component
    sums. Iteration `j` handles component `(j+1) mod 64`, which is correct because `a^(2^64) = a` in `K`
    (`fk_pow_two_pow_64`).
  - The PoW answers' booleanity rows run as 7 power-of-two loops instead of one block per answer.

  The row layout changes and nothing else does. The prover embeds the new blob files with no code change. `T`
  (dense 749,008 / padded 868,999 ≤ 0.95·2^20) still fits [exact]. `Φ_Q` at `E3` costs 49.7 ms on dev against #22's
  ≈ 70 ms [measured, timing lock]. Lean: `rowNuGL_ok`, `hs_rowLeafGL` and `powOk_of_blks` over the
  looped blocks (`LvmQRingCrtL`, `LvmQRingCrtLSem`, `LvmE2QAsmSpec`). The generic `rowNuOk_of_hs` keeps #22's
  `rowNuG_ok` as an instance.
- **`V`'s opening shares work across claims.**
  - The small opening's row claim shares the 18 coordinates common to its 7 regions (`RowR`/`RowZ` data through
    `tapeDFG`/`callerDFG`, `tensorDotT_split`, `rowStackW`).
  - The typed claims' halves are evaluated as pairs (`FItem.pairG`, `pairWS`).

  Both are proved equal to the spec decision (`decideProgFFG_eq`, `decideProgFF_eq`), so `V_S` refines the
  compiled `P_S` exactly as before.
- **`V` badge** [measured, dev, timing lock, CPU 8, all arms in the same runs, medians of `V_S` per check]:

  | step | #21 | #22 | this |
  |---|---|---|---|
  | small (`n ≤ 2^18`) | 96.6 ms | ≈ 164 ms | **111.1 ms** |
  | big | 90.1 ms | ≈ 138 ms | **96.1 ms** |

  The split for #25 (small/big, ms): opening 28.9/15.0, `Φ_Q` 50.5/51.0, tape 10.4, `KS` caller
  8.5/8.0, `KS` link 2.0, typed 4.7/4.5. `V_S`'s start-up (module initialisation, untimed) falls from ≈ 44 s to
  ≈ 19 s [measured].
- **Checks** [measured]:
  - `V_S` accepts all 10 honest blob-v4 files (5-step `S,1` stream across both shapes, `S,0` at 5 lengths).
  - It rejects every `V`-side tamper and all 14 prover tampers.
  - v4p = v2 = dev = the linked `.s`, and v4 under SDE, give byte-identical proofs.
  - `staticOkBF20` holds natively with every conjunct.
- **Prover: `packed-front` (#23) and `wide-lanes` (#24), merged.** The prover carries their speed-ups. They do
  not change the bytes:
  - the `E2` nonce requests go on the Fiat–Shamir connection, polled, with per-`g` batch sizes;
  - the v4 tier's tape and `KS` GKR at `E2` gets #23's six kernel changes (−11.5 % SDE instructions per tape layer)
    and #24's further v4 kernels (only `prover-v4.s` changes).
  With them merged on blob v4, v4p, v2, the linked `.s` and v4 under SDE reproduce the honest blob-v4 stream byte
  for byte [measured]. The details are in #23's and #24's NOTES.

## Changes in #22 (pinned-front), since #21

**Conclusion.** The proof shrank from 332,336 to 306,992 B [exact] and the prover's slope fell by 1.22–1.37 s per 2^20
chain steps on dev [measured]; the native `V` grew by 20–45 ms per check on dev, almost all of it `Φ_Q` [measured]. The
front (tape GKR, wire, slots, the then `KS` GKR and link) moved to `E2`: 16-B scalars, and every `E2` challenge pays its
own grinding (an 8-B nonce, `powOK g` on the answer's lane 2, `g` the least with `c·2^-g ≤ 7/8`). After `C_main`'s
cap, `V` samples the root OOD pin `z ∈ E^23`. Reads carry per-read widths (24, 16 or 8 B). The certificate was `certificateF20S` with the standard three axioms; the claim, the
theorem's statement and `εFS`'s form were unchanged. The full section is in #22's NOTES (`pinned-front`).

## Changes in #21 (lone-root, roll 11 "M′"; since #20)

pr21-94f86c9c3d9b: S = 2.070 (P̄ 1.238, V̄ 0.832), S× = 1.2485, mean `V` 62.0 ms, Lean kernel 291.1 s on the
evaluation machine.
- **`C_rec` merged into `C_main`:** one commitment, one opening. The child's 17 stream columns, `σ'` and the `X` rows
  became `C_main`'s stream block `S` (2^19 words at 5,767,168; small shape 2,621,440), column stride 2^14, in lanes
  40–47 of both shapes; the root leaf grew to 47 lanes (376 B, 4 permutations).
- `|π|` 464,544 → 332,336 B, `qS` 5,464 → 3,895; trace 105,472 → 75,593 lanes; mini-bus record (12, 1, 6, 633).
- The certificate `certificateM20`: `kcertSM` with one list (`L₀ = 124` candidate pairs, was 37,696); the extractor
  decodes the window at three levels (`decodeMP2` → `decodeMP1` → `decodeMP0`, list luck 2^-159.93 [exact]); the
  guard gained `sigInSB`.
- Dev, against #20's code: step medians 2^17 −0.106 s, 2^18 + 1 −0.111 s, 2^20 +0.022 s; V badge 0.847× / 0.773×.

## Changes in #20 (typed-spartan, rolls 7 and 8; since pr19-0bdb3ad5e872)

pr20-79a1a990cd1a: S = 2.341, S× = 1.258, Lean kernel 293.1 s (592.8 s on dev: eval/dev = 0.494).
- **The typed, bus-free backend (roll 8).** `T` holds one word per `K` result and three per `E` result; four static
  matrices `W`, `A`, `B`, `D` give `(Az)(x)·(Bz)(x) + (Dz)(x) + (Wz)(x) = 0` per constraint slot. Phases: a degree-3
  zerocheck (20 rounds), a degree-2 wiring sumcheck (21 rounds), the relayout of the child's trace, the accumulator
  at `Φ_Q`, and a depth-13 logup mini-bus for `capTpl`'s data-addressed reads only. `holds_of_wiring` turns the
  relation into `Program.Holds`/`Asserts`, so the gadget theorems do not see the backend. `Φ_Q`'s operands fall in
  four classes (bit maps, shifts, record reads by carry automata, points), compiled into atom code (`PhiQC_eq`).
- **`C_main` at ν = 23, rate 1/4:** (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, 58), lists of ≤ 124, 231, 615 members.
- **Two shapes split at `n = 2^18`:** small steps commit on the even words (half the NTT and level-0 hashing), with
  the big shape's proof size and queries. **`KS` at 2^13 rows.** **#17's Z2.**
- The certificate on the typed objects with a runtime guard; the bus path pruned; lazy Keccak layer weights in `V`.
- `|π|` 644,576 → 464,544 B, `qS` 7,426 → 5,464; dev against roll 7: steps −0.32 to −0.75 s, V badge 0.64×.

## Changes in pr19-0bdb3ad5e872 (since pr11-c65f417243e9)

pr11-c65f417243e9 was accepted at S = 3.508 (P̄ 1.684, V̄ 1.824), S× = 1.738, |π| 783,192 B.

- **`C_rec` at the Johnson radius (J2′):** (6, 1/4, 115) then (4, 1/8, 77), one OOD sample after level 0, final 2^9.
  Its lists have at most 304 and 311 members.
- **Knowledge soundness from one invariant used as the `KCert`'s luck, with no doom** (`kcertOfInv`, `kcertSJ`):
  "every non-good candidate pair fails some running claim". The invariant holds on honest runs. Each group's
  escape from it has the bound of the matching soundness escape, so KS costs only the extractor's list luck.
- **Extraction without a list decoder.** Off the list luck `LuckBJ`, the transcript is advice that singles out the
  good list member. The UD decoder programs (`decodeRec1`, then level 0) return it at the same fuel (`extJ`,
  `decode_SJ`).
- **#17's Z2**, ported, at 48/35 lanes.
- **Shared address columns** (EVD2): table evaluations 2,851 → 2,576.
- **Prover plumbing** with byte-identical proofs: the table build is off the witness critical path (`BITS` cone,
  H-taint), buffers are prepared before `ready`, and `prover setup` picks the worker count by timing a step.
- |π| 783,192 → 644,576 B. Evaluation: S = 3.088, S× = 1.555.

## Earlier rolls of PR #11

- **pr11-c65f417243e9** (S 3.508, S× 1.738):
  - grinding (g = 14) on every WHIR level, inside the query group (nonce `read`, PoW challenge);
  - `C_main` at the Johnson radius with OOD (230/115/77 queries), from longfellow-zk's proofs (`LvmJB*`);
  - a second UD level on `C_rec`;
  - shared position-bit tables (4,299 → 2,851 evaluations);
  - the faster native `V` (`VS20G`);
  - #12's chain kernel and #13/#15's v4 Keccak GKR.
- **pr11-9e756ce6880a** (S 4.374, S× 1.993): the digest-only chain tape (one depth-24 GKR segment, a 20-round wiring
  sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ m]`, a ring switch). `C_main` went from 2^26 to 2^24 words.
- **pr11-2f57ce79224a**: the chain link gated by `n`, and fast verifier twins proved equal (505 → 264 ms per check).
- **pr11-983bdcfa21d6** (S 10.17, S× 8.19): the first accepted version.

## Idea

### Trust surface: what is proved, and what is checked when V runs

- **The theorem.** `certified : CertificateR declared submission`.
  - `submission = submissionF20 = subGF staticOkF20 (VSFX NTF20)` (`LvmCertF20Inst`), with
    `staticOkF20 = staticOkBF20`.
  - `certified` is `Lvm.CT.certificateF20S` (`LvmCertF20Inst`; stage `S2GF`).
  - It uses only the axioms `propext`, `Classical.choice` and `Quot.sound` [measured, `#print axioms`]. There is no
    `sorry`, no `native_decide` and no added `axiom`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`, `fuel t = 2^46 + 8192·t`.
- **Proved in Lean, with no hypothesis left open.**
  - KS of the IOP. leanVM's doom-certificate framework is used with no doom. The luck is "the invariant broke, or
    the extractor's list luck" (`kcertOfInv`; M′'s `kcertSM` on `PSWithM`, here at the pinned middle phases:
    `kcertSF`, `εFS_kcertSF`).
    - The pin: `pin_escape`, `candZ_subsingleton`, `openPostP_of`, `midSpecP_of` (`LvmE2FPin`, `LvmE2FCert`).
    - The middle phases at `candZ` (`midSpecP_F₂`): the `E2` front (`tapeSpecE2`, `wireSpecE2`, `slotSpecE2`,
      `ksSpecE2`, `ksLinkSpecE2`, `rowSwitchSpec`, with `e2Sample`/`sampleG_escape` for the ground challenges), the
      word claims' split (`splitE2_sound`, `wordClaimE2`), and the typed phases on twin rows (`typedSpecX`:
      zerocheck with `ω`, wiring, relayout, the accumulator at `Φ_Q`, the mini-bus), relocated onto `C_main`'s
      stream block by `reloc20`.
  - The generic FS compiler from a doom certificate to the library's `KState`, which gives `KS`, now with per-read
    widths (`schemeSW`; `runW_eq_run` at width 24).
  - The node relation: `nodeF20 : NodeSound (VSFX NTF20) vk (GoodTF ∧ SBlk) (childSP P20F)` on stream-block pairs,
    with the window fact `childF20_win`. It rests on:
    - `holds_of_wiringX` and `twin_of_wiringX` (the typed relation with twin rows ⇒ `Holds`, `Asserts`);
    - `ReaddOk` from the mini-bus and the static reads; the input map, QLT's constants and `BITS`;
    - roll 7's gadget theorems (`chain_of_tape`, `qlink_sound`, `qsig_sound`) and the `E2` gadgets
      (`gE2mul_sem`, `gE2lin_sem`, `powRange_sem`);
    - the S2GF HAR `harithF20` (`Q_arith`'s rows ⇒ `V_S`'s decision: the front's phases, the typed claims, the
      opening's claims with the pin first, `PwOk`/`PosOk`);
    - `Φ_Q(acc_out) = y` through `PhiQCX_eq`.
  - The native `V` refines the compiled IOP verifier: `refinesF20` (`VSFX N` ⇒ `schemeSW` at `PSWithM (midP …)`).
    Its fast twins are proved equal to their originals (`decideProgFF_eq`, `tensorDotT_eq`, `dOpenFF_eq`, …).
  - The extractor's output and cost: `computesXF20`, `ext_eqF20` at the declared fuel.
  - The Johnson code facts of every WHIR level (`codeFacts_johnson`; `cfgMain23Jq`), from the vendored
    longfellow-zk theorems (`LvmJB*`; `LICENSE-longfellow`).
  - `E2` is a field (`no_root` by the additive Hilbert 90 criterion, `card_E2`); `FE2`'s fast product equals it
    (`fe2_mul_eq`).
- **Discharged by kernel `decide` at the frozen record:** the S2GF schedule's sizes and read widths
  (`checks_P20F`), the extractor's replay facts (`replayOK_stF20`), the phases' lanes, the typed region's end and
  the tape's start, `Q_link`'s static checks (`hQF20`), the plan facts of the circuit.
- **Checked when V runs: the guard `staticOkBF20`.**
  - The kernel cannot build `Q` or evaluate the layout solver's output, so these facts are one closed `Bool`:
    - `staticOkTF20`: `Q.wf`, `lay.Ok Q`, `twinsOk`, `Φ_Q`'s two coordinate caches against the matrices, V's
      regions, the mini-bus record, QLT's constants, `g`-injectivity;
    - `nodeChkBG` (at 4,295 sponge blocks and 750 `PUB` lanes), `sigInSB`, `oneOkB`;
    - `harChkBF20`: the typed region's end, the PoW lanes, the opening's position, the typed regions' regularity.
  - The certificate case-splits on the guard without evaluating it (`certificateR_guardF`): soundness holds for
    either value; only completeness depends on the guard being `true`. It is `true` at P20 [measured].
- **Completeness** is the `W` kind (`P := encode`, error 0). The SNARK prover is tested by the harness.
- **Soundness error.**
  - Model: ≈ 2^-128.33, unchanged: `C_main` level 0's query group (115 positions at rate 1/4, after the 2^-14 PoW
    discount). The ground `E2` groups sit at 2^-129.0 (c 1 and 2), 2^-128.42 (c 3) and 2^-128.48 (c 46); the pin
    at 2^-174.6 [model].
  - Lean: `εFS = ε + εB + hash ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128` (`εFS_kcertSF`), the same form as #21.
    `εI = εS = 7·2^-131` bounds every group's escape, the middle phases' lead is `errE (C(124,2)·23) + 6·2^-131`,
    and `εL = 2^-132` is the list luck.
  - The hash term covers collisions, state repeats and 32-byte window hits at any offset of any query.

### Construction

**Tree shape: one SNARK per step.** Every output is `nodeStmt c_L (leafStmt h n)`.
- The right child is a witness-sending leaf `⟨encode (leaf s n), [], σ_leaf⟩`; `V` checks `σ_leaf` natively, and
  the SNARK proves `chainEnd s n = h`.
- The left child is the previous signed proof `(π', tr', σ')`, committed and verified in the circuit.

A flag `b` selects leaf mode (step 1's first proof) or node mode. There is one schedule and two commitment shapes
chosen by `n`, so every proof has the same size and makes the same queries. A `W` proof never starts with `'S'`.

**Chain tape (2^20 rows, only the digest `D[4]` committed).** Row `i`'s input is virtual (`Pad43(s)`, then
`Pad43(D[i−1])` up to `m = n − 1`, then zero). `D = Keccak-f(in)[0..4)` is proved by leanVM's GKR (RMFE χ), one
segment of 24 rounds, at `E2` with grinding. A 20-round wiring sumcheck with the public kernel
`ι(x + 1)·[x + 1 ≤ m]`, a slot reduction and a row switch tie the GKR's input claim to bit-slice claims on `D`.
The boundary `D̃(bits(m)) = h` gives `chainEnd s n = h` (`chain_of_tape`).

**Sponge table `KS` (2^13 rows).** The same GKR (two 12-round segments) at `E2`, with a word-linear sponge link:
the child's trace sponge (message lanes = the stream block's columns), one WOTS walk and the statement hashes.
`BITS` rows decompose words for prefixes, WOTS digits, positions and range checks.

**One commitment, pinned.** `C_main`: 2^23 `K` words: `D` (2^22), `T` (2^20), `KS`, the stream block `S` (2^19
words at 5,767,168; 2,621,440 in the small shape, on even words), `KSY2` and the mini-bus columns. The stream's
physical words lie in lanes 40–47, the only lanes `Ex` decodes. Right after the cap, the root OOD pin (`z ∈ E^23`,
`a = C̃_main(z)`) cuts the list to `candZ`, of at most one member.

**Stacked WHIR at the Johnson radius, with grinding.** (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, 58); caps
2^8/2^7/2^7; OOD after levels 0–1; final 2^9; lists of ≤ 124, 231, 615. Every level grinds 14 bits. Every claim is
`K`-linear on `C_main`; an `E2` claim enters as its two halves.

**The extractor decodes `C_main`'s window with UD programs on advice.** `decodeMP2` (2^13 positions) →
`decodeMP1` (2^16) → `decodeMP0` (2^19, lanes 40–47), list luck 2^-159.93 [exact], within the
declared fuel (`computesXF20`; the generic `computesXS` over the S2GF schedule). No list is ever enumerated.

**Fiat–Shamir is a hash chain over the contract oracle.** `q₀ = "lvm/1\0\0"`, then the seed `a₀ ‖ header`; each
query is `st ‖ pending messages`; a challenge is lanes 0–2 of the answer (`E3`), or lanes 0–1 (`E2`, with lane 2 the
PoW). Reads are 24, 16 or 8 B by position. Merkle leaves and nodes are queries; paths stop at the cap.

**Verifier circuit: LoopIR on a typed backend.** `Q = Q_link ++ Q_sig ++ Q_arith` runs the child's verifier on its
trace: `Q_link` (the trace follows the schedule), `Q_sig` (the WOTS walk, the header and statement), `Q_arith`
(`V_S`'s accept bit: the pin, the `E2` front with its PoW checks, the typed phases, the opening). Blocks are row
templates over loop dimensions with affine addresses; `E2` values are twin rows. The backend commits only results.

**The recursion fixed point: a self-fold accumulator (A23).** Every `S` proof folds `acc_in = (pt ∈ E^44, y)` with
its own matrix values: `κ ∈ E^3`, `y_own = Σ_o eq(κ, o)·v_o`, a degree-44 line polynomial `h` with `h(0) = acc_in.y`,
`h(1) = y_own`, then `acc_out = (line(t), h(t))`. `V` checks only `Φ_Q(acc_out.pt) = acc_out.y`, natively; the
parent's circuit recomputes the child's fold.

**Native `V`.** `VSFX NTF20 = VSF P20F accVF (decideFFX P20F NTF20)`: parse, drive the S2GF schedule, then
`decideFFX` (the core checks and `Φ_Q(acc_out) == y`). It is direct functional Lean on `UInt64` field kernels proved
equal to CompPoly; it does not interpret `Q`.

### What came from where

| | kept | cut | changed |
|---|---|---|---|
| leanVM protocol | `K`, `E` (and `E2`, from leanVM's `gf2_64x2`); Keccak GKR with RMFE; `g`-power bus, grand product (the mini-bus; since stage `S2GL` it ends in three linear claims on `C_main`, with no table sumcheck); ring switching; stacked WHIR with OOD at the Johnson radius | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine | KS from an invariant used as luck, with no doom; `C_rec` extracted by UD decoders on advice; grinding inside the query group; hash-chain FS; Merkle through the oracle with caps; one commitment with a root OOD pin; the front at `E2` with per-challenge grinding; per-read widths; LoopIR; digest-only chain tape; accumulator; typed backend |
| Spartan (Setty) | a zerocheck over row constraints, then a sumcheck against sparse wiring matrices | SPARK and every committed matrix | a write matrix over the result memory; equality mode over `E`; the matrices' extension evaluated by class kernels and carry automata, once per proof through the accumulator |
| leanVM `formal/` (4.35) | DSL, `Cert`, doom rules; Keccak GKR, sumcheck, grand product, bus, spine, ring switching; WHIR (≈ 120 modules, ported to 4.34.1) with its OOD and Johnson path | VCVio, ArkLib, Clean, leanISA, `Extraction`, `Cost`, `Guest` | `LevelCode` with Johnson constants on both commitments; `kcertOfInv` |
| longfellow-zk `formal/ligero` (Apache-2.0, via the Flock entry's flat port) | the Johnson list bound, Haböck's strong MCA (`LvmJB*`, 30 modules / 7.8 k lines) | — | module and namespace names only (`LICENSE-longfellow`) |
| leanVM Rust | `primitives`, `parallel`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core` (gkr, leaf, constraints), std-only | `rand`, `tracing`, jemalloc | transcript, Merkle, WHIR config, portable clmul tiers, a layers-only GKR entry point (`prover/src/lv/PATCHES.md`) |
| leanvm-gkr-fast (#13), leanvm-fast-verify (#15) | v4 tier only: #13's re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0, `src/lv/keccak_gkr_v4/`), with #15's every-round storage | #13's `pcs`/`primitives`/`hash` changes; #15's Lean | `generate_uncommitted` for the tape's extents; `every` = 1 (`PATCHES.md`) |
| relay-slim (#17) | Z2: root leaves of occupied lanes only (`Scheme.occ`, `padRow`, the circuit's zero window, the extractor's reader; Apache-2.0); the C-order link in `build-asm.sh` | its prover scheduling, the 2-lane tape ramp | lanes recomputed: 46/35 at ν = 23 (#20), 47 at M′ (one commitment) |
| lone-root (#21), typed-spartan (#20), listless-whir (#19) | everything not listed under "Changes since #21" | #19's bus backend | this root's previous rolls |
| relay-echo (#12) | the AVX-512VL chain kernel generator `gen_vlasm.py` (Apache-2.0, unmodified; `LICENSE`) | its C and Lean | emitted as Rust `asm!`, chosen at run time |
| leanerVM | bus `lookup_sound`, generator facts | ArkLib-typed PIOP layers | — |
| earlier Flock-class entry | field kernels; extractor DSL, log index, sort, lookup, FS scan; barycentric decoder; `mca_ud_line`; Keccak sponge layer; W/S dispatch; oracle client, format, asm pipeline | PIOP, layout, Ligerito proofs; BLAKE2s circuits | decoding over `K` rows in the novel basis |
| organiser library | `WitnessSending`, `KState`/`KS`, fast Keccak and signature twins | — | — |

## Result

**Harness.**

| run | result |
|---|---|
| pr11-983bdcfa21d6, evaluation machine | ACCEPT; S = 10.17, S× = 8.19 |
| pr11-9e756ce6880a, evaluation machine | ACCEPT; S = 4.374, S× = 1.993 |
| pr11-c65f417243e9, evaluation machine | ACCEPT; S = 3.508, S× = 1.738 |
| pr19-0bdb3ad5e872, evaluation machine | ACCEPT; S = 3.088 (P̄ 1.511, V̄ 1.577), S× = 1.555; Lean kernel 260.1 s |
| pr20-79a1a990cd1a (#20), evaluation machine | ACCEPT; S = 2.341, S× = 1.258; Lean kernel 293.1 s |
| pr21-94f86c9c3d9b (#21), evaluation machine | ACCEPT; S = 2.070 (P̄ 1.238, V̄ 0.832), S× = 1.2485, mean V 62.0 ms; Lean kernel 291.1 s |
| #22 (pinned-front), harness cert (dev VM, pin 7ecd179, timing lock) | ok, gate PASS; Lean default kernel **553.9 s** at the default cap (≈ 274 s on the evaluation machine at #20's 0.494× [model]); `build_s` 627.5 s (8 CPUs), peak 4.90 GB, 516 modules built [measured] |
| #22, local quick season (dev VM, 8 CPUs; the first 24 published lengths) | ACCEPT; S 3.125 (P̄ 2.215, V̄ 0.910), S× 2.252, mean V 134.0 ms, \|π\| 306,992 B [measured]; host loaded (`c_P` drift 0.096), and a prefix is not comparable with full-season numbers |
| #22, evaluation machine | ACCEPT; S = 2.0495 (P̄ 1.125, V̄ 0.924), S× 1.145, mean V 88.3 ms |
| #25 (looped-rows), harness cert (dev VM, CPUs 8–15, host loaded) | ok, gate PASS; Lean kernel 572.8 s (548.0 s in an earlier run of the same Lean), `build_s` 953 s, 519 modules [measured] |
| #25, local quick season (24 lengths, host loaded) | ACCEPT; S 3.179 (P̄ 2.338, V̄ 0.841), S× 2.366, mean V 113.0 ms, \|π\| 306,992 B [measured] |
| #23 (packed-front, prover-only on #22), evaluation machine | ACCEPT; S = 1.9973 (P̄ 1.073, V̄ 0.925), S× 1.092 (sum record) |
| this version, harness cert and local quick season | in the PR body (dev VM, timing lock) |

**Frozen P20 record (stage `S2GF`)** [exact, `checks_P20F`]:

| quantity | value |
|---|---|
| `\|π\|` | **306,992 B** (#21: 332,336 B) |
| `qS` | **3,959** (`qV` 16,384) |
| reads | 6,973 per proof: 1,085 × 8 B (nonces), 4,283 × 16 B (`E2` scalars), 1,605 × 24 B (`E3`) |
| trace | 73,001 lanes (584,008 B; 4,295 sponge blocks of KS13's 7,680) |
| typed region `T` | 739,864 words dense, 859,855 padded; 317,394 rows; 551,317 constraint slots |
| `Φ_Q` | 44 variables; two coordinate caches, 445,694 `E` products per evaluation (#21 ≈ 216 k) |
| root leaf | `C_main` 376 B (47 lanes, 4 permutations) |
| P8 | `\|π\|` 153,968 B, `qS` 1,900 |

**Prover, dev VM.** QEMU, 8 threads, shared host; its cpuid hides PCLMULQDQ (the instruction executes), and
VPCLMULQDQ/GFNI do not, so the runs use v4p (AVX-512 + PCLMUL).
- **Step times** against #21: see "Changes since #21".
- **Grinding:** 1,085 challenges and 6.0–6.8 k attempts per proof; search wall 0.074–0.107 s per proof including
  the accepted FS steps [measured].
- **`.s` files.** v2 50.0 MB, v4 49.4 MB, v4p 48.6 MB (embedded layout dumps); `prover/` is ≈ 175 MB, under the
  256 MiB cap; the linked binary is 86.0 MB and picks v4p on dev. No local path string appears in any `.s`.
- **`prover setup`** self-tests each variant against the portable reference's digest and writes a cap that
  `dispatch.s` honours. v4 was byte-identical to v2 under Intel SDE.

**Verifier**, dev VM (one core, CPU 8 under the timing lock):

| | small step | big step |
|---|---|---|
| #21's `V` (same tool) | ≈ 105 ms | ≈ 100 ms |
| #22, first S2GF `V` | ≈ 1,970 ms | ≈ 1,137 ms |
| #22, shipped (fast twins) | **≈ 145 ms** | **≈ 123 ms** |

Per phase in the shipped `V` (small / big): tape ≈ 10 ms, `KS` ≈ 9 ms, `KS` link ≈ 1 ms, opening ≈ 37 / 15 ms, `Φ_Q`
≈ 70 ms [measured]. The first `V` spent its time in quadratic list lookups of the Keccak layers' `eq` table and in the
row switch's weight, which recomputed 128 × 128 products per evaluation; fast twins proved equal to the originals
(`decideProgFF_eq`) replaced them with no change to statements or proof bytes. Start-up ≈ 44 s per process (#21 ≈ 14 s),
outside the timed check.

**Score.** On the evaluation machine:

| version | S | S× |
|---|---|---|
| pr11-983bdcfa21d6 | 10.17 | 8.19 |
| pr11-9e756ce6880a | 4.374 | 1.993 |
| pr11-c65f417243e9 | 3.508 | 1.738 |
| pr19-0bdb3ad5e872 | 3.088 | 1.555 |
| pr20-79a1a990cd1a | 2.341 | 1.258 |
| pr21-94f86c9c3d9b | 2.070 | 1.2485 |
| #7 | 105.9 | 505.8 |

**Error budget (model, P20, per fresh query, log₂).** After the pin, the middle phases' groups take no union over
candidates (`L₀ = 1`; #21: 124, +6.95 bits), so the `E3` rows below are #21's lowered by 6.95 bits. The WHIR query
groups include the 2^-14 PoW discount.

| group | bound |
|---|---|
| root OOD pin (`C(124,2)·23/\|E\|`) | −174.6 |
| `E2` groups with grinding: c 1, g 1 / c 2, g 2 / c 3, g 2 / c 46, g 6 | −129.0 / −129.0 / −128.42 / −128.48 |
| `E3` typed groups: `τ`, `ω`, `κ` / zerocheck rounds / wiring and relayout rounds / accumulator `t` | ≤ −186 |
| mini-bus fingerprint (depth 12) | ≤ −177 |
| row switches (7 `E3` ring-map samples each) | ≤ −189 |
| stacked-claim batching (`(J − 1)·124/\|E\|`, `J ≤ 2^40`) | ≤ −129 |
| WHIR folds (levels 0–2) | −130.00, −132.00, −130.00 |
| WHIR OOD points (levels 0–1) | −173.22, −170.77 |
| WHIR query groups (levels 0–2) | **−128.33**, −129.07, −129.92 |
| extractor list luck / hash | −159.93 [exact] / Lean ≤ −139 |
| **worst** | **−128.33** (Lean: `εFS ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128`) |

**Lean.** `lean/` holds 873 flat modules, ≈ 264 k lines (#21: 703, ≈ 213 k); the cert builds 516 of them (`Solution`'s closure; #21: 638). Roll E2-FT added 170
modules and changed 513 (+130 k / −79 k lines against #21, including a mechanical fold of 267 single-importer modules
into 121 hosts, whose old files stay as one-line import stubs) [measured, `git diff --shortstat`].

## What failed, and why

**Roll E2-FT.**
- **`V` got slower, not faster.** The design modelled −3.6 ms of `V` on the evaluation machine for the `E2` front
  [model]; the shipped `V` is +20 to +45 ms per check on dev [measured].
  - `Φ_Q` went from ≈ 40 to ≈ 70 ms: 445,694 `E` products against ≈ 216 k. The split per segment [measured]: the
    front +78 k (the twin rows' second coordinate alone 64.7 k), the typed phases and opening +102 k (one unrolled
    block of 33,023 rows evaluates every claim's weight: ≈ 525 claims at ≈ 63 rows), the 1,085 one-instance PoW
    blocks +72 k. The evaluator's cost is products, at ≈ 130 ns an instruction (software clmul).
  - Looping the PoW blocks (blob "v2") cut terms by 28 % but raised products by 7.7 % and `Φ_Q` to 76.7 ms: the
    loops' strides (63/62/58 words) are not powers of two. Only the row switches' loops were kept.
  - The first S2GF `V` took 1.1–2.0 s per check (quadratic `List.getD` over a 2,048-entry `eq` table per bit, and a
    row-switch weight that recomputed 128 × 128 products per evaluation). Fast twins brought it to 0.12–0.15 s.
  - Start-up rose from ≈ 14 to ≈ 44 s (untimed); the model's ≈ 23 s was not reached.
- **The typed backend at `E2` (stage `S2GT`) did not ship.** Its 10 statements are proved and its prover runs
  (typed phases 0.87 s against 1.50 s at S,0, n = 1, on a loaded dev build [measured]), but its circuit was not
  built in time. It is the next roll's lever on `Φ_Q` (two `E2` products cost less than one `E3` product).
- **Statements found false or unsatisfiable while proving** (each fixed before or at the freeze, none relaxed):
  - the typed zerocheck's group: `ω` is drawn with `τ` and no prover move between them, so the group has 21 samples;
  - the middle phases' good pair needed S2GF's `KS` continuation rows: with #21's 4,447 blocks an honest S2GF run on
    a column with no continuation at row 4,300 passes every check;
  - the compiled reading took 24 B per read, so no S2GF verifier could refine any program: hence per-read widths;
  - the four `V_S` bugs of "Changes since #21".
- **Elaboration and kernel traps.** Any term elaborated against `pinProg.NoCommit` ran out of heartbeats (`whnf`
  unfolds the 23 nested samples); defeq through builder runs hung the kernel (`rowValD …` against the switch's
  `eqR`). The fixes: never state the unfolded property, state values as patterns and rewrite with explicit lane
  equalities, `rw` instead of `simp` with `rfl` lemmas over program terms.

**Rolls 7 to 11.**
- Roll 7 alone grew the proof (ν = 24 leaves need 58 lanes) and modelled about −3 % on S, so it shipped inside #20.
- The design's per-block padding gave `T` 1.07 M words; binary chunks give 0.81–0.86 M.
- Protocols rejected at design [model]: GKR over the program's DAG (depth in the thousands), SPARK or any committed
  matrix (+110 KB), per-instance native wiring evaluation (≈ 90 ms), committing the awkward operands under a logup.
- `Φ_Q`'s first evaluator took 254,900 products and 68.4 ms against a 150 k / 28 ms design estimate.
- V start-up was 205.8 s per process at first (quadratic template recomputation, bucket copies, array-building
  comparisons); fast copies proved equal to the originals brought it to 16.5 s.
- Integration bugs: `KS` aliases mapped lane-major, the small-shape mux at the wrong ν, a mini-bus record with no
  fixpoint, the tape's start 2,805 lanes early.
- `irreducible_def` produces an `opaque` constant, which the gate rejects.

**Earlier.**
- **leanVM's extractor.** Guruswami–Sudan decoding has a proved cost of ≤ 2^81 + …. Even Berlekamp–Welch over
  64 lanes × 2^55 is ≈ 2^12 over the cap. Hence `Ex` decodes only the stream, with UD decoders and the transcript as
  advice.
- **A relativised doom for Johnson `C_rec`.** It holds on honest runs, so as a doom it applied only with an empty
  good set. The fix (pr19) uses the invariant as the complement of luck.
- **Johnson from BCIKS20's bound.** It gives correlated, not mutual, agreement, and is a `sorry` in ArkLib at our
  pin. `C_main`'s level 0 would need 297 queries at its size.
- **Witness-sending nodes over SNARK leaves.** Each leaf is ≥ 0.75 MB, so the 64 MiB cap breaks near step 85.
- **Step 1 as one SNARK over two chains.** That needs a 2^27 commitment (≈ 14.6 GiB).
- **leanVM's VM guest as the circuit.** Guest correctness is 300 k+ lines of proofs, and a 2^20 chain is
  2^27–2^28 cycles.
- **Committing the whole chain row** (v1: 3,456 bits a row, `C_main` at 2^26). The digest tape commits 256 bits.
- **One field.** `K` alone cannot carry 2^-128 per challenge; `E2` can only after the pin removes the list union.
- **In-circuit self-evaluation of the fixed columns** (≥ 1.5–2.5 M words) and **plain deferral** (no sound fold
  challenge). The accumulator replaced both.
- **Kernel-deciding the whole program.** `mergeSort` is well-founded recursion, and a structural sort is OOM-killed
  at 12 GB. Hence the runtime guard.
- **The extractor's FS replay by query prefix** was unsound, because abandoned branches share prefixes.
- **Testing v4 without the machine.** v4 raises SIGILL on the dev VM. Under Intel SDE its proofs are
  byte-identical to v2's.

## What to try next

1. **`Φ_Q` back under 45 ms on dev** by the circuit's shape [estimate, untested]: loop the opening's per-claim basis
   over claims of one shape (≈ 112 k → ≈ 20 k products, ≈ −15 ms); loop the unrolled front blocks (≈ −5 to −10 ms);
   copy each PoW answer's lane 2 into a stride-1 region and loop the range checks in power-of-two runs (≈ 72 k →
   ≈ 10 k products, ≈ −10 ms).
2. **The typed backend at `E2` (`S2GT`)**: statements and prover exist; `|π|` 305,072 B at occupancy 46 [model].
3. **Batch each `E2` claim's halves before the opening** (one challenge per pair): half the front's claims.
4. **The affine-combiner WHIR at `E2`**, which removes `E3` arithmetic from the PCS: −17.5 KB [model].
5. **Start-up** (≈ 44 s, untimed): fewer `Φ_Q` terms shorten the cache build and its check.
6. **Prover speed.** The tape GKR is most of the slope; the 8-wide `E2` local rounds are still unported
   (≈ 4 % of a layer [estimate]). The `C_main` commit is bound by the oracle's Merkle hashing.
