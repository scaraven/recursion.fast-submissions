# looped-rows

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #11, #7, #12, #13, #15, #17, #19, #20, #21, #22, #23, #24

This root continues #22 (`pinned-front`, roll "E2-FT" = pr22-88df56a2750c), which continued #21 (`lone-root`), #20
(`typed-spartan`), #19 (`listless-whir`) and PR #11 (`leanvm-inspired`), and it carries the prover-only rolls
`packed-front` (#23, the current sum record at S = 1.9973) and `wide-lanes` (#24). This root is stage `S2GF` on blob
v4: the same proof size, transcript and statement as #22, with a circuit that evaluates the same relation in fewer
`Φ_Q` products and a `V` whose opening shares work across claims. "Changes since #22" is relative to #22's submitted
version, which was evaluated at S = 2.0495, S× = 1.1454 (mean `V` 88.3 ms). The sections from "Changes since #21" on
describe #22's construction, which is otherwise unchanged.

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, ring switching and
stacked WHIR. It is reshaped for the contract in four ways:
- an extractor that decodes only the child's stream block (lanes 40–47 of `C_main`), with unique-decoding
  programs on advice;
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

## Changes since #22 (pinned-front)

**Conclusion.** The native `V` falls by **≈ 53 ms on small steps and ≈ 42 ms on big ones** against #22 on dev
[measured]. The proof (306,992 B), the transcript, the prover's code and the claim are unchanged. The circuit
evaluates the same relation with **31 % fewer `Φ_Q` products** (445,694 → 306,139 [exact]), and two `V`-side
changes cut the opening's work. The certificate is still `certificateF20S` with the standard three axioms; the
theorem's statement and `εFS` are unchanged. #22 was evaluated at S = 2.0495 with mean `V` 88.3 ms; the projection
for this version is **V̄ ≈ 0.78, S ≈ 1.91** [model: V̄ = c_V·(V/c₀ + |π|/2^21) with #22's eval/dev `V` ratio].

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

  The split for this version (small/big, ms): opening 28.9/15.0, `Φ_Q` 50.5/51.0, tape 10.4, `KS` caller
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
- **Next.** The code for stage `S2GT` (typed phases at `E2`, `Φ_Q` evaluated with `E2` products) is in `lean/` but
  outside `Solution`'s closure. Its statements are in progress. Measured on dev, it reaches 104.4 / 85.5 ms.

## Changes since #21 (lone-root)

**Conclusion.** The proof shrinks from 332,336 to **306,992 B** [exact] and the prover's slope falls by
**1.22–1.37 s per 2^20 chain steps** on dev [measured]. The native `V` is slower: **+20 to +45 ms per check** on dev
over roll 11 [measured], almost all of it `Φ_Q`, which grew with the circuit. The certificate is `certificateF20S`
with the standard three axioms; the claim, the theorem's statement and `εFS`'s form are unchanged. Projected on the
evaluation machine: S ≈ 1.96–2.02 (−2.5 to −5.4 % against #21's 2.070), S× ≈ 1.09–1.11 (−11 to −13 %) [model, below].

- **The front at `E2` (tape GKR, wire, slots, `KS` GKR, `KS` link).** Every challenge of those phases is in `E2`,
  every prover scalar there is 16 B (two `K` words, `re` then `im`), and every `E2` challenge pays for its own
  grinding.
  - An `E2` challenge is lanes 0–1 of the 24-B `E` answer (`e2OfE`). It is preceded by its own 8-B nonce (one `K`
    word) and accepted iff lane 2 is `< 2^(64−g)` (`powOK g`). `g` is the least with `c·2^-g ≤ 7/8`, for the group's
    numerator `c`: (c, g) = (1, 1) ×62, (2, 2) ×87, (3, 2) ×900, (46, 6) ×36; 1,085 nonces per proof [exact].
  - One separator sample (its answer discarded) follows the prover's message and comes before the first nonce of
    a run of front phases, so no nonce can be ground against the previous answer.
  - The doom calculus is generic in the field (`{F} [Field F] [Algebra K F] [CharP F 2]`): the Keccak GKR (RMFE
    layers, `layersSpecE2`), the wiring kernels, the zero test and the `KS` link algebra are stated once and used at
    `E2` (`tapeSpecE2`, `wireSpecE2`, `slotSpecE2`, `ksSpecE2`, `ksLinkSpecE2`, `e2Sample`, `sampleG_escape`,
    `sumcheckRoundG`). The RMFE needed no new literal check at `E2`.
  - The two bit-slice ring switches (the wire's and `KS`'s) are row switches: 2^7 rows, 7 `E3` ring-map samples, no
    nonce (`rowSwitchSpec`).
  - Word claims enter the PCS by the tensor switch: an `E2` claim on a `K` column is two `K`-linear claims (`re`,
    then `im`, in place), whose weights `V` evaluates in `Quad Ext3` (`wordClaimE2`, `tensorW_eq`).
- **The root OOD pin.** Right after `C_main`'s cap, `V` samples `z ∈ E^23` and reads the claimed value
  `a = C̃_main(z)` (24 B). The pin's claim is the first claim of the opening's list.
  - The list members consistent with `(z, a)` number at most one, except with probability
    `C(124, 2)·23/|E| ≈ 2^-174.6` (`pin_escape`). The middle phases then run against `candZ (z, a)`, which has at
    most one element by construction (`candZ_subsingleton`), so their groups take no union: `L₀ = 1` (#21: 124).
    That is what makes 128-bit challenges enough.
  - M′'s certificate is reused unchanged: `P_S = PSWithM (midP mid)`, and `kcertSF` is `kcertSM` at the pinned
    middle phases (`midSpecP_of`, `midShapeP_of`). The middle phases' lead is `leadF₂ = 6·2^-131`; the pin's
    `errE (C(124,2)·23)` sits in front of it, under `εS = 7·2^-131`.
- **Twin-row `E2` cells and the coordinate-split typed zerocheck.** The circuit verifies the child's `E2` front.
  - An `E2` value is two `K` cells written by two adjacent rows `Op.e2 f false` and `Op.e2 f true` with the same
    operands (`f` is `a·b + d` or `a + k·b + k'`). `Ty`, the memories, the layout's word maps and `interp_unique`'s
    statement are unchanged (`twinsOk`, `e2Pair_of_holds`).
  - The first row's constraint slot carries both coordinates. The zerocheck draws `ω ∈ E` after `τ` (in `τ`'s
    group), `V` reads 6 values at `r_x` (A0, A1, B0, B1, C0, C1) instead of 3, and the wiring reads 8 matrix values
    `v_{o,s}` (tag `o + 4s`) instead of 4 (`twin_of_wiringX`, `holds_of_wiringX`, `typedSpecX`).
  - `Φ_Q` has 44 variables (3 selector bits lowest, then 20 for `x`, 21 for `y`); the accumulator's `κ` has 3
    coordinates and `h` 45 scalars (`PhiQCX_eq`).
  - In-circuit `E2` arithmetic and the PoW range check are gadgets with proved semantics (`gE2mul_sem`,
    `gE2lin_sem`, `powRange_sem`).
- **The compiled scheme reads with per-read widths.** A read takes 24, 16 or 8 bytes (`Scheme.rw`, `schemeSW`),
  so `V_S` at `S2GF` refines a compiled program: 6,973 reads per proof, 1,085 × 8 B, 4,283 × 16 B and 1,605 × 24 B
  [exact, `checks_P20F`]. The library theorems (`isNode_unique`, `kstate_of_kcert`, `ks_of_kcert`,
  `queries_V_le`) keep their statements for mixed widths; the old uniform `run` is the instance `rw = 24`.
- **Sizes (stage `S2GF`) [exact, `checks_P20F`; measured on every proof below].**
  - **`|π|` 332,336 → 306,992 B (−25,344 B, −7.6 %)**, `qS` 3,895 → 3,959.
  - The child's trace 75,593 → 73,001 lanes (584,008 B), sponge blocks 4,447 → 4,295. The root leaf keeps 47 lanes.
  - P8: `|π|` 177,288 → 153,968 B.
  - `T`: 739,864 words dense, 859,855 padded (≤ 996,147), 317,394 rows, 551,317 constraint slots (#21: 509,014).
- **The certificate** (`certified` is `Lvm.CT.certificateF20S`, `LvmCertF20Inst`):
  - KS: `kcertSF` on `midSpecP_F₂` (the pinned middle phases at `candZ`, every group `≤ εS`, lead `leadF₂`).
  - The node relation: `nodeF20` on stream-block pairs (`GoodTF ∧ SBlk`), through the S2GF HAR `harithF20`
    (`Q_arith`'s rows ⇒ the S2GF decision procedure and the accumulator equation).
  - The refinement: `refinesF20`, the native `VSFX NTF20` ⇒ the width-aware compiled `P_S`.
  - The extractor: the same decoders and fuel; `ext_eqF20` ties the executable extractor (`EXF20`, `extXF20`) to it
    on the S2GF schedule, through a stage-generic agreement (`ext_eqS_gen`).
  - The guard: `staticOkBF20 = staticOkTF20 && nodeChkBG … && sigInSB && harChkBF20 && oneOkB`; it is `true` at
    P20 [measured].
- **Prover.** The `E2` transcript (16-B scalars, nonce search, separators), the generic front (`keccak_gkr/front.rs`)
  at `E2`, the pin, the `E2` word claims as point-like terms that share patterns, the row switches as `E2` rings,
  `Op::E2` rows in the typed witness, a fused coordinate-split zerocheck, and the pin's opening on the committed
  extent only.
- **Measured on dev** (QEMU, v4p, 8 threads):
  - **Prover A/B against #21's prover** (LTO builds, timing lock, CPUs 8–15, 3 interleaved rounds, load 5–10),
    step medians: **2^17 1.576 → 1.419 s**, **2^18 2.366 → 2.098 s**, **2^18 + 1 2.580 → 2.195 s**, **2^20 7.510 →
    6.289 s**; slope 6.78 → 5.57 s per 2^20 (Δb −1.22). An earlier session read Δb −1.37 (2^20 7.473 → 6.292).
  - Inside those: `open main` +0.0125 s over #21, the typed phases +0.08 s, grinding 0.075–0.088 s per proof
    (6.2–6.8 k attempts), all included in the step times.
  - **V badge** (`btime` on `submissionF20`: parse and `acc`, start-up excluded; CPU 8 under the lock; node-step
    files): **small ≈ 145 ms, big ≈ 123 ms**, against roll 11's ≈ 105 / ≈ 100 ms on the same tool, so **+20 to
    +45 ms per check**. `Φ_Q` takes ≈ 70 ms of it (roll 11 ≈ 40; `PhiQCX` 73.0 ms against 39.8 in the same runs).
  - **V start-up ≈ 44 s per process** (roll 11 ≈ 14 s in the same runs), untimed by the harness. It builds `Q`, the
    layout and `Φ_Q`'s two coordinate caches, then checks the guard.
- **Checks [measured].**
  - The Lean `VSFX NTF20` (the shipped `V_S`) accepts the prover's 5-step P20 stream that crosses both shapes in
    both directions (n = 1, 2^18 + 1, 2^17, 2^20, 2^18) and S,0 at n = 1, 2^17, 2^18, 2^18 + 1 and 2^20.
  - 14 prover tampers are rejected: the nonce, an `E2` scalar, a front sumcheck scalar, the pin's value and point,
    the PoW, the shape, an `E2` cell word, a stream word, a `σ'` word, a row result, `v_S`, and two `h` tampers (the
    second one only by `Φ_Q`, as designed). The V-side set (header `n`, the root leaf's window lanes 40–46, an
    absent-lane word, the 512-B leaf, Σ flips at the pin, typed, tape, `KS` and `KS` link checkpoints) is rejected
    on all 10 files.
  - v4p, v2 and v4 (under Intel SDE) give byte-identical proofs, and the linked `.s` prover's stream equals the
    cargo build's.
  - Harness cert and bench: see Result.
- **Four `V_S` bugs were found by proving `refinesF20`, all in new code** (none in #20/#21's shipped `V`): the
  typed hypothesis read a 43-coordinate `acc_in` header at 44; `V_S` started its decision at #21's header length,
  24 B early; the pin's claim head differed from the certificate's off the ν coordinates; and a width-8/16 read was
  counted as no read. A spec was also found false: the good pair needed S2GF's own `KS` continuation rows (4,295
  blocks), not #21's 4,447.
- **Projection [model].** From #21's evaluated steps: every `P_i` minus 0.5 × (1.22 to 1.37 s)·n/2^20, `|π|` 306,992,
  and `V` +24 ms on small steps and +14 ms on big ones (dev badge × 0.60): **S ≈ 1.96–1.98, S× ≈ 1.09–1.11**. With
  `V` +27 ms on every step: S ≈ 2.00–2.02. The prover gain is mostly S×'s; the size gain (−0.040 of V̄) and the `V`
  loss (+0.09 to +0.14) decide S.

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
| leanVM protocol | `K`, `E` (and `E2`, from leanVM's `gf2_64x2`); Keccak GKR with RMFE; `g`-power bus, grand product, table sumcheck (now only the mini-bus); ring switching; stacked WHIR with OOD at the Johnson radius | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine | KS from an invariant used as luck, with no doom; `C_rec` extracted by UD decoders on advice; grinding inside the query group; hash-chain FS; Merkle through the oracle with caps; one commitment with a root OOD pin; the front at `E2` with per-challenge grinding; per-read widths; LoopIR; digest-only chain tape; accumulator; typed backend |
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
| this version, harness cert (dev VM, pin 7ecd179, timing lock) | ok, gate PASS; Lean default kernel **553.9 s** at the default cap (≈ 274 s on the evaluation machine at #20's 0.494× [model]); `build_s` 627.5 s (8 CPUs), peak 4.90 GB, 516 modules built [measured] |
| this version, local quick season (dev VM, 8 CPUs; the first 24 published lengths) | ACCEPT; S 3.125 (P̄ 2.215, V̄ 0.910), S× 2.252, mean V 134.0 ms, \|π\| 306,992 B [measured]; host loaded (`c_P` drift 0.096), and a prefix is not comparable with full-season numbers |
| this version, evaluation machine | from this PR's evaluation (projected S ≈ 1.96–2.02, S× ≈ 1.09–1.11 [model]) |

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
| this version, first S2GF `V` | ≈ 1,970 ms | ≈ 1,137 ms |
| this version, shipped (fast twins) | **≈ 145 ms** | **≈ 123 ms** |

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
