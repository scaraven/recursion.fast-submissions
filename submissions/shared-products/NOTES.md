# pruned-caps

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #11, #7, #12, #13, #15, #17, #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30, #31, #32, #33, #34, #35, #36, #37

This root continues #37 (`pruned-caps`, stage `S2GB`, cap pruning), #36 (`counted-cores`, prover-only), #35
(`wide-packs`, RMFE packs of 32), #34 (`swift-twins`, `V` twins and `lean/` consolidation), #33 (`sealed-leaf`, stage
`S2GS`, σ_LEAF), #32 (`tableless`, stage `S2GL`, MB-LIN), #31 (`trimmed-phi`), #30, #29 and #28 (prover-only) and #27
(`single-tape`, stage `S2GU`), which continued #26 (`halved-phi`), #25, #22, #21, #20, #19 and PR #11. This root is a
`V`-only roll on #37 (with #36's prover fix): `V_S` does fewer field products, through fast twins proved equal to
the evaluators they replace. Proofs, blob B and `|π|` are #37's. "Changes since #37" is relative to #37; the sections
from "Changes in #37" on describe the earlier rolls.

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

## Changes since #37 (pruned-caps)

**Conclusion.** `V_S` does about 33 k fewer `E2` products per check and is **6.4–6.7 ms faster on dev** [measured],
with the certified statement byte-identical. Nothing a prover sends changes: the proofs, blob B, `|π|`, the claim
and the axioms are #37's. Two evaluators get fast twins, each proved equal to the old one and switched in at one
definition.

- **`Φ_Q` evaluator** (`PhiQGCKT`, proofs in `LvmE2VPhiTCse`). One `Φ_Q` call per check did 184,401 `E2` products and
  19,140 products by a `K` element [exact, census of blob B's cache].
  - *Repeated products, computed once.* In the fused codes, 95,828 op-7 instructions add `F[a]·F[b]` to the
    accumulator, and 24,625 of them repeat an earlier pair `{a, b}` [exact]. A static pass, run once at start-up,
    lists every repeated pair. Each call computes `E[k] = F[a_k]·F[b_k]` once and appends `E` to `F` in place.
    The pair's instructions become op 5 (add `F'[n₀ + k]`). The rewrite is checked instruction by instruction
    against the operands each op reads, and the code falls back to the original on any mismatch.
    `PhiQGCKT_eq : PhiQGCKT c (phiPre c) pt = PhiQGCK c pt` is proved for every cache, with no `decide`.
  - *Tables once.* The eq levels are computed once for both coordinates, not twice (5,116 products). 58 of the 63
    table recipes of coordinate 1 equal a recipe of coordinate 0, so their tables are reused after a run-time
    recipe check.
  - *The switch.* `NTB20`'s `Φ_Q` field is now `PhiQGCKT cacheB20 preB20`, with `preB20 := phiPre cacheB20` a
    constant. `PhiQGC` itself is unchanged: compiled as a two-argument function, it would redo the static pass on
    every call. Start-up, which the harness does not time, is unchanged within noise (93.5 vs 94.4 s on a loaded
    dev host) [measured].
  - `Φ_Q` alone: 29.23 → 26.06 ms (n = 1), 28.80 → 25.09 ms (2^18 + 1) [measured dev].
- **The K = 32 tape's correlations** (`corrAllF`, `LvmE2VFastK`). Each layer's `weightedCF` needs 50 correlations
  `corr(r)` of two six-variable eq kernels, and each one walked the six carry bits of `z + r` alone. Now one binary
  tree of carry states over the low bits, shared by all 64 residues r, gives every correlation. Products per layer
  go from 924 to 162 [exact]. `corrAllF_getD` proves each entry equal to `corrAF` by induction and `ring`. In the
  same file, `eqKernelAF` builds `(x + x·r, x·r)`, one product per entry instead of two. The switched definitions are
  `weightedSE2` and `eqKernelAF`.
- **Statement and kernel** [exact]. `certified` (source and `pp.all`) is byte-identical, with the three axioms. The
  only value changes are `NTB20`, `weightedSE2` and `eqKernelAF`, plus their equation lemmas. Cone 1,281.22 M hb,
  +1.16 M against #37.
- **#36's prover fix** is merged (`tstep` revived, the in-process service copy, a pool cap of 30), and the `.s` are
  regenerated.
- **Checked locally** [measured]:
  - dev `V_S`, timing lock, 7 interleaved rounds against #37's `V_S`: n = 1 65.70 → 60.21 ms (paired median
    −6.35 ms), 2^18 + 1 63.70 → 57.40 ms (−6.65 ms);
  - e2e 15/15 accepted; NGATE-B's tamper sets: 47/47 and 217/217 verdicts identical to #37's;
  - identall 10/10 on the linked `.s` (v4p, v2, v4 under Intel SDE), every hash equal to #37's; `prover setup` keeps
    the v4p cap and times `tstep` at 8/6/5/4 workers on blob B;
  - {{REL: cert, quick bench}}.
- **Projected** [estimate]: dev reaches eval at about 0.8× (#34: −4.4 ms dev gave −3.6 ms eval), so eval `V` is about
  −5 ms, ΔS ≈ −0.025. S× gains through `V/v_ref`.
- **Not done, and why.**
  - *Products by constants through tables* (four Russians): NO-GO. A reduced byte table makes a product 3× faster
    (7.7 vs 25.8 ns), but with compiled Lean's boxed `Array UInt64` one table costs 55 µs to build, so it pays only
    after about 3,000 products. The circuit's weights have 8,142 distinct values, used about twice each, and the
    most-reused general operands are used at most 255 times [measured/exact].
  - *Circuit-side CSE of the RMFE addition plans* (g = 8): −5,775 `Φ_Q` products against blob B [exact], but only
    about 35 % of it survives the evaluator CSE above, about −0.25 ms [model]. Not worth a blob refreeze. κ = Σμ
    gains nothing.
  - *QLT-RUN*: a circuit-only split gains only −1,073 products [exact]. The full form, the QLT entries as 95 affine
    runs with a new compiler class in `V`, models at −1.0 to −1.2 ms dev and does not overlap the CSE. It is left
    for a later roll.

## Changes in #37 (pruned-caps), since #35 (wide-packs)

**Conclusion.** Stage `S2GB` ("cap pruning") stops sending the Merkle caps of the three opened `C_main` WHIR levels.
Until #35 each level sent its whole cap of 2^m nodes (8 KB at level 0, 4 KB at levels 1 and 2), and every query path
stopped there. Now a level sends 2^c nodes (level 0: 2; levels 1 and 2: the root). Each path still climbs D = h − m
levels inline. `V` rebuilds the 2^m-node layer from the paths' tops plus a π tail of the uncovered nodes, then hashes
it up to the sent nodes with 2^m − 2^c node queries. The proof is no longer of fixed length:
`|π| = 269,336 + 32·Σ_r (2^m_r − |X_r|)`, **mean 279,400 B** (−5,472 against 284,872) [model, 20 k runs]. The claim, the
contract theorem's form, `εFS ≤ 2^-128` and the axioms (`propext`, `Classical.choice`, `Quot.sound`) are unchanged. The
certificate is `certificateS20B`.

- **The protocol** (frozen P0, with re-freezes P1 and P2) [exact]. It covers the opened levels L0/L1/L2:
  (t, h, m, D) = (115, 19, 8, 11), (77, 16, 7, 9) and (58, 13, 7, 6). Rec levels are not opened.
  1. *Commit.* The cap item carries A[2^c], …, A[2^(c+1) − 1] of the level's heap-indexed tree (A[1] the root), with
     c = 1 at L0 (64 B) and c = 0 at L1/L2 (32 B). The next FS query absorbs them, as before. P1 fixed c = 1 at L0:
     with a root-only commit, the pin's first FS query `st ‖ root` is 64 B, a node query's length, which the length
     rule forbids.
  2. *Paths.* Each sampled position q gets its leaf query and D levels of siblings inline, as in #35, with no
     per-path cap check.
  3. *Layer.* With X = {q ≫ D}, L[x] is the top of the first path (in sample order) with q ≫ D = x. Otherwise L[x]
     is the next 32 B of the tail, read in ascending x. `V` rejects unless every path's top equals L[q ≫ D].
  4. *Heap.* For k = 2^m − 1 down to 2^c, `V` makes one node query lhs ‖ rhs, and A[k] is its answer. The halves are
     L[2j], L[2j+1] for k = 2^(m−1) + j, and A[2k], A[2k+1] above. That is 254 + 127 + 127 = 508 static queries,
     logged right after the level's paths.
  5. *Cap check.* `V` rejects unless A[2^c + i] equals sent node i.
  6. *Tail and length.* Static items keep their order. One tail follows the last static byte: per level in opening
     order, the uncovered layer nodes in ascending x. Tail bytes, like siblings, are never FS-absorbed. `parseOk`
     checks piStatic ≤ |π| ≤ piStatic + 16,288. At the end `V` requires the body cursor at piStatic and the tail
     cursor at |π|.
  7. *Mini-bus at depth 13 (P2).* The layer check `readd`s the heap-bottom regions (13·2^(m−1) lanes). The seed arrays
     grow 187 → 272 and the push leaves 4,080 → 5,440, past 2^12. Depth 12 cannot hold the 3,328 heap cells plus
     1,088 read leaves under any pairing. The cost is +720 B (30 `E3` scalars), +8 FS queries and +10 sponge blocks.
- **Sizes** [exact; Lean `sizes_P20B` by `decide` = Rust twin = model].
  - piStatic 284,872 → **269,336** (−15,536). The tail is at most 16,288 B, mean 10,064 [model].
  - `|π|`: mean **279,400**, q0.99 279,800 [model]. Its range is 277,720 to 285,624 B [exact]: the maximum, with
    every level's paths in one x, is 752 B above #35's fixed size. Honest files read 279,256 to 279,672 [measured].
  - `qS` 3,618 → 4,134 (+508 heap, +8 bus). The hashed trace grows 537,336 → 575,208 B: the heap's 508 logged node
    queries and the bus's 8, less the 16,256 cap bytes no longer absorbed. Sponge blocks 3,952 → 4,230, under the
    guard's 4,295.
- **Soundness.**
  - *Reduction to #35's Merkle check (lead decision D-V1).* The compiled scheme runs on the expanded proof
    `fillB P20B π w`. This is π's static part with each path's m − c upper siblings taken from `w`, and the tail
    dropped (`pzB` = 325,336 B [exact]). It is #35's scheme with a cap of 2^c nodes (`schemeSWB`, `capOfB`; `capOfB_agree`
    by `decide`).
  - `refinesB20`: if `V_S` (`VSSB`) accepts π on an oracle log, then for some `w` the compiled verifier accepts
    `fillB π w` on the same log. The witness `w` is the heap's halves: every sibling above the layer is the input of
    a node query the heap made, so the log already answers the full paths.
  - Knowledge soundness and the extractor follow from the existing chain at that scheme. `ext_eqB20`: `E` reads π as
    static ‖ tail, the tail taken from the heap-bottom halves at x ∉ X, and its output equals the scheme's extractor
    on `fillB π w`. `computesXB20` keeps `E` within the declared fuel.
  - The layer is bound to the sent nodes only through the heap's node queries. Their collisions fall under `εFS`'s
    existing hash term (2^-139).
  - *Budget.* One group changes: the mini-bus fingerprint at depth 13, `abError = 4·2^13/|E|`, goes from 2^-178 to
    **2^-177** [exact, `errsL_atB`], still ≤ εS = 7·2^-131. The worst group is still `C_main` level 0's query group
    (2^-128.33 [model]). Lean's `εFS ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128` is unchanged.
- **Completeness.** The claim's completeness is still the witness-sending kind (`P := encode`, error 0). For the SNARK
  route, `V_S` accepts honest `S2GB` proofs (e2e 15/15 [measured], below), and the guard `staticOkBB20` holds natively
  on blob B [exact].
- **The circuit (blob B).**
  - `Q_link` checks the child's pruned openings with three loop gadgets: the layer (`layerLoop_spec`), the heap as one
    descending 1-D loop (`heapLoop_spec`) and the cap check (`capChk_spec`). `qlinkB_sound` lifts them to the child's
    trace (`LaneLinkB`, under `StreamOkB`).
  - `Φ_Q` has **252,126 products** (blob W: 247,973; **+4,153**) [exact]. About +2.0 k are the heap, +0.2 k the cap
    check, and the rest the depth-13 mini-bus [exact, dev-blob census].
  - `T` pads to 947,584 (limit 996,147) [exact].
  - Blob B regenerates byte-identically from the Lean source, and blob W still does.
- **Lean** (stage `S2GB`, `certificateS20B`).
  - `Params.capPrune` and `P20B := { P20S with capPrune, busDepth := 13, tableEvals := 888 }`; `capSendBits`.
  - `sizes_P20B`; the native `VSSB` with its length rule (`piSizeB`, `szB_of_VSSB`); `refinesB20`; `THypSB`/`errsL_atB`.
  - The node relation: `harithB20`/`nodeB20`, verifying an `S2GB` child read as static ‖ tail (`childSPB`).
  - The extractor: `ext_eqB20`, `computesXB20`, `childB20_win`.
  - The middle phases: `midSpecPinB20`.
  - The chain `certificateSB20`/`certificateS20B` with the guard split `certificateR_guardSB`. The new modules are
    `LvmS2GB*` and `LvmQCap*`.
  - `certified`'s source text and pp.all statement are byte-identical to #35's. The other changed `S2GS` statements
    are classified intended edits: `capPrune`-gated definitions, and proof-help lemmas that read the cap width taking
    `hcp : p.capPrune = false`.
  - The kernel cone of `certified` is 1,280.06 M heartbeats [exact] (#35: 1,229.05 M).
- **The prover.**
  - The FrontCfg flag `cappr` sets the default stage to `S2GB`. The sent cap nodes come from the stored tree.
  - Each proof makes +508 heap node queries in about 22 more oracle requests, and runs the mini-bus at depth 13.
    The cost is +1 to +2 ms per step [estimate].
  - Blob B is embedded and the `.s` are regenerated. `prover setup`'s self-test proves an `S2GB` P20 `S,0` and keeps
    the v4p cap on dev.
- **Checked locally** [measured]:
  - harness cert: Lean kernel 468.4 s (stop 560, cap 600), `build_s` 1,035.0 s (the build shared the host with
    other jobs; the kernel ran on a quiet host);
  - 0 `sorry`; `checkall` clean; axioms of `certified` the three;
  - e2e: `V_S` accepts all 15 files of the honest stream set (`S,0`/`S,1` at n = 1, 2^17, 2^18, 2^18 + 1, 2^20,
    and a 5-step stream);
  - **NGATE-B**: 20/20 honest files and controls accepted, **244/244** tampers rejected. These are the K3 modes on
    `S,0`, and on `S,1` whose child is the tamper: a covered path's sibling (including later paths of a covered x),
    tail nodes, a truncated and an extended tail, and heap halves changed in the child trace (circuit side). They also
    include #35's NGATE-W modes re-run at `S2GB`, and cross-stage and cross-blob files;
  - identall **10/10** on the linked `.s` (v4p, v2, v4 under Intel SDE);
  - quick bench (the first 24 steps; decisions only): **ACCEPT**, S 2.683 (P̄ 2.015, V̄ 0.668), S× 2.025, mean `V`
    70.3 ms, |π| 279,429 B, `c_P` drift 0.02. Other jobs shared the host (calibration cv 0.12); #35's quick run on a
    quiet host read S 2.549 (P̄ 1.886, V̄ 0.663), mean `V` 66.0 ms, so P̄ and `V` are not like-for-like.
- **Projected** [estimate], from #35's projection:
  - `|π|` −5,472 B [model] ≈ −0.0086;
  - `Φ_Q` +4,153 products ≈ +0.0016;
  - `V`'s +516 queries and +278 sponge blocks ≈ +0.001 to +0.0018;
  - the prover ≈ +0.0009 to +0.0018.
  - **ΔS ≈ −0.002 to −0.005** (central −0.0035). S× does not gain, because `|π|` does not enter it.

## Changes in #35 (wide-packs), since #34 (swift-twins)

**Conclusion.** Roll W32 packs 32 Keccak tape GKR instances per RMFE element with a (32, 53 → 105) RMFE (14 places;
`rmfeEmbed_eq`, `rmfeProject_eq`, `rowsOk_lit` and `colsOk_lit` by kernel `decide`, so ψ(φ(a)·φ(b)) = a ∧ b on F₂^32).
The prover's carry-less Skip pass then runs 10 mixed points per half instead of 38.

- Per instance-layer under Intel SDE: Skip 360 → 127 cycles of carry-less multiplier and Product +7.9 %
  instructions [measured]. That is ≈ −216 of ≈ 898 tape cycles on Zen 4 [model].
- Sizes [exact]: one pack round fewer per layer, so `qS` 3,642 → 3,618; the trace is 537,336 B in 3,952 blocks.
  **`|π|` 263,560 → 284,872 B.**
- The `s` group grinds 7 bits: `104·2^-135 = 2^-128.30`.
- Blob W builds the RMFE projection and embedding from 4-bit subset-sum tables (`q2Proj4`, `q2Inst4`): `Φ_Q` 247,973
  products (+17,501) and `T` padded 940,222 [exact].
- `callerSpec` and the caller-phase specs gain `1 ≤ P`. The unused E3 Keccak chain was removed (138 declarations).
- The self-test now proves a P20 `S,0`; its K = 16 proofs would have capped setup at v2.
- Checked: cert ok, kernel 453.1 s, cone 1,229.05 M heartbeats; NGATE-W 204/204; identall 10/10; quick bench S 2.549,
  mean `V` 66.0 ms.
- Projected: ΔS ≈ −0.030 to −0.033 at a realisation of 0.65 of the SDE model (break-even ≈ 0.35) [model].

## Changes in #34 (swift-twins), since #33 (sealed-leaf)

- `V` runs eight proved fast twins of its hot loops (`LvmE2VFast`, each with an `_eq` theorem), switched in at hinge
  lemmas whose statements do not change. Untimed `V_S` is −3.0 to −5.8 ms per proof [measured, dev].
- `lean/` lost 417 modules outside `Solution`'s closure and 17 single-importer merges (1,014 → 580 files).
- The protocol, the proof bytes, blob S and the prover are #33's.
- Checked: statement gate 0 changes; NGATE-S 179/179; kernel 599.3 s at host load ≈ 42 (cone 1,206.43 M).

## Changes in #33 (sealed-leaf), since #32 (tableless)

- Stage `S2GS` ("σ_LEAF") moved the leaf signature `σ_leaf` (4,776 B) out of the header into `C_main`'s window (the
  stream block's column 17, words 1024..1620).
- The node program walks it as a second WOTS instance under the header's `vk`, specialised to the constant message
  `traceDigest []`: 204 chain steps, the key leaf and the path (`qSigLeaf_sound`, `qsigNoSl_sound`).
- `E` decodes it from the window (`ext_eqS20`).
- `|π|` 268,336 → 263,560 B, trace 517,752 B, 3,808 blocks [exact]. No group was added.
- `Φ_Q` has 230,472 products (blob S). The certificate is `certificateS20S`.
- The prover signs the empty trace once per step on its own thread, and carried PFAST4's byte-identical rider.
- Kernel 515.7 s (host loaded); NGATE-S rejected 147/147 tampers.

## Changes in #32 (tableless), since #31 (trimmed-phi)

- Stage `S2GL` deleted the mini-bus's table phase. Its 211 tables have no constraints and affine flushes, so each
  product tree's final GKR claim is one `K`-linear claim on `C_main` (`mbLeafLin`, `mbClaimsL_iff`; the seeds'
  address columns in closed form).
- `|π|` 283,960 → 268,336 B, `qS` 3,642 [exact]. `Φ_Q` has 217,507 products (blob L).
- `V_S` −3.1 / −5.3 ms on dev [measured]. The certificate is `certificateL20S`.
- Evaluated **S 1.5313** (`V` 41.2 ms), the sum record.

## Changes in #31 (trimmed-phi), since #29 (planned-phi)

- `V`-side: the wire target's `ω` comes from five convolution loops instead of 260 unrolled lane forms (blob U′),
  so `Φ_Q` falls 249,188 → 230,349 products. `runF2` runs without state allocation.
- Together these take −3.9 / −4.4 ms off `V`'s `Φ_Q` on dev [measured].
- GOLF2 moved 8,506 unused constants out of `certified`'s import closure, and GOLF3 golfed proofs only. The cone fell
  1,412 → 1,206 M heartbeats with 0 theorem types changed. Kernel 454.0 s [measured].

## Changes in #29 (planned-phi) and #28 (brisk-tape)

- Prover-only, with proofs byte-identical to #27's.
- #28 removed the typed phases' serial stretches: typed phase 0.137 → 0.088 s per step on dev.
- #29 planned the `Φ_Q` batch once at setup (311,698 runs → 17,007 lists, unreduced `E2` kernels) and kept the
  zerocheck's j = 0-only chunks small: 0.075 → 0.045 s [measured].
- #28's typed gain reached the evaluation machine at ≈ 0.28× its dev size [model].

## Changes in #27 (single-tape), since #26 (halved-phi)

**Conclusion.** The Keccak sponge table `KS` and its link merged into the tape (stage `S2GU`): one GKR of depth 24
over `μ = 21` rows proves both the chain (rows `< 2^20`) and the in-circuit sponges (rows `2^20 + j`, virtual input
`cont_j·Y[j−1] + Msg[j]`). One wire sumcheck over `x < 2^20` of `K_ch·G_D + K_ks·G_Y + I_ks·G_M` follows, with `K̃_ks`
evaluated in closed form over `cont`'s intervals. The root leaves carry 46 lanes. The proof shrank to 283,960 B
(−22,032) [exact]; `Φ_Q` 249,188 products (blob U); the claim and `εFS ≤ 2^-128` were unchanged; certificate
`certificateU20S`. `V` badge 78.7 / 72.4 ms (small / big) against #26's 86.6 / 81.1 in the same runs; step at 2^17
1.561 → 1.422 s [measured, dev]. The full section is in #27's NOTES (`single-tape`).

## Changes in #26 (halved-phi), since #25 (looped-rows)

**Conclusion.** The typed backend moved to `E2` (stage `S2GT`): the zerocheck, the wiring, the relayout and A23 run
with 16-B scalars, each of the 87 typed `E2` challenges with its own nonce and PoW, and `V` evaluates `Φ_Q` with `E2`
Karatsuba products (`PhiQGC_eq`, valid under the guard's `linOkX`: no product meets two `E3`-carrying factors). The
proof shrank to 305,992 B [exact]; `Φ_Q` 294,419 products (blob GT); certificate `certificateG20S`. `V` badge 84.9 /
76.8 ms (small / big) against #21's 91.9 / 83.8 [measured, dev, timing lock]. The full section is in #26's NOTES
(`halved-phi`).

## Changes in #25 (looped-rows), since #22

**Conclusion.** The circuit's row switches (`rowLeafGL`, `rowNuGL`: Frobenius squaring and `ν` loops over the 64
components) and the PoW booleanity rows ran as loops, so `Φ_Q` fell 445,694 → 306,139 products (−31 %) [exact];
`V`'s opening shares coordinates across claims (`decideProgFFG_eq`). The proof, the transcript and the prover's code
were unchanged; it merged #23's and #24's prover speed-ups. `V` badge 111.1 / 96.1 ms (small / big) against #22's
≈ 164 / 138 [measured, dev, timing lock]. The full section is in #25's NOTES (`looped-rows`).

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
  - `submission = submissionS20B`, the guarded `S2GB` submission: `V_S` is `VSSB NTB20` when the guard `staticOkBB20`
    holds, and witness sending otherwise (`LvmS2GBCert`).
  - `certified` is `Lvm.CT.certificateS20B` (`LvmS2GBCert`; stage `S2GB`).
  - The names below are the `S2GF` stage's. Each later stage re-proves them under its own suffix. For `S2GB` these
    are `refinesB20` (on `fillB`), `nodeB20`/`harithB20`, `ext_eqB20`/`computesXB20`, `midSpecPinB20` and the guard
    `staticOkBB20`.
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
- The right child is a witness-sending leaf `⟨encode (leaf s n), [], σ_leaf⟩`; `σ_leaf` lies in `C_main`'s window and
  the node program checks it (S2GS; until #32 `V` checked it natively from the header), and the SNARK proves
  `chainEnd s n = h`.
- The left child is the previous signed proof `(π', tr', σ')`, committed and verified in the circuit.

A flag `b` selects leaf mode (step 1's first proof) or node mode. There is one schedule and two commitment shapes
chosen by `n`, so every proof makes the same queries (since `S2GB`, `|π|` varies with the tail of uncovered cap-layer
nodes). A `W` proof never starts with `'S'`.

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

**Stacked WHIR at the Johnson radius, with grinding.** (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, 58); cap
layers 2^8/2^7/2^7, of which only 2/1/1 nodes are sent (`S2GB`: `V` rebuilds each layer by a heap of node queries);
OOD after levels 0–1; final 2^9; lists of ≤ 124, 231, 615. Every level grinds 14 bits. Every claim is `K`-linear on
`C_main`; an `E2` claim enters as its two halves.

**The extractor decodes `C_main`'s window with UD programs on advice.** `decodeMP2` (2^13 positions) →
`decodeMP1` (2^16) → `decodeMP0` (2^19, lanes 40–47), list luck 2^-159.93 [exact], within the
declared fuel (`computesXF20`; the generic `computesXS` over the S2GF schedule). No list is ever enumerated.

**Fiat–Shamir is a hash chain over the contract oracle.** `q₀ = "lvm/1\0\0"`, then the seed `a₀ ‖ header`; each
query is `st ‖ pending messages`; a challenge is lanes 0–2 of the answer (`E3`), or lanes 0–1 (`E2`, with lane 2 the
PoW). Reads are 24, 16 or 8 B by position. Merkle leaves and nodes are queries; paths stop at the cap layer.

**Verifier circuit: LoopIR on a typed backend.** `Q = Q_link ++ Q_sig ++ Q_arith` runs the child's verifier on its
trace: `Q_link` (the trace follows the schedule), `Q_sig` (the child's WOTS walk, the header and statement, and the node's own leaf signature), `Q_arith`
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

**Roll CAP (`S2GB`).**
- A root-only commit at level 0 breaks the FS length rule. The pin's first query `st ‖ root` is 64 B, the length of a
  node query. Hence c = 1 at L0 (re-freeze P1, +32 B).
- The mini-bus at depth 12 cannot hold the layer check's reads [exact]. Depth 13 costs +720 B of π and +10 sponge
  blocks. Together with the mini-bus's growth in `Φ_Q`, that takes about half of the gain MPG had modelled on `S2GL`
  (ΔS −0.006 to −0.008).
- The first blob B kept blob W's cell numbers in its `BITS` source specs: `p1C` compiled `qlink`, not `qlinkB`.
  Every gate on `S,0` passed. Only the honest `S,1`, whose node program checks an `S2GB` child, failed. It was fixed
  at the generator, and blob W still regenerates byte-identically.

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
