# `flock-recursive` blueprint: adversarial cryptographic review

Reviewed: `docs/v4/flock-recursive/BLUEPRINT.md` at `30b6999`, against
`.contract/RecursionFast/Contract/*.lean` at `15dac52` (`KState`, `Computes`, `Submission.acc`,
`runSeq`, `SigOk`), `.contract/docs/DESIGN-v4-srom.md` §1–2, the phase-0 memos and the Flock paper
(App. A, C). Numbers below were recomputed by `logs/`-free scratch scripts (ladder, error table,
final-level cost) and a randomised small-parameter probe of the MCA-UD lemma (K = GF(256) ⊃
F = GF(16), n ≤ 12, k ≤ 2); where a number of the blueprint is wrong the correct one is given.

Findings: `BP-C-M<i>` major (must fix before implementation), `BP-C-m<i>` minor. Section numbers
are the blueprint's.

---

## Majors

### BP-C-M1. `node_sound` cannot conclude `acc`: the child's statement check is not in the circuit

`Submission.acc vk cᵢ pᵢ` requires `(V vk cᵢ πᵢ).runSeq trᵢ = some true`. `V` (§3) rejects, before
`runIR`, unless `cᵢ = leafStmtF hᵢ nᵢ` (leaf child) or `cᵢ = nodeStmtF c₁ᵢ c₂ᵢ` (node child): a
BLAKE2s computation of 1 or 2 compressions that `V` performs itself (§3.3) outside the IR. The
node circuit asserts (§4.3, items 1–7) the item constants, the FS chain, the seed payload
(`vk`, `cᵢ`, `hdrᵢ`), the IR ops, the Merkle steps, the size constants and `SigOk`; nothing ties
`cᵢ` to the header's `(hᵢ, nᵢ)` or `(c₁ᵢ, c₂ᵢ)`. H's block count (§4.3: `2 × 20,113 + 996`) has
no block for it, and `FRVIRCircuit.compile_sound` is generic in the IR, which does not contain it.

*Counterexample.* A prover builds a self-consistent child trace whose seed item carries an
arbitrary `cᵢ` and a header with `(hᵢ, nᵢ)` such that `leafStmt hᵢ nᵢ ≠ cᵢ`, signs the trace (the
adversary of `∀ vk` holds `sk`), and proves the node honestly. Every circuit assertion holds, the
node verifies, the extractor returns `pᵢ`, and `acc vk cᵢ pᵢ = false` at the statement check:
`Rel (acc vk) c w` fails and `final` is unprovable.

*Fix.* Per child, one H block (leaf: `tagLeaf ‖ h ‖ enc64 n`, 41 bytes) or two (node: 65 bytes)
computing the statement, with the output wired by an element equality to the seed item's `cᵢ`
and the inputs wired to the header fields; count them in §4.3 and §4.5. Cleaner: make the
statement check an IR op (`hashStmt`) so that `V = parse; runIR` exactly, which
`runSeq_eq_runIR` (§4.3 (c)) already assumes.

### BP-C-M2. Missing degree-126 rows in the error table; the answer-sharing rule breaks `step`

The paper's App. A charges the **lincheck's** univariate-skip round `2(2^k_s − 1)/|F| = 126/2^128`
besides the zerocheck's. The blueprint's L2 row has only "9 rounds degree 2". The same applies to
every reduction that ends in a claim on the quirky `ẑ` and must dispose of the skip coordinate:

- **B** (step 7) batches ≤ 8 claims at points with *different* skip coordinates (λ from Z, `t`'s
  univariate coordinate from Lc, the Sh/IO points) by "one extra sumcheck of degree 2 over `m`
  variables ... charged like Z3". Over the quirky polynomial the round for the skip variable has
  degree ≤ 63 + 63 = 126 (Lagrange kernel × `ẑ(r, ·)`): `126/2^128`, not `3/2^128`. A plain
  multilinear sumcheck over `m` variables is a different object (`ẑ_quirky(r′, λ) ≠ ẑ_MLE`) and
  would not be sound for these claims.
- **Sh**, **IO**: the digest regions (bits `256 … 511`, `520 … 775`) have their 6 low position bits
  ranging over `S`; a sum over `S` of `ẑ(r, ·)` becomes one evaluation claim only through a
  univariate round (degree ≥ 63). Not charged.
- **Z2**: the verifier reconstructs `P^{ab}` as the degree-≤127 interpolant through 128 points
  (`P^z|_S`, `P^{ab}|_Λ`); `P^{ab} − Q` then has up to **127** roots, not 126, unless the verifier
  checks the top coefficient. `127/2^128 = 2^-120.99` still fits.

Each such row is `2^-121.0`, below `εR = 2^-120 − 2^-124 = 2^-120.093`. But §1.2/§5.2 let "two F
challenges of two different phases share one answer ... never with the skip challenge λ": two of
the *new* degree-126 challenges on one 32-byte answer charge `252/2^128 = 2^-120.02 > εR`, and
`step` fails on that query.

*Fix.* Add a row per univariate round (Lc skip, B skip, Sh/IO collapse, any E/Lr analogue);
forbid answer-sharing for every phase whose row exceeds `2^-124` (or simply: one squeeze, one
phase); state `skip_bad_le` for the interpolant actually computed (degree ≤ 127) or add the
coefficient check to the IR.

### BP-C-M3. The final level's `Enc` cost is under-counted 16× (B-3's accounting)

At level 3 the fold `u ∈ K^{n₃}` is compared with `Enc₃(g⁽⁴⁾)[j]`, where `g⁽⁴⁾ ∈ K^{k₃}` is the
level-3 code's message (the `16 × k₄` clear message recombined: `k₃ = 8 k₄`). Evaluating a
degree-`< k₃` polynomial at `D[j]` from its `k₃` values on `S` costs `k₃` K×F products (`2 k₃`
F-products) plus the `k₃` inverses `1/(D[j] − D[s])`, which depend on the random `j` and are not
constants. `logs/blueprint/sizes.py` line 30 uses `kf = k₄`.

| | m = 30 | m = 32 |
|---|---|---|
| blueprint (`k₄ t₃`) | 4,256 F | 16,896 F |
| actual `2 k₃ t₃` F-products | **68,096** (+34,048 inverses) | **270,336** (+135,168 inverses) |

In `V` this is ≈ +20 ms at `m = 32` (fits `T_V`). In the node circuit it is ≈ 3 rows per `(s, j)`
(difference, inverse, product): ≈ 4·10^5 committed elements ≈ `2^25.6` bits ≈ 3,100 blocks per
`m = 32` child, +6,200 blocks for LL (§4.3's 46.4 k → ≈ 52.6 k) and the element zerocheck grows
from ≈ `2^18.5` to ≈ `2^20` rows (K §4.1 budgeted `2^17.6`; §4.5's tightening is consumed
several times over).

B-3's reason for dropping levels 4–5 ("the UD radius slack `3/(δn)` pushes `(1−γ)^t` above the
cap") holds for BCHKS25's Theorem 7 but **not for B-5's own lemma**, whose only hypothesis is
`2e < n − k + 1`, so `γ = δ/2` is admissible: at `ρ = 1/32`: `n = 2^10 (2^12)`, `t = 126`,
`(1−γ)^t = 2^-120.41`; at `ρ = 1/64`: `t = 124`, `2^-121.23`; both under the cap, with
`2e < d` checked.

*Fix.* Reinstate levels 4–5 (final message `2^5`/`2^7` F, `k₅ = 4`/`16`), or keep four levels and
re-budget M, H and the element zerocheck with the correct count; in either case fix `sizes.py`
and §3.1/§4.5.

### BP-C-M4. The systematic code ("message = values on `S`") destroys the MLE-friendliness that the consistency claims need

§2.3 step 11: "`Enc(f⁽ⁱ⁺¹⁾)[j]` is an evaluation claim on the next level's polynomial, folded into
the running claim". After folding, the verifier must evaluate the batched weight
`ŵ(r) = Σ_j eq(κ_c, j) · Ĝ_j(r)` at the final point, `Ĝ_j(r) := Σ_x eq(r, x) G_j(x)` with
`G_j(x)` the `j`-th row of the generator matrix. Ligerito/WHIR's `O(log k)` evaluation
(ACFY25, NA25; paper App. C.2 fn. "MLE-friendly") rests on the **novel polynomial basis**
(LCH14): `G_j(x) = Π_v Ŵ_v(D[j])^{x_v}` is a tensor, so `Ĝ_j(r) = Π_v (1 − r_v + r_v Ŵ_v(D[j]))`.
With §2.1's systematic map `G_j(x) = L_{s(x)}(D[j]) = (Z_S(D[j])/Z_S′) · (D[j] − s(x))⁻¹`, which
is not a tensor in the bits of `x`; `Ĝ_j(r)` costs `Θ(k)` per position: `290 × 2^17 ≈ 2^25`
F-mults at level 0 for `m = 30` (`2^27` at `m = 32`), in `V` (≈ 2.4 s, `T_V` cap 206 ms) and as
M rows in every node. §3.1 has no term for it; the blueprint's `T_V` and §4.5 silently assume
the novel basis while §2.1 defines the systematic one. (SR's `RS.lean` and LV's `NovelBasis.lean`,
listed in I-reuse as the sources of `FRRS`, are novel-basis codes; T §4.5's "no novel-basis
bridge is owed" was drawn for the Gao route.)

*Fix.* Define `Enc` in the LCH basis (CompPoly `NovelPolynomialBasis` / SR `RS.lean`:
`normalizedW`, `basis_deg`, `code_dist`), and prove `Ĝ_j` = the product form (the one lemma that
makes the consistency weights `O(log k)`). The extractor then owes a basis change per decoded
row (values on `A ⊇ k` points → novel coefficients): `O(k²)` schoolbook adds ≈ `2^40` F-products
at level 0, `m = 30` (`2^45.7 → ≈ 2^46.7` total; raise `fuel` to `2^47.5 + 2^12 t`, still ≤
`2^48`), or an additive-NTT program with a proved step count (`m = 31` fallback then needs it).
Re-budget §6.3 and withdraw B-5's "message = values on `S`" wording in §2.1 and §6.5 (5).

### BP-C-M5. `leaf_sound` and `node_sound` are false without a `one = 1` constraint per block

The block's constant `1` (slot 8) is a witness position. The block R1CS forces constants through
rows `(one, one) ↦ z[k]`, outputs through `(out form, one)`: with `one = 0` the block is the
all-zero assignment (which §4.3 itself uses for unused H blocks) and satisfies `Holds blockR1CS`
with Boolean inputs, zero constants and zero outputs. The stated hypotheses of `leaf_sound`
(Boolean, `Holds` per block, `ChainLinks`, `IOHolds`) do not exclude it.

*Counterexample (leaf).* Honest blocks `0 … n−2` from `s`; block `n−1` with `one = 0`: its output
is `0`, `ChainLinks` holds (its input is the honest `d_{n−1}`), `IOHolds` with `h = 0`. `V`
accepts `c = leafStmt 0 n`; the extracted `.leaf s n` has `chainEnd s n ≠ 0`. In the node, a zero
block inside a trace-digest chain forges `traceDigest`; inside a WOTS chain it forges a step.
(SR's `block_sound` carries "with `1` at position 512" as a hypothesis and SR's wiring rows
`512 + 2^14 t ↦ pub(0)` discharge it; the blueprint drops the wiring rows (B-6) without a
replacement.)

*Fix.* One evaluation claim per shape: the MLE of `i ↦ z[blk i, one]` over the used blocks equals
the constant-1 MLE (an IO row, `(m−14)/2^128`), listed in §4.1, §4.3 and §5.2; `block_sound`'s
`one = 1` hypothesis stated explicitly in `leaf_sound`/`node_sound`.

### BP-C-M6. The T↔H identification (§4.4) cannot be two structured-point claims

Child 2's trace sits at T element offset `2^17` ("a sub-cube boundary") while its H blocks
"follow child 1's" at block index `N₁ = 20,113` (LL). The map `(i, j) ↦ T[512 i + j]` then fails
for child 2 (`512 · N₁ = 2^23.3 ≠ 2^24`), so the two sides are not one aligned sub-cube pair. A
pair of structured points over `2^a ≥ N_H^{hash}` blocks needs `2^a = 2^16` (`N₁ + N₂ = 40,226`),
i.e. the whole cube: it would identify the message slots of the WOTS, M, T, L and P blocks with
T bytes. Padding child 1's chain to `2^15` blocks costs `2 × 12.6 k` extra H blocks: 71 k > 65,536
(B-2's kill test fails).

*Fix.* Drop the T region: read the trace bytes from the H blocks' message slots directly
(`Hbase + i·2^14 + 512 + j`), in the irregular-read addresses, `reassemble` and the extractor;
the two chains are then contiguous in block index and no identification claim exists. (Or an
arbitrary-offset shift-MLE sumcheck of degree 2 over 24 variables, one more Sh-type phase.)

### BP-C-M7. Two circuit variants do not cover the children the tree and the stream produce

The NN variant must replay children of kind `L` (stream leaf, `m = 30`) and kind `N` (variant LL
or NN). These are **three different `vprog`s**: §2.3's last paragraph says the node adds steps 5
(node form), 6, 9, 10, so a node child's trace has more FS items, different item offsets in its
trace and a different `piSize`; a node child's E/Lr replay also depends on *its* variant
(`evalM variant`). §4.3 item 1 fixes "the shape's constants" per item and §4.4 fixes the irregular
columns "at addresses from the item layout": a different child program is a different matrix, so a
different circuit. §4.5's "per child ≈ 190 k rows" counts one program. The tree needs
`(N-LL, N-LL)` at level 2 and `(N-NN, N-NN)` above; the stream needs `(N, L)`.

*Fix.* Either (a) one `V` program and one trace layout for every `m = 30` shape (the stream leaf
runs the node's E/Lr/node-form steps over empty regions; LL and NN share round counts and differ
only in template tables, both evaluated and selected by the committed variant bit), so that NN
has one child program; or (b) enumerate the variants that occur (`LL`; `L L`; `L N`; `N N`, with
`N` children's variant muxed) with a `decide` per variant, and redo B-2's count. Either way,
state in §4.3 item 1 that the seed item's `hdrᵢ` bytes (kind, shape, variant) are among the
asserted constants, which is what rejects a mismatched variant byte.

### BP-C-M8. `mca_ud_line` is stated for F-valued rows and one line; the fold needs K-valued rows and `2^{ℓ−r}` lines

The lemma (§5.3) takes `u₀ u₁ : Fin n → F` and concludes with `v₀ v₁ ∈ C_F`. After round 1 of a
level the rows are **K-valued** (the fold `(1−z)u₀ + z u₁` with `z ∈ K`), and rounds `2 … ℓ`
fold K-valued rows. For K-valued input the stated conclusion is false: `u₀ = u₁ = w ∈ C_K \ C_F`
makes every `z` close with full agreement and no `(v₀, v₁) ∈ C_F²` agreeing anywhere, so
`|bad| = |K|`. `fold_preserves` ("induction over the rounds") therefore cannot be derived from the
lemma as stated. Also each round applies the lemma to `2^{ℓ−r}` lines (32 at round 1 of level 0),
so the P1 row is `2^{ℓ−r} · ((2n+3)(e+1)) + 2`, `2^-212` at level 0, `m = 32`, not `2^-217`
(harmless, but FR-R2′ demands exact rows).

The proof plan's step 4 ("`r_j(Z)` has numerator degree `≤ 2(e+1)`") is not justified: `Q = N/E`
by long division in `K(Z)[X]` has coefficient Z-degrees up to ≈ `k(e+1)` (each division step adds
a factor `1/lc_X(E)`), so the route proves a constant ≈ `n k (e+1)` (`2^57` at level 0, `m = 32`:
`2^-199` over K), which suffices, not `(2n+3)(e+1)`. Small-parameter probe (random and
structured words, 30 trials each, `n ≤ 12`, `k ≤ 2`, `e` up to the UD radius): the worst bad
count observed was `e` (the cancellation positions), far below the bound; no counterexample to
the F-valued statement.

*Fix.* State the lemma over K-valued rows with `v₀ v₁ ∈ C_K`; recover F-valuedness once per level
(the interpolant through F-valued data on F-points is F-valued, `|A| ≥ k`); carry the line count
into P1; make the constant a parameter of the lemma fixed by the proof that closes (any
`poly(n, k, e)` is `≤ 2^-190` over K), and drop "`(2n+3)(e+1)`" from B-5, D-20 and §5.2.

---

## Minors

### BP-C-m1. The H row's count of in-play digests is wrong

"`(4 · logCap + 8)/2^256`" assumes ≤ 4 in-play digests per entry. A cap absorb carries 512
digests in one query; any query carries up to `queryCap/32 = 2^15`. The potential must charge a
fresh answer equal to **any** 16-byte-aligned 32-byte window of any logged query or answer (a
later preimage of a cap entry or of an inner Merkle node changes `W⁽ⁱ⁾` read off `L`). Count:
`Σ_e (|q_e|/16 + 1) ≤ 2^16 · logCap`, i.e. `2^-144` per fresh query (Security.lean's own
"`2^15` digests per query ≈ `2^-145`"). Fits (`2^-120.28 + 2^-144 ≤ εR`); state `bad_step_le`
with that label set.

### BP-C-m2. §1.1–§1.2's sizes are T's six-level numbers

For the four-level ladder: siblings `Σ tᵢ(depthᵢ − capᵢ) = 290·9 + 178·8 + 145·6 + 133·4 = 5,436`
(`m = 30`), `290·11 + 178·10 + 145·8 + 132·6 = 6,922` (`m = 32`), not 5,934 / 7,924 (T's six
levels); column bytes `290·64·16 + 455·16·16 = 413,440`, not 477,440 (six levels); "5,934 →
110,592" is not `32 ×`. The totals (≈ 719 KB) come out close by cancellation; the trace sizes,
the `31.7 k` sibling elements, the `witWords` estimate and the irregular-read counts inherit the
error. `piSize` will fix it; recompute §1.1, §1.2, §4.5 and §1.4 from it.

### BP-C-m3. Z1's sampling sentence is self-contradictory

"8 per 128 bits ⇒ `⌈(m−13)/2⌉` squeezes": 8 coordinates per 128 bits would be 16-bit
coordinates and `Z1 = 17/2^16`. The squeeze count is right for two full 128-bit F coordinates
per answer. Fix the wording; make `card_chF_fiber` the only F sampler.

### BP-C-m4. E1's point size

"`log₂ N_M ≤ 18`" against ≈ `2^18.5` rows per node (§4.5; more after M3): 19–20 coordinates,
`20/2^128`. Harmless; tie the row to `nodeLayout`'s constant.

### BP-C-m5. Booleanity of the L region's bit-elements must be an explicit claim

Position bits enter the Merkle rows as `cur = left + b·(right − left)` with `b` "a bit-element
`(b, 0, …, 0)`". `b` is a GF(2) coordinate of `z` by `unpack`, but the 127 zero coordinates of
the element are constraints on `z` that nothing listed imposes. If omitted, `b ∈ F` is free: for
any `cur` the prover chooses `left` and sets `right := left + (cur − left)/b`, so the next query's
halves are unrelated to `cur` and the path check is void; the answer-to-bits decomposition
`a = Σ bᵢ eᵢ` is also void. Add the zero-sub-cube evaluation claim (or Lr's linear rows) for L
and charge it (`≤ 20/2^128`).

### BP-C-m6. §5.4 step 3's Booleanity sentence trails off

"the zerocheck's `Sel ⊗ I` rows force `z[k] = …` with Boolean inputs... Booleanity is enforced
as in Flock by ..." — Booleanity is definitional (`z := unpack f` is GF(2)-valued); the `Sel ⊗ I`
rows do not enforce it and the zerocheck's DT24 pinning *needs* it (p Boolean on the cube, paper
§4.3). State the one-line reason and remove the alternative.

### BP-C-m7. The completeness fallback and `V`'s recursion

The `W` branch runs `acc vk cᵢ pᵢ` on children, hence `V vk cᵢ πᵢ` recursively; `V` must be
defined by well-founded recursion on `π.size` (a child proof is a proper substring) and `acc`
inlined (`FRSubmission.acc_eq`), since `Submission.acc` refers to `S.V`. The DoS bound holds
(`|π| ≤ proofCap` is `acc`'s first conjunct, so a `W` node's children traces total ≤ 1 MiB:
≤ 16 k compressions). No change to the design; state it in §3 and §5.5.

### BP-C-m8. Extractor fuel after M3/M4

With the novel basis (M4) the level-0 basis change adds ≈ `2^40` products (`2^45.7 → 2^46.7`
statements at `m = 30`); with four levels kept (M3) nothing changes in `ext`. `fuel t = 2^46 +
2^12 t` is then too small; `2^47.5 + 2^12 t ≤ extractorBudget t` still holds. Re-derive §6.3.

### BP-C-m9. `queries_le` and the trace constants depend on M7

`qV = 8,192` covers every single program (≈ 8,810 items at `m = 32` per §1.2 is **above**
8,192 — the §1.2 table's own item count exceeds `qV`; with m2's corrected sibling count the
`m = 32` trace has ≈ 745 + 6,922 + 140 ≈ 7,807 items, under 8,192 by 5 %). Make `qV` a theorem
of `gen`'s exact count, with the margin stated, after M2 (extra squeezes) and M7 are settled.

---

## What was checked and holds

- Sampling: F from 16 bytes and K from 32 bytes are exact; positions use `b` bits per index with
  `n` a power of two (no modulo bias); the martingale over a multi-answer phase (`extCount_split`)
  is exact for Z1's coordinates and P2's positions; no phase's bad set depends on a later prover
  message (every challenge is squeezed after the data it tests is absorbed: `cap₀` before Z1,
  `capᵢ₊₁` before P2 of level `i`).
- P2's `(1 − γ)^t` with `e = ⌊γn⌋`: `|A_c| ≤ n − e − 1 ⇒ (|A_c|/n)^t ≤ (1−γ)^t`; recomputed
  `2^-120.35, -120.67, -120.28, -121.09` (`m = 30`), `-120.36, -120.69, -120.34, -120.38`
  (`m = 32`); `2e < n − k + 1` at every level; `t` and cap depths as stated.
- The agreement-set extractor: under non-bad P1 (MCA, once M8 is fixed) and P2, the fold's
  agreement set with `Enc(g⁽ⁱ⁺¹⁾)` has `≥ n − e ≥ k` positions and is the joint agreement set of
  all `2^ℓ` rows, so row-wise interpolation from any `k` of them is the unique nearest codeword:
  what §6.2 step 4 computes.
- `final`'s first-preimage reading: collisions and in-play hits are `Bad`; the verifier's path
  and the extractor's top-down walk read the same entries on a collision-free log.
- `∀ vk`: no branch accepts because of a signature; the `W` branch decides `Rel (acc vk)` itself,
  the SNARK branch proves `acc` on committed children. `SigOk`'s length and index conjuncts hold
  by the output layout; `|π| ≤ proofCap`, `|tr| ≤ qV`, `|q| ≤ queryCap` are shape constants.
- `Computes` under B-8 (`computes_Eof` probe) and the fuel/`εR` arithmetic.
- Completeness: degenerate challenges only; `δ = 2^-100` is loose by ≥ 10 bits.

## Verdict

**Not ready for implementation.** Eight majors. None kills the approach, but M3, M4 and M7
change the Lean plan and the circuit budget materially (the novel basis enters the Lean; the
final level or its cost returns; the NN variant must be one program or several variants), and
M1, M5, M6 are missing constraints without which `node_sound`/`leaf_sound` are false as stated.
M2 is a cap violation under the blueprint's own answer-sharing rule. After the fixes the error
table's maximum per fresh query stays at P2 level 2 (`2^-120.28 + 2^-144`), under `εR`.

---

## Round 2

Reviewed: `BLUEPRINT.md` revision 2 (`de0d708`), its §10 fix pass, `logs/blueprint/sizes.py` /
`sizes.txt`, against the same contract files and the Flock paper (§4.6, App. A, C).

### Verdict per round-1 finding

| Finding | Verdict | Note |
|---|---|---|
| BP-C-M1 | **closed** | `hashStmt` is an IR op and 2 H blocks per slot; `V = parse; stmtOk; runIR`. Wording slip: the inputs are in the statement-fields absorb (item 1), not the seed payload (R2-m5). |
| BP-C-M2 | **closed** | L3, S3, I2, B2 rows at `127/2^128`; Z2 restated at degree ≤ 127; one squeeze per phase. (The I1 row has a new problem of its own: R2-M4.) |
| BP-C-M3 | **closed** | Five levels, `e = ⌊(n−k)/2⌋`; recomputed `(1−e/n)^t`: `2^-120.36, -120.70, -120.36, -120.45, -120.41`; `2e < d` at every level; final `Enc₄ = 2 k₅ t₄ = 4,032`. |
| BP-C-M4 | **closed** | LCH basis; the tensor identity is correct; the back-substitution is valid as the half-split recursion (`X_x` with `msb(x) = κ−1` vanishes on `D[0…k/2)`, `Ŵ_{κ−1} = 1` on the upper coset, so the upper block is a `k/2` instance on the coset): `T(k) = 2T(k/2) + k²/4 = k²/2` per row as charged. |
| BP-C-M5 | **closed** | `one = 1` a public-pattern claim, explicit in `leaf_sound`/`node_sound`. |
| BP-C-M6 | **closed** | T region dropped; trace = message slots of the chain's blocks; address rule stated. |
| BP-C-M7 | **partly closed** | One program `P30`, one trace layout, fixed dimensions. Open: the selector is one bit for three kind bytes, and kind-dependent public constants are "computed by the verifier" (R2-M1). |
| BP-C-M8 | **closed** | K-valued words, `C_K`, `C_mca ≤ 2^60`, line factor `2^(ℓ−r)`, `interp_F` once per level; the proof plan states the `O(k(e+1))` degree honestly. The statement is sufficient for `fold_preserves` (joint agreement set = the fold's agreement set, round by round). |
| BP-C-m1 … m9 | **closed** | m1: `2^16 · logCap` windows; m2: sizes recomputed (one residual: S2's round count, R2-m1); m3, m4, m5, m6, m7, m8, m9 as §10 says. |

### Attacks on what the fix pass introduced

#### BP-C-R2-M1. The child-kind selector has the wrong arity, and kind-dependent public patterns cannot be "computed by the verifier"

§4.3 (1): "the kind selector `sᵢ ∈ {0,1}` equals the kind byte of the seed payload's `hdr`". There are
**three** kind bytes (`'L'`, `'P'`, `'N'`) and a `P30` child's replay differs between its leaf and node
uses: `Sel`, the `evalM`/`evalL` matrices (empty for `'P'`), the second digest chain, WOTS, the
`hashStmt` variant (`leafStmt h n` from `enc64 n ‖ h ‖ 0^24` against `nodeStmt c₁ c₂` from the same
64 bytes), and the kind-selected `t_lo`/`f0`/padding patterns. A one-bit selector cannot be asserted
equal to one of three bytes, and the replay of the E/Lr phases must use the child's own constants:

- if every `P30` child is replayed with the node constants, honest `'P'` children (the stream leaf)
  fail the replay (their zero E/Lr messages do not satisfy the node's `evalM` checks; `hashStmt`
  computes `nodeStmt` of a leaf's fields): the stream link is unprovable;
- if with the leaf constants, a `'N'` child's E/Lr checks are replayed as `0 = 0`: the replay
  accepts a child trace whose own `V` rejects, `acc vk cᵢ pᵢ = false`, and `node_sound` is false.

Second, §4 says the public-pattern right side "is computed by the verifier", but for the chain
blocks the pattern depends on the child's kind (its block count, last-block `t_lo = |B|`, `f0`,
padding), which the parent's `V` does not know: the kinds are committed, not in `c` or `vk`.

*Fix.* Selector = the kind byte itself as a 16-byte element of item 0 asserted equal to
`Σ_κ s_κ · const_κ` with one-hot bits `s_L, s_P, s_N` (three L bits, `Σ s_κ = 1` a linear row);
every kind-dependent constant, import address and matrix is the `s`-weighted sum of the three
(two irregular entries and one product row per import, as the muxed imports already are). Every
kind-dependent pattern claim is linear in `z` with the selector as a witness term: `Σ_i eq(θ,i)
z[i,s] − Σ_κ z[s_κ] · patSum_κ(θ) = 0`, where the verifier computes the three `patSum_κ(θ)`; its
soundness is the same SZ bound (given `Σ s_κ = 1`, the claim is `Σ eq(θ,i)(z − pat_{κ*})`). State
in §4.3 (1)–(2) and §4 ("public-pattern claims"), and recount the worst slot (it is the `'N'` child).

#### BP-C-R2-M2. `final` fails on `W` proofs longer than `proofCap`

`V`'s `W` branch accepts `encode w` for **every** witness (it must: `CompleteWithError … 0` quantifies
every `w` of `Rel`, and a node witness's children may carry traces of `qV × queryCap` bytes, so
`encode w` runs to `2^34` bytes). `KState.final` has no size guard: for such a `π` and any `L`,
`(V c π).runLog L = some true` and `E c π L` must return the witness. §6.2 step 1 copies "`⌈|π|/8⌉`
words of `π` to the output (**cap: `2^17` words**)": for `|π| > 2^20` the copy is truncated,
`decodeWit` reads a field past the end and returns `none` (or a wrong witness), and `final` is
unprovable. (`Computes` is not affected: its domain is `|π| ≤ proofCap`.)

*Fix.* Cap the copy loop by the tape length (`capFn = t`, affine; the input holds `|π|/8 ≤ t`
words), so `E` copies any `W` proof; the fuel `2^47.5 + 2^12 t` covers a linear copy. (The output
cap is only demanded on the domain.) Alternatively `V`'s `W` branch rejects `|π| > proofCap`, but
then completeness fails for the large witnesses, so the first fix is the only one.

#### BP-C-R2-M3. Deduplicating repeated positions makes the item sequence answer-dependent

A.2: positions are drawn with repetition, and "each repeated position is opened once in the
trace". At level 0 the collision probability per proof is ≈ `t₀²/(2n₀) ≈ 0.16` (`m = 30`), so a
noticeable fraction of honest traces have fewer items than `items kind` says. Then
`FRVIRSpec.items_length` is false, `piSize` (A.3 rows 11–12, "position by position") is not a
constant, `reassemble` needs the dedup rule, and the node circuit's fixed-address imports (§4.4:
"a column in a chain's message slots" at an address fixed by the item layout) read the wrong
cells — B-6/B-7's premise ("`runSeq` on a well-shaped trace is the straight line") fails.

*Fix.* Open every index: a repeated position's column and path queries are asked again (`runLog`
answers them from the log; `runSeq` and `traceDigest` take the duplicate entries; a repeated
query is not a fresh query, so `step` is untouched). Item counts, `piSize`, and the layout are then
constants. Delete the dedup sentence from A.2 and A.4.

#### BP-C-R2-M4. The I1 row charges one multilinear; the public-pattern mechanism issues many at one `θ`

§4 defines one claim per slot or bit (`one`, `t_lo`, `f0`, chain starts `h_in` (2 slots), the
last-block padding (up to 4 slots), `Sel`'s complement, `P` (6 slots), the two IO endpoints), all
tested at the **same** `θ`. The bad event is the union over the false claims: `#claims × (log N +
slot bits)/2^128`; with ≈ 15–20 claims of 16–30 coordinates that is `≈ 2^-119 … 2^-118.8`, above
`εR`. The row's lemma ("SZ on a ≤ 25-variate multilinear") does not match the mechanism.

*Fix (free).* All pattern differences `d_j(i) = z − pat_j` are GF(2)-valued, so batch the claims
with **fixed GF(2)-independent constants** `c_j ∈ F` (the DT24/`pinned_rank` argument: `Σ_j c_j
d_j(i) ≠ 0` whenever some `d_j(i) ≠ 0`, up to 128 claims): one multilinear, one `θ`, bad `≤
30/2^128`. Or one squeeze `κ_pat` for a random batching (`(#claims − 1)/2^128`) before `θ`. State
the choice and make the I1 row its bound.

#### BP-C-R2-m1. The shift argument is `m − 14` rounds, not one

Paper §4.6: `Σ_y eq(τ, y) Out(y) = Σ_y shift(τ, y) In(y)` is checked by a sumcheck over the `n`
block variables (16 at `m = 30`, 18 at `m = 32`) plus one round over the selector bit. §2.3 step 4
("S2 one round of degree 3"), A.3 row 5 ("S2 round 48") and the FS item counts assume one round.
Per-query error unchanged (each round its own squeeze, `3/2^128`); `piSize` grows by `≤ 17 × 48`
per chain, items by `≤ 2 × 17` (node: two chains); `qV`'s margin absorbs it. Re-run `sizes.py`.

#### BP-C-R2-m2. B2 has `m − 6` multilinear rounds

The quirky `ẑ` has `m − 6` multilinear variables and one univariate; §2.3 step 7 and A.3 row 7
say `m` rounds (`m × 48`). Cosmetic; fix the count.

#### BP-C-R2-m3. `Ã_L, B̃_L, C̃_L` cost one product per nonzero

§3.1 prices the L R1CS's sparse sums at `≈ 2^15 F`; `Σ_{(r,c) ∈ nnz} eq(τ,r) eq(σ,c)` with `nnz ≈ 2^18`
is `2^18` products (eq tables of `2^15` each are the cheap part): +18 ms in `T_V`, and in the
parent's replay of a `'N'` child ≈ `2^18` rows per slot (`N_M`'s margin 1.50× → ≈ 1.2×) unless L's
matrices are templated like M's. Count it in `evalL`'s row cost and in §4.5.

#### BP-C-R2-m4. `invF`'s two rows leave `a⁻¹` free at `a = 0`

A.5: "`a · a⁻¹ = 1 ∨ a = 0` via a selector", 2 rows; `semIR` fixes `invF 0 = 0`. With `a·inv = sel`
and `a(1 − sel) = 0` only, `inv` is unconstrained when `a = 0`, so a circuit-satisfying assignment can
differ from `semIR` downstream of a zero denominator (a univariate round's Lagrange weights at
`λ ∈ S ∪ Λ`, say) and `compile_sound` (circuit ⇒ `semIR = accept`) is false for that op. Add the row
`inv · (1 − sel) = 0` (3 rows) or make the op's compiled form assert `a ≠ 0` (`sel = 1`) where `V`
would reject anyway.

#### BP-C-R2-m5. `hashStmt`'s inputs

§4.2: "inputs wired to the header fields read from the seed payload": `h`, `n` (leaf kinds) and
`c₁ ‖ c₂` (node) are in the statement-fields absorb (item 1), the seed payload holds only `hdr`
(`kind`, `m`, `pub = s`). Wire to item 1's payload; for a leaf child the second allotted block's
patterns (`t_lo`, `f0`, message) must be defined (unused but `one = 1` or excluded from `usedH`).

### Checks that hold

- Error table: every row recomputed; maximum `2^-120.36 + 2^-144 ≤ 15/2^124 = 2^-120.093`; the
  univariate rows `2^-120.99`; P1 `≤ 2^-190` with `C_mca ≤ 2^60` and the `2^(ℓ−r)` lines; H `2^-144`.
  One squeeze per phase removes the sharing attack. (R2-M4's I1 row excepted.)
- `mca_ud_line` over K: the statement is true for the F-valued case by the round-1 probe and the
  BCIKS20 argument, applies verbatim to K-valued words (one field), and gives exactly what
  `fold_preserves` needs (the fold's agreement set is the joint set); `interp_F` is sound (the
  interpolant through F-valued data on F-points, `|A| ≥ k`, has F-coefficients in the novel basis
  too, since the `X_x` have F-coefficients).
- Novel basis: `D` a subspace, `Wᵥ` linearised, `X_x` of degree `x` so `{X_x}_{x<k}` spans degree
  `< k` (distinct degrees); distance `n − k + 1`; the tensor identity; the half-split
  back-substitution (above); `Enc(g)[j]` as a multilinear evaluation at `(Ŵᵥ(D[j]))_v`.
- `one = 1`: the claim's difference is GF(2)-valued, SZ `16/2^128`; the all-zero spare blocks are
  excluded from the pattern's support and satisfy the block R1CS, as stated.
- `hashStmt`: 1–2 compressions per child, output tied to `cᵢ`, `V` itself hashes `stmtOk` once.
- `W` completeness at `δ = 0`: `P := encode`, `V` decides `Rel (acc vk)` with `accWith V = acc`
  (`acc_eq`) and `decode ∘ encode = id`; no query, so `failProb = 0`; `V` well-founded on `π.size`.
- Coordinate split as a K-linear combination of the two F-claims by `(1 − z_c, z_c)`: `1/2^256`,
  inside P1's `+ 2`.
- Budgets: `qV = 10,240 ≤ 2^16`; `piSize ≤ proofCap` with ≥ 300 KB to spare for A.3 row 5 and
  R2-m1; `outCap`; `fuel ≤ B`; `N_M` margin 1.5× before R2-m3.

### Overall verdict

**Not ready to fork, by four local fixes; no structural change is needed.** R2-M1 (three-way
selector; selector-linear pattern claims), R2-M2 (uncapped `W` copy), R2-M3 (open repeated
positions) and R2-M4 (batch the pattern claims) are each a few lines of the blueprint and change
no module boundary, no budget beyond R2-m1/m3's recount, and no theorem shape except the `I1`
row's lemma and `node_sound`'s selector hypothesis. With those applied, and the minors folded into
S-0's `sizes.py` re-run, the tracks can fork.
