# Phase 0 · I: reuse inventory for `flock-recursive`

Work package **I** of `PLAN.md` §3. For each Lean component the entry needs, this document lists what
already exists and where, what it proves and under which hypotheses, how large it is, whether it is
field-generic, and what adapting it involves. Adaptation is described by the work it consists of,
never by duration. Line counts are `wc -l` (whole files) unless marked "code", which means the
core's `scripts/loc.py` count (`logs/phase0-I/loc-*.txt`). Nothing here was built. The inventory is
read-only: no source repository was edited or built.

Sources, at the revisions read (2026-10-27):

| Tag | Source | Revision |
|---|---|---|
| **SR** | `submissions/spartan-srom/lean/` (this worktree): 66 modules, 24,940 lines, 17,901 code | `f07d028` |
| **LV-main** | leanerVM `main` (`LeanerVM/`) | merge-base `a37b2b04` |
| **LV-stack** | leanerVM open stack #114–#156, top `stack/43-headline-unconditional` (fresh clone in `logs/ref/leanerVM`) | `921e893f` |
| **CP** | CompPoly at the core's pin (`recursion.fast-v4/.lake/pkgs-local/CompPoly`) | `572f997` (2026-09-29) |
| **CP-head** | CompPoly upstream `main` (fresh clone in `logs/ref/CompPoly`) | `1cb8f5c` (2026-10-20) |
| **AL** | ArkLib at the core's pin (`pkgs-local/Arklib`); ArkLib remote `main` and open PRs (the local checkout `/home/devops/Verified-zkEVM/ArkLib` is stale at `db7005f`) | `7653a90`; `59e5b779` (2026-10-27) |
| **VC** | VCVio at the core's pin (ArkLib's own manifest pins VCVio `d7089e46`, not `a4232d0`) | `a4232d0` |
| **Core** | `.contract` (core PR #18 head) `RecursionFast/{Contract,Library,Controls}` | `15dac52` |

Licences: leanerVM, CompPoly, ArkLib and VCVio are Apache-2.0. The repository is Apache-2.0. leanerVM
has no NOTICE file. Files with third-party copyright lines are listed in §5.

---

## 1. Summary

**The most valuable reuse, in order of value per line:**

1. **SR's certified skeleton.** The entry already certified under v4 has the generic MLE
   (`SpartanSromMLE`), sumcheck counting lemmas, ring switching (`ring_inj`, `stage_bad_le_one`), the
   Merkle tree over the oracle with `open_binding`, the Fiat–Shamir transcript with exact-uniformity
   fiber counts, the potential-over-chains `step` law (`muG_step`), the path-uniform query bound
   `AtMost`, and the BLAKE2s chain circuit with `block_sound` and `chain_sound`. It is all on the
   allowlist and kernel-checked at the pin. Most of it is generic over a characteristic-2 field.
2. **CompPoly's `Tower.Fast` `FastBT128`.** It is a compiled GF(2^128) on two `UInt64` limbs, with
   `Field FastBT128` and `ringEquiv : FastBT128 ≃+* ConcreteBTField 7`, and no `sorry` or `csimp`.
   Also **`BF128Ghash`**, GF(2)[x]/(x^128+x^7+x^2+x+1), with a kernel-checked Rabin irreducibility
   proof (`ghashPoly_irreducible`). Neither is on the allowlist, so whichever we use is copied.
3. **CompPoly's Gao decoder.** It is a computable unique RS decoder over **any field and any set of
   distinct points**, so it works over GF(2^128) on an additive subspace. It comes with
   `decode_eq_some`, `decode_eq_none_iff` and `decode_unique`. It is the specification-level decoder
   of the extractor. It is not on the allowlist and is quadratic.
4. **CompPoly's additive NTT.** `additiveNTT_correctness` holds for any finite field `L` over
   `𝔽q = GF(2)` with an independent basis `β`, `β 0 = 1`. It is executable
   (`computableAdditiveNTTFast_eq_additiveNTT`). The inverse and the coset transform are in open
   CompPoly PR #405 (Mathlib-only). leanerVM's `Whir/Transform.lean` already has `fwd`/`inv` with
   `fwd_inv`/`inv_fwd` over its K = GF(2^64) domain.
5. **leanerVM's WHIR soundness core** (`Whir/{Lanes,Exact,FoldSound,BoundarySound,FinalSound,…}`).
   It is generic in per-level `Par`, which carries `ListBound`/`McaBound`. `listBound_unique` already
   gives list size 1 in the unique-decoding (UD) regime. Its mathematics needs Mathlib plus
   `CompPoly.Multilinear`. Its statements are ArkLib `Component.Security` objects, so the counting
   lemmas copy and the security statements are restated against the contract's `KState`.
6. **leanerVM's Flock algebra** (generic `[Field F] [CharP F 2]`): zerocheck with univariate skip
   (`Flock/Tables.lean`, `Zerocheck.lean`), lincheck, ring switching and the `flockError` per-round
   table (z_skip `127/|F|`). Also its deterministic Merkle binding by log replay
   (`MerkleLog.binding_of_log`) and the generic chain history (`HashChain.history_determined`).
7. **ArkLib's unique-decoding proximity gaps.** These are proved at the pin and absent from ArkLib's
   `axiom_baseline.json`:
   - `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` and `rs_mcaError_le_of_le_relUDR`,
     both at `n/|F|`;
   - **`rs_epsCa_le_in_unique_decoding_range`** (BCHKS25 Thm 1.3, with no factor `n`);
   - DG25's `reedSolomon_multilinearCorrelatedAgreement` (the tensor fold);
   - the half-gap binary-fold MCA, `tensorFoldBad_probability_le`, at `h·2n/|F|` for `δ ≤ 1/2 − ρ`.

   Their closures are large (≈ 42–45k lines with VCVio, PolyFun and CompPoly), and their probability
   statements use VCVio notation that the source rule refuses. They are copied and restated over
   counting.
8. **The core's machine library** (`Library/Machine.lean`). It has the `Runs` relation with one
   composition lemma per statement and `run_of_runs`, plus two worked `Computes` proofs:
   `WitnessSending.computes` (21 statements) and `Controls/LogScan.scan_computes` (106 statements,
   `16 · t` steps).

**The biggest gaps** (§4):

- **G1, the extractor as a machine program.** A step-counted Reed–Solomon decoder written as an
  `XProg`, with `Computes` proved. Nothing exists that programs or verifies anything of that size on
  the contract's machine. There is no structured-programming layer, no verified compiler and no
  field-arithmetic macros.
- **G2, half-distance mutual correlated agreement for the folding steps up to `(1−ρ)/2`.**
  - ArkLib's proved material covers correlated agreement in the whole UD range: BCIKS20 at `n/|F|`,
    BCHKS25 without the factor `n`, and DG25's tensor form.
  - It covers **mutual** CA only up to `δ ≤ 1/2 − ρ` (half-gap plus tensor fold), and the glue lemma
    there is missing.
  - All of it is stated over VCVio's `Pr` and must be restated over counting to be copied.
  - leanerVM has only exact agreement and Johnson-regime MCA. SR's lemma is AHIV22 at `3e < d`.
  - The gap is the remainder: MCA up to `(1−ρ)/2`, or a parameter choice inside `1/2 − ρ` (T).
- **G3, a UD Ligerito/WHIR instance.** The new `McaBound` inhabitant, the per-round error ≤ 2^-120
  table, and the restatement of leanerVM's ArkLib-framed round-by-round (RBR) theorems as `KState`
  potential steps.
- **G4, GF(2^256)** with fast compiled arithmetic. Neither CompPoly nor leanerVM has one.
  `ConcreteBTField 8` exists only abstractly, with no fast form.
- **G5, the recursive node circuit.** The child verifier's arithmetic in R1CS, the trace digest, WOTS
  (≈ 300–500 compressions), and its circuit-correctness lemma. That lemma is the bridge that makes
  decoding the committed witness give `Rel`.
- **G6, the bridge from the novel basis to the monomial basis.** Gao returns a polynomial in the
  monomial basis, while the code encodes in the novel basis. The owed lemma is that the novel
  polynomials span degree `< 2^κ`. CompPoly's `NovelPolynomialBasis` has the ingredients.

---

## 2. Component tables

Legend for "Gen.": **G** generic (any field / char-2 field / any code); **B64** tied to
GF(2^64)/GF(2^192) or to SR's parameters; **K** tied to leanerVM's K = GF(2^64) domain; **ROM-fw**
stated in an ArkLib/VCVio framework that the entry cannot import (§5).

### 2.1 Binary fields with fast compiled arithmetic

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| CP `Fields/Binary/BF64/*` | `BF64 = GF(2)[x]/(x^64+x^4+x^3+x+1)` on `BitVec 64`. Irreducibility by Rabin certificate (`BaseCertificate`). `BF64.Ext3 = BF64[y]/(y^3+y+1)`, `ext3Poly_irreducible`, `nat_card_ext3 = 2^192` | ≈ 1.5k (BF64 files; the allowlisted CompPoly closure is 28 modules, ≈ 8.4k lines) | B64 | **yes** (root) | none; compiled `BitVec` code is `Nat` arithmetic, so it is slow |
| CP `Fields/Extension/{Defs,Arithmetic,Field,Cardinality,Bridge,Binomial}` | Generic computable extension `Ext P` of any finite field by a monic modulus. `instField` (Fermat inverse), `ringEquivQuot : Ext P ≃+* AdjoinRoot`, `card_quot = q^d` | 1.5k | G | **yes** (in the closure) | GF(2^128) = `Ext` of BF64 by an irreducible quadratic `y^2+y+α` (Tr α = 1), with a no-root irreducibility proof as `Ext3`'s. GF(2^256) is a quartic or a quadratic over that. Needs fast twins (below) |
| SR `FieldBase`, `FieldBaseCorrect` | `F` = GF(2^64) on `UInt64`: Karatsuba over `clmul32`, `reduce`, Itoh–Tsujii inverse. `toBF64_mul`, `ringEquivBF64 : F ≃+* BF64`, `instField`, `card_F` | 99 + 812 code | B64 | own | reusable as the base of a degree-2 tower GF(2^128) = F[y]/(y^2+y+α), following the `FieldExt*` pattern |
| SR `FieldExt`, `FieldExtCorrect` | `EF` = GF(2^192): 3-term Karatsuba, adjugate inverse. `toExt3_mul`, `ringEquivExt3`, `instField`, `card_EF`. Proof pattern: `linear_combination` mod `g^3 = g+1` and char 2 | 56 + 359 code | B64 | own | the pattern transfers to a quadratic extension; the identities are re-proved for `y^2 = y + α` |
| LV-stack `Parameters/ToCompPoly/BF64Fast.lean` (#119) | `clmul32` (BearSSL masked multiply), `clmul64` Karatsuba, `reduceWords`. `toPoly_clmul32`, `toPoly_clmul64`, `toPoly_reduceWords`, `mulFast_eq`, `invFast_eq` | 720 | B64 | copy | registered with `@[csimp]`, which entries may not use. Copy the word functions and their equalities and call them directly |
| LV-stack `Parameters/ToCompPoly/ExtensionFast.lean` | `mulDeg3` with `mulDeg3_eq` over any ring, `invDeg3`/`invDeg3_eq` (Cramer). Generic over CompPoly `Ext P` | 353 | G (deg 3) | copy | write the degree-2 analogue (`mulDeg2`, `invDeg2`) |
| CP `Fields/Binary/BF128Ghash/*` | `BF128Ghash = AdjoinRoot ghashPoly`, `ghashPoly_irreducible` (Rabin: `X^(2^128) ≡ X`, `gcd(X^(2^64)+X, P) = 1`, kernel-checked certificates). `ConcreteBF128Ghash` on `BitVec 128`, `mul = reduce_clMul ∘ clMul`, `instFieldConcreteBF128Ghash`, `BF128Ghash_card = 2^128`. No `sorry`, 135 `noncomputable` defs (specification side) | 3,822 (7 files) | GHASH | copy (closure outside the allowlist: the 7 files themselves) | the compiled `BitVec 128` code is slow. A two-`UInt64` twin with `clmul64` (leanerVM's) and a proof of equality is owed, as SR did for BF64. Matches the field of Flock/POLYVAL if the blueprint chooses GHASH's modulus |
| CP `Fields/Binary/Tower/{Fast,FastDefs}.lean` (+ `Concrete/*`, `Abstract/*`, `Support/*`) | Binary tower (Fan–Paar/Binius). `FastBT k` on one `UInt64` for `k ≤ 6`, **`FastBT128` (level 7) on two limbs**. `Field BT8 … BT64`, **`instance : Field FastBT128`**, `ringEquiv : FastBT128 ≃+* ConcreteBTField 7`. Multiplication is recursive Karatsuba with 256-entry byte tables (`mul8Table`), not `clmul`. No `sorry`, no `csimp` | 10,079 (27 files); `Tower.Fast` closure 6,248 lines outside the allowlist | tower | copy | ready-made, proved GF(2^128) with compiled code. Its speed against a `clmul` route is a phase-0 **M** measurement. Tower basis ≠ polynomial basis, so its byte layout and the Flock prover must agree (blueprint) |
| CP `Fields/Binary/Tower` level 8 | `ConcreteBTField 8` (GF(2^256)) is defined generically (`ConcreteBTField k`) | — | tower | copy | **no fast form**; G4 |
| CP-head | No binary-field change since the pin (4 commits: secp256k1, Goldilocks, CI, **Lean bump to v4.35.0** (#400)) | — | — | — | copying from head means back-porting to v4.34.1 |

### 2.2 Additive NTT and Reed–Solomon codes over binary fields

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| CP `Fields/Binary/AdditiveNTT/*` | Novel polynomial basis (LCH14; `normalizedW`, `W_linearity`, `novelPolynomialBasis`). **`additiveNTT_correctness`**: output `j` = `P.eval (evaluationPointω … j)`, with `P = polynomialFromNovelCoeffs …`. Executable twins `computableAdditiveNTT_eq_additiveNTT`, `computableAdditiveNTTFast_eq_additiveNTT`. Hypotheses: `[Field L] [Fintype L]`, `𝔽q` with `card 𝔽q = 2`, `[Algebra 𝔽q L]`, `β : Fin r → L` linearly independent with `β 0 = 1`, `ℓ + R_rate < r`. Forward only | 5,617 (8 files); closure 6,293 lines outside the allowlist | G (any char-2 finite field, subspace domain) | copy | instantiate at GF(2^128) with the polynomial-basis `β`. The inverse is in CP PR #405 below |
| CP PR #405 (open, head `1504725`) | Additive NTT over a coset `shift + S_l` and **its inverse** (LCH14). The inverse recovers coefficients from values for any twiddles. "Any field of characteristic 2 and any basis, no `Fintype`; imports only Mathlib" | +839 | G | copy (unmerged, Lean v4.35 base) | the fast interpolation on a subspace that a quasi-linear decoder needs |
| LV-main `Protocol/NovelBasis.lean` | `encode (φ : K →+* S) κ R m` (Annex B `Enc`), `encode_eq_eval`, `encode_columnWeight`, **`encode_eq_of_agree`/`encode_injective`** (distance `2^(κ+R) − 2^κ + 1`), `basisElt_linearIndependent`, `natDegree_novelPoly` | 552 | K | copy | K = GF(2^64) with basis `g^c` and `decide +kernel` facts. With GF(2^128) built over BF64 and domains inside K (`κ+R ≤ 64`) it carries over |
| LV-stack `Whir/Transform.lean`, `TransformWords.lean` | `fwd`, `inv` (LCH recursion), `fwd_inv`, `inv_fwd`, `fwd_getElem (hj : j ≤ 64)`, `encodeFast_getElem (κ+R ≤ 64)` | 314 + 151 | K | copy | as above |
| LV-stack `Whir/DecodeNtt.lean` (#134) | `exactNtt`: `inv` on the first coset, then a re-encode check. `exactNtt_spec`, `exactNtt_of_codeword`. **Exact codewords only** | 114 | K | copy | the fast path of a decoder; not error-correcting |
| SR `RS.lean` | Generic RS over `K ⊂ E` in the unnormalised subspace basis `W κ i`. `basis_deg`, **`code_dist`** (min distance `|ι| − 2^ℓ + 1`), `rsCode_kRational`, `encAt_eq` | 313 code | G | own | reusable as the code definition |
| AL `Data/CodingTheory/{ReedSolomon,InterleavedCode,Erasure,BerlekampWelch/*}` | `ReedSolomon.code (domain : ι ↪ F) deg` (any injective domain, so additive subspaces too), `minDist_of_le`, `uniqueDecodingRadius_RS_eq`. `InterleavedCode` (`jointProximity`, `jointAgreement`). `eq_of_consistent_with_erased`. Berlekamp–Welch `decoder_eq_some`, `hammingDist_le_of_decoder_eq_some`, but the decoder is **noncomputable** (`linsolve` uses `Classical.choose`) | 656 + 1,022 + …; RS closure 9,962 lines (pulls CompPoly Univariate) | G | copy | spec-side definitions only; no computable decoder (Gao, §3, is the computable one) |

### 2.3 Multilinear extensions, sumcheck, zerocheck, lincheck, univariate skip

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| SR `MLE.lean` | Over a comm ring: `eq_sum_one`, `eq_mle`, `mle_split`, `eq_frob` (char 2), `mle_cube`, `mle_fix0`. Computable `eqTable`, `mleEval`, `bind0`, proved equal (`tbl_eqTable`, `mleEval_eq`) | 260 code | G | own | none |
| SR `Sumcheck.lean` | `round_bad_le` (`≤ d` bad challenges, `Polynomial.card_roots'`), `round_bad_le_of_check`, `round_escape_le`, **`zerocheck_bad_le`** (fixing variable 0 of a nonzero table gives zero for ≤ 1 value), `batch_bad_le`, `sumcheck_complete` | 310 code | G | own | none for multilinear rounds. The univariate-skip round is new (below) |
| LV-main `ToArkLib/Flock/Tables.lean` | **Univariate skip**: `SkipDomain`, `skipTable`, `pValue`, `pPoly`, `natDegree_pPoly_le`, `skipClaim_skipMessage`, `batchHolds_iff`, `sum_eRow_zTable`, `mTable`. ArkLib-free | 585 | G char 2 | copy | needs `CMlPolynomialEval` (CompPoly `Multilinear.Basic`, 1,187 lines, off the allowlist), or a port to `Vector F (2^n)` as SR did |
| LV-main `ToArkLib/Flock/{Zerocheck,Lincheck,Rounds,Reduction,Security}.lean` | `flockSecurity : Component.Security (flock …) relIn relOut (flockError P s')`. Hypotheses: `hnodes` (injective skip nodes), `hfixed`, `hinj` (ring switching injective), `hIn`/`hOut`, `hcell` (packing), `hbool`, `hread`. `flockError` per challenge over `|F|`: 1 per point coordinate; `2·2^s − 1` on z_skip (127 at `s = 6`); 2 per zerocheck/lincheck round; 3 on α; 1 per ring-switching coefficient. Refutation controls `skipDraw_unzeroed_not_rbr`, `alphaDraw_noConst_not_rbr`, `linEnd_unchecked_no_stateFunction` | 313 + 184 + 242 + 202 + 744 | G char 2, ROM-fw | copy the algebra | the statements are ArkLib `OracleReduction` objects. Copy the counting cores (`card_false_batch_le`, `natCard_restrictedZero_update_le`, `card_interpolateAt_eq_le`) and restate each round as a doom predicate with a counting bound in SR's `SoundnessSpartan` form. `Rounds`' fast forms are `@[csimp]` and must be dropped |
| LV-main `ToArkLib/{SumcheckRound,Sumcheck,ProductSumcheck,Batch}.lean` | `roundsSecurity` (RBR knowledge soundness at `d/|F|`), `weightedSecurity`, `plainSecurity`, `normalizedSecurity`, `transport` (a round message sent without one coefficient), `batchSecurity` at `(k−1)/|F|` | 445 + 818 + 194 + 90 | G, ROM-fw | design template | as above |
| LV-main `ToCompPoly/{Multilinear,WeightedCube,TableFold,EqBatch,…}` | `evalMle_eq_sum`, `cubeSplit`, `weightedCubeSum_lowCoords`, `evalMle_append_eq_bindHighs`, … | ≈ 3k | G | copy | only `CMlPolynomialEval` from CompPoly |
| LV-main `ToCompPoly/Interpolation.lean` | `interpolateAt_eval`, `card_interpolateAt_eq_le` (two interpolants of degree `< N` agree on ≤ N−1 points). Mathlib-only | 129 | G | copy | none |
| CP `Multilinear/*` | `CMlPolynomial`, `CMlPolynomialEval` (computable multilinear polynomials) | 1,187 (`Basic`) | G | copy | — |
| AL (pin) `Data/MvPolynomial/Multilinear.lean`, `SchwartzZippelCounting.lean`; `Sumcheck/Interaction` | `eqPolynomial`, `MLE`, `MLE_eval_zeroOne`, `schwartz_zippel_counting` (noncomputable, proved). `Sumcheck.Interaction.MultivariateRound.execute_soundness` (plain soundness, `count·deg/|F|`, sorry-free, closure about 32k lines plus VCVio). The legacy `Sumcheck/Spec` RBR theorems are `sorry`, and its verifier is wrong at the pin (fixed by ArkLib #1244) | 426 + … | G, ROM-fw | copy small pieces | SR's `Sumcheck` already covers this; the ArkLib framework is not worth copying |
| AL `main` `RingSwitching/Packing/ProductSumcheck` | `ProductSumcheck.rbrKnowledgeSoundnessWorstCase`: `Σ A(b)·p(b)` to `p(r)`, 2/|C| per round, field-generic | 956 | G, ROM-fw (Lean v4.35, newer VCVio) | template | the best template for lincheck-shaped steps. No field-generic zerocheck, lincheck, GKR or Spartan soundness exists in ArkLib (Hachi's are over `ZMod q`) |

### 2.4 Ring switching

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| SR `RingSwitch.lean` (leanerVM-derived `frobMap`) | `frobMap_eq_sum`, `stage_bad_le_one` (each Frobenius stage has ≤ 1 bad `f_p`), **`ring_inj`** (a nonzero `δ ∈ E^n` has some `Σ x^i δ_i^(2^k) ≠ 0`, `k < n`; hypotheses: distinct conjugates of `x`, `a^(2^n) = a` on K, `{1, y, y²}` spans E over K, the Frobenius-twisted bases), `ring_complete`, `ring_final`, `weight_mle` | 321 code | G (K ⊂ E, char 2) | own | `ring_inj` assumes a degree-3 extension (`1, y, y²`). For GF(2^64) ⊂ GF(2^128) it is re-proved with `{1, y}`, or for the 1-bit-packed Flock route over GF(2) ⊂ GF(2^128) as leanerVM's `ringSwitch_injective` |
| SR `RingSwitchField.lean` | `ring_inj_EF`: every hypothesis discharged at `F`, `EF` | 45 code | B64 | own | redone at the new field |
| LV-main `ToArkLib/Flock/FrobeniusMap.lean`, `RingSwitch.lean`, `Protocol/FlockFields.lean` | `card_frob_root_le_one`, `card_stage_zero_le_one`. `pair_ringWeight`, `pair_ringWeight_eq_ringTarget`, `ringSwitchComplete`. `ringSwitch_injective` (δ : Fin 64 → E), `fixedWeights_independent`, `limbs_eq_zero_of_frob` | 163 + 280 + 484 | G / B64 | copy | `FlockFields` is re-proved for the new E |
| AL pin `ProofSystem/RingSwitching/*`; AL `main` (#1256 … #1325) | At the pin: `RingSwitching/Packing` is `sorry` (14 tainted). Proved: `Transport/Eval.lean` `evalAt`, `eq_of_evalAt_eq` (86 lines, Mathlib-only), `Transport/Coeffs.lean` `embedCoeffs_eval`. On `main`: **`RingSwitching.Packing.RingSwitch.rbrKnowledgeSoundnessWorstCase`** (DP24, cites Flock), hypotheses `[NoZeroDivisors C] [Fintype C]`, `pc.Functional`, injective `algebraMap`, error `bat.error + m·2/|C|`, sorry-free | ≈ 5.1k; closure ≈ 27.5k + VCVio | G, ROM-fw | template | Lean v4.35 and a newer VCVio; the probability statements are restated over counting. SR's `ring_inj` route is lighter |

### 2.5 Proximity gaps and correlated agreement

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| SR `Proximity.lean` | Over any linear code `C ⊆ E^ι` with `MinDist C d`: **`far_bad_le`** (AHIV22, counting form; if `U` is not `e`-close with **`3e < d`** and `d < |E|`, at most `d·|E|^(m−1)` of the `r` make `Σ r_i U_i` `e`-close), `far_bad_card` ((e+1)·|E|^(m−1)), `line_close`, `exists_far_comb`, **`close_unique`** (`2e < d`), `close_in_K`, `miss_le` | 274 code | G | own | the interleaved-code proximity for the Ligero-style first round at one third of the distance. Ligerito/WHIR folding needs the half-distance MCA (G2) |
| LV-main `Whir/Lanes.lean`, `Whir/Exact.lean` | Interfaces in counting form: `Cl κ R a m F V`, `McaBad`, `McaBound κ R a N := ∀ F, Nat.card {c // McaBad …} ≤ N`, `ListBound`. `lift_fold`, `card_fold_bad_le`. Inhabitants: **`listBound_unique (ha : 2^κ + 2^(κ+R) ≤ 2a) : ListBound κ R a m 1`**, `listBound_exact`, `mcaBound_exact` (exact agreement only) | 245 + 111 | K | copy | the UD inhabitant of `McaBound` is the missing piece |
| LV-stack `ToArkLib/McaJohnson.lean`, `Whir/Johnson.lean` (#130) | `McaJohnson` (Johnson-regime MCA as an interface), `mcaJohnson_comparisonEstimate` from ArkLib's proved `mcaError_affineLine_johnson_le`, `mcaError_foldLine_eq_affineLine` (any field), `natCard_isMCA_le_of_mcaError_le`, `mcaBound_of_mcaJohnson` | 142 + 532 | G / ROM-fw | design template | the pattern for turning an `mcaError` bound into `McaBound`; FR-D3 excludes the Johnson regime |
| AL `ProximityGap/BCIKS20/{AffineLines/UniqueDecoding,EpsCa}.lean` | **`RS_correlatedAgreement_affineLines_uniqueDecodingRegime`**: for δ ≤ the relative UD radius, correlated agreement for affine lines with ε = n/|F|. **`rs_epsCa_le_of_le_relUDR`**, **`rs_mcaError_le_of_le_relUDR`** (0 < δ ≤ UD radius: ε_mca of the affine-line generator ≤ n/|F|). Sorry-free, not in `axiom_baseline.json` (checked). The list-decoding `RS_correlatedAgreement_affineLines` is `sorry` | 51 + 173; closure ≈ 42–45k (ArkLib 13–16k, CompPoly 10.7k, VCVio 5.6k, PolyFun 6.9k) | G (any injective domain) | copy | **closes most of G2**. Restate over counting (VCVio's `Pr{…}` notation is a `syntax`/`macro` the source rule refuses). n/|F| at `n ≈ 2^20`–`2^29`, `|F| = 2^128` is `2^-108`…`2^-99`, above `errorCap`, so GF(2^256) challenges or the BCHKS25 form below are needed (T) |
| AL `ProximityGap/CapacityBounds/UniqueDecoding.lean` (+ `UniqueDecoding/Internal.lean`) | **`rs_epsCa_le_in_unique_decoding_range`** (BCHKS25 Thm 1.3): for `d_min/(3n) ≤ δ ≤ (1−ρ)/2 − 1/n`, `δ < δ_int`, `epsCa ≤ max((1−ρ−δ)/(δ(1−ρ−2δ)|F|), δ_int/((δ_int−δ)|F|))`. **No factor n.** Proved (the `EpsCa.lean` docstring calling it an external admit is stale) | 136 + 1,321 | G | copy | the n-free UD bound: the route to ≤ 2^-120 over GF(2^128). It is correlated agreement for lines; the mutual form is via `mcaError_le_epsCa_of_pos_of_two_mul_lt_dist` (`ProximityGap/Errors.lean`) |
| AL `ProximityGap/DG25/{Basic,MainResults,ReedSolomon}.lean` | `affine_gaps_lifted_to_interleaved_codes` (DG25 Thm 3.1), `interleaved_affine_gaps_imply_tensor_gaps` (AER24 Thm 3.6), **`reedSolomon_multilinearCorrelatedAgreement`** (DG25 Cor 3.7: δ ≤ UD radius, if Pr over r ∈ F^ϑ that `r ⨂ u` is δ-close exceeds `ϑ·n/|F|` then u has joint agreement). Stated with alphabet = scalar field | 226 + … | G | copy | the Ligerito/Basefold tensor-fold step in the UD regime (correlated, not mutual) |
| AL `ReedSolomon/MutualCorrelatedAgreement/HalfGap/Line.lean`, `ProximityGenerator/BinaryTensorFold{Agreement,Probability}.lean` | `exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le` (agreement ≥ k + n/2: ≤ 2n exceptional challenges, i.e. δ ≤ 1/2 − ρ). `TensorMCA.tensorFoldBad_card_le` (≤ h·e·|F|^(h−1) bad tuples), `tensorFoldBad_probability_le` (h·e/|F|), assuming `FullSetLevelWitness` | 373 + 592 + …; HalfGap closure 11.6k (no VCVio) | G | copy | gives a sorry-free **mutual** CA bound `h·2n/|F|` for the binary fold at δ ≤ 1/2 − ρ. The glue to `UniformExactPowerAgreement` is not in-tree. Mutual CA up to (1−ρ)/2 (BCHKS25 half-distance MCA) is still absent: G2 narrowed |
| AL `ProximityGap/AHIV22.lean` | `e_le_dist_over_3`, `prob_of_bad_pts` (e < d/3; interleaved word far gives row-span e-close with prob ≤ d/|F|) | — | G | — | SR's `far_bad_le` already re-proves this without ArkLib |

### 2.6 Ligerito / WHIR / FRI folding soundness

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| LV-main `Whir/{Open,OpenSound,Level,LevelSound,FoldSound,BoundarySound,FinalSound,Counting,Glue,Stage,Word}.lean` | `whirOpen_rbrSoundness (L) (ps : L.Pars) : Component.Security (whirOpen sh κ L) (relOpen …) Set.univ (openErr L ps)`. Counting cores: `card_fold_challenge_le`, `card_agree_folded_lt` (query term `((a−1)/n)^t`), `card_ood_step_le`, `card_positions_bad_le`, `card_batch_bad_le`, `card_ood_bad_le`, `positions_err_eq`. Generic over a `Ladder` of levels with per-level `Par` | ≈ 2.8k | K, ROM-fw | copy the counting, restate the security | with UD `Par` (L = 1, a UD `McaBound`) the theorem applies unchanged: the OOD term `C(L,2)/|E|` is 0. Ligerito differs from WHIR (no OOD, no shift queries; sumcheck-folded); the per-level counting lemmas are the reusable part |
| LV-stack `Whir/Deployed*.lean`, `Parameters/Whir.lean` | the deployed ladder and its budget (`openErr_le_budget`); query rounds reach 2^-111 without grinding, 2^-128 with 17-bit grinding | 184 + 239 + 334 | B64 | no | new parameter tables at GF(2^128), UD, ≤ 2^-120 per round (work package T) |
| LV-stack `ListBinding*.lean`, `ToArkLib/Relist.lean` | `listBinding_compile`, `listBinding_rbrKnowledgeSoundness`, `commitPick`, `Component.Front.relist` (error × L) | 623 + 242 + 312 + 339 | ROM-fw | template | at L = 1 the relisting is the identity |
| SR `Ligero.lean`, `PCSBounds.lean`, `SoundnessPCS.lean` | the Ligero PCS: `verify1`/`verify2`, `colCheck_iff`. **`r0_answers`** (far mode, ≤ 2^-169), **`decode_exists`/`decode_unique`** (close mode, the decoded message matrix exists and is unique, entries in F), `far_Dset_card`, `close_Dset_card`, `accept_not_mem`, **`r7_far`/`r7_close`** (`t = 260` queries miss D) | 392 + 109 + 560 code | B64 | own | the query-phase counting (`r7_*`, through `card_idx_fiber`) and the far/close case split are the template for each Ligerito level's query phase |
| AL pin `ProofSystem/{Fri,BatchedFri,Stir,Binius/*}` | **No sorry-free protocol soundness at the pin**: FRI relations are `:= sorry`; `fri_soundness`, `stir_rbr_soundness` are `sorry`; Binius `BinaryBasefold`/`FRIBinius` RBR theorems are tainted (54 declarations). WHIR's `folding_preserves_distance` (Lemma 4.9) is tainted (in `axiom_baseline.json`, checked). Proved fragments: `fold_advances_evaluation_poly` (Binius Lemma 4.13), STIR `out_of_dom_smpl_1/2`, `combine_theorem` | — | — | — | — |
| AL `main` (#1326 from PR #383, still open, +35.6k) | Binary Basefold / FRI-Binius: `fullOracleVerifier_rbrKnowledgeSoundnessWorstCase`, `fullRbrKnowledgeError_sum_le_concrete` (≤ 2ℓ/|L| + 2^(ℓ+𝓡)/|L| + (1/2 + 1/(2·2^𝓡))^γ, **unique decoding**), `FRIBinius.RingSwitch.fullVerifier_rbrKnowledgeSoundnessWorstCase`. Over 𝔽q = GF(2) ⊂ L, any finite L (so GF(2^128)). Extractor existential, not a cost-bounded function | closure ≈ 68.6k ArkLib + AdditiveNTT + VCVio + PolyFun | G, ROM-fw | template | the closest proved relative of a UD binary-field fold-and-query PCS. Too large to copy; its per-round error decomposition is the template. Lean v4.35 / newer VCVio. FRI end-to-end KS (#992, #1327, #1328) needs `NonBinaryField`. **No WHIR or Ligerito protocol anywhere** |

### 2.7 Merkle binding by log replay (ROM)

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| SR `Merkle.lean` | Leaves `[H(0x00‖col)]₃₁`, nodes `[H(0x01‖λₗ‖λᵣ)]₃₁`. **`path_complete`**, `tree_of_log`, **`open_binding`** (`¬ Collision L` and an accepting `verify` on `L` give `colL L w root ℓ c = some col`), **`colL_prefix`** (under `¬ Hit`, a column under a label from a prefix is read off that prefix), `colL_append` | 546 code | G (any oracle, contract `OProg`) | own | single-path openings. Ligerito opens many positions per level: per-path is enough; pruned (octopus) openings are an optimisation |
| SR `SoundnessLog.lean` | **`bad_step_le`**: on a log without bad events, ≤ `|L|·(3·2^8+1)+1` of the `2^256` answers make it bad (31-byte labels); `bad_step_frac` at `logCap`. The transcript forest (`predIdx`, `back`), `fresh_leaf`, `frontier_append`, **`extCount_split`** (martingale step of a multi-answer round), chains (`Matches`, `IsChain`, `chains_append`) | 599 code | G in the oracle; transcript shape in `Matches` | own | `Matches`/`shape κ` are SR's §6.2 shape; parameterise by the new protocol's shape |
| LV-stack `ToVCVio/MerkleLog.lean` (#128), `Protocol/MerkleBinding.lean` | **`binding_of_log`**: under a consistent log with no collision and no fresh hit, an accepted pruned walk's payloads equal `positions.map (extractLeaf …)`, deterministically. `extractLeaf_determined`, `extractLeaves` (one HashMap pass) | 622 + 362 | G (any hash function or log) | copy | re-type VCVio's `QueryLog` as a plain list. Copy only the `NodeAlgebra`/`fold`/`prunedRoot` half of `ToVCVio/Merkle.lean` (676), without PolyFun's `_hom` lemmas |
| LV-stack `ToVCVio/{QueryLog,HashChain}.lean` | `history_determined (¬ HasCollision log)`, `history_take_of_noCollision_noHit`, `step_of_history`. Mathlib-only | 336 + 590 | G | copy | none |
| VC `CryptoFoundations/MerkleTree/**`, `ToMathlib/Data/IndexedBinaryTree/Basic.lean` | Pure layer (≈ 1.3–1.9k lines, Mathlib-only): `buildMerkleTreeWithHash`, `getPutativeRootWithHash`, `generateProof`, **`getPutativeRootWithHash_binding_collision`** (computable `findCollision`), `hashed_binding`. ROM layer: `extractability_rom_bound` (≈ qb²/(2|α|)), `anyCheckpointDisagreement_rom_bound_of_prefixQueryBound`. Deterministic adversaries, no extractor cost | 14.8k (55 files); ROM closure 41–48k | G / ROM-fw | copy pure layer only | SR's `open_binding` and LV's `binding_of_log` already serve; ≈ 45 of the closure's VCVio files trip the source rule's word scan |

### 2.8 The random-oracle potential (`KState`)

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| Core `Contract/Security.lean` | `KState R V E ε` (`μ`, `empty`, `step`, `final`), `KS`, `CompleteWithError`, `errorCap = 2^-120`, `logCap = 2^96`, `completenessCap = 2^-40` | 157 (33 code) | — | contract | — |
| Core `Library/Security.lean` | `KState.ofBool`, `KState.zero`, `KState.mono`, **`step_of_hits`** (a potential rising by ≤ 1 only on a set `T` of ≤ `ε·2^256` answers satisfies `step`), `final_unguarded`, `step_unstopped`, `one_le_of_jump`, `no_kstate_of_empty`, `acceptAll_kstate_iff` | 166 code | G | yes | — |
| Core `Library/PaperTheorem.lean`, `Compose.lean`, `Completeness.lean` | `paper` (Pr ≤ `n·ε` for a lazily sampled oracle), `compose`/`walk` (the tree composition: leaf starts, a BLAKE2s collision, or a forgery), `complete_withError_zero`, `failProb_eq_prob` | 110 + 201 + 61 code | G | yes | — |
| SR `SoundnessKSBase.lean` Part A, `SoundnessDefs.lean` Part A | **`muG_step`**: for any doom predicate `D` and per-chain charge `φ`, the potential `μ L = [Bad ∨ Esc] + Σ_{chains on the frontier} φ` satisfies `step` from one local inequality `hloc` (a chain plus one fresh query) and `hseed`, with bad-event term `(2^96·769+1)/2^256`. `muG_step_of` reduces `hloc` to per-position facts (absorb rows keep doom; a round's escape count) | 1,651 + 258 code (Part A is the generic half) | G in `D`, `φ`; tied to SR's `Matches`/`shape`/`squeezeQ` | own | the main template for the new potential. Generalise `Matches` to a protocol shape parameter, then add one per-round lemma per Flock/Ligerito round |
| SR `SoundnessKS`, `SoundnessFinal`, `SoundnessChain`, `SoundnessKState` | `mu_step_chain`, **`runLog_chain`** (an accepted SNARK run on a log without bad events is a complete chain), `accept_not_doomed`, `leaf_final`, `kstate vk`, `ks vk` | 842 + 217 + 1,100 + 23 code | B64 / SR shape | own | `runLog_chain` (blocks `sqBlock`/`rdBlock`, `chain_of_linked`) is the template for the new verifier's transcript |
| LV-stack `ToVCVio/ChargedInvariant.lean`, `RandomOracleBound.lean`, `HashMisbehaves.lean`, `Core.lean`, `Headline.lean` | `potential_le_expected_charge`, `prEvent_bind_le_of_potential`, `misbehaves_rom` (Pr[HashMisbehaves] ≤ `niError ε V Q = (Q+V)·ε + (Q+V)(4(Q+V)+8)/2^256`), `core` (deterministic: accept ∧ ¬extract ⇒ collision ∨ hit ∨ flip), `verify_knowledgeSound_rom`. **Selective** (statement fixed before the adversary) | 830 + 583 + 297 + 354 + 236 | ROM-fw (VCVio) | template | the contract's `KState` replaces this framework. `core`'s case split (collision, hit, flip) is the shape of the new `final` proof |

### 2.9 Fiat–Shamir transcript

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| SR `Transcript.lean`, `Oracle.lean` | `seed`/`absorb`/`squeeze` as contract queries (`0x10`/`0x20`/`0x30` tags; the statement is in the seed, C15). **`card_chE_fiber`** (each `EF` value has exactly `2^64` answers), **`card_idx_fiber`** (tuples of indices are exactly uniform), `card_fiber_dec24` (any bijective decoder of 24 bytes), `pred_unique_lt`. Lawful `Monad OProg`, `runLog_eq_some_iff` (the log view) | 279 + 167 code | G except `chE` | own | `chE` reads 24 bytes into GF(2^192). GF(2^128) reads 16 bytes (`2^128` answers per value) and GF(2^256) all 32 (exactly one answer per value); generalise `card_fiber_dec24` to `n` bytes |
| SR `Queries.lean` | `AtMost n p` (≤ n queries on every answer path), `AtMost.runSeq_length`, `AtMost.queries_length`, closure lemmas | 66 code | G | own | none |
| LV-stack `Transcript.lean`, `Proof.lean` (#125, #126) | leanVM's duplex (`observe`, `sample`, `checkPow`, `grind`), the proof reader/writer monads | 332 + 707 | B64 | template | grinding (`checkPow`) is the model for FR-D3's proof-of-work rounds |
| AL / VC | ArkLib `FiatShamir/Basic`, `DuplexSponge` are `sorry` scaffolds, `BCS/Basic` a stub; VCVio's Fiat–Shamir covers sigma protocols only. At the pin, RBR KS ⇒ KS is `sorry` (`Implications.lean`) and `rbrSoundness_implies_soundness` is false as stated (ArkLib PR #1245). On `main`: `GuardedForm.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWorstCaseWith` (#1349), `StateRestoration.stateRestoration_knowledge_soundness` ((Q + rounds)·ε) | — | ROM-fw | template | nothing to copy; the contract's `KState` with SR's transcript is the route |

### 2.10 BLAKE2s R1CS circuit

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| SR `Blake2sCircuit`, `Blake2sWords`, `Blake2sCompress` (leanerVM `95957214`) | Product-gate circuits, `R1CS (Az)∘(Bz) = z`. Word gadgets `sound_addW`, `sound_add3W`, gate counts `ok_addW`, `ok_add3W`. **`blake2s_sound`** against the contract's `compress` | 450 + 630 + 463 code | G (comm ring char 2) | own | reusable as is for the leaf chain, the WOTS chains and the trace digest |
| SR `Blake2sR1CS`, `Blake2sGeneric`, `Blake2sWalk`, `Blake2sWitness` | **`block_sound`**/`block_complete` (one chain step as a 2^14 block), `not_holds_flip`, `sim_compressW` (the generic gadget simulation), **`walk_eq_sum`** (the verifier's `Ã0`, `B̃0` in `O(|circuit|)`), `fastTrace_eq` | 324 + 337 + 180 + 215 code | G | own | the walk is the lincheck evaluator a Flock verifier needs |
| SR `Chain*.lean` | `chain_sound`, `chain_complete` (the chain R1CS on `2^(15+κ)` rows), `shift_mle`, `matrix_mle_eq`, `col_chainA` | ≈ 2k code | G char 2 | own | the leaf relation; reusable |
| LV-stack `Protocol/Blake2sCircuit.lean`, `Flock/{Circuit,Words,Builder}` (`244039df`) | generalised over any carrier (`Lin`/`Lin.Hom`, `blake2sGates_map`, `natural_*`). `Flock/CircuitFast.lean`, `Semantics/Blake2sFast.lean` use `@[csimp]` | +168/−78 etc. | G | copy | the carrier-generic form is useful for evaluating the circuit over E inside a node circuit |
| AL / VC / CP / leanVM `formal/` | No BLAKE2s, BLAKE2 or BLAKE3 anywhere. VCVio `HashSig/SLHDSA/Concrete/{Sha2,Keccak}.lean` are executable but unproved; `VCVio/Extern/Hashing.lean` is `@[extern] opaque` | — | — | — | SR's circuit is the only one |

### 2.11 Decoding and the extractor

| Source | Statement / content | Lines | Gen. | Allowlist | Adaptation |
|---|---|---|---|---|---|
| CP `Univariate/ReedSolomon/{GaoDecoder,GaoCorrectness,GaoNTT}` | **Gao's unique decoder**, any field, any distinct points (§3) | 75 + 341 + 153; closure 8,147 lines outside the allowlist | G | copy | §3 |
| CP `Bivariate/GuruswamiSudan/`, `Univariate/Roots/` | GS list decoding; root finding including Shoup char-2 | 16,765 (52 files); 13,073 | G | copy | not needed under FR-D3 (UD) |
| LV-stack `Whir/Decode.lean`, `DecodeNtt.lean`, `ToCompPoly/LinearSolve.lean`, `RandomOracleGame.lean` (#133–#135) | `ListDecoder κ R a ℓ` (`decode`, `mem_iff`, `nodup`), `ListDecoder.bruteForce` (exponential), `exactNtt`, `gaussSolve_sound`. **`extract`**: a computable Lean function that reads the level-0 word off the log (`extractAllRows`) and decodes. **Not step-counted, no cost bound.** leanerVM issue #157: off codewords it never returns at deployed sizes | 482 + 114 + 155 + 286 | K | template | the extractor's shape (read rows off the log, then decode, then pick). A UD `ListDecoder` from Gao, through `encode_eq_of_agree`, is #157's step 1 |
| SR (no decoder) | SR's extractor is the library's copy extractor: leaves carry `s` in clear. `decode_exists`/`decode_unique` prove a decoded matrix exists (classically); nothing computes it | — | — | — | the recursive node needs a real decoder (G1) |
| Core `Controls/LogScan.lean` | `scan_computes : Computes scan findE (16·t)`: a 106-statement program that finds a log entry by its answer | 399 | — | yes | the pattern for reading Merkle preimages off the tape |
| AL `CodingTheory/BerlekampWelch/*`, `Erasure.lean` | `decoder_eq_some`, `hammingDist_le_of_decoder_eq_some`; the decoder is noncomputable. `eq_of_consistent_with_erased` | — | G | copy (spec) | spec-side alternatives to Gao; not executable |

### 2.12 Programs for the contract's word machine

See §6. Nothing outside the core touches `XProg`: leanerVM, CompPoly and ArkLib have no step-counted
programs (leanerVM's only fuel is leanISA's executor and grinding, LV report §11).

---

## 3. CompPoly in depth: decoders and binary fields (user request, 2026-10-27)

Read at the core's pin `572f997` (`recursion.fast-v4/.lake/pkgs-local/CompPoly`, Apache-2.0) and at
upstream `main` `1cb8f5c` (clone in `logs/ref/CompPoly`). The pin has **no `sorry`** in the
directories below (grep), consistent with leanerVM issue #157's "empty axiom baseline". Every module
uses the Lean module system (`module`, `public import`, `@[expose] public section`). SR's copies strip
these annotations (`SpartanSromBlake2sCircuit` header).

### 3.1 leanerVM issue #157 (open)

"protocol: the extractor is efficient only on codewords; list decoding with CompPoly's Gao and
Guruswami–Sudan decoders". leanerVM's `extract` (#135) decodes the level-0 word with `nttFirst`
over `bruteForce`. It is exact on codewords and does not finish otherwise. One accepted cheat (a
corrupted leaf) makes the extractor run about `2^1019` Gaussian eliminations at the smallest deployed
size. The issue proposes:

1. **Gao first.** Return `[c]` when Gao's candidate `c`, decoded lane by lane, has `agree(c) ≥ a` and
   `agree(c) + a ≥ n + 2^κ`. `mem_iff` then needs only `encode_eq_of_agree`. A second theorem from
   `decode_eq_some` shows the fallback is never reached within the radius.
2. GS, which needs a `BF64` root context and per-level checks.

It notes three things. Both decoders return a polynomial in the **monomial** basis, while leanerVM
encodes in the **novel** basis on a subspace. So the candidate is re-evaluated on the domain, and a
bridge lemma is owed: the novel polynomials span degree `< 2^κ`. Gao's fast interpolant exists
only on multiplicative radix-2 domains, so on a subspace domain the caller supplies the interpolant
and the vanishing polynomial to `decodeFrom`. Gao's partial Euclid is quadratic: about `2^28`
operations per lane at `n = 2^14`, and infeasible at `n = 2^26` (estimates in the issue).

### 3.2 Gao's unique decoder

`CompPoly.ReedSolomon` (`Univariate/ReedSolomon.lean`, 89 lines):

- `Domain F := {a : Array F // a.toList.Nodup}`: **any array of distinct points**, with no
  multiplicative structure;
- `messagePoly`, and `encode D msg`, the evaluations of the message polynomial in the **monomial**
  basis.

`ReedSolomon/GaoDecoder.lean` (75 lines):

- `nodalPoly D = ∏ (X − aᵢ)`;
- `receivedInterpolant D r`, which is `CLagrange.interpolate`, a quadratic Lagrange interpolation;
- `partialGcd k D r = CPolynomial.xgcd (nodalPoly D) (receivedInterpolant D r) ((n+k+1)/2)`;
- `decode k D r : Option (CPolynomial F)`: with `(g, _, v) := partialGcd`, it returns `g / v` when
  `v ∣ g` and `deg (g/v) < k`.

All of these are `def`s, not `noncomputable`, so they compile. They are evaluated in CompPoly's tests
(`tests/CompPolyTests/Univariate/Interpolation.lean`, `#guard ReedSolomon.Gao.decodeNTT 3 D received
== some (messagePoly msg)` on a two-error word). The field requirements are `[Field F] [BEq F]
[LawfulBEq F]`, plus `[DecidableEq F]` for the theorems.

`ReedSolomon/GaoCorrectness.lean` (341 lines). All hypotheses are `[Field F]` and `hkn : k < D.n`.

- **`decode_sound`**: `decode k D r = some f₁ → ∃ msg, messagePoly msg = f₁ ∧ hammingDist r (encode D
  msg) ≤ (D.n − k)/2`.
- **`decode_eq_some`**: `2 * hammingDist r (encode D msg) ≤ D.n − k → decode k D r = some
  (messagePoly msg)`.
- `decode_eq_none`: if `r` is beyond radius `(n−k)/2` of every message, the result is `none`.
- `decode_none_farness`: `none → ∀ msg, D.n − k < 2 * hammingDist r (encode D msg)`.
- **`decode_eq_none_iff`**: `decode k D r = none ↔ ∀ msg, D.n − k < 2 * hammingDist r (encode D msg)`.
- `decode_unique`: two messages within the radius have equal message polynomials.

`ReedSolomon/GaoNTT.lean` (153 lines):

- **`decodeFrom k n g₀ g₁`**: the Euclidean stage on caller-supplied `(g₀, g₁)`;
- `decode_eq_decodeFrom` (by `rfl`);
- `decodeNTT`/`decodePlan` on a multiplicative NTT domain, with `decodeNTT_eq_decode` and
  `decodePlan_eq_decode`. They are not usable on an additive domain.

`NTTEncode.lean` (100 lines) does the same for the multiplicative NTT encoder.

**Over GF(2^128) on an additive subspace.** It works as stated. `Domain` only asks for distinct
points, and every theorem is over an arbitrary `Field`. What is owed:

- the `Field`/`BEq`/`LawfulBEq`/`DecidableEq` instances on the chosen GF(2^128) type;
- the domain as an `Array` of the subspace's points;
- the basis bridge (#157): our code word is `Enc` in the novel basis. Gao decodes the monomial-basis
  polynomial of degree `< k` that agrees with the word, and the two codes are equal as sets of words
  when the novel basis spans degree `< 2^κ` (CompPoly `NovelPolynomialBasis`: `novelPolynomialBasis`,
  `natDegree` facts; leanerVM `natDegree_novelPoly`). Since unique decoding is a statement about
  words, `decode_eq_some` gives the codeword and the novel-basis message follows from it by `inv`
  (the inverse additive NTT) or by `encode_injective`.

**Cost.** Gao is quadratic as written (Lagrange interpolation, schoolbook `CPolynomial` arithmetic,
partial `xgcd`). That cost is irrelevant to the certificate. The extractor that `Computes` checks is
an `XProg`, not this Lean function (§6). Gao's role in the entry is the **specification**: it proves
that a decoded word exists and is unique within the radius, and it serves as the reference for the
machine program (§6.3).

**Allowlist.** It is not on the allowlist at `15dac52`. The closure of `GaoCorrectness` is
20 CompPoly modules, all outside the allowlisted 28, about 8,147 lines:

- `Univariate/{Basic, Raw.*, ToPoly.*, DivisionCorrectness, EuclideanAlgorithm, Lagrange, Linear,
  ReedSolomon}`;
- `Data/{Array,List}.Lemmas`, `ToMathlib/{Order.WithBot, Polynomial.Roots}`.

Two of those modules register `@[csimp]` lemmas: `Univariate/Basic.lean` (`eval₂_eq_eval₂Horner`,
`eval_eq_evalHorner`) and `Univariate/Raw/Proofs.lean` (two more). As untrusted (copied or imported)
code, these fail gate rule 3. A copy drops the `csimp` attribute and keeps the lemmas, which changes
compiled speed only. **Options:**

- (a) copy the 20 modules with provenance, dropping the attributes and the module-system annotations;
- (b) ask the core to add `CompPoly.Univariate.ReedSolomon.GaoCorrectness` to the organiser's roots,
  as it did for BF64/Ext3 (FIXLIST Q2). That is a core pull request, and the pin moves.
- (c) Prove the decoder program correct against a small self-contained specification. Only the
  uniqueness half is needed (`close_unique` in SR already gives it for `2e < d`), so Gao itself
  becomes optional (§6.3).

### 3.3 Guruswami–Sudan and root finding

- **`Bivariate/GuruswamiSudan/`**: 52 files, 16,765 lines; the closure of `CompPoly.Bivariate.GuruswamiSudan`
  is 171 modules, 59,836 lines outside the allowlist.
  - **`gsFilteredCore_sound`**: a candidate in `gsFilteredCore points interpContext rootContext
    params radius` comes from an interpolation `Q` with `ValidInterpolationWitness`,
    `degreeLt p params.messageDegree`, `composeY Q p = 0` and `candidateMismatchCount ≤ radius`.
  - **`gsFilteredCore_complete_of_enough_matches`**: under `∃ Q, ValidInterpolationWitness`,
    `degreeLt p k`, distinct x-coordinates, `weightedDegreeBound < multiplicity · matchingPointCount`
    and `passesCandidateDistance`, the candidate `p` is in the output.
  - The backends are parameters: dense, Lee–O'Sullivan or approximant-basis interpolation;
    Roth–Ruckenstein or Alekhnovich roots.
- **`Univariate/Roots/`**: 13,073 lines.
  - `rootsInFiniteField_sound`/`_complete`/`_spec` behind a `FiniteFieldContext` (q, `a^q = a`) and a
    `LinearFactorProductSplitter`.
  - Splitters: Shoup's small-characteristic trace splitting (`Roots/Shoup`, `shoupSplitLinearFactorsWith_complete`), the
    smooth-subgroup splitter, and Las Vegas Cantor–Zassenhaus with probability bounds.
  - CompPoly's wiki (`docs/wiki/coding-theory.md`, "Gaps") lists **binary-tower root contexts for
    32/64-bit widths as missing**. Root finding is not needed for UD decoding.

FR-D3 (unique decoding) needs neither. They are listed for completeness, and as the route if the
regime is ever relaxed.

### 3.4 CompPoly's binary-field types

| Type | Module(s) | Representation / compiled code | Field proof | Lines | Allowlist |
|---|---|---|---|---|---|
| `BF64` | `Fields/Binary/BF64/{Basic,Impl,Reduce,BaseCertificate,Bytes}` | `BitVec 64` (compiled `Nat` arithmetic); x^64+x^4+x^3+x+1 | Rabin certificate (`irreducible_of_rabin_prime_power`-style, generated, kernel-checked) | ≈ 1.5k | **yes** |
| `BF64.Ext3` (GF(2^192)) | `BF64/Ext3.lean` on `Fields/Extension/*` | `Ext ext3Params` (vector of 3 `BF64`) | `ext3Poly_irreducible` (a cubic with no root), `nat_card_ext3` | 210 + 1.5k | **yes** |
| `Ext P` (generic) | `Fields/Extension/*` | `Vector F d`, computable Karatsuba-free arithmetic; `@[csimp]` in `Extension/Arithmetic` (allowed only because the module is pinned) | `instField` given irreducibility | 1.5k | **yes** |
| `BF128Ghash`, `ConcreteBF128Ghash` (GF(2^128)) | `Fields/Binary/BF128Ghash/*` | `BitVec 128`, `mul = reduce_clMul (clMul a b)` (GHASH polynomial, polynomial basis) | `ghashPoly_irreducible` (Rabin over GF(2), two kernel-checked certificate chains), `instFieldConcreteBF128Ghash`, `BF128Ghash_card` | 3,822 | no (closure: only these 7 files plus allowlisted `Common`, `CanonicalNat`) |
| `ConcreteBTField k` (binary tower, any level) | `Fields/Binary/Tower/{Concrete,Abstract,Support}` | bit vectors, tower multiplication by recursion | `instFieldConcrete`, irreducibility and trace-map facts per level | ≈ 8k | no |
| `FastBT k` (k ≤ 6), **`FastBT128`** (level 7) | `Tower/{FastDefs,Fast}.lean`, `Tower/Fast/Multilinear.lean` | one `UInt64` (k ≤ 6) / **two `UInt64` limbs** (level 7); Karatsuba down the tower with 256-entry byte tables (`mul8Table`, `inv8Table`) | `fieldOfHoms` → `Field BT8 … BT64`, **`Field FastBT128`**, `ringEquiv : FastBT128 ≃+* ConcreteBTField 7`; `toConcrete_evalWithProducts` for `CMlPolynomial FastBT128 n` | 1,442 + 412 + 45 (closure 6,248 outside) | no |
| GF(2^256) | — | `ConcreteBTField 8` only (no fast form) | generic | — | — |
| `Aes` (GF(2^8)) | `Fields/Binary/Aes/*` | byte | certificate | 428 | no |
| Additive NTT, novel basis | `Fields/Binary/AdditiveNTT/*` | executable, generic in L, β | `additiveNTT_correctness` (§2.2) | 5,617 | no |

**Upstream since the pin** (`572f997..1cb8f5c`, 4 commits):

- secp256k1, Goldilocks, CI;
- **the Lean/Mathlib bump to v4.35.0** (#400);
- no change to the binary fields or the decoders except 12 lines of AdditiveNTT for the bump.

Open pull requests that matter:

- **#405, "the additive NTT over a coset, and its inverse"**: +839 lines, Mathlib-only. It adds the
  inverse network and the `W_j` iterates for a Cantor basis. It is the fast subspace interpolation
  that a quasi-linear decoder, or Gao's `decodeFrom` on a subspace, needs.
- #403 (coset Lagrange) and the KoalaBear/NTT performance PRs are not relevant.

Anything taken from the head or from #405 is on Lean v4.35 and must be back-ported to v4.34.1.

---

## 4. Gaps: needed, nothing to reuse

| Id | Gap | Nearest material |
|---|---|---|
| **G1** | **The extractor as an `XProg`, with `Computes`.** It reads the node proof's committed root, then the committed word's Merkle leaves off the log (the log-index sort and binary search within `2^16·t`), then decodes the interleaved RS word (UD) within `2^48 + 2^16·t`. It outputs the children's signed proofs (`decodeWit` format, `outCap = 2^24` words) | Core `LogScan.scan_computes`, `WitnessSending.computes`, `Library/Machine.lean` (§6). Spec side: Gao (§3.2), SR `close_unique`, LV `encode_eq_of_agree`. No compiler, no field macros, no procedures |
| **G2** | **Mutual correlated agreement up to `(1−ρ)/2`** for the folding rounds. Also, every ArkLib UD proximity statement restated over counting, with no VCVio | ArkLib (§2.5): `rs_mcaError_le_of_le_relUDR` (n/|F|), `rs_epsCa_le_in_unique_decoding_range` (BCHKS25, n-free, CA), `reedSolomon_multilinearCorrelatedAgreement` (DG25), half-gap + `tensorFoldBad_probability_le` (MCA at δ ≤ 1/2 − ρ; glue to `UniformExactPowerAgreement` missing). LV `McaBound`, `mcaBound_of_mcaJohnson` pattern |
| **G11** | **A Ligerito (or WHIR) protocol with proved soundness.** None exists anywhere: not at the ArkLib pin, not on ArkLib `main`, not in any PR. The closest proved relative is ArkLib `main`'s Binary Basefold/FRI-Binius UD RBR KS (#1326, Lean v4.35) | ArkLib `main` Binary Basefold (template); LV WHIR counting core |
| **G3** | **The Ligerito UD instance in `KState` form.** The per-level fold, query and sumcheck-fold rounds as doom predicates with counting bounds ≤ 2^-120, the shape of the transcript (`Matches`), and `runLog_chain` for the new verifier | LV `Whir/*Sound` counting lemmas; SR `muG_step`, `runLog_chain`, `r7_*` |
| **G4** | **GF(2^256)** with fast arithmetic and a field proof (if T's per-round table needs 256-bit challenges) | CP `Ext` over a fast GF(2^128) (a quadratic), CP `ConcreteBTField 8`, LV `ExtensionFast` pattern |
| **G5** | **The node circuit**: the child verifier's arithmetic, the BLAKE2s trace digest of the child's trace, one WOTS verification, and **circuit correctness** (`R1CS_node(c, c₁, c₂, z) → children accepted`) | SR BLAKE2s circuit and `chain_sound`; the walk (`walk_eq_sum`); nothing for a verifier circuit |
| **G6** | **The novel-to-monomial basis bridge** and decoding on a subspace domain | CP `NovelPolynomialBasis`, CP #405 inverse, LV `inv`/`fwd_inv`, `natDegree_novelPoly` |
| **G7** | **Univariate skip, lincheck and the Flock zerocheck in `KState` form** (the algebra exists; the potential-step lemmas do not) | LV `Flock/Tables`, `flockError`; SR `SoundnessSpartan` table |
| **G8** | **Grinding / proof-of-work rounds** as potential events (FR-D3) | Contract header (a leading-zero test on a fresh answer is an ordinary potential event); LV `checkPow` (VCVio) |
| **G9** | **A fast-twin GF(2^128) proved equal to the chosen reference field** without `csimp` (unless `FastBT128` is chosen) | SR `FieldBaseCorrect` pattern; LV `clmul64`/`reduceWords` |
| **G10** | **A UD `ListDecoder`-style decoder spec with an efficient path off codewords** (leanerVM #157 step 1, generalised) | CP Gao; LV `exactNtt` |
| — | Logup, FRI, an adaptive KS statement, a generic Fiat–Shamir compiler | absent everywhere (LV report); none is required by the plan |

---

## 5. The allowlist and the copying rules

**What an entry may import** (`AGENTS.md` §6, gate rules 6–8, `harness/org-setup.sh`). Only the import
closure of the organiser's roots at the pin:

```
ROOTS=Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls,
      CompPoly.Fields.Binary.BF64.Ext3,CompPoly.Fields.Binary.BF64.Bytes
```

The rest is the entry's own modules. `org-setup.sh` writes the closure to `ORG/.lake/rf/allowlist.txt`.
CompPoly's part is 28 modules:

- `Data/{Bytes.*, Classes.*, Fin.BigOperators, Nat.Bitwise, Polynomial.{Frobenius,Rabin,RabinCertificate},
  RingTheory.CanonicalEuclideanDomain}`;
- `Fields/Binary/{BF64.*, Common, Common.Arithmetic}`;
- `Fields/Extension/*`;
- `ToMathlib/Polynomial/Irreducible`.

So the generic `Ext P` extension framework and the Rabin certificate machinery **are** importable.
`BF128Ghash`, `Tower`, `AdditiveNTT`, `Multilinear`, `Univariate/*` (Gao), ArkLib, VCVio, PolyFun and
leanerVM **are not**.

**What "outside the closure" means mechanically.** The gate classifies every module that is neither
in the olean manifest as trusted nor pinned as **untrusted**, that is, checked as the entry's own code
(`Gate.lean`, `GateCtx.untrusted`). A direct import of an off-list module of a pinned package is
therefore not rejected for being off the list. Instead, the whole of it is subject to:

- rules 2–3: no `unsafe`/`partial`/`opaque`; no `csimp`, `implemented_by`, `extern`, `init`
  (including `initialize` and `register_*`), `cpass` or `computed_field`;
- rule 7: no definition that refers to `Lean.Elab`/`Lean.Meta`/`Lean.Compiler` internals;
- rule 8, on the badge root.

In practice:

- **VCVio** has `initialize`/`register_*` in 15 files, `elab`/`macro`/`syntax` in 15 and
  `csimp`/`implemented_by`/`extern` in 12.
- **ArkLib** has 1, 7 and 2.
- **CompPoly** has 1, 3 and 8. In Gao's closure the culprits are `Univariate/Basic.lean` and
  `Raw/Proofs.lean` (`csimp`).

So ArkLib and VCVio code cannot be imported, and CompPoly modules only where their closure is clean.

**VCVio's probability notation blocks verbatim copies of ArkLib statements.** Nearly every ArkLib
probability statement is written as `Pr{let x ← $ᵗ S}[…]` with `SampleableType`. That notation is a
`syntax`/`macro` with `meta import Lean` (`VCVio/EvalDist/ProbabilityNotation.lean:27`,
`EvalDist/Defs/Basic.lean:114`), which the source rule refuses. About 45 of the 183 VCVio files in the
Merkle-plus-birthday closure trip the rule's word scan, which includes comments. So:

- ArkLib statements are restated over counting (`card filter / card`), as SR's `far_bad_le` is.
- Most ArkLib proofs already reduce to counting (`SampleableType.prEvent_uniformSample_eq_ofReal`),
  so the restatement is mechanical at the statement layer.
- Copied CompPoly files carry commented `#eval` lines (`Data/Nat/Bitwise.lean:203`,
  `Multilinear/Basic.lean`) that must be cleaned.

**`@[csimp]` inside the allowlist.** `CompPoly/Fields/Extension/Arithmetic.lean:355`
(`mul_eq_mulTbl`) is a `csimp` lemma inside the allowed closure, and `Ext3`'s compiled
multiplication depends on it. It is accepted because the module is pinned: the gate reports it as a
note (`tests/gate/GateCompPoly.lean`). An entry may not write one.

**Lean version.** ArkLib `main` (#1329) and CompPoly `main` (#400) are on Lean v4.35.0. ArkLib up to
#1320 is still on v4.34.0, but from #1309 on it uses a VCVio (`afa6593`) that diverges from the
core's `a4232d0`. Anything taken from either `main` is back-ported.
`AGENTS.md` §6 states the CompPoly case ("An import of one is checked as your own code").
`BF128Ghash`, `Tower.Fast` and `AdditiveNTT.*` have no `csimp` in their closures. **Copying** is the
recommended route regardless: the harness builds the entry in a sandbox from the private package
tree, and the source rule (`scripts/source-rule.py`) runs on the entry's sources only.

**How to copy** (the SR precedent, `submissions/spartan-srom/README.md` "Licences and provenance", the
`SpartanSromBlake2sCircuit` header):

- Put the source's licence in the root as `LICENSE-<source>` (SR ships `LICENSE-leanerVM`).
  leanerVM, CompPoly, ArkLib and VCVio are Apache-2.0, so §4(b) applies: each copied file states that
  it was modified.
- Each copied Lean file gets a provenance header: repository URL, commit, source path(s), and a
  list of modifications. The modifications include dropping the module-system annotations, renaming
  the namespace to the entry's prefix, and making the `private` lemmas public where needed.
- Keep third-party copyright lines. In leanerVM: `ToArkLib/KnowledgeAppend.lean` (ArkLib
  Contributors), `ToVCVio/ScalarExpectation.lean` (Devon Tuma, VCVio PR 817),
  `ToCompPoly/{PowerBatching,AmbientStacking}.lean` (Leanth Contributors). `ToClean/ExpressionPolynomial.lean`
  is MIT (zkSecurity) and not needed.
- Module names are fresh and flat in `lean/` with the entry's prefix (`AGENTS.md` §3.3).
- Strip, or rewrite as direct calls:
  - `@[csimp]` lemmas (leanerVM's fast paths, CompPoly `Univariate/Basic`);
  - `#eval`, `#guard`, `elab`, `macro`, `syntax`, `run_cmd`, `initialize`;
  - `import Lean…`/`Qq`, and any of those words in comments (the source rule scans comments);
  - `native_decide`.
- The **budget** matters: SR's 17.9k code lines already cost 5–10 min of kernel time (PLAN FR-R4).
  Copy the minimal closure, e.g. `Tower.Fast`'s 13 modules rather than all of `Tower`.

---

## 6. The core library's machine tooling

### 6.1 What the contract fixes (`Contract/Machine.lean`, `Contract/Extractor.lean`)

- **The machine.**
  - `XOp`: `add sub mul mulhu divu remu and or xor shl shr ltu eq` and **`clmul`, `clmulh`** (the low
    and high words of the 64×64 carry-less product).
  - `XStmt`: `op`, `const`, `load`, `store`, `input`, `out`, `seq`, `ite`, `loop`. It is three-address
    code with no sub-expressions, **no procedures or calls**, and no function-typed field.
  - `XProg = ⟨mem, memPerWord, body⟩`: memory is `mem + memPerWord·t` zeroed words, charged one step
    per word.
  - `XStmt.exec` costs one fuel unit per statement executed (`seq` and `ite` included). `XProg.run p
    input fuel`.
- **The obligation.** `Computes p E fuel`: on every `c`, every `π` with `π.size ≤ proofCap` and every
  log of queries `< 2^64` bytes whose tape fits in `2^64` words, `p.run (extractorInput c π L) (fuel
  t) = some o`, `o.length ≤ outCap = 2^24`, and `decodeWit o = E c π L`.
- **The caps** (`Certificate.cap`): `fuel t ≤ extractorBudget t = 2^48 + 2^16·t` and
  `ext.body.size ≤ progCap = 2^20` statements. The tape is `packBytes c ++ bytesWords π ++ logWords
  L`, and the output is read by `decodeWit`, which is strict.

### 6.2 What the library and controls provide

| Module | Content | Code lines |
|---|---|---|
| `Library/Machine.lean` | `XStmt.Runs I s M o n M' o'` (s runs in exactly `n` steps, whatever follows). One lemma per statement: `runs_op`, `runs_const`, `runs_load`, `runs_store`, `runs_input`, `runs_out`, `runs_seq`, `runs_ite_true`/`false`, `runs_loop_zero`, `runs_loop_step`. Also `exec_mono`, `exec_none_of_le`, `exec_seq`/`out`/`loop_ne`/`loop_eq`, `runs_mono_eq`, `seqs`, **`XProg.run_of_runs`**, `run_lt_mem`, `run_eq`, `getD_toArray` | 112 |
| `Library/Words.lean` | the tape and output formats: `packBytes_length`, `wordByte_packBytes`, `packBytes_wordsBytes`, `unpack_packBytes`, `enc64_inj`. **`witWords`** (the encoder an extractor implements), **`decodeWit_witWords`** (reads it back under `Wit.Fits`), `readWit_witWords`, and the per-reader lemmas (`readTrace_logWords`, `readSig_sigWords`, `readSigned_signedWords`). Linear twins `packFast`, `witWordsF` | 228 |
| `Library/WitnessSending.lean` | `ext : XProg := ⟨5, 0, .seq pre (.loop 2 step)⟩` (21 statements, copies the proof's words), `fuel t = 8t`, **`computes`**, through `pre_exec`, `loop_exec` (the loop by induction with an explicit state `st m i y`), `extractorInput_eq`, `pre_mem`, `ext_run` | 231 |
| `Controls/LogScan.lean` | `scan` (16 memory words, 106 statements): finds the first log entry whose answer is the statement. **`scan_computes : Computes scan findE (16·t)`**, `scan_kat` (the kernel runs it), `scan_fuel_short`, `scan_not_none`. Proof by symbolic execution (`head_exec`, `iter_next`, `iter_found`, `iter_end`, loop lemma `scan_loop`) with the state as an explicit `Array Word` (`st cw p n i x acc y`) | 399 lines |
| `Controls/Machine.lean`, `Controls/Extractor.lean` | KATs of `XOp.eval` (`clmulh (2^64−1)² = 0x5555…`), `count_short` (a `k`-iteration loop needs `> 2k+6` steps), `mem_charged`, `poke_affine`. Negative controls: `toolong_not_computes`, `enum_no_computes` (enumerating `2^128` candidates is excluded), `decodeWit` KATs | 200 + 255 |

### 6.3 What is missing for a decoding extractor, and what it implies

- **The style of every existing proof.** Each proof is hand symbolic execution over a raw
  `Array Word`, with `setIfInBounds` and `getD`. LogScan spends 399 lines on 106 statements. A UD
  decoder for an interleaved code would have:
  - Merkle-leaf lookup;
  - field arithmetic (GF(2^64) multiply: `clmul`, `clmulh` and a reduction by `x^4+x^3+x+1`, about
    ten statements; GF(2^128) about 30–40);
  - an inverse additive NTT, or Euclid's algorithm.

  That is thousands of statements, and at LogScan's density it does not fit the Lean budget (FR-R4).
  Nothing exists for:
  - **(i)** a macro or "assembler" layer: named registers, field-op macros, and loops over arrays
    with a stated invariant;
  - **(ii)** a lemma library: a `Runs` specification per macro, proved once and composed. `runs_seq`
    and `runs_loop_step` are the only combinators;
  - **(iii)** a verified translation from a small first-order Lean IR (straight-line field code and
    counted loops) to `XStmt`, with a simulation theorem and a cost function. Its statement would
    be: if IR program `P` computes `f` with cost `c`, then `compile P` `Runs` to `f`'s output in
    `≤ k·c` steps.

  One of (i)–(iii) is the first deliverable of L-ext (G1).
- **Which direction of decoding must be proved.** `Computes` asks that the program's output
  *denote* `E c π L`. `KState.final` asks that `E` return a witness of `Rel` whenever `μ L < 1` and the
  verifier accepts. If `E` is **defined** as the witness that the program's output denotes (`E c π L
  := decodeWit (output of ext on the tape)`), then:
  - `Computes` reduces to termination within the fuel and the `outCap` bound on **every** tape (no
    functional correctness);
  - `final` needs only that, on the tapes `final` cares about (an accepted node proof under a good
    log), the program's decoder **succeeds**, i.e. the completeness direction (`decode_eq_some`'s
    shape: within radius `(n−k)/2`, it returns the codeword);
  - the farness direction (`decode_eq_none_iff`) is never needed.

  So Gao's Lean decoder is optional. What must be proved of the machine program is one direction
  plus a step bound. This needs checking against `Controls/Extractor.lean`'s intent and the core's
  O-21 notes before the blueprint relies on it.
- **Budget arithmetic** (statement counts, not durations).
  - A node's committed word is about `2^29` symbols (issue #7, F1 §3.3).
  - An additive-NTT-based UD decoder (inverse NTT on a subset, then error location by Euclid or BW on
    syndromes) costs `O(n log n)` to `O(n log² n)` field operations, about `2^34`–`2^38` products.
    At about 10–40 statements per product that is about `2^38`–`2^43` steps, inside the fixed
    `2^48`.
  - A quadratic Gao on `2^29` symbols (`2^58` products) is not.
  - Memory is affine in `t` (`memPerWord`), so the word is held in proportion to the tape.

---

## 7. `spartan-srom` module by module

Classification for GF(2^128): **R** reusable as is (generic); **A** adapt (generic core, but the
instance or a hypothesis is GF(2^64)/GF(2^192)- or Ligero-specific); **N** node or format work for
v4's SROM (rewritten for recursion); **X** replaced (Ligero-specific, or field-specific). Code lines are
`loc.py`'s.

| Module | Code | Class | Note |
|---|---|---|---|
| `Field`, `FieldBase`, `FieldBaseCorrect`, `FieldControls` | 3 + 99 + 812 + 21 | A | GF(2^64) base; kept if GF(2^128) is a tower over it, X if GHASH or `FastBT128` is chosen |
| `FieldExt`, `FieldExtCorrect` | 56 + 359 | X / pattern | GF(2^192); the quadratic analogue follows its proof pattern |
| `MLE`, `MLEControls` | 260 + 51 | R | |
| `Sumcheck` | 310 | R | add the univariate-skip round |
| `RingSwitch` | 321 | A | `ring_inj` assumes a cubic extension (`1, y, y²`) |
| `RingSwitchField` | 45 | X | |
| `RS`, `RSControls` | 313 + 101 | R | the code; add the novel-basis bridge |
| `Proximity` | 274 | A | `3e < d` regime; `close_unique` reusable |
| `PCSBounds`, `Ligero`, `LigeroControls`, `SoundnessPCS`, `SoundnessPCSControls` | 109 + 392 + 28 + 560 + 49 | X | Ligero; the `r7_*` and far/close split are templates |
| `Oracle`, `Queries` | 167 + 66 | R | |
| `SnarkQueries` | 88 | A | re-done per verifier |
| `Merkle` | 546 | R | |
| `Transcript`, `TranscriptControls` | 279 + 83 | A | `chE` and `card_fiber_dec24` parameterised by byte width |
| `SoundnessLog`, `SoundnessLogControls` | 599 + 229 | A | `Matches`/`shape` parameterised |
| `SoundnessDefs`, `SoundnessKSBase` | 258 + 1,651 | A | Part A generic (`muG_step`); Parts B–C are SR's rounds |
| `SoundnessKS`, `SoundnessKSFinal`, `SoundnessKState`, `SoundnessFinal`, `SoundnessChain`, `SoundnessSpartan`, `SoundnessPack` | 842 + 26 + 23 + 217 + 1,100 + 194 + 15 | A / template | per-round doom table and `runLog_chain` for the new protocol |
| `Blake2sCircuit`, `Blake2sWords`, `Blake2sCompress`, `Blake2sGeneric`, `Blake2sR1CS`, `Blake2sWalk`, `Blake2sWitness` | 450 + 630 + 463 + 337 + 324 + 180 + 215 | R | leanerVM-derived; generic char 2 |
| `Chain`, `ChainCols`, `ChainMle`, `ChainSound`, `ChainTables`, `ChainHonest` | 288 + 195 + 486 + 338 + 255 + 117 | R | the leaf relation |
| `ChainInner`, `ChainEval` | 245 + 99 | A | Spartan's evaluators; re-done for lincheck |
| `SpartanProtocol` | 538 | X | Spartan |
| `Verifier`, `VerifierTop`, `Prover`, `Kat`, `Run` | 101 + 216 + 254 + 142 + 43 | X | per protocol |
| `Node`, `NodeBytes`, `NodeControls`, `Decode` | 340 + 180 + 434 + 147 | N | v4 formats; the σ0 bundle is replaced by recursive nodes |
| `Submission`, `Final`, `Controls`, `SpartanSrom`, `Solution` | 145 + 20 + 92 + 64 + 17 | N | assembly; `Submission`'s `Facts` pattern carries over |

Totals: **R** 6,092 code lines, reusable as is. **A** 7,478, which adapt or serve as templates. The
remainder (about 4.3k) is X or N. SR's 47 unchanged v3 modules showed that a port at the pins is cheap
when the statements do not change.
