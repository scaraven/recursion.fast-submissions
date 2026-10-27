# S-C (track L-piop): RESULT

Stage S-C of `flock-recursive`, core part: `FRMLE` (+ `FRMLEControls`), `FRSumcheck`, `FRShift`,
`FRRingSwitch`, `FRSkip`, `FRSpartan`. 2026-10-27, branch `v4/flock-recursive`, uncommitted on top
of `2709159`. **Written against BLUEPRINT revision 3.2** (frozen). Revisions 3 and 3.1 arrived
while the stage ran; `FRShift` was rewritten twice and `FRSkip`/`FRSpartan` were written
directly against 3.1/3.2 (journal). Build tree `logs/fr-build-piop/`. Evidence tags:
**kernel** (theorem name; `logs/S-C/axioms.log` lists 51 of them, each on `propext`,
`Classical.choice`, `Quot.sound` at most) and **measured** (log under `logs/S-C/`).

## 1. What was built

Code lines by the core's `scripts/loc.py`:

| Module | code (total) | Budget (§7) | Content |
|---|---|---|---|
| `FRMLE` | 281 (427) | 300 | spartan-srom's `MLE` (namespace only) plus `mle_sub`, `mle_smul`, `mle_sum`, `mle_eqPt`, `fixLow`, `mle_fixLow` |
| `FRSumcheck` | 444 (648) | 350 | spartan-srom's `Sumcheck` plus `trueSum_bindAll'`, `innerExpr`/`prod_trueSum`/`tbl_ofFn`/`bindT` (moved from SR's `SoundnessSpartan`), `batch_pow_bad_le`, `batch2_bad_le`, `uni_bad_le`, `pair_bad_le` (`α × β`), `seq_bad_le` |
| `FRShift` | 271 (410) | 350 | successor and its extension (`shift_mle`, `shiftPair`); rev. 3.1's P1-D5 argument: `ChainLinks`, residuals, S1/S2 lemmas, collapse rounds, two chains by `1, y` |
| `FRRingSwitch` | 493 (723) | 650 | leanerVM/SR staged Frobenius map, MBP (`weightEval`, `mleEval_weightTable`); `ring_complete`/`ring_final` generalised to any packing basis; **`ring_inj_basis`** (new); the A.7 pack at F (`bitF`, `bitBasis`, `ring_inj_F`, `unpack_boolean`, `pack_unpack`); the doom chain; **`rs1_joint`** |
| `FRSkip` | 513 (667) | 700 | interpolation (leanerVM, on functions); `ζ`, `S`, `Λ`, `skip_bad_le` and Z2's forms; `skipExt`; `PinnedIndep`, `pinned_sound`; A.1's two-level set with the shipped inverse (`pinned_rank`); the negative `rev2Rho_not_pinned` |
| `FRSpartan` | 333 (532) | 450 | prefix sums (`prefixP`), `selWeight_eq`, `selWeight_split`; the block zerocheck (Z1–Z3); the lincheck (L1–L2); `quirky_claim_split`; spartan-srom's sparse Spartan (Lr, E) |
| `FRMLEControls` | 95 (207) | 50 | spartan-srom's controls plus §3 below |
| **total** | **2,430** (3,614) | 2,850 | |

Outside the entry: `probe/fr-piop/gen_skip.py` (independent shift-and-add reference: `ζ`, the
pinned sets, the 128 products, their GF(2) inverse, with the assertion `M · Minv = I`),
`FRSkip.template`, `render.py` (renders the literals into `FRSkip.lean`); outputs
`logs/S-C/gen_skip_{two,one}.out`.

## 2. The §5.2 rows and their lemmas (counts are bad challenges out of `|F|` unless stated)

| Row | Count | Lemma(s) |
|---|---|---|
| Z1 pinned (7) | 0 | `pinned_sound` (needs `PinnedIndep ρ`; `pinned_rank` for A.1's set) on bit-valued residuals (`bzRes_bit`) |
| Z1 free | 1 per coordinate | `zerocheck_bad_le` / `zc_escape_le`; start `bz_start`, end `bz_end`; any number of coordinates jointly: `seq_bad_le`, two per answer: `pair_bad_le` |
| Z2 | 127 | `bz_skip_le` = `zc_skip_bad_le` (zeros on `S`, message on `Λ`) with `bzPoly_natDegree` (≤ 126) and `bzPoly_node`; general form `skip_bad_le`; completeness `zc_skip_complete`, `lagrangeS_eval` |
| Z3 | 3 per round | `round_escape_le` with `bzExpr` (`bzExpr_deg = 3`), `bz_trueSum` (`= P*(λ)`), `bz_final`, `bz_triple_wrong`; `ŵ(r′)` by `selWeight_eq` / `prefixP_eq` |
| L1 | 1 | `lin_alpha_le` (= `batch2_bad_le`) |
| L2 | 2 per round (14 rounds) | `round_escape_le` with `innerExpr`; `lin_trueSum` (`= â* + α b̂*`), `lin_final` (claim `ẑ(r_k, r_blk)`) |
| S1 | 1 per `θ`/`τ` coordinate; 1 for `κ_s` | `shift_sound` (start), `shift_coord_le`, `zerocheck_bad_le`, `shift_kappa_le` |
| S2 | 2 per round (block and collapse) | `shift_round_le` (`shift2Expr`, degree 2), `shift_trueSum` (`= target + D̃(θ,τ) + κ D̃₀(θ)`), `shift_final`, `shW_mle`; collapse `collapse_mle`, `collapse_final` (`innerExpr`), `slotW_mle_aligned`; node: `chainLinks_batch` |
| Lr1–Lr4, E1–E4 | 1 per point coordinate; 3; 2 (κ batching three claims); 2 | spartan-srom's table: `zc_start`, `zc_escape_le`, `zc_end`, `outer_start`, `outer_final`, `triple_wrong`, `batch_escape_le` (`batch_bad_le`: 2), `inner_trueSum`, `inner_final` |
| RS1 (joint, rev. 3.2) | `(7 + J − 1)·|F|^7` of `F^8` | **`rs1_joint`** (start `rs_column` + `rs_start_F`; stages `rsJ_escape_le`; `κ` by `batch_pow_bad_le`); claim weights `ml_claim_split`, `quirky_claim_split` |
| B′ | `J_f − 1` | `batch_pow_bad_le` |

Main statements (all **kernel**), in brief:

- `ring_inj_basis : Fintype.card L = 2^n → GF2Indep b → δ ≠ 0 → ∃ k < n, Σ_i b i * δ i ^ 2^k ≠ 0`
  for any field `L` of characteristic two; `ring_inj_F` is `n = 128`, `b = bitBasis` (A.7).
- `pinned_sound : PinnedIndep ρ → (∀ u, e u = 0 ∨ e u = 1) → e ≠ 0 → fixLow e ρ ≠ 0`;
  `pinned_rank : PinnedIndep pinnedRho` (A.1's two-level set, `pinnedRho_spec`, `pinnedG_spec`).
- `skip_bad_le : P.natDegree ≤ 127 → v ≠ (P at the nodes) → #{l | lagrangeS v l = P.eval l} ≤ 127`.
- `shift_trueSum`: the S2 true sum is `shiftTarget θ τ κ sV hV + D̃(θ, τ) + κ · D̃₀(θ)`, with
  `chainLinks_iff : ChainLinks Out In sV hV ↔ chainD = 0 ∧ chainD0 = 0`.
- `selWeight_eq : mle (eq(r,·) · selOf ivs) r′ = Σ_{(a,b) ∈ ivs} (prefixP b − prefixP a)`.
- `rs1_joint : (∃ j, δ_j ≠ 0) → #{(fs, κ) | Σ_j κ^j T_j = Σ_j κ^j truth_j} ≤ (7 + J') · |F|^7`
  (`J = J' + 1` claims).

## 3. Controls (`FRMLEControls`, `FRSkip`; all **kernel**)

| Definition | Positive | Negative |
|---|---|---|
| `eqTable`, `mleEval`, `bind0`, `eqPts`, sumcheck, `Phi`, `phiTable`, `weightEval`, `bindT`, `Sat` | spartan-srom's (ZMod 7 / ZMod 2 KATs, tightness of `round_bad_le`, `zerocheck_bad_le`, `batch_bad_le`) | spartan-srom's |
| `shiftMle`/`shiftPair` | `shiftPair_pos` (= the defining double sum, `n = 2`) | `shiftPair_neg` (the predecessor relation differs) |
| `ChainLinks`, `chainD` | `chainLinks_pos` (a two-block chain) | `chainLinks_neg` (a broken link) |
| `prefixP`, `ŵ` | `prefixP_pos` | `prefixP_neg`; `selWeight_ne_control` (`ŵ(r′) ≠ eq(r,r′)·Sẽl(r′)`, BP-C-R4-m1) |
| `interpolateAt` | `interpolateAt_pos` (recovers `X²`) | `interpolateAt_neg` |
| `bitBasis` (pack) | `bitBasis_pos` (bit 64 is `y`) | `bitBasis_neg` (`c₁ ‖ c₀` order would give `1`) |
| `GF2Indep`, `ring_inj_F` | `ring_inj_F_pos`, `pinned_rank` | `gf2Indep_neg` (a repeated element) |
| `PinnedIndep` | `pinned_rank` | `rev2Rho_not_pinned` (revision 2's candidate: rank ≤ 64, BP-E-R2-M3 (a)); general `not_pinnedIndep_of_base` |
| `ζ` | `zeta_eq`, `zeta_order` (`ζ^255 = 1`, `ζ^85, ζ^51, ζ^15 ≠ 1`) | (the order checks are the negatives) |
| `BHolds` | `bHolds_pos` | `bHolds_neg`; `bHolds_sel` (off the used blocks nothing is required) |
| `unpack` | `pack_unpack`, `unpack_boolean` | `bitBasis_neg` |

## 4. Build and kernel times (development VM, shared, 32 vCPU)

| Measure | Value | Log |
|---|---|---|
| build of the 7 modules (field modules prebuilt), lake | **57.9 s wall** (FRMLE 5.9, FRSumcheck 6.7, FRShift 6.0, FRRingSwitch 7.6, FRSkip 23, FRSpartan 7.1, FRMLEControls 4.7 s) | `logs/S-C/build.log` |
| source rule | 35 files, 0 findings | (run at the end) |

Per module, `lake env lean --profile`, run one at a time:

| Module | wall | kernel (type checking) | elaboration | import | Log |
|---|---|---|---|---|---|
| `FRMLE` | 6.3 s | 0.53 s | 0.29 s | 2.5 s | `logs/S-C/profile-FRMLE.log` |
| `FRSumcheck` | 6.9 s | 0.38 s | 0.44 s | 2.9 s | `profile-FRSumcheck.log` |
| `FRShift` | 6.9 s | 0.35 s | 0.40 s | 3.4 s | `profile-FRShift.log` |
| `FRRingSwitch` | 8.2 s | 0.60 s | 0.49 s | 3.5 s | `profile-FRRingSwitch.log` |
| `FRSkip` | 25.2 s | **18.7 s** (`pinnedW_eq` 9.8 s, `pinned_cert` 7.1 s) | 0.49 s | 3.7 s | `profile-FRSkip.log` |
| `FRSpartan` | 9.1 s | 0.64 s | 0.58 s | 3.8 s | `profile-FRSpartan.log` |
| `FRMLEControls` | 6.5 s | 0.53 s | 0.27 s | 3.5 s | `profile-FRMLEControls.log` |

`pinned_rank`'s certificate is linear kernel work as BP-E-R2-m7 asks (one pass over the inverse per
row), but the 254 F products of `eqTable` cost 9.8 s in the kernel (≈ 39 ms per product): the
dominant item of this stage.

## 5. Deviations from the blueprint

1. **`FRSkip` (Z2's message form).** The lemmas are stated for leanerVM's form (the verifier
   interpolates zeros on `S` and the message on `Λ`, `zcMsg`); rev. 3.2 §2.3 absorbs
   `P^{ab} ‖ P^z`. `skip_bad_le` covers any reconstruction whose values differ from the honest
   polynomial's on `S ∪ Λ`, so BP-C-M2's `(P^z|_S, P^{ab}|_Λ)` form is one line on top; S-0 should
   say which form `gen` uses.
2. **`FRSkip`: no fast Lagrange form.** `lagrangeS` uses the generic `Π_{j≠i}` weights; the
   subspace identity (all denominators equal to `Π_{v≠0} v`, which makes A.8's `lagrangeS` op cheap)
   is not proved here.
3. **`FRShift`: the collapse weight's closed form is proved only for a slot at an aligned base**
   (`slotW_mle_aligned`: `h_out` at 256…511, `h_in` at 0…255). The chain block's `d` slot at
   520…775 is not 256-aligned; its weight's extension (an "add a constant" MLE) is open
   (question 2).
4. **`FRShift`: tables are slot-indexed** (`Out`, `In` on `s + n` variables); the link to positions
   is the hypothesis `hT` of `collapse_mle` (a slot is read from `z` at `pos σ`).
5. **`FRSpartan`'s layouts are abstract.** The zerocheck works on 64 skip slices of tables on `ℓ`
   variables; the lincheck on positions-low/blocks-high tables with verifier row weights `rw`. The
   identification with the cube layout of A.6 and the quirky row point (`rw(k) =
   L_{k_skip}(λ) · eq(r′_pos, k_hi)`; `skipExt_eval`, `quirky_claim_split` supply the pieces) is
   L-cert's assembly.
6. **`FRSumcheck` is 94 lines over its budget** (444 against 350), since `innerExpr`/`bindT` moved
   in and `seq_bad_le`/`pair_bad_le` serve RS1 and the per-answer accounting. `FRMLEControls` is
   95 against 50. The stage total, 2,430, is under the sum of budgets (2,850).
7. spartan-srom's cubic-extension `ring_inj`, `frob_sums_eq_zero` and `ybasis_of_period` are
   dropped (GF(2) ⊂ F needs the general-basis form). Revision 3's univariate rounds (L3, S3, B3),
   the range-restricted shift and the `sliced` framework written for them were removed when
   rev. 3.1 withdrew them; `uni_bad_le` (generic) remains.

## 6. Open questions

1. **`FR.lean`** (owner: L-cert or the orchestrator) should import `FRMLEControls` (which imports
   every S-C module), so that the controls are built and gated.
2. **The `d` slot's weight** (520…775): the verifier needs `Σ_σ eq(θ, σ) eq(520 + σ, r)` in closed
   form. A carry recursion like `shiftMle`'s gives it in `O(log)`; S-C can add it when S-0 fixes
   the slot layout of the collapse (8 or 10 `θ` coordinates: §2.3 says "θ (10 slot coordinates)").
3. **Z2's message form** (deviation 1), for S-0's `gen`.
4. **`pinned_rank`'s 17 s of kernel time.** If FR-R4′ gets tight: check `eqTable` against
   shipped products with a cheaper multiplication (e.g. a Nat-level carry-less product proved equal
   to `F.mul`), or ship the 128 products with a per-row factorisation check.
5. **`FRPatterns`** is withdrawn; **`FRPubTarget`** (rev. 3.1) was not taken: no room in this
   stage. The verifier's `Ê(r)` and `Sẽl` pieces it needs are the `prefixP`/`selWeight_eq` lemmas
   here.
6. RS1's joint count is over `F^8` (seven stage coefficients, then `κ`). The mapping to the four
   squeeze answers (two F coordinates each, A.2) is L-cert's (`pair_bad_le` and the fiber counts).

## 7. Definition of done (this part of S-C)

| Item | Status |
|---|---|
| every module builds with its controls | yes (`logs/S-C/build.log`); controls §3 |
| every §5.2 row from these modules has its lemma with the exact count | yes, §2 (Z1–Z3, L1–L2, S1–S2, Lr, E, RS1, B′) |
| `FRSkip` parametric in `ρ`; certificate for the normative set | `PinnedIndep ρ` throughout; `pinned_rank` for A.1's two-level set (rev. 3.1 replaced `y^(2^j)`; that set's rank 128 is the Python check `gen_skip.py one`) |
| `FRShift` general in the block count | yes (`n`, `s` parameters) |
| axioms | three at most (`logs/S-C/axioms.log`); no `sorry`, no `native_decide` |
| source rule | 0 findings |

## Fix pass (revision 3.4; review `reviews/S-C-review.md`)

All changes build (`logs/S-C-fix/build.log`: 51.6 s for the 7 modules, **no warnings**); source
rule 0 findings (`logs/S-C-fix/source-rule.log`); 60 declarations on the three axioms at most
(`logs/S-C-fix/axioms.log`). Statement check with S-A's tool (`logs/S-C-fix/Stmts.lean`,
`stmts-before.txt`/`stmts-after.txt`, hygiene suffixes stripped, `stmts.diff`): the only changed
types are the intended ones below; every other public declaration is unchanged.

| Finding | Change |
|---|---|
| S-C-M2 (1) | `bzExpr = w·(ab + z) + W_E` over five tables (`W_E = eq(r,·)·Sel·Ê(λ,·)`); `bz_trueSum` (still `= P*(λ)`), `bz_final` (`ŵ(ρ)(Ã B̃ + Z̃) + Ŵ_E`) and `bz_triple_wrong` restated; new `targetMLE_eq` (`Ŵ_E(λ, ρ) = Σ_i Σ_hi Σ_blk L_i(λ)·eq(r_hi,hi)eq(ρ_hi,hi)·eq(r_blk,blk)eq(ρ_blk,blk)·Sel(blk)·E`). `bzPoly`/Z2 unchanged. `bz_start` lost its unused `Sel`-Boolean hypothesis. |
| S-C-M1 / rev. 3.4 lincheck | per-kind folded columns: `kindExpr` (degree 2, `kindExpr_deg`), `kindTables`, `zfoldK`, `linAK`; **`lin_trueSum_kinds`** (true sum `â* + α b̂*` with `A = Σ_κ Ind_κ ⊗ A₀^κ`), **`lin_final_kinds`** (`Σ_κ M̃_κ(r_k) v_κ`), **`lin_walk_adjust`** (one walk with `rw′ = rw · Σ_κ v_κ free_κ`), `zfoldK_mle`, **`lin_beta_claim`** (the `β`-batched claim is `⟨W_β, z⟩`, `W_β(j,t) = eq(r_k,j) eq(r′_blk,t) Σ_κ β^κ Ind_κ(t)`), **`lin_beta_le`** (row L3: 6 bad `β` for 7 kinds, `batch_pow_bad_le`). The single-kind lemmas (`lin_trueSum`, `lin_final`) stay for the leaf. |
| S-C-M2 (3) | **`z2_pair_bad_le`** (`FRSkip`): `gen`'s Z2 form (`z2Vals`: `P^z` interpolated over `Λ` plus `P^e` on `S`, the `P^{ab}` message on `Λ`); a nonzero residual on `S` or a wrong `P^z` message leaves ≤ 127 bad `λ`. `zcMsg` stays (controls). |
| rev. 3.4 RS weight | `ring_complete`, `ring_final`, `rs_end`, `rsTruth`, `rs1_joint` take any high weight `g` instead of `eq(r, ·)` (partials `Σ_u g(u) Q_i(u)`; `g = eq(r,·)` is the old statement by `mle`'s definition), so `W_β`'s block weight (a tensor prefix sum over the kinds' intervals, as `ŵ`, `selWeight_eq`) is consumed directly. |
| S-C-m1 | `slotW_mle` (any slot map: `Σ_σ eq(θ,σ) eq(r, pos σ)`, for `d` at 520…775) beside `slotW_mle_aligned`; the lemmas are generic in `s` and `q` (`q = 10` collapse coordinates). |
| S-C-m2 | `FR.lean` left to the orchestrator. |
| S-C-m3 | all ~40 warnings fixed (deprecated `if_pos/if_neg/dif_pos/dif_neg/if_true/Fin.coe_*` renamed, `<;>` linter, unused simp arguments, `omit [CharP R 2]`, unused hypothesis). |
| S-C-m4 | budgets below. |
| S-C-m5 | golf below. |
| S-C-m6 | **How `rs1_joint` is consumed.** RS1 is one phase of 4 squeezes (A.2: two F coordinates per answer, `f₀ f₁ | f₂ f₃ | f₄ f₅ | f₆ κ`). `rs1_joint` bounds the escaping tuples of `F^8` by `(7 + J − 1)·|F|^7`; the potential charges the phase's open chain `φ = (7 + J − 1)/|F|` and, after each answer, the conditional count over the remaining coordinates: `seq_bad_le` gives the per-prefix counts (1 per stage coefficient from a doomed prefix, `J − 1` for `κ`), `pair_bad_le` combines the two coordinates of one answer, and L-cert's `extCount_split` sums the per-answer conditional counts into the phase's martingale step (each fresh answer's bad set is `≤ (b_{2a} + b_{2a+1})·2^128` of `2^256` answers by `card_chF_fiber`). |

**Golf (kernel time).**

| Item | Before | After | Note |
|---|---|---|---|
| `pinned_cert` | 7.1 s | **6.5 s** | `bitN` on `toNat.testBit`, the row walk adds with `F.add` (statement unchanged). A Nat-xor row product measured 5.0 s but needs a Nat ↔ `F.add` bridge; not taken. |
| `pinnedW_eq` | 9.8 s | 9.6 s (unchanged) | The review assumed CompPoly's `Ext` product; it already runs on S-A's two-`UInt64` twin (`F.mul`, ≈ 38 ms per product in the kernel). A list `flatMap` table measured 6.6 s (`T14` probe) but needs a `List`/`Array` bridge lemma for `eqTable`; declined for budget. |
| `skipNode_eq_zero`, `S_disjoint_Λ` | < 0.6 s together | unchanged | Deriving them from `GF2Indep gW` would replace a 128-case check by a 128-subset one; no gain. |
| `uni_bad_le` | — | removed | unused after rev. 3.1 (Z2 uses `card_interpolateAt_eq_le`). |

Sequential kernel times (`lake env lean --profile`, `taskset -c 5`, `logs/S-C-fix/profile-*.log`):

| Module | wall | kernel |
|---|---|---|
| `FRMLE` | 9.4 s | 1.29 s |
| `FRSumcheck` | 12.1 s | 1.60 s |
| `FRShift` | 10.5 s | 1.23 s |
| `FRRingSwitch` | 14.6 s | 2.32 s |
| `FRSkip` | 26.9 s | 20.2 s (`pinnedW_eq` 9.56, `pinned_cert` 6.5, others ≤ 1.5) |
| `FRSpartan` | 15.2 s | 1.85 s |
| `FRMLEControls` | 8.1 s | 1.61 s |

(The first table, §4, was not pinned to one core; these are the comparable numbers from now on.)

**Lines (loc.py code), before → after:** `FRMLE` 281 → 281; `FRSumcheck` 444 → 439 (budget
350); `FRShift` 271 → 279; `FRRingSwitch` 493 → 493; `FRSkip` 513 → 541; `FRSpartan` 333 → 462
(budget 450: the per-kind lincheck and `targetMLE_eq`); `FRMLEControls` 95 → 95 (budget 50);
**total 2,430 → 2,590** (sum of budgets 2,850).

**Open after the fix pass.** `kindFoldWeight`'s closed form (A.8: `W̃_β` at the RS point as a tensor
prefix sum over the kinds' intervals) is `selWeight_eq`'s computation with `Σ_κ β^κ Ind_κ` in place
of `Sel`; the instance lemma is for whoever writes `kindFoldWeight` in `FRVIR`. The two kernel
bridges above (≈ 4.5 s together) remain available if FR-R4′ tightens.

## Revision 3.8 rework (3.8.1, `af0c0d0`; §10 "Stage-review changes 6" and "7")

Builds under the 16G memory scope (`logs/fr-build-piop/b.sh`); `logs/S-C-fix/build-38.log` (58.1 s,
8 modules, no warnings); source rule 0 findings (`source-rule-38.log`); 66 declarations on the three
axioms at most (`axioms-38.log`). Statement diff against the 3.4 fix pass
(`logs/S-C-fix/stmts-38.diff`, S-A's tool): changes only in the zerocheck, the lincheck's count, the
new declarations below and the controls; everything else is unchanged.

**Statement changes.**

| Module | Change |
|---|---|
| `FRSpartan` | `BHolds`, `bzRes` lose `Sel` (rev. 3.8: whole cube, `Sel ≡ 1`; the `free` kind). `bzPoly`/`bzPoly_node`/`bz_skip_le` replaced by `pabPoly` (≤ 126), `pzPoly` (≤ 63), `bz_node` (`P^{ab} + P^z + P^e = r̃es` at a node of `S`), `bz_end` (now the hypothesis of `skip_pair_bad_le`). **`bzExpr = w·a·b`** over three tables (`bzTables rs λ a b`), **`bz_trueSum = P^{ab}(λ)`**, **`bz_final = eq(r, r′)·â·b̂`**, `bz_triple_wrong` on the pair `(â, b̂)`. Lincheck: **`linM_free`** (`A₀ = B₀ = I`: `M_free = (1 + α)·rowW`, no walk), **`lin_beta_le`** now 9 claims, ≤ 8 bad `β`. **`rowW`, `rowW_eq`** (A.8: `Σ_k rowW(λ, r′_hi)(k)·T(k) = Σ_h eq(r′_hi, h)·T̂(λ, h)`). `selWeight_eq`, `selWeight_split`, `targetMLE_eq` removed (`prefixP`, `selOf`, `eW` stay for `FRPubTarget` and the controls). |
| `FRSkip` | **`skip_pair_bad_le` (126)**: `P^{ab}*` through the 127 nodes `S ∪ Λ₀…₆₂` from `z2Vals pz pab pe` (`P^z*` interpolated over `Λ` plus `P^e` on `S`, the 63 `P^{ab}` values on `Λ₀…₆₂`), `P^z*` through `Λ`; a nonzero residual on `S` or a wrong `P^z` message leaves ≤ 126 bad `λ`. Replaces 3.4's `z2_pair_bad_le` (127). |
| `FRPubTarget` (new, 35 lines) | `targetS` (`P^e(σ) = Σ_{x′} eq(r,x′) E(x′,σ)`), **`targetS_eq`** (per kind and pinned position: `Σ_hi eq(r_hi,hi) Σ_κ E_κ(σ,hi)·Ĩnd_κ(r_blk)`), **`intervalMle_eq`** (`Ĩnd_κ` as prefix-sum differences over the kind's intervals). Per-block affine patterns (`t_lo`) are not covered (S-0/L-cert if `targetS` needs them). |
| `FRShift` | **`shiftEq_eq`** (A.8 `shiftEq`: `(shiftPair τ r).2` is the successor's extension). |
| `FRRingSwitch` | unchanged statements; **`rs1_four`** instantiates `rs1_joint` at `J_z = 4` (≤ `10·|F|^7`). The Z claim `ẑ(r, λ)` is its weighted-claim case with the quirky low weight (`quirky_claim_split`) and `g = eq(r,·)`; its position (first) does not enter the bound. |
| `FRMLEControls` | `bHolds_pos/neg` restated, `bHolds_sel` removed; new `free_rows_pos` (`z·z = z + 0` on bits), `free_rows_neg` (3.8's `(var k, one)` rows fail on `z = 0`, BP-C-R5-M1), `targetS_pos/neg`. |

§5.2 rows now: Z1 0/1, **Z2 126**, Z3 3, L1 1, L2 2, **L3 8**, S1 1, S2 2, RS1 `7 + J − 1 = 10`
(`rs1_four`), Lr/E as before.

**Sequential kernel times** (`taskset -c 5`, `logs/S-C-fix/profile38-*.log`): `FRMLE` 1.37 s,
`FRSumcheck` 1.72 s, `FRShift` 1.24 s, `FRRingSwitch` 2.39 s, `FRSkip` 20.8 s (`pinnedW_eq` and
`pinned_cert` as before), `FRSpartan` 1.94 s, `FRPubTarget` 0.10 s, `FRMLEControls` 1.84 s;
total ≈ 31.4 s.

**Lines (code):** `FRMLE` 281, `FRSumcheck` 439, `FRShift` 283, `FRRingSwitch` 500, `FRSkip` 548,
`FRSpartan` 415, `FRPubTarget` 35, `FRMLEControls` 100; total **2,601**.
