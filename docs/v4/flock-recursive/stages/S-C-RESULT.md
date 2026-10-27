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
