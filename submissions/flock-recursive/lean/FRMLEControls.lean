-- Copied from `submissions/spartan-srom/lean/SpartanSromMLEControls.lean` (this repository, branch
-- `v4/flock-recursive` at `783328c`), namespace `SpartanSrom` → `FR`; that file was ported from v3
-- `spartan-chain` (submissions repo, local `main` at `1f59b38`). Changes are listed in the module
-- docstring.
import FRSpartan
import Mathlib.Algebra.Field.ZMod

/-!
# Controls for track L-piop: `FRMLE`, `FRSumcheck`, `FRShift`, `FRRingSwitch`, `FRSkip`, `FRSpartan`

(BLUEPRINT §5.6.) The first sections are spartan-srom's controls (changes: the namespace); the
last section is new. `FRSkip`'s field-level controls are in `FRSkip` itself (`zeta_order`,
`pinned_rank` and its negative `rev2Rho_not_pinned`).

A positive and a negative control for each computable definition the certificate relies on,
kernel-checked by `decide` on small instances over `ZMod 7` (`ZMod 2` where characteristic two
matters), and tightness controls for the counting lemmas (each bound is attained, so no
hypothesis is vacuous and no bound is loose by construction).
-/

namespace FR

open Finset

/-! ## `eqTable`, `mleEval`, `bind0`, `eqPts` -/

/-- `eq((2, 3), u)` for `u = 0, 1, 2, 3`, variable `0` the low bit. -/
theorem eqTable_pos : eqTable [(2 : ZMod 7), 3] = #[2, 3, 4, 6] := by decide

/-- The big-endian order is not the table. -/
theorem eqTable_neg : eqTable [(2 : ZMod 7), 3] ≠ #[2, 4, 3, 6] := by decide

/-- At the Boolean point `(1, 0)` (index `1`) the extension is the entry `t[1]`. -/
theorem mleEval_pos : mleEval #[(5 : ZMod 7), 1, 4, 2] [1, 0] = 1 := by decide

/-- At `(0, 1)` (index `2`) it is not `t[1]`. -/
theorem mleEval_neg : mleEval #[(5 : ZMod 7), 1, 4, 2] [0, 1] ≠ 1 := by decide

/-- Variable `0` fixed to `3`: `(5 + 3·(1 - 5), 4 + 3·(2 - 4))`. -/
theorem bind0_pos : bind0 #[(5 : ZMod 7), 1, 4, 2] 3 = #[0, 5] := by decide

/-- Fixing the high variable instead is not `bind0`. -/
theorem bind0_neg : bind0 #[(5 : ZMod 7), 1, 4, 2] 3 ≠ #[5 + 3 * (4 - 5), 1 + 3 * (2 - 1)] := by
  decide

theorem eqPts_pos : eqPts [(2 : ZMod 7), 3] [1, 0] = 3 := by decide

theorem eqPts_neg : eqPts [(2 : ZMod 7), 3] [0, 1] ≠ 3 := by decide

/-! ## Sumcheck -/

/-- The summand `t₀ · t₁`. -/
def prodExpr : Expr := .mul (.var 0) (.var 1)

/-- Two tables of size `4` over `ZMod 7`; `Σ_u t₀[u] t₁[u] = 5 + 12 + 0 + 4 = 0`. -/
def ctlTables : Array (Array (ZMod 7)) := #[#[1, 2, 3, 4], #[5, 6, 0, 1]]

/-- The honest rounds pass from the true claim `0`, and the final claim is `t̃₀(r) · t̃₁(r)`. -/
theorem sumcheck_pos :
    verifyRounds prodExpr.deg 0 ((honest prodExpr ctlTables [2, 3]).zip [2, 3]) =
      some (mleEval #[1, 2, 3, 4] [2, 3] * mleEval #[5, 6, 0, 1] [2, 3]) := by
  decide +kernel

/-- From the false claim `1` the same rounds are rejected. -/
theorem sumcheck_neg :
    verifyRounds prodExpr.deg 1 ((honest prodExpr ctlTables [2, 3]).zip [2, 3]) = none := by
  decide

/-- A round polynomial with the right sum but too few coefficients is rejected. -/
theorem sumcheck_neg_size : verifyRounds 2 (3 : ZMod 7) [(#[1, 1], 0)] = none := by decide

/-- In characteristic two the check ignores `c_0` (`peval_zero_add_one`): `g = 1 + X` and
`g = X` both pass from the claim `1`. -/
theorem check_char_two :
    verifyRounds 1 (1 : ZMod 2) [(#[1, 1], 0)] = some 1 ∧
      verifyRounds 1 (1 : ZMod 2) [(#[0, 1], 0)] = some 0 := by decide

/-- L-S1 is tight: `X²` and `1` (degree `2`) agree at the two points `±1` of `ZMod 5`. -/
theorem round_bad_tight :
    (univ.filter fun r : ZMod 5 ↦ peval #[0, 0, 1] r = peval #[1, 0, 0] r).card = 2 := by decide

/-- L-S2 is tight: fixing variable `0` of the nonzero table `(1, 0)` gives zero at `c = 1`. -/
theorem zerocheck_tight :
    (univ.filter fun c : ZMod 5 ↦
      fix0 (fun u : Fin (2 ^ 1) ↦ if u.val = 0 then (1 : ZMod 5) else 0) c = 0).card = 1 := by
  decide

/-- L-S3 is tight: `(1, 0, 0)` and `(0, 0, 1)` agree at `ρ = ±1`. -/
theorem batch_tight :
    (univ.filter fun ρ : ZMod 5 ↦ 1 + ρ * 0 + ρ ^ 2 * 0 = 0 + ρ * 0 + ρ ^ 2 * 1).card = 2 := by
  decide

/-! ## Ring switching -/

/-- `Φ` with every coefficient zero is the identity. -/
theorem phi_zeros_pos (a : ZMod 7) : Phi (List.replicate 6 0) a = a := frobMap_stages_zeros _ _ _

/-- `Φ` with one coefficient nonzero is not: over `ZMod 2`, `Φ_{[1]}(1) = 1 + 1² = 0`. -/
theorem phi_neg : phiApply [(1 : ZMod 2)] 1 ≠ 1 := by decide

/-- Two stages, `f = (1, 1)` over `ZMod 2`: `Φ(a) = Σ_k c_k a^(2^k)` with all `c_k = 1`. -/
theorem phiTable_pos : phiTable [(1 : ZMod 2), 1] = #[1, 1, 1, 1] := by decide

theorem phiTable_neg : phiTable [(1 : ZMod 2), 0] ≠ #[1, 1, 1, 1] := by decide

/-- The verifier's `W̃` against the extension of the prover's table, by evaluation. -/
theorem weightEval_pos :
    weightEval [(1 : ZMod 2), 1] [1, 0] [0, 1] = mleEval (weightTable [1, 1] [1, 0]) [0, 1] := by
  decide +kernel

/-! ## Soundness rounds -/

/-- `bindT` binds variable `0` first: `(5, 1, 4, 2)` at `(1, 0)` is the entry `t[1]`. -/
theorem bindT_pos : bindT #[(5 : ZMod 7), 1, 4, 2] [1, 0] = #[1] := by decide

theorem bindT_neg : bindT #[(5 : ZMod 7), 1, 4, 2] [1, 0] ≠ #[4] := by decide

/-- The start of R1 is reachable: a one-row R1CS with `1 · 1 ≠ 0` is unsatisfied
(`zc_start` applies). -/
theorem sat_neg :
    ¬Sat (a := 0) (b := 0) (fun _ _ ↦ (1 : ZMod 2)) (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ ↦ 1) := by
  simp [Sat, matVec]

/-- ... and `1 · 1 = 1` is satisfied. -/
theorem sat_pos :
    Sat (a := 0) (b := 0) (fun _ _ ↦ (1 : ZMod 2)) (fun _ _ ↦ 1) (fun _ _ ↦ 1) (fun _ ↦ 1) := by
  simp [Sat, matVec]

/-! ## Controls added by S-C: shift, prefix sums, interpolation, pack, ring switching, block zerocheck -/

/-- `shiftPair` against the defining double sum at `n = 2` over `ZMod 7`. -/
theorem shiftPair_pos :
    (shiftPair [(2 : ZMod 7), 3] [4, 5]).2 =
      ∑ u : Fin (2 ^ 2), ∑ v : Fin (2 ^ 2), eq ![(2 : ZMod 7), 3] (cube u) * succT u v *
        eq (cube v) ![4, 5] := by decide

/-- The predecessor relation has a different extension. -/
theorem shiftPair_neg :
    (shiftPair [(2 : ZMod 7), 3] [4, 5]).2 ≠
      ∑ u : Fin (2 ^ 2), ∑ v : Fin (2 ^ 2), eq ![(2 : ZMod 7), 3] (cube u) * succT v u *
        eq (cube v) ![4, 5] := by decide

/-- A two-block chain over `ZMod 2` (one slot bit): `in(0) = s`, `in(1) = out(0)`, `out(1) = h`. -/
theorem chainLinks_pos :
    ChainLinks (s := 0) (n := 1) (R := ZMod 2) ![1, 0] ![1, 1] ![1] ![0] := by
  rw [chainLinks_iff]; decide

/-- Breaking the link (`in(1) ≠ out(0)`) is caught by the residual. -/
theorem chainLinks_neg :
    ¬ChainLinks (s := 0) (n := 1) (R := ZMod 2) ![1, 0] ![1, 0] ![1] ![0] := by
  rw [chainLinks_iff]; decide

/-- `prefixP` is the prefix sum: `n = 2`, `c = 3`. -/
theorem prefixP_pos :
    prefixP 2 (eW ![(2 : ZMod 7), 3] ![4, 5]) 3 =
      ∑ x : Fin (2 ^ 2), if x.val < 3 then eq ![(4 : ZMod 7), 5] (cube x) *
        eq ![(2 : ZMod 7), 3] (cube x) else 0 := by decide

theorem prefixP_neg :
    prefixP 2 (eW ![(2 : ZMod 7), 3] ![4, 5]) 3 ≠
      ∑ x : Fin (2 ^ 2), if x.val < 2 then eq ![(4 : ZMod 7), 5] (cube x) *
        eq ![(2 : ZMod 7), 3] (cube x) else 0 := by decide

/-- **The zerocheck weight is not the factor form** (BP-C-R4-m1): with `Sel = [x < 1]`,
`ŵ(r′) ≠ eq(r, r′) · Sẽl(r′)`. -/
theorem selWeight_ne_control :
    mle (fun x : Fin (2 ^ 1) ↦ eq ![(2 : ZMod 7)] (cube x) * (if x.val < 1 then 1 else 0)) ![3] ≠
      eq ![(2 : ZMod 7)] ![3] * mle (fun x : Fin (2 ^ 1) ↦ if x.val < 1 then (1 : ZMod 7) else 0) ![3] := by
  decide

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Interpolation at three nodes of `ZMod 7` recovers `X²`. -/
theorem interpolateAt_pos : interpolateAt ![(0 : ZMod 7), 1, 2] ![0, 1, 4] 3 = 2 := by decide +kernel

/-- Changed values interpolate to something else at `3`. -/
theorem interpolateAt_neg : interpolateAt ![(0 : ZMod 7), 1, 2] ![0, 1, 5] 3 ≠ 2 := by decide +kernel

/-- The pack (A.7): bit 64 is `y` (bit 0 of `c₁`). -/
theorem bitBasis_pos : bitBasis ⟨64, by norm_num⟩ = F.y := by decide

/-- The swapped order `c₁ ‖ c₀` would make bit 64 the constant `1`. -/
theorem bitBasis_neg : bitBasis ⟨64, by norm_num⟩ ≠ 1 := by decide

/-- `GF2Indep` is a real constraint: a repeated element is dependent. -/
theorem gf2Indep_neg : ¬GF2Indep ![(1 : F), 1] := fun h ↦ by
  have := h univ (by simp [Fin.sum_univ_two, CharTwo.add_self_eq_zero])
  exact Finset.univ_nonempty.ne_empty this

/-- `ring_inj_F` applies: the family with one nonzero slice error. -/
theorem ring_inj_F_pos : ∃ k < 128, ∑ i, bitBasis i * (Pi.single 0 1 : Fin 128 → F) i ^ 2 ^ k ≠ 0 :=
  ring_inj_F _ fun h ↦ one_ne_zero ((congrFun h 0).symm.trans (Pi.single_eq_same _ _)).symm

/-- `BHolds` over a one-variable toy: `1 · 1 = 0 + 1` holds, `1 · 1 = 1 + 1` does not. -/
theorem bHolds_pos : BHolds (ℓ := 0) (fun _ ↦ 1) (fun _ _ ↦ 1) (fun _ _ ↦ 1) (fun _ _ ↦ 0)
    (fun _ _ ↦ 1) := fun _ _ _ ↦ by simp

theorem bHolds_neg : ¬BHolds (ℓ := 0) (fun _ ↦ 1) (fun _ _ ↦ 1) (fun _ _ ↦ 1) (fun _ _ ↦ 1)
    (fun _ _ ↦ 1) := fun h ↦ by
  have := h 0 0 rfl
  simp [CharTwo.add_self_eq_zero] at this

/-- `Sel` matters: the same violation off the used blocks is not a violation. -/
theorem bHolds_sel : BHolds (ℓ := 0) (fun _ ↦ 0) (fun _ _ ↦ 1) (fun _ _ ↦ 1) (fun _ _ ↦ 1)
    (fun _ _ ↦ 1) := fun _ _ h ↦ absurd h zero_ne_one

end FR
