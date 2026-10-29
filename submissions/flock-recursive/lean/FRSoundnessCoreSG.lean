-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-1): the position-free
-- declarations of the 3.x soundness modules that revision 4.1 reuses, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessWeights` (2). Content: the two weight lemmas that
-- read `FRVIRFinalsSG` (`uHat`, `eqCellK`): `mleN_wSplit`, `eqCellK_eq`. Not theory-only: it goes
-- into `FRSoundnessCoreWeights` once `uHat`/`eqCellK` move to a verifier core module (step 4). The
-- 3.x modules import this one.
import FRSoundnessCoreWeights
import FRVIRFinalsCoreSG

/-! ## From `FRSoundnessWeights` (2 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

/-- **The coordinate split's extension** (A.9): variable `0` is the split bit, weighted `1` or
`u`, so its extension is `û(ρ₀) = 1 + ρ₀(1 + u)` times the rest. -/
theorem mleN_wSplit (n : ℕ) (W : ℕ → K) (ρ : Fin (n + 1) → K) :
    mleN (n + 1) (wSplit W) ρ = uHat (ρ 0) * mleN n W (Fin.tail ρ) := by
  rw [mleN, mle_fix0, mleN, ← mle_smul]
  congr 1
  funext u
  have h1 : (2 * u.val + 1) / 2 = u.val := by omega
  have h2 : (2 * u.val + 1) % 2 = 1 := by omega
  have h3 : 2 * u.val / 2 = u.val := by omega
  have h4 : 2 * u.val % 2 = 0 := by omega
  simp only [fix0, dbl, wSplit, uHat, Bool.toNat_false, Bool.toNat_true, add_zero, h1, h2, h3,
    h4, ite_true, one_ne_zero, ite_false, mul_one]
  rw [show W u * K.u - W u = W u * (K.u - 1) by ring, uK_sub_one]
  ring

section Level0

/-- `finPf`'s `eqCellK` is `eqCell` at the point's 23 coordinates (characteristic two:
`1 + ρ = 1 − ρ`). -/
theorem eqCellK_eq (ρ : Array K) (c : ℕ) :
    eqCellK ρ c = eqCell (fun v : Fin 23 => ρ.getD v 0) c := by
  rw [eqCellK, foldl_mulK, one_mul]
  have : ((List.range 23).map fun v => if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0).prod =
      ∏ v ∈ range 23, (if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0) := by
    simp only [Finset.prod, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.prod_coe]
  rw [this, ← Fin.prod_univ_eq_prod_range, eqCell]
  refine prod_congr rfl fun v _ => ?_
  simp only [CharTwo.sub_eq_add, add_comm (1 : K)]

end Level0

end FR.Snd
