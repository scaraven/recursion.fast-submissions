-- New for lvm6 (WP-V1b): fast twin of the sponge link (`ksLinkProgE2 hk xl rows`, season 1's `KS` link at `E2`:
-- `hk + 5` ground coordinates, `hk` shift rounds, four scalars, the check). The shift sum over the rows reads the two
-- equality kernels through their low six and high bits (two small tables per point, three products a row).
import Lvm6VTwR
import Lvm6KProgS6

/-!
# Fast twins: the sponge link

* `eqSp ρ lo hi i` (`= eqAtF ρ i`, `eqSp_eq`), `contShiftFast` (`contShiftFast_eq`), `map_prodF`, `map_contShiftF`.
* **`fKsLink`**, **`tw_ksLink`**; K2's tree phase: **`fTreeProgS6`**, **`tw_treeProgS6`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

section Gen

variable {F : Type} [Field F] [Algebra K F]

/-- `eq(ρ, i)` from the tables of the low six and the high coordinates (`eqAtF` off the tables). -/
def eqSp (ρ : List F) (lo hi : Array F) (i : ℕ) : F :=
  if 6 ≤ ρ.length ∧ i < 2 ^ ρ.length then lo.getD (i % 64) 0 * hi.getD (i / 64) 0 else eqAtF ρ i

theorem eqSp_eq (ρ : List F) (i : ℕ) : eqSp ρ (eqKernelAF (ρ.take 6)) (eqKernelAF (ρ.drop 6)) i = eqAtF ρ i := by
  unfold eqSp
  split
  · rename_i h
    obtain ⟨h6, hi⟩ := h
    have ht : (ρ.take 6).length = 6 := by simp [h6]
    have hd : (ρ.drop 6).length = ρ.length - 6 := by simp
    have hp : 2 ^ ρ.length = 64 * 2 ^ (ρ.length - 6) := by
      rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add]; congr 1; omega
    rw [eqKernelAF_getD, eqKernelAF_getD, ht, hd, if_pos (by rw [show (2:ℕ) ^ 6 = 64 from rfl]; omega),
      if_pos (by rw [hp] at hi; exact Nat.div_lt_of_lt_mul hi)]
    conv_rhs => rw [← List.take_append_drop 6 ρ]
    rw [eqAtF_append, ht, show (2:ℕ) ^ 6 = 64 from rfl, eqAtF_mod (ρ.take 6) i, ht,
      show (2:ℕ) ^ 6 = 64 from rfl]
  · rfl

/-- The shift sum over `rows` from the split tables. -/
def contShiftFast (rows : List ℕ) (ρ ρ' : List F) : F :=
  let lo := eqKernelAF (ρ.take 6)
  let hi := eqKernelAF (ρ.drop 6)
  let lo' := eqKernelAF (ρ'.take 6)
  let hi' := eqKernelAF (ρ'.drop 6)
  sumF (rows.map fun i => eqSp ρ lo hi i * eqSp ρ' lo' hi' (i - 1))

theorem contShiftFast_eq (rows : List ℕ) (ρ ρ' : List F) : contShiftFast rows ρ ρ' = contShiftF rows ρ ρ' := by
  simp only [contShiftFast, contShiftF, eqSp_eq]

end Gen

section Map

variable {F F' : Type} [Field F] [Field F'] (φ : F →+* F')

theorem map_prodF (l : List F) : φ (prodF l) = prodF (l.map φ) := by
  unfold prodF
  rw [map_foldl_mul, map_one]

theorem map_contShiftF (rows : List ℕ) (ρ ρ' : List F) :
    φ (contShiftF rows ρ ρ') = contShiftF rows (ρ.map φ) (ρ'.map φ) := by
  simp only [contShiftF, map_sumF, List.map_map, Function.comp_def, map_mul, map_eqAtF]

end Map

/-- **Fast `ksLinkProgE2 hk xl rows`.** -/
def fKsLink (hk xl : ℕ) (rows : List ℕ) : VF (List FE2 × (List FE2 × FE2) × List FE2) :=
  VF.bind (fE2Samples gC1 (hk + 5)) fun kchal =>
  VF.bind (fSumcheck gC2 0 3 (List.replicate hk none)) fun kshift =>
  VF.bind (fE2Reads 4) fun vals =>
  VF.guard (decide (kshift.2 = contShiftFast rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 + selXF xl kshift.1 * vals.getD 3 0)))
    (VF.pure (kchal, kshift, vals))

/-- The decoding of the link's value. -/
def lkD (r : List FE2 × (List FE2 × FE2) × List FE2) : List E2 × (List E2 × E2) × List E2 :=
  (r.1.map FE2.toE2, scD r.2.1, r.2.2.map FE2.toE2)

theorem tw_ksLink (hk xl : ℕ) (rows : List ℕ) : TwinF lkD (ksLinkProgE2 hk xl rows) (fKsLink hk xl rows) := by
  unfold ksLinkProgE2
  refine tw_bind (tw_e2Samples _ _) fun kchal => ?_
  refine tw_bind (tw_sumcheckPlain gC2 3 hk 0) fun kshift => ?_
  refine tw_bind (tw_e2Reads 4) fun vals => ?_
  refine tw_guard _ _ ?_ (tw_pure rfl)
  refine Iff.trans (Eq.congr_right ?_) (toE2_eq_iff _ _)
  rw [contShiftFast_eq]
  simp only [scD, ← coe_tE, map_add, map_mul, map_contShiftF, map_eqEvalF, map_getD, selXF, map_prodF,
    List.map_take, List.map_drop]

/-- **Fast `treeProgS6 sh x`** (K2: `treeProgS29` behind `TreeShapeOK`). -/
def fTreeProgS6 (sh : Lvm6.Shape) (x : Lvm6.Hdr) : VF TreeSF :=
  if Lvm6.K.TreeShapeOK sh ∧ sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN ∧ sh.logN ≤ 28 then
    VF.bind (fTreeProg (sh.logN + 1)) fun out => VF.pure (toSF (sh.logN + 1) x.h out)
  else fun _ _ => none

theorem tw_treeProgS6 (sh : Lvm6.Shape) (x : Lvm6.Hdr) :
    TwinF TreeSF.dec (Lvm6.K.treeProgS6 sh x) (fTreeProgS6 sh x) := by
  unfold Lvm6.K.treeProgS6 fTreeProgS6
  by_cases h1 : Lvm6.K.TreeShapeOK sh <;> by_cases h2 : sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN ∧ sh.logN ≤ 28
  · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
    exact tw_bind (tw_treeProg _) fun out => tw_pure (toSF_dec _ _ _)
  all_goals
    first
    | (rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; intro π tr; rw [replayP_fail]; exact Option.Rel.none)
    | (rw [if_neg h1, if_neg (fun h => h1 h.1)]; intro π tr; rw [replayP_fail]; exact Option.Rel.none)

end Lvm6.V
