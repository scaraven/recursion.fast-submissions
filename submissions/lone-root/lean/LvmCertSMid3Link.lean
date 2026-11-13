-- WP-16b (CERT). New for lvm (O6 link, the `KS` link): the `KS` link's assembled claims
-- (`ksLinkClaimsE`) holding on the commitments give WP-8's `KsLinkClaims` with WP-14c's accessors.
-- lvm2 S2 (WP S2-CERT): `KS` at `C_main` word `4·2^20` (FRZ-0); v1's `CH` link is gone.
import LvmCertSMid3Blk

/-!
# The links' claims

* **`ksLinkClaims_of`**: the four combined claims `yC`, `inC`, `mC` (on `C_rec`), `xC`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## Helpers -/

/-- Equality weights at a cube point: the indicator of the index. -/
theorem lk_eqAt_boolPoint {m z w : ℕ} (hz : z < 2 ^ m) (hw : w < 2 ^ m) :
    eqAt (boolPoint m z) w = if w = z then 1 else 0 := by
  have e := eqEval_boolPoint_eqAt (boolPoint m z) w
  rw [length_boolPoint] at e
  rw [← e, Complete.eqEval_boolPoint_boolPoint m z w hz hw]
  by_cases hwz : w = z
  · simp [hwz]
  · simp [hwz, Ne.symm hwz]

/-- A sum weighted by `eq(a ‖ sel(t), ·)` over `h + 6` coordinates is slot `t`'s. -/
theorem lk_sum_sel {h t : ℕ} {a : List E} (ha : a.length = h) (ht : t < 2 ^ 6) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ (h + 6)), eqAt (a ++ selE t 6) n * F n =
      ∑ x ∈ range (2 ^ h), eqAt a x * F (x + 2 ^ h * t) := by
  have hs : (selE t 6).length = 6 := by simp [selE, selectorPoint_eq_boolPoint]
  have e := col_split (s := selE t 6) ha F
  rw [hs] at e
  rw [e, Finset.sum_eq_single t]
  · simp only [selE, selectorPoint_eq_boolPoint]
    rw [lk_eqAt_boolPoint ht ht, ite_eq_left rfl, one_mul]
  · intro o ho hne
    simp only [selE, selectorPoint_eq_boolPoint]
    rw [lk_eqAt_boolPoint ht (Finset.mem_range.1 ho), ite_eq_right hne, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 ht) hn

/-- A list sum over `range k` is the `Finset` sum. -/
theorem lk_sum_map_range (g : ℕ → E) :
    ∀ k, ((List.range k).map g).sum = ∑ l ∈ range k, g l
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, lk_sum_map_range g k,
      Finset.sum_range_succ]
    simp

/-- A placed point weight paired with the stack is the block's extension at the point. -/
theorem lk_sum_placed {μ : ℕ} (blk : VPlacement) (z : List E) (hz : z.length = blk.variableCount)
    (hal : 2 ^ blk.variableCount ∣ blk.index) (hfit : blk.index + 2 ^ blk.variableCount ≤ 2 ^ μ)
    (q : Column μ) :
    ∑ x : Fin (2 ^ μ), blk.eqAbove (boolPoint μ x) *
        LeanVM.Protocol.Verifier.eqEval z ((boolPoint μ x).take blk.variableCount) *
        ofK (q.values.getD x 0) =
      ∑ n ∈ range (2 ^ blk.variableCount), eqAt z n * ofK (q.values.getD (blk.index + n) 0) := by
  obtain ⟨v, off⟩ := blk
  simp only at hz hal hfit ⊢
  rw [sum_block hal hfit]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  subst hz
  rw [eqEval_boolPoint_eqAt]

/-- **A `sumClaimE` claim on its commitment** is the combination of its parts' block extensions. -/
theorem lk_holds_sumClaim {μ k : ℕ} (F : ℕ → E × VPlacement × List E) (val : E) (q : Column μ)
    (hF : ∀ l < k, (F l).2.2.length = (F l).2.1.variableCount ∧
      2 ^ (F l).2.1.variableCount ∣ (F l).2.1.index ∧
      (F l).2.1.index + 2 ^ (F l).2.1.variableCount ≤ 2 ^ μ)
    (h : StackClaim.Holds μ (sumClaimE μ ((List.range k).map F) val).onStack q) :
    ∑ l ∈ range k, (F l).1 * ∑ n ∈ range (2 ^ (F l).2.1.variableCount),
      eqAt (F l).2.2 n * ofK (q.values.getD ((F l).2.1.index + n) 0) = val := by
  have h' : ∑ x : Fin (2 ^ μ), (sumClaimE μ ((List.range k).map F) val).onStack.1 (boolPoint μ x) *
      ofK (q.values.getD x 0) = val := h
  have key : ∀ x : Fin (2 ^ μ),
      (sumClaimE μ ((List.range k).map F) val).onStack.1 (boolPoint μ x) * ofK (q.values.getD x 0) =
        ∑ l ∈ range k, (F l).1 * ((F l).2.1.eqAbove (boolPoint μ x) *
          LeanVM.Protocol.Verifier.eqEval (F l).2.2
            ((boolPoint μ x).take (F l).2.1.variableCount) * ofK (q.values.getD x 0)) := by
    intro x
    have h1 : ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (boolPoint μ x) = 1 := by
      rw [eqAbove_boolPoint (by simp) x.isLt, Nat.div_eq_of_lt x.isLt, Nat.zero_div, ite_eq_left rfl]
    have h2 : (boolPoint μ x).take μ = boolPoint μ x := List.take_of_length_le (by simp)
    show ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (boolPoint μ x) *
        LeanVM.Protocol.Verifier.sumE (((List.range k).map F).map fun (c, blk, z) =>
          c * blk.eqAbove ((boolPoint μ x).take μ) *
            LeanVM.Protocol.Verifier.eqEval z (((boolPoint μ x).take μ).take blk.variableCount)) *
        ofK (q.values.getD x 0) = _
    rw [h1, h2, one_mul, LeanVM.Protocol.Verifier.sumE, foldl_add_eq, zero_add, List.map_map,
      lk_sum_map_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Function.comp_apply]
    generalize F l = p
    obtain ⟨c, blk, z⟩ := p
    dsimp only
    ring
  rw [← h', Finset.sum_congr rfl fun x _ ↦ key x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  obtain ⟨hz, hal, hfit⟩ := hF l (Finset.mem_range.1 hl)
  rw [← Finset.mul_sum, lk_sum_placed _ _ hz hal hfit]


/-! ## The links -/

/-- A two-block list of parts is one `range` map. -/
theorem lk_range_append {α : Type} (k : ℕ) (F G : ℕ → α) :
    (List.range k).map F ++ (List.range k).map G =
      (List.range (k + k)).map fun j ↦ if j < k then F j else G (j - k) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun j hj ↦ by rw [if_pos (List.mem_range.1 hj)]
  · exact List.map_congr_left fun j _ ↦ by
      simp only [Function.comp_apply, if_neg (show ¬ k + j < k by omega), Nat.add_sub_cancel_left]

/-- **The `KS` link's claims** (KS13, lvm2 roll 8, B1: `ρ'` has 13 coordinates, `λ` 5; `M` cut at 7,680, `X` on
`2^9` rows; roll 7: KS14, 14, 15,360, `2^10`; lvm2 roll 11, M′ `S2GM`: `X_l` is the stream block's column `l` from
the split, stride `2^14`). -/
theorem ksLinkClaims_of (kchal : List E) (kshift : List E × E) (vals : List E)
    (h1 : kchal.length = 18) (h2 : kshift.1.length = 13) {qm : Column CMain.nu20} {qr : Column 19}
    (h : ∀ e ∈ ksLinkClaimsE kchal kshift vals, HoldsC qm qr e) :
    Lvm.KG.KsLinkClaims 13 9 (ksCol qm) (Lvm.KG.ksYRow 13 ksY2 (colM qm) (ksCol qm)) (msgM qr)
      (msgX qm) (kchal, kshift, vals) := by
  have hlam : (kchal.drop 13).length = 5 := by simp [h1]
  have hom : ∀ l < 25, (LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0 =
      eqAt (kchal.drop 13) l := fun l hl ↦ by
    rw [eqKernel_getD, hlam, ite_eq_left (by omega)]
  have hlo9 : (kshift.1.take 9).length = 9 := by simp [h2]
  have hy := h _ (List.mem_cons_self ..)
  have hi := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hm := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hx := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := lk_holds_sumClaim (μ := CMain.nu20) (k := 25) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0, (ksYPartE l kshift.1).1,
        (ksYPartE l kshift.1).2)) (vals.getD 0 0) qm ?_ hy
    · dsimp only at e ⊢
      rw [← e]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.1 hl
      rw [hom l hl']
      refine congrArg (eqAt (kchal.drop 13) l * ·) ?_
      unfold LeanVM.Protocol.KeccakGkr.stepMle
      by_cases hl14 : l < 14
      · simp only [ksYPartE, hl14, ↓reduceIte, ksBlk]
        rw [show slotLog = 6 from rfl, lk_sum_sel h2 (by omega)]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, ksCol, Lvm.NS.wd]
      · simp only [ksYPartE, hl14, ↓reduceIte]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, colM, Lvm.NS.wd, ksY2Off, ksY2]
    · intro l hl
      dsimp only
      by_cases hl14 : l < 14
      · simp only [ksYPartE, hl14, ↓reduceIte, ksBlk]
        exact ⟨by simp [h2, selE, selectorPoint_eq_boolPoint, slotLog], ⟨10, by norm_num [slotLog]⟩,
          by norm_num [slotLog]⟩
      · simp only [ksYPartE, hl14, ↓reduceIte]
        exact ⟨h2, ⟨739 + (l - 14), by rw [ksY2Off]; ring⟩, by rw [ksY2Off]; norm_num; omega⟩
  · have e := lk_holds_sumClaim (μ := CMain.nu20) (k := 25) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0,
        ({ variableCount := 13 + slotLog, index := CMain.ksOff20 } : VPlacement),
        kshift.1 ++ selE l slotLog)) (vals.getD 1 0) qm
      (fun l hl ↦ by
        dsimp only
        exact ⟨by simp [h2, selE, selectorPoint_eq_boolPoint, slotLog], ⟨10, by norm_num [slotLog]⟩,
          by norm_num [slotLog]⟩) hi
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l hl']
    refine congrArg (eqAt (kchal.drop 13) l * ·) ?_
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    rw [show slotLog = 6 from rfl, lk_sum_sel h2 (by omega)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [ksCol, Lvm.NS.wd]
  · have hm' : HoldsC qm qr (.crec, sumClaimE 19 ((List.range (17 + 17)).map fun j ↦ if j < 17 then
        ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD j 0,
          ({ variableCount := 13, index := j * 2 ^ 14 } : VPlacement), kshift.1) else
        ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD (j - 17) 0 * Lvm.KG.selX 9 kshift.1,
          ({ variableCount := 9, index := (j - 17) * 2 ^ 14 + ksSplit P20 } : VPlacement),
          kshift.1.take 9)) (vals.getD 2 0)) := by
      simpa only [lk_range_append] using hm
    have hsp : ksSplit P20 = 7680 := ksSplit_P20
    have e := lk_holds_sumClaim (μ := 19) (k := 17 + 17) _ (vals.getD 2 0) qr (fun j hj ↦ by
        by_cases hj17 : j < 17
        · rw [if_pos hj17]
          exact ⟨h2, ⟨2 * j, by ring⟩, by dsimp only; omega⟩
        · rw [if_neg hj17]
          exact ⟨hlo9, ⟨(j - 17) * 32 + 15, by dsimp only; rw [hsp]; omega⟩, by dsimp only; rw [hsp]; omega⟩) hm'
    rw [← e, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [if_pos hl', if_neg (show ¬ 17 + l < 17 by omega), Nat.add_sub_cancel_left]
    dsimp only
    rw [hom l (by omega), mul_assoc, ← mul_add]
    refine congrArg (eqAt (kchal.drop 13) l * ·) ?_
    rw [← Lvm.KG.cut_split (hk := 13) (xl := 9) (by norm_num) h2 (fun n ↦ ofK (msgM qr n l))]
    have hsN : Lvm.KG.ksSplitN 13 9 = 7680 := by decide
    simp only [msgM, Lvm.NS.wd, hsp, hsN, Nat.add_assoc]
  · have e := lk_holds_sumClaim (μ := CMain.nu20) (k := 17) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0,
        ({ variableCount := 9, index := xOff + l * 2 ^ 14 } : VPlacement), kshift.1.take 9))
      (vals.getD 3 0) qm
      (fun l hl ↦ ⟨hlo9, ⟨11279 + 32 * l, by rw [xOff]; ring⟩, by
        have hl' := Finset.mem_range.1 (Finset.mem_range.2 hl)
        show xOff + l * 2 ^ 14 + 2 ^ 9 ≤ 2 ^ 23
        simp only [xOff, CMain.xOff20]; omega⟩) hx
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l (by omega)]
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    refine congrArg (eqAt (kchal.drop 13) l * ·) (Finset.sum_congr rfl fun x _ ↦ ?_)
    simp only [msgX, Lvm.NS.wd, CMain.ksXW20_eq, xOff]
    rfl

end Lvm.ASM
