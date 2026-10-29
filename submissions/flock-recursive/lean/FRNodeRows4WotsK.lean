-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, R-4-m2; stage S-E13b, track L-circ).
import FRNodeRows4WotsF
import FRNodeRows4Ext
import FRNodeSound4R

/-!
# `Gap4.wots` from the node rows

* **`actW_eq`**: the rows' activity form is `selSum` of the sub-slot;
* **`ind_ev`**: on S-E12c's activity profile (`act_profile`), `ind j` is `[k = j]`;
* **`hDig4_mD`**: the digit rows make the digest H computes for the reader's segment count
  (`hDig4 κ σ (kOf …)`) the digest of the digit bits `mD` (an aggregate's through the `k`-mux);
* **`gap4_wots`**: on `StmtN4` and the node rows, `Gap4.wots` holds at `rd4 pf`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block

theorem actW_eq (κ : NodeKind) (a i : ℕ) : actW κ a i = selSum κ (N4c.sub κ a i) := by
  simp [actW, selSum, selR, selIx, Circ.kinds, Lin.cell, List.range_succ, Nat.add_assoc]

/-- **The segment-count indicator** on the activity profile. -/
theorem ind_ev {κ : NodeKind} {a k : ℕ} {w : Asg} (hk1 : 1 ≤ k) (hkm : k ≤ κ.maxK)
    (hP : ∀ i < κ.maxK, (selSum κ (N4c.sub κ a i)).ev w = if i < k then 1 else 0) {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j ≤ κ.maxK) : (ind κ (actW κ a) j).ev w = if k = j then 1 else 0 := by
  unfold ind
  simp only [actW_eq]
  split_ifs with h1 h2 h2
  · rw [Lin.ev_sub, hP _ (by omega), hP _ (by omega), if_pos (by omega), if_neg (by omega), sub_zero]
  · rw [Lin.ev_sub, hP _ (by omega), hP _ (by omega)]
    by_cases h3 : j - 1 < k <;> by_cases h4 : j < k <;> simp [h3, h4] <;> omega
  · rw [hP _ (by omega), if_pos (by omega)]
  · rw [hP _ (by omega), if_neg (by omega)]

/-- `h_out` of a block read through its elements equals `mD` when the elements are the packed digit
bits. -/
theorem readDigest_mD {κ : NodeKind} {σ : ℕ} {w : Asg} {blk : ℕ} (h : ∀ h < 2, w (hc blk (2 + h)) = pkD κ σ w h) :
    Block.readDigest (bitsB4 w blk) 256 = mD κ σ w := by
  rw [readDigest_hc]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn, mD, h _ (show i / 16 < 2 by omega)]

/-- **The digest H computes for the reader's `k` is `mD`.** -/
theorem hDig4_mD (pf : Trace → Proof) {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ} (hσ : σ < 2)
    (hd : ∀ r ∈ digRows κ σ (actW κ (aggOf κ σ)), r.Holds w)
    (hprof : isAgg κ σ = true → ActK κ (aggOf κ σ) (N4s.kAct κ (aggOf κ σ) w) w ∧
      ∀ i < κ.maxK, (selSum κ (N4c.sub κ (aggOf κ σ) i)).ev w = if i < N4s.kAct κ (aggOf κ σ) w then 1 else 0) :
    hDig4 κ σ (kOf (N4s.rd4 pf) κ w σ) w = mD κ σ w := by
  unfold hDig4
  by_cases hA : isAgg κ σ = true
  · obtain ⟨ha, hc'⟩ := agg_of_isAgg κ hσ hA
    obtain ⟨⟨hk1, hkm, -⟩, hP⟩ := hprof hA
    have hk : kOf (N4s.rd4 pf) κ w σ = N4s.kAct κ (aggOf κ σ) w := by
      simp only [kOf, hA, if_true]; exact N4s.kA_rd4 pf κ ha w
    rw [hk]
    refine readDigest_mD fun h hh => ?_
    simp only [digRows, hA, if_true] at hd
    have hT : ∀ j < κ.maxK, w (tmC κ σ (j + 1) h) =
        (if N4s.kAct κ (aggOf κ σ) w = j + 1 then 1 else 0) * w (hc (finBlk κ σ (j + 1)) (2 + h)) := by
      intro j hj
      have r := hd _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
        List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩⟩))
      simp only [Row.Holds, Lin.ev_cell] at r
      rw [← r, ind_ev hk1 hkm hP (by omega) (by omega)]
    have e := eqR_val hone (hd _ (List.mem_append_right _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩)))
    rw [← pkD] at e
    rw [← e]
    simp only [Lin.ev, List.map_map, Function.comp_def, one_mul]
    rw [List.map_congr_left fun j hj => hT j (List.mem_range.1 hj)]
    obtain ⟨m, hm⟩ : ∃ m, κ.maxK = N4s.kAct κ (aggOf κ σ) w + m := ⟨_, (Nat.add_sub_cancel' hkm).symm⟩
    rw [hm, List.range_add, List.map_append, List.sum_append]
    obtain ⟨k', hk'⟩ : ∃ k', N4s.kAct κ (aggOf κ σ) w = k' + 1 := ⟨_, (Nat.sub_add_cancel hk1).symm⟩
    rw [hk', List.range_succ, List.map_append, List.sum_append]
    have z1 : ((List.range k').map fun j => (if k' + 1 = j + 1 then (1 : F) else 0) *
        w (hc (finBlk κ σ (j + 1)) (2 + h))).sum = 0 :=
      List.sum_eq_zero fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        rw [if_neg (by have := List.mem_range.1 hj; omega), zero_mul]
    have z2 : ((List.range m).map fun j => (if k' + 1 = k' + 1 + j + 1 then (1 : F) else 0) *
        w (hc (finBlk κ σ (k' + 1 + j + 1)) (2 + h))).sum = 0 :=
      List.sum_eq_zero fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        rw [if_neg (by omega), zero_mul]
    simp only [List.map_map, Function.comp_def] at z2 ⊢
    rw [z1, z2]
    simp
  · have hk : kOf (N4s.rd4 pf) κ w σ = 0 := by simp [kOf, hA]
    rw [hk]
    refine readDigest_mD fun h hh => ?_
    simp only [digRows, hA, if_false, Bool.false_eq_true] at hd
    have e := eqR_val hone (hd _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩))
    simpa [pkD] using e

theorem readSig_rd4 (pf : Trace → Proof) (κ : NodeKind) (σ : ℕ) (w : Asg) :
    ((N4s.rd4 pf).sgn κ σ w).σ = N4s.readSig4 κ σ w := by
  simp only [N4s.rd4, N4s.sgn4]; split_ifs <;> rfl

/-- **`Gap4.wots` from the node rows**: on the node's truths and the node rows (`xRows`, folded into
slot 1's link rows), both signed children's signatures sign the digest H computes. -/
theorem gap4_wots (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hX : ∀ r ∈ xRows κ, r.Holds w) :
    ∀ σ < 2, SigOk vk (hDig4 κ σ (kOf (N4s.rd4 pf) κ w σ) w) ((N4s.rd4 pf).sgn κ σ w).σ = true := by
  obtain ⟨hZ, hSh, hL, hE, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  have hF := N4s.protoFit_of hone hE
  intro σ hσ
  have hW : ∀ r ∈ wotsRows κ σ (actW κ (aggOf κ σ)), r.Holds w := fun r hr => hX r (by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · exact List.mem_append_left _ (List.mem_append_right _ hr))
  have hd : ∀ r ∈ digRows κ σ (actW κ (aggOf κ σ)), r.Holds w := fun r hr =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inr (.inr (.inl hr))))))))
  rw [readSig_rd4, hDig4_mD pf hone hσ hd fun hA => ?_]
  · exact wots_sound4 hZ hSh hL hP hσ hW
  · obtain ⟨ha, -⟩ := agg_of_isAgg κ hσ hA
    have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ (aggOf κ σ) i), r.Holds w :=
      fun i hi => N4s.linkRows_hold hF (sub_facts κ ha hi).1 hE
    have hK := N4s.actK_kAct hone ha hL hlk
    exact ⟨hK, act_profile hone ha hL hlk hK⟩

end W4
end FR
