-- New for lvm6 (WP NODE6). NODE5a's residual 1, `OutShape`: the lengths of `node6E`'s output cells, from the
-- generators' structure (`HsA` facts generic in the batch sizes, the lanes and the gate; no layout is evaluated).
import Lvm6NodeFinC

/-!
# The shape of `node6E`'s output cells (WP NODE6, residual 1)

Every statement is generic in the generators' parameters (batch exponent `κ`/`h`, first lane `a`, gate); the
deployed sizes enter only through `node6E`'s arguments (`treeG6 18`, `spG6 13`) in `hsA_node6E_shape`.
* **`hs_layBody_shape`**, **`hsA_layer6G_shape`**, **`hsA_laysG_shape`**: a layer keeps the claim's point length
  and hands on an `lt` claim (the `failG` branch asserts `1 = 0`: vacuous under the gate).
* **`hs_treeEndCore_shape`** / **`hs_spEndCore_shape`**: the ends' slice points have `κ + 6` / `h + 6` cells and
  their slices `64` (`sc2`'s answers: `hs_sc2`).
* **`hsA_treeG6_shape`**, **`hsA_spG6_shape`**, **`hs_ksLinkG6_shape`**, **`hs_wire6_shape`**, **`hs_ty6_shape`**.
* **`hsA_node6E_shape`**: `HsA … (node6E …) OutShape`; **`outShape_n6`**: `OutShape (n6 lay ⟨nK, 0⟩).1` where the
  deployed families' rows and assertions hold and the gate is on.
-/

set_option autoImplicit false

namespace Lvm6.Node.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK Lvm6.QD Lvm6.Node Lvm6.Node.Dep

variable {c : Ctx} {M : Mem}

/-! ## Binds that carry nothing -/

theorem hs_bind_n {α β : Type} {m : BM α} {f : α → BM β} {Q : β → Prop} (hf : ∀ a, Hs c M (f a) Q) :
    Hs c M (m >>= f) Q := hs_bind (P := fun _ ↦ True) (fun _ _ ↦ trivial) fun a _ ↦ hf a

theorem hsA_bind_n {α β : Type} {m : BM α} {f : α → BM β} {Q : β → Prop} (hf : ∀ a, HsA c M (f a) Q) :
    HsA c M (m >>= f) Q := hsA_bind (P := fun _ ↦ True) (fun _ _ _ ↦ trivial) fun a _ ↦ hf a

theorem sc2_len {R q : ℕ} {claim : C2} {o : List C2 × C2}
    (h : o.1 = (sc2Ans R q).map ld2 ∧ o.2.val M = scFold2 (fun k ↦ (ld2 k).val M) R q (claim.val M)) :
    o.1.length = R := by
  rw [h.1]; simp [sc2Ans]

/-! ## The layers -/

/-- **A layer's body keeps the point's length and hands on an `lt` claim.** -/
theorem hs_layBody_shape (κ step q : ℕ) (claim : ClaimC) (gate : Cell) (z one : C2) (fs : List C2)
    (dotG : List C2 → BM C2) :
    Hs c M (layBody κ step q claim gate z one fs dotG) fun o ↦
      o.point.length = claim.point.length ∧ ∃ pos β, o.w = .lt pos β := by
  unfold layBody
  iterate 13 refine hs_bind_n fun _ ↦ ?_
  refine hs_bind (Lvm6.QK.hs_eqRounds6_len _ _ _) fun vp hvp ↦ ?_
  iterate 9 refine hs_bind_n fun _ ↦ ?_
  exact hs_pure ⟨hvp, _, _, rfl⟩

/-- **A layer keeps the point's length and hands on an `lt` claim** (gate on). -/
theorem hsA_layer6G_shape (κ step q : ℕ) (claim : ClaimC) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (layer6G κ step q claim gate) fun o ↦
      o.point.length = claim.point.length ∧ ∃ pos β, o.w = .lt pos β := by
  unfold layer6G
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ hsA_bind (hsA_of_hs (hs_g2One z)) fun one hone ↦ ?_
  rw [hz, add_zero] at hone
  cases hcw : claim.w with
  | first rl =>
    simp only [layW]
    exact hsA_bind_n fun _ ↦ hsA_bind_n fun _ ↦ hsA_of_hs (hs_layBody_shape κ step q claim gate z one _ _)
  | lt pos β =>
    simp only [layW]
    split_ifs
    · exact hsA_bind_n fun _ ↦ hsA_bind_n fun _ ↦ hsA_bind_n fun _ ↦ hsA_bind_n fun _ ↦
        hsA_of_hs (hs_layBody_shape κ step q claim gate z one _ _)
    · exact hsA_failG hone hg

/-- **The layers keep the point's length**; after one layer the claim is `lt`. -/
theorem hsA_laysG_shape (κ : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    ∀ (steps : List ℕ) (q : ℕ) (claim : ClaimC),
      HsA c M (laysG κ steps q claim gate) fun o ↦ o.point.length = claim.point.length ∧
        ((∃ pos β, claim.w = .lt pos β) ∨ steps ≠ [] → ∃ pos β, o.w = .lt pos β)
  | [], _, _ => hsA_pure ⟨rfl, fun h ↦ h.elim id fun h' ↦ absurd rfl h'⟩
  | step :: steps, q, claim => by
    simp only [laysG]
    refine hsA_bind (hsA_layer6G_shape κ step q claim gate hg) fun o ho ↦ ?_
    exact hsA_mono (hsA_laysG_shape κ gate hg steps _ o) fun o2 h2 ↦
      ⟨h2.1.trans ho.1, fun _ ↦ h2.2 (Or.inl ho.2)⟩

theorem hsA_layers6G_shape (κ q : ℕ) (claim : ClaimC) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (layers6G κ q claim gate) fun o ↦
      o.point.length = claim.point.length ∧ ∃ pos β, o.w = .lt pos β :=
  hsA_mono (hsA_laysG_shape κ gate hg (List.range 12) q claim) fun _ h ↦
    ⟨h.1, h.2 (Or.inr (by simp))⟩

/-! ## The ends -/

/-- **The tree end's slice point and slice** (`κ + 6`, `64` cells). -/
theorem hs_treeEndCore_shape (κ q : ℕ) (claim : ClaimC) (pos : List C2) (β : C2) (gate : Cell) (hκ : 5 ≤ κ)
    (hpt : claim.point.length = κ - 3) :
    Hs c M (En.treeEndCore κ q claim pos β gate) fun o ↦ o.2.1.length = κ + 6 ∧ o.2.2.length = 64 := by
  unfold En.treeEndCore
  iterate 6 refine hs_bind_n fun _ ↦ ?_
  refine hs_bind (hs_sc2 11 q _) fun lv hlv ↦ ?_
  iterate 4 refine hs_bind_n fun _ ↦ ?_
  have hl := sc2_len hlv
  refine hs_pure ⟨?_, by simp [En.slC]⟩
  simp only [List.length_append, List.length_take, List.length_drop, List.length_cons, List.length_nil, hl, hpt]
  omega

theorem hs_treeEndG_shape (κ q : ℕ) (claim : ClaimC) (gate : Cell) (hκ : 5 ≤ κ)
    (hpt : claim.point.length = κ - 3) (hw : ∃ pos β, claim.w = .lt pos β) :
    Hs c M (En.treeEndG κ q claim gate) fun o ↦ o.2.1.length = κ + 6 ∧ o.2.2.length = 64 := by
  obtain ⟨pos, β, hw⟩ := hw
  simp only [En.treeEndG, hw]
  exact hs_treeEndCore_shape κ q claim pos β gate hκ hpt

/-- **The sponge end's slice point and slice** (`h + 6`, `64` cells). -/
theorem hs_spEndCore_shape (h q : ℕ) (claim : ClaimC) (pos : List C2) (β : C2) (gate : Cell) (hh : 4 ≤ h)
    (hpt : claim.point.length = h - 3) :
    Hs c M (En.spEndCore h q claim pos β gate) fun o ↦ o.2.1.length = h + 6 ∧ o.2.2.length = 64 := by
  unfold En.spEndCore
  iterate 3 refine hs_bind_n fun _ ↦ ?_
  refine hs_bind (hs_sc2 10 q _) fun lv hlv ↦ ?_
  iterate 4 refine hs_bind_n fun _ ↦ ?_
  have hl := sc2_len hlv
  refine hs_pure ⟨?_, by simp [En.slC]⟩
  simp only [List.length_append, List.length_take, List.length_drop, hl, hpt]
  omega

theorem hs_spEndG_shape (h q : ℕ) (claim : ClaimC) (gate : Cell) (hh : 4 ≤ h)
    (hpt : claim.point.length = h - 3) (hw : ∃ pos β, claim.w = .lt pos β) :
    Hs c M (En.spEndG h q claim gate) fun o ↦ o.2.1.length = h + 6 ∧ o.2.2.length = 64 := by
  obtain ⟨pos, β, hw⟩ := hw
  simp only [En.spEndG, hw]
  exact hs_spEndCore_shape h q claim pos β gate hh hpt

/-! ## The heads -/

theorem hs_treeHeadG_shape (κ a : ℕ) (hκ : 2 ≤ κ) :
    Hs c M (treeHeadG κ a) fun hd ↦ hd.ρ.length = κ - 1 ∧ hd.sl.length = 6 := by
  unfold treeHeadG
  iterate 8 refine hs_bind_n fun _ ↦ ?_
  refine hs_pure ⟨?_, by simp⟩
  simp only [List.length_cons, List.length_map, List.length_range]
  omega

theorem hs_spHeadG_shape (h a : ℕ) :
    Hs c M (spHeadG h a) fun hd ↦ hd.r.length = h ∧ hd.v.length = 25 ∧ hd.sl.length = 6 := by
  unfold spHeadG
  iterate 6 refine hs_bind_n fun _ ↦ ?_
  exact hs_pure ⟨by simp, by simp, by simp⟩

/-! ## The batches, the link, the wiring -/

/-- **The tree batch's slice point and slice.** -/
theorem hsA_treeG6_shape (κ a : ℕ) (hκ : 5 ≤ κ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (treeG6 κ a gate) fun o ↦ o.pt.length = κ + 6 ∧ o.s.length = 64 := by
  unfold treeG6
  refine hsA_bind (hsA_of_hs (hs_treeHeadG_shape κ a (by omega))) fun hd hhd ↦ ?_
  refine hsA_bind (hsA_layers6G_shape κ _ _ gate hg) fun cl hcl ↦ ?_
  have hpt : cl.point.length = κ - 3 := by
    rw [hcl.1]
    simp only [claim0, List.length_append, List.length_drop, List.length_take, List.length_cons, hhd.1, hhd.2]
    omega
  refine hsA_bind_n fun _ ↦ ?_
  exact hsA_bind (hsA_of_hs (hs_treeEndG_shape κ _ cl gate hκ hpt hcl.2)) fun en hen ↦ hsA_pure hen

/-- **The sponge batch's slice point, slice and scalars.** -/
theorem hsA_spG6_shape (h a : ℕ) (hh : 5 ≤ h) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (spG6 h a gate) fun o ↦ o.pt.length = h + 6 ∧ o.s.length = 64 ∧ o.v.length = 25 := by
  unfold spG6
  refine hsA_bind (hsA_of_hs (hs_spHeadG_shape h a)) fun hd hhd ↦ ?_
  refine hsA_bind (hsA_layers6G_shape h _ _ gate hg) fun cl hcl ↦ ?_
  have hpt : cl.point.length = h - 3 := by
    rw [hcl.1]
    simp only [claim0, List.length_append, List.length_drop, List.length_take, hhd.1, hhd.2.2]
    omega
  refine hsA_bind_n fun _ ↦ ?_
  exact hsA_bind (hsA_of_hs (hs_spEndG_shape h _ cl gate (by omega) hpt hcl.2)) fun en hen ↦
    hsA_pure ⟨hen.1, hen.2, hhd.2.1⟩

/-- **The link's four values.** -/
theorem hs_ksLinkG6_shape (hk xl B K₁ K₂ a : ℕ) (gate : Cell) :
    Hs c M (ksLinkG6 hk xl B K₁ K₂ a gate) fun o ↦ o.vals.length = 4 := by
  unfold ksLinkG6
  iterate 20 refine hs_bind_n fun _ ↦ ?_
  exact hs_pure (by simp)

/-- **The wiring's point** has `yVars` cells (`sc2 yVars`'s answers). -/
theorem hs_wire6_shape (Ti : Ty.TInst6) (pubC : ℕ → Cell) (v : List C2) (a : ℕ) (gate : Cell) :
    Hs c M (wire6 Ti pubC v a gate) fun o ↦ o.ry.length = Lvm.Typed.yVars := by
  unfold wire6
  iterate 5 refine hs_bind_n fun _ ↦ ?_
  refine hs_bind (hs_sc2 _ _ _) fun rf hrf ↦ ?_
  iterate 13 refine hs_bind_n fun _ ↦ ?_
  exact hs_pure (sc2_len hrf)

theorem hs_ty6_shape (Ti : Ty.TInst6) (pubC : ℕ → Cell) (ain : List C2) (yIn : C2) (own : List C2) (ownY : C2)
    (a : ℕ) (gate : Cell) :
    Hs c M (ty6 Ti pubC ain yIn own ownY a gate) fun o ↦ o.wire.ry.length = Lvm.Typed.yVars := by
  unfold ty6
  refine hs_bind_n fun _ ↦ ?_
  refine hs_bind (hs_wire6_shape _ _ _ _ _) fun wo hwo ↦ ?_
  iterate 3 refine hs_bind_n fun _ ↦ ?_
  exact hs_pure hwo

/-! ## `OutShape` -/

/-- **`node6E`'s output cells have `OutShape`'s lengths** (gate on). -/
theorem hsA_node6E_shape (Ti : Ty.TInst6) (pubC : ℕ → Cell) (ain : List C2) (yIn : C2) (own : List C2)
    (ownY : C2) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (node6E Ti pubC ain yIn own ownY gate) OutShape := by
  unfold node6E
  refine hsA_bind (hsA_treeG6_shape 18 aTree (by norm_num) gate hg) fun t ht ↦ ?_
  refine hsA_bind (hsA_spG6_shape 13 aSp (by norm_num) gate hg) fun s hs ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_ksLinkG6_shape 13 10 3816 7567 8032 aLink gate)) fun l hl ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_ty6_shape Ti pubC ain yIn own ownY aTy gate)) fun y hy ↦ ?_
  exact hsA_pure ⟨ht.1, ht.2, hs.1, hs.2.1, hs.2.2, hl, hy⟩

/-- **Residual 1 (`OutShape`) on the deployed circuit**: where the deployed families' rows and assertions hold
at `⟨nK, 0⟩` and the gate is on. -/
theorem outShape_n6 {lay : Lvm.Typed.Lay} (hOk : OkAt c M (famQ6 lay) ⟨nK, 0⟩) (hg : gateC.val M = 1) :
    OutShape (n6 lay ⟨nK, 0⟩).1 :=
  hsA_node6E_shape _ _ _ _ _ _ _ hg ⟨nK, 0⟩ (famQ6_parts hOk).1.1 (famQ6_parts hOk).1.2

end Lvm6.Node.Fin
