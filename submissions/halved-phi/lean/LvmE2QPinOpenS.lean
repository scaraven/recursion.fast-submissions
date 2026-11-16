-- New for lvm2 E2-FT (E2F-QH5): `C_main`'s opening at S2GF in the small shape, circuit side: the term pairs of the
-- regular `E2` claims (`halfTermsZ_spec`, `rowPairZ_spec`: big keys on the block, moved keys on the block moved down,
-- one leaf), on the pattern of `LvmQShapeB.rgPair_spec`.
import LvmE2QPinOpenZ

/-!
# The small shape's term pairs

* `pairT_spec`: a pair on a regular block with any leaf: the big term is `sc·eqAbove_blk(x)·leaf`, the moved one
  `sc·eqAbove_{blk − 3·2^20}(x)·leaf`;
* **`halfTermsZ_spec`**: a regular half's pairs sum to `sc·(halfB …).onStack(x)` (big) and `sc·Σ (shiftB part)` (moved);
* **`rowPairZ_spec`**: a regular row claim's pair: `sc·bc.onStack(x)` and `sc·(shiftB bc).onStack(x)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape

variable {c : Ctx} {M : Mem}

/-- The pair of a leaf on a regular block. -/
def pairOf (sc lf : Cell) (blk : Placement) : ZT :=
  ⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩

theorem pairT_spec (xb : ℕ) {blk : Placement} (hr : RegP blk) (sc lf : Cell) :
    tval M (fun i ↦ M.e (xb + i)) CMain.nu20 (pairOf sc lf blk).big =
        sc.val M * (blk.eqAbove (xsOf M CMain.nu20 xb) * lf.val M) ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 (pairOf sc lf blk).sml =
        sc.val M * ((shiftP blk).eqAbove (xsOf M CMain.nu20 xb) * lf.val M) ∧
      (pairOf sc lf blk).pb.length = CMain.nu20 - 20 ∧ (pairOf sc lf blk).ps.length = CMain.nu20 - 20 := by
  have hnu : CMain.nu20 = 23 := rfl
  have hv := hr.1
  refine ⟨?_, ?_, topK_length _, topK_length _⟩
  · simp only [pairOf, ZT.big]
    rw [← keyOf_top _ hv, tval, kprod_keyOf, eqAbove_prod blk _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length]; omega) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length]
    ring
  · simp only [pairOf, ZT.sml]
    rw [keyOf_congr (selbit blk) (selbit (shiftP blk)) _ 20 (fun i h1 h2 ↦ (selbit_shift_lo blk hr h1 h2).symm),
      ← keyOf_top _ hv, tval, kprod_keyOf, eqAbove_prod (shiftP blk) _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length, shiftP_vc]; omega) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length, shiftP_vc]
    ring

/-- **The pairs of a regular half's parts** (`halfTerms … true`): big `sc·Σ eqAbove_blk·coord(wordW·c)`, moved
`sc·Σ eqAbove_{shifted blk}·coord(wordW·c)`, no plain terms. -/
theorem halfTermsZ_spec {F : FCtx} (hF : FCtxOk M F) {xb : ℕ} (sc : Cell) (h : Bool) :
    ∀ (parts : List (C2 × Placement × List C2)) (m6 : Memo6),
      (∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧ RegP e.2.1) →
      Memo6Ok M xb m6 →
      Hs c M (halfTerms F CMain.nu20 xb sc h true parts m6) (fun r => Memo6Ok M xb r.1 ∧ r.2.2 = [] ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum =
          sc.val M * (partsV M parts |>.map fun e => (partH h e).onStack.1 (xsOf M CMain.nu20 xb)).sum ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum =
          sc.val M * (partsV M parts |>.map fun e => (shiftB (partH h e)).onStack.1 (xsOf M CMain.nu20 xb)).sum ∧
        ∀ t ∈ r.2.1, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], m6, _, hm => hs_pure ⟨hm, rfl, by simp [partsV], by simp [partsV], by simp⟩
  | (cv, blk, zl) :: ps, m6, hp, hm => by
    obtain ⟨hcK, hzK, hzl, hreg⟩ : KC2 cv ∧ (∀ x ∈ zl, KC2 x) ∧ zl.length = blk.variableCount ∧ RegP blk :=
      hp _ (List.mem_cons_self ..)
    have hnu : CMain.nu20 = 23 := rfl
    have hvc : blk.variableCount ≤ CMain.nu20 := by have := hreg.1; omega
    unfold halfTerms
    refine hs_bind (w6Leaf_spec hF.z hF.o xb cv zl hcK hzK m6 hm) fun r ⟨hm', hr⟩ => ?_
    refine hs_bind (halfTermsZ_spec hF sc h ps r.1 (fun e he => hp e (List.mem_cons_of_mem _ he)) hm')
      fun rs ⟨hm'', hn, hb, hs, hl⟩ => ?_
    simp only [ite_true]
    have hlf : (if h then r.2.2 else r.2.1).val M =
        c6 h (FE6.mul (wordWD (zl.map (C2.val M)) ((xsOf M CMain.nu20 xb).take blk.variableCount))
          (FE6.ofE2 (cv.val M))) := by
      have hW : wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M)) =
          wordWD (zl.map (C2.val M)) ((xsOf M CMain.nu20 xb).take blk.variableCount) := by
        rw [wordF_eq_wordWD, xs_take CMain.nu20 xb _ hvc, List.length_map, hzl]
      rw [← hW, ← hr]
      cases h <;> rfl
    obtain ⟨pb, ps', l1, l2⟩ := pairT_spec (M := M) xb hreg sc (if h then r.2.2 else r.2.1)
    refine hs_pure ⟨hm'', hn, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, show (⟨sc, if h then r.2.2 else r.2.1, topK (selbit blk),
        topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ : ZT).big =
        (pairOf sc (if h then r.2.2 else r.2.1) blk).big from rfl, pb, hb]
      simp only [partsV, List.map_cons, List.sum_cons]
      rw [hlf]
      simp only [partH, BlockClaim.onStack]
      ring
    · rw [List.map_cons, List.sum_cons, show (⟨sc, if h then r.2.2 else r.2.1, topK (selbit blk),
        topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ : ZT).sml =
        (pairOf sc (if h then r.2.2 else r.2.1) blk).sml from rfl, ps', hs]
      simp only [partsV, List.map_cons, List.sum_cons]
      rw [hlf]
      simp only [partH, shiftB, BlockClaim.onStack, shiftP_vc]
      ring
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨l1, l2⟩
      · exact hl t ht

end Lvm.Q2
