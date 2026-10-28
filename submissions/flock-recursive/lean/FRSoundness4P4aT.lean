-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 S2 → RS0; stage P4a pass 4 (P4d)):
-- 3.x's `trueL_two` (`FRSoundnessFrS`) at P4b's `trueL4`.
import FRSoundness4P4aL
import FRSoundness4P4bRS

/-!
# S's claim into RS0 at revision 4.1

* **`trueL4_two`**: P4b's `trueL4` at RS claim 3 (index 2, the Sh claim at `shPtL`) is `zS2`, `ẑ`
  at S2's point `(r_blk, r_pos)`, when the witness `zw` is the unpacked `f⁽⁰⁾` of P4b's source
  (`WitOf`: at X4, `zw := T4.zW` and `R.fz := fF (kindOfC es)`, so it holds by `rfl`).
* **`pendS4_pendBad4`**: S2's doom at its end is RS0's `PendBad4` at claim 3 (3.x's
  `okF_pendS`), through `endS4`.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- **The witness is the unpacked `f⁽⁰⁾` of P4b's source** at the log's kind. -/
def WitOf (R : P4b.FSrc) (zw : Wit) : Prop :=
  ∀ L es b, zw (kindOfC es) L es b = unpack (R.fz L es (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

theorem rpL_length4 (κ : CKind) (es : Log) : (rpL κ es).length = 10 := by simp [rpL]

/-- **RS claim 3's true value is `ẑ` at S2's point** (3.x's `trueL_two`). -/
theorem trueL4_two (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {zw : Wit} (hzw : WitOf R zw)
    (L es : Log) : P4b.trueL4 R kf (kindOfC es) L es 2 = zS2 zw L es := by
  unfold zS2
  have hzw' := fun b => hzw L es b
  revert hzw'
  generalize kindOfC es = κ
  intro hzw'
  have hm : κ.m = nbC κ + 14 := by unfold nbC; rcases κ.m_mem with h | h | h <;> omega
  have hP0 : κ.m - 7 = nbC κ + 7 := by omega
  set xS := P4b.xSL4 κ es
  set sP := shPtL κ.m es
  have hxS : xS.length = 7 := by simp [xS, P4b.xSL4]
  have hsP : sP.length = nbC κ + 7 := by simp [sP, shPtL]; omega
  have hcw : ∀ i : Fin 128, P4b.cwL4 κ es ((2 : Fin 4) : ℕ) i = eqAtR (ptOf 7 xS) i := by
    intro i
    rw [P4b.cwL4, show ((2 : Fin 4) : ℕ) = 2 from rfl, cwF]
    change (eqTab xS.toArray).getD i 0 = _
    rw [eqTab_getD _ (by simp [hxS]), List.size_toArray, hxS, eqBits, bitSel,
      eqAtR, ← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun l _ => ?_
    simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hg : ∀ u : Fin (2 ^ (κ.m - 7)), P4b.gL4 kf κ es 2 u = eqAtR (ptOf (κ.m - 7) sP) u := by
    intro u
    have hl : (P4b.rsPtsL4 κ es).getD 2 [] = sP := by cases κ <;> rfl
    have h2 : (2 : ℕ) < (P4b.rsPtsL4 κ es).length := by
      rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num
    have h2' : ((2 : Fin 4) : ℕ) = 2 := rfl
    rw [P4b.gL4, h2', if_pos h2, if_neg (show (2 : ℕ) ≠ 1 by norm_num), mul_one, hl,
      eqPts_eq _ _ (hsP.trans hP0.symm) (by simp [bitsL, hsP, hP0]), hsP, ← hP0,
      ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (κ.m - 7))),
      algebraMap F F (P4b.rsQ4 R L es (κ.m - 7) i u) = zw κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [P4b.rsQ4, hzw', Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  have step1 : P4b.trueL4 R kf κ L es 2 = ∑ u ∈ range (2 ^ (nbC κ + 7)), ∑ i ∈ range (2 ^ 7),
      eqAtR (ptOf 7 xS) i * eqAtR (ptOf (nbC κ + 7) sP) u * zw κ L es (i + 2 ^ 7 * u) := by
    unfold P4b.trueL4
    simp only [hcw, hg, hq, mul_sum]
    rw [sum_comm, hP0]
    rw [Fin.sum_univ_eq_sum_range (fun y => ∑ x : Fin 128, eqAtR (ptOf 7 xS) x *
      (eqAtR (ptOf (nbC κ + 7) sP) y * zw κ L es (x + 2 ^ 7 * y)))]
    refine sum_congr rfl fun y _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun x => eqAtR (ptOf 7 xS) x *
      (eqAtR (ptOf (nbC κ + 7) sP) y * zw κ L es (x + 2 ^ 7 * y)))]
    exact sum_congr rfl fun x _ => by ring
  have hP7 : ptOf 7 (xS ++ sP) = ptOf 7 xS := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < xS.length by rw [hxS]; exact l.isLt)]
  have hPd : (xS ++ sP).drop 7 = sP := by rw [List.drop_left' hxS]
  have step2 : P4b.trueL4 R kf κ L es 2 = ∑ b ∈ range (2 ^ (14 + nbC κ)),
      eqAtR (ptOf (14 + nbC κ) (xS ++ sP)) b * zw κ L es b := by
    rw [step1, show 14 + nbC κ = 7 + (nbC κ + 7) by omega, sum_eqAtR_split, hP7, hPd]
  rw [step2, sum_eqAtR_split]
  have hD : (xS ++ sP).drop 14 = rbL κ es := by
    rw [show (14 : ℕ) = 7 + 7 from rfl, ← List.drop_drop, hPd]
    simp only [sP, shPtL]
    rw [List.drop_left' (by simp)]; rfl
  have hpre : xS ++ (List.range 3).map (fun l => rch 114 es (κ.m - 7 + l)) = rpL κ es := by
    rw [rpL, show (10 : ℕ) = 7 + 3 from rfl, List.range_add, List.map_append, List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun l _ => ?_)
    simp only [Function.comp_apply]; congr 1; omega
  have h14 : ptOf 14 (xS ++ sP) = ptOf 14 (rpL κ es ++ [0, 0, 0, 0]) := by
    have he : xS ++ sP = (rpL κ es ++ [0, 0, 0, 0]) ++ (List.range (κ.m - 14)).map (rch 114 es) := by
      rw [← hpre]; simp only [sP, shPtL, List.append_assoc]; rfl
    rw [he]; funext l
    simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_append_left
      (show l.val < (rpL κ es ++ [0, 0, 0, 0]).length by simp [rpL_length4])]
  have hQ10 : ptOf 10 (rpL κ es ++ [0, 0, 0, 0]) = ptOf 10 (rpL κ es) := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < (rpL κ es).length by
        rw [rpL_length4]; exact l.isLt)]
  have hQd : (rpL κ es ++ [0, 0, 0, 0]).drop 10 = [0, 0, 0, 0] :=
    List.drop_left' (rpL_length4 κ es)
  rw [hD, h14]
  have inner : ∀ y ∈ range (2 ^ nbC κ), ∑ x ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rpL κ es ++ [0, 0, 0, 0])) x * eqAtR (ptOf (nbC κ) (rbL κ es)) y *
        zw κ L es (x + 2 ^ 14 * y) = ∑ q ∈ range (2 ^ 10),
      eqAtR (ptOf (nbC κ) (rbL κ es)) y * eqAtR (ptOf 10 (rpL κ es)) q * zNodeC zw κ L es y q := by
    intro y _
    simp only [mul_assoc]
    rw [show (14 : ℕ) = 10 + 4 from rfl, sum_eqAtR_split, hQ10, hQd]
    rw [sum_eq_single 0]
    · simp only [eqAtR_zeros4 (show 0 < 16 by norm_num), if_true, mul_one, mul_zero, add_zero]
      refine sum_congr rfl fun q _ => ?_
      simp only [zNodeC, show y * 2 ^ 14 + q = q + 2 ^ (10 + 4) * y by ring]
      ring
    · intro h hh h0
      rw [eqAtR_zeros4 (mem_range.1 hh), if_neg h0]
      simp
    · intro h; exact absurd (mem_range.2 (by norm_num)) h
  rw [sum_congr rfl inner, sum_comm]

/-- **At S2's end its doom is RS0's `PendBad4` at claim 3** (3.x's `okF_pendS`): the Sh binding
`oSh4` fails at claim 3's true value. -/
theorem pendS4_pendBad4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F)
    {oZ oLc : CKind → Log → F → Prop} {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit}
    {wNS : CKind → Log → F} (hzw : WitOf R zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es))
    (h : D2S wN zw L es) (hl : 170 ≤ es.length) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ oLc (oSh4 wNS)) L es := by
  refine ⟨2, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => endS4 hNS hL h hl ?_⟩
  have ho' : oSh4 wNS (kindOfC es) es (P4b.trueL4 R kf (kindOfC es) L es 2) := ho
  rwa [trueL4_two R kf hzw] at ho'

end FR.Snd.P4a
