-- New for `flock-recursive` (stage P4a pass 3 (P4c)): controls for `FRSoundness4P4aS`/`Fin`/`S2`.
import FRSoundness4P4aZ

/-!
# Controls for pass 3

* `ZwSame`: T4's witness reads before 3 (`zwSame_zW`, +); a witness of the log's length does not
  (`not_zwSame_len`, −).
* `truthS`'s guard: past the kind's blocks a segment's truth holds (`truthS_seg_out`, +); inside
  them it is the masked `ShHoldsSeg` (`truthS_seg_in`, value).
* `shSeg`/`final_seg`: the masked successor cuts the link out of `L` (`shSeg_cut`, −) and keeps the
  others (`shSeg_link`, +).
* `eqAtR_padN`: past `2^a` the padded `eq` is `0` (`eqAtR_padN_out`, −), below it the short one (+).
* `oSh4`: with a nonzero weight the binding accepts one value (`oSh4_unique`, −); it accepts
  `c_Sh / w` (`oSh4_self`, +).
-/

namespace FR.Snd.P4a
open RecursionFast Finset FR.Impl

/-- Control (negative): a witness reading the log's length does not read before 3. -/
theorem not_zwSame_len : ¬ ZwSame fun _ _ es _ => if es.length = 0 then 0 else 1 := fun h => by
  have hS : T4.Same [] [] [] (List.replicate 3 default) 3 :=
    T4.same_of_agree [] fun p hp => by
      simp only [entAt, List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none,
        List.getElem?_replicate, if_pos hp, Option.getD_some]
  have := congrFun (h (.seg .L32) [] [] [] (List.replicate 3 default) 3 hS le_rfl) 0
  simp at this

/-- Control (positive): past the kind's blocks a segment's S truth holds (the guard; `V_A`'s
`n ≤ cap` excludes such logs from accepted runs). -/
theorem truthS_seg_out {truthSN : CKind → Log → Log → Prop} {zw : Wit} {L es : Log}
    (hn : (kindOfC es).isNode = false) (hL : 2 ^ nbC (kindOfC es) ≤ lastL es) :
    truthS truthSN zw L es := by
  simp only [truthS, hn, Bool.false_eq_true, if_false]; intro h; omega

/-- Control (value): inside the kind's blocks a segment's S truth is the masked `ShHoldsSeg`. -/
theorem truthS_seg_in {truthSN : CKind → Log → Log → Prop} {zw : Wit} {L es : Log}
    (hn : (kindOfC es).isNode = false) (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    truthS truthSN zw L es ↔ ShHoldsSeg (nbC (kindOfC es)) (lastL es)
      (zNodeC zw (kindOfC es) L es) (sbL (kindOfC es) es) (hbL (kindOfC es) es) := by
  simp only [truthS, hn, Bool.false_eq_true, if_false]; exact ⟨fun h => h hL, fun h _ => h⟩

/-- Control (negative): the masked successor has no link out of block `L`. -/
theorem shSeg_cut {nb : ℕ} (τ : Fin nb → F) (κ : F) (Lb : ℕ) : shSeg τ κ Lb (Lb + 1) = 0 := by
  simp [shSeg]

/-- Control (positive): every other link is kept. -/
theorem shSeg_link {nb : ℕ} (τ : Fin nb → F) (κ : F) {Lb y : ℕ} (hy : y ≠ Lb) :
    shSeg τ κ Lb (y + 1) = eqAtR τ y := by
  simp [shSeg, hy]

/-- Control (negative): the padded `eq` vanishes past the short point's cube. -/
theorem eqAtR_padN_out {a n : ℕ} (han : a ≤ n) (xs : List F) (hx : xs.length = a) {i : ℕ}
    (hi : i < 2 ^ n) (ha : 2 ^ a ≤ i) :
    eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i = 0 := by
  rw [eqAtR_padN han xs hx hi, if_neg (by omega)]

/-- Control (positive): below it, it is the short point's `eq`. -/
theorem eqAtR_padN_in {a n : ℕ} (han : a ≤ n) (xs : List F) (hx : xs.length = a) {i : ℕ}
    (ha : i < 2 ^ a) :
    eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i = eqAtR (ptOf a xs) i := by
  rw [eqAtR_padN han xs hx (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) han)), if_pos ha]

/-- Control (negative): with a nonzero weight the Sh binding accepts one value only. -/
theorem oSh4_unique {wNS : CKind → Log → F} {κ : CKind} {es : Log} {v v' : F}
    (hw : wSumL4 wNS κ es ≠ 0) (h : oSh4 wNS κ es v) (h' : oSh4 wNS κ es v') : v = v' :=
  mul_left_cancel₀ hw (h.symm.trans h')

/-- Control (positive): the binding accepts `c_Sh / w`. -/
theorem oSh4_self {wNS : CKind → Log → F} {κ : CKind} {es : Log} (hw : wSumL4 wNS κ es ≠ 0) :
    oSh4 wNS κ es (claimSL4 κ es / wSumL4 wNS κ es) := by
  unfold oSh4; field_simp

end FR.Snd.P4a
