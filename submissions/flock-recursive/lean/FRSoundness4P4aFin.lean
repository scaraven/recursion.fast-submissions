-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.8 `targetS`, A.9 `finSh`; stage P4a pass 3 (P4c)).
import FRSoundness4P4aS

/-!
# A segment's finals on the specifications: `finSh` (ii) and Z2's `P^e` (B-12)

* **`eqAtR_padN`**: `eq` at a point zero-padded from `a` to `n` coordinates is `eq` at the short
  point on `[0, 2^a)` and `0` past it. Both bridges below sum the padded coordinates out with it.
* **`final_seg`**: a segment's S2 weight (`wSeg`, the successor masked at `L`) has extension
  `E·slotW₀ + (Sh + κ_s·E₀)·slotW₁` at S2's point, with `(E, Sh, E₀)` the segment's `shiftMask`
  specification (`Rev4.shiftSegS`) at the padded points and `L`'s bits (3.x's `final_leaf`).
  **`wSumSeg`** is that value on the log, **`wSumSeg_eq`** the extension of `wS` at `rbL`, `rpL`.
  `claimSL4`, **`oSh4`** (`finSh` (ii)'s binding `c_Sh = (w_out + w_in)·v`; a node's weight value
  `wNS` is a parameter).
* **`peL_seg`**: Z2's `P^e` at a segment is `Rev4.targetSSegS` at the verifier's operand (Z1's
  `m − 13` coordinates zero-padded to 19 entries, then `L`'s bits).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## `eq` at a zero-padded point -/

theorem eqAtR_padN {a n : ℕ} (han : a ≤ n) (xs : List F) (hx : xs.length = a) {i : ℕ}
    (hi : i < 2 ^ n) :
    eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i = if i < 2 ^ a then eqAtR (ptOf a xs) i else 0 := by
  set g : ℕ → F := fun l => if i.testBit l then (xs ++ List.replicate (n - a) 0).getD l 0
    else 1 - (xs ++ List.replicate (n - a) 0).getD l 0
  have hp : ∀ l, (xs ++ List.replicate (n - a) 0).getD l 0 = if l < a then xs.getD l 0 else 0 :=
    fun l => by
      simp only [List.getD_eq_getElem?_getD]
      split_ifs with h
      · rw [List.getElem?_append_left (by omega)]
      · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
        split_ifs <;> rfl
  have e : eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i = ∏ l ∈ range n, g l :=
    Fin.prod_univ_eq_prod_range g n
  rw [e, ← prod_range_mul_prod_Ico _ han]
  split_ifs with hia
  · have h1 : ∏ l ∈ Ico a n, g l = 1 := prod_eq_one fun l hl => by
      have ht : i.testBit l = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hia (Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 hl).1))
      simp only [g, hp, ht, if_neg (show ¬ l < a by have := (mem_Ico.1 hl).1; omega)]; simp
    rw [h1, mul_one]
    refine (prod_congr rfl fun l hl => ?_).trans
      (Fin.prod_univ_eq_prod_range (fun l => if i.testBit l then xs.getD l 0 else 1 - xs.getD l 0) a).symm
    simp only [g, hp, if_pos (mem_range.1 hl)]
  · obtain ⟨l, hl, hb⟩ : ∃ l ∈ Ico a n, i.testBit l = true := by
      by_contra hc
      push Not at hc
      refine hia (Nat.lt_pow_two_of_testBit i fun l hl => ?_)
      by_cases hln : l < n
      · simpa using hc l (mem_Ico.2 ⟨hl, hln⟩)
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [prod_eq_zero hl (by simp only [g, hp, hb, if_true, if_neg (show ¬ l < a by
      have := (mem_Ico.1 hl).1; omega)]), mul_zero]

/-- **Summing over a zero-padded point** is summing over the short point. -/
theorem sum_eqAtR_padN {a n : ℕ} (han : a ≤ n) (xs : List F) (hx : xs.length = a) (g : ℕ → F) :
    ∑ i ∈ range (2 ^ n), eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i * g i =
      ∑ i ∈ range (2 ^ a), eqAtR (ptOf a xs) i * g i := by
  rw [sum_congr rfl fun i hi => by rw [eqAtR_padN han xs hx (mem_range.1 hi)]]
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext i; simp only [mem_filter, mem_range]
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) han
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-! ## `finSh` (ii) at a segment -/

/-- The masked successor is the unmasked one plus the link at `L` (characteristic two). -/
theorem shSeg_eq {nb : ℕ} (τ : Fin nb → F) (κ : F) (Lb y : ℕ) :
    shSeg τ κ Lb y = shL τ κ y + if y = Lb + 1 then eqAtR τ Lb else 0 := by
  unfold shSeg shL
  by_cases h : y = Lb + 1
  · subst h
    have h1 : ¬ (1 ≤ Lb + 1 ∧ Lb + 1 - 1 ≠ Lb) := by omega
    have h2 : 1 ≤ Lb + 1 := by omega
    rw [if_neg h1, if_pos h2, if_pos rfl, Nat.add_sub_cancel]
    linear_combination (-(eqAtR τ Lb)) * CharTwo.two_eq_zero (R := F)
  · rw [if_neg h, add_zero]
    by_cases h1 : 1 ≤ y
    · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
    · rw [if_neg (by omega), if_neg h1]

theorem eqPoint_zero18 (rb : List F) (hrb : rb.length = 18) :
    eqPoint (Array.replicate 18 0) rb.toArray = eqAtR (ptOf 18 rb) 0 := by
  have h := eq_zero_pt rb hrb
  rwa [show (List.replicate 18 (0 : F)).toArray = Array.replicate 18 0 from rfl] at h

/-- **A segment's final value** (A.9 `finSh` (ii) with B-12's `shiftMask`): the masked weight's
extension at `(r_blk, r_pos)` is `E·slotW₀ + (Sh + κ_s E₀)·slotW₁` on `shiftSegS` at the padded
points and the operand's last block `L`. -/
theorem final_seg {nb : ℕ} (hnb : nb ≤ 18) (τs rb bits : List F) (hτ : τs.length = nb)
    (hrb : rb.length = nb) {Lb : ℕ} (hL : Lb < 2 ^ nb)
    (hbits : Rev4.lastAt (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray 18 = Lb)
    (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb),
        eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q =
      (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
          (rb ++ List.replicate (18 - nb) 0).toArray).1 * slotWS 0 θ rp +
        ((Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.1 +
          κ * (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.2) * slotWS 1 θ rp := by
  set τP := τs ++ List.replicate (18 - nb) 0
  set rP := rb ++ List.replicate (18 - nb) 0
  have hτP : τP.length = 18 := by simp [τP, hτ]; omega
  have hrP : rP.length = 18 := by simp [rP, hrb]; omega
  have hA : ptA 18 (τP ++ bits).toArray = ptOf 18 τP := funext fun l => by
    simp only [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.val < τP.length by omega)]
  have hB : ptA 18 rP.toArray = ptOf 18 rP := ptA_toArray _ _
  -- the three components
  have h1 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).1 = eqPoint τP.toArray rP.toArray := by
    rw [eqPoint_eq, List.size_toArray, hτP, ptA_toArray, ptA_toArray]
    simp only [Rev4.shiftSegS, hA, hB]
  have hmle : shiftMle 18 (ptOf 18 τP) (ptOf 18 rP) = shiftEqS τP.toArray rP.toArray := by
    rw [← shiftEq_meets _ _ (by simp [hτP, hrP]), shiftEqI, List.toList_toArray, List.toList_toArray,
      shiftPair_eq 18 τP rP hτP hrP]
  have hc : (if Lb + 1 < 2 ^ 18 then eqAtR (ptOf 18 τP) Lb * eqAtR (ptOf 18 rP) (Lb + 1) else 0) =
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    have h18 : 2 ^ nb ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hnb
    rw [eqAtR_padN hnb τs hτ (by omega), if_pos hL]
    by_cases h : Lb + 1 < 2 ^ nb
    · rw [if_pos (by omega), if_pos h, eqAtR_padN hnb rb hrb (by omega), if_pos h]
    · rw [if_neg h]
      split_ifs with h'
      · rw [eqAtR_padN hnb rb hrb h', if_neg h, mul_zero]
      · rfl
  have h2 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.1 = shiftEqS τP.toArray rP.toArray +
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    simp only [Rev4.shiftSegS, hA, hB, hbits, hmle]
    rw [← hc]
  have h3 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.2 =
      eqPoint (Array.replicate 18 0) rP.toArray := by
    rw [eqPoint_zero18 rP hrP]; simp only [Rev4.shiftSegS, hB]
  rw [h1, h2, h3]
  -- the masked weight is the leaf weight plus the link at `L`
  have hw : ∀ y q, wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q = wLeaf (ptOf nb τs) (ptA 10 θ) κ y q +
      (if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) * slotT (ptA 10 θ) 520 q := fun y q => by
    simp only [wSeg, wLeaf, shSeg_eq]; ring
  simp only [hw, mul_add, sum_add_distrib]
  rw [final_leaf hnb τs rb hτ hrb θ rp κ]
  have hlink : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
      eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
        slotT (ptA 10 θ) 520 q) =
      (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
        slotWS 1 θ rp := by
    have e : ∀ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
        eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
          slotT (ptA 10 θ) 520 q) =
        (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
          (eqAtR (ptA 10 rp) q * slotT (ptA 10 θ) 520 q) := fun q _ => by
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_range]
      split_ifs <;> ring
    rw [sum_congr rfl e, ← mul_sum, sum_slot_eqAtR _ _ (by norm_num), slotWS_eq]
    rfl
  rw [hlink]
  ring

/-! ## The segment's weight value on the log -/

/-- The segment's masked-shift operand `τ ‖ 0 ‖ L` (`gFinSh`'s first `packFK`). -/
def tauLL (κ : CKind) (es : Log) : Array F :=
  (tauL κ es ++ List.replicate (18 - nbC κ) 0 ++ lastBits es).toArray

/-- **`w_out + w_in` on the log at a segment** (A.9 `finSh` (ii) with `shiftSegS`). -/
def wSumSeg (κ : CKind) (es : Log) : F :=
  (Rev4.shiftSegS (tauLL κ es) (pad18 κ (rbL κ es))).1 * slotWS 0 (thL es).toArray (rpL κ es).toArray +
    ((Rev4.shiftSegS (tauLL κ es) (pad18 κ (rbL κ es))).2.1 +
      ksL es * (Rev4.shiftSegS (tauLL κ es) (pad18 κ (rbL κ es))).2.2) *
      slotWS 1 (thL es).toArray (rpL κ es).toArray

theorem sum_bits_self (n N : ℕ) (h : N < 2 ^ n) :
    (∑ l ∈ range n, if N.testBit l then 2 ^ l else 0) = N :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_sum_bits (fun l => N.testBit l) n j]
    by_cases hj : j < n
    · simp [hj]
    · simp [hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num)
        (by omega : n ≤ j)))]

/-- **The operand's last block is `lastL`.** -/
theorem lastAt_tauLL (κ : CKind) (es : Log) : Rev4.lastAt (tauLL κ es) 18 = lastL es := by
  have hl : (tauL κ es ++ List.replicate (18 - nbC κ) 0).length = 18 := by
    simp [tauL]; have := nbC_le κ; omega
  unfold Rev4.lastAt tauLL
  have e : ∀ l ∈ range 18, (if (tauL κ es ++ List.replicate (18 - nbC κ) 0 ++ lastBits es).toArray.getD
      (18 + l) 0 = 1 then 2 ^ l else 0) = if (lastL es).testBit l then 2 ^ l else 0 := fun l hl' => by
    have hl'' := mem_range.1 hl'
    have hg : (tauL κ es ++ List.replicate (18 - nbC κ) 0 ++ lastBits es).toArray.getD (18 + l) 0 =
        (lastBits es).getD l 0 := by
      simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show (tauL κ es ++ List.replicate (18 - nbC κ) 0).length ≤ 18 + l
          by omega), hl, Nat.add_sub_cancel_left]
    rw [hg, lastBits_getD es hl'']
    split_ifs <;> simp_all
  rw [sum_congr rfl e, sum_bits_self 18 _ (lastL_lt es)]

section WSum
variable (wN : CKind → Log → ℕ → ℕ → F)

/-- **A segment's weight value is the extension of `wS` at S2's point.** -/
theorem wSumSeg_eq {es : Log} (hn : (kindOfC es).isNode = false)
    (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    wSumSeg (kindOfC es) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
      eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wS wN (kindOfC es) es y q := by
  generalize hκ : kindOfC es = κ at hn hL
  have hθ : ptA 10 (thL es).toArray = ptOf 10 (thL es) := ptA_toArray _ _
  have hr : ptA 10 (rpL κ es).toArray = ptOf 10 (rpL κ es) := ptA_toArray _ _
  have hτ : (tauL κ es).length = nbC κ := by simp [tauL]
  have hrb : (rbL κ es).length = nbC κ := by simp [rbL]
  have e := final_seg (nbC_le κ) (tauL κ es) (rbL κ es) (lastBits es) hτ hrb hL
    (lastAt_tauLL κ es) (thL es).toArray (rpL κ es).toArray (ksL es)
  rw [hθ, hr] at e
  simp only [wS, hn, Bool.false_eq_true, if_false]
  rw [e]
  rfl

end WSum

/-- **The Sh weight value by kind**: a segment's `wSumSeg`, a node's `wNS` (S-E's, a parameter). -/
def wSumL4 (wNS : CKind → Log → F) (κ : CKind) (es : Log) : F :=
  if κ.isNode then wNS κ es else wSumSeg κ es

/-- S2's last claim (after the kind's `nb + 10` rounds). -/
def claimSL4 (κ : CKind) (es : Log) : F :=
  clR2 114 16 readF (fun d => chF d 0) c0SL [] es (nrS κ)

/-- **The Sh claim's binding** (A.9 `finSh` (ii)): `c_Sh = (w_out + w_in)·v` (P4b's `oSh`). -/
def oSh4 (wNS : CKind → Log → F) (κ : CKind) (es : Log) (v : F) : Prop :=
  claimSL4 κ es = wSumL4 wNS κ es * v

/-! ## Z2's `P^e` at a segment -/

theorem peL_range4 (M : ZLM4) (es : Log) (σ : Fin 64) : peL M es σ =
    ∑ u ∈ range (2 ^ mC 6 (kindOfC es)), eqAtR (ptOf (mC 6 (kindOfC es)) (zrL es)) u *
      M.Et (kindOfC es) es (u / 256) (pAt σ u) := by
  unfold peL eZ
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf (mC 6 (kindOfC es)) (zrL es)) u *
    M.Et (kindOfC es) es (u / 256) (pAt σ u))]
  exact sum_congr rfl fun u _ => by rw [eq_cube_eqAtR]

theorem zrL_length (es : Log) : (zrL es).length = mC 6 (kindOfC es) := by
  have := CKind.m_mem (kindOfC es)
  simp only [zrL, List.length_append, List.length_ofFn, List.length_map, List.length_range, mC]
  omega

theorem zrL_getD4 (es : Log) (l : ℕ) (hl : l < mC 6 (kindOfC es)) :
    (zrL es).getD l 0 = if h : l < 7 then pinnedRho ⟨l, h⟩ else coordAt es 2 (l - 7) := by
  have hm := CKind.m_mem (kindOfC es)
  unfold zrL
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
      List.getElem?_ofFn, dif_pos h, Option.getD_some]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_map, List.getElem?_range (show l - 7 < (kindOfC es).m - 13 by
      unfold mC at hl; omega), Option.map_some, Option.getD_some]

/-- **The segment operand's point is Z1's, zero-padded to 26 coordinates.** -/
theorem segPt_eq {es : Log} {r : Array F}
    (hr : ∀ l < (kindOfC es).m - 13, r.getD l 0 = coordAt es 2 l)
    (hz : ∀ l, (kindOfC es).m - 13 ≤ l → l < 19 → r.getD l 0 = 0) :
    Fin.append (zLo r) (Rev4.blkOf r) =
      ptOf (8 + 18) (zrL es ++ List.replicate (8 + 18 - mC 6 (kindOfC es)) 0) := by
  have hm := CKind.m_mem (kindOfC es)
  have hlen := zrL_length es
  have hp : ∀ l, (zrL es ++ List.replicate (8 + 18 - mC 6 (kindOfC es)) 0).getD l 0 =
      if l < mC 6 (kindOfC es) then (zrL es).getD l 0 else 0 := fun l => by
    simp only [List.getD_eq_getElem?_getD]
    split_ifs with h
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
      split_ifs <;> rfl
  funext l
  refine Fin.addCases (m := 8) (n := 18) (fun i => ?_) (fun i => ?_) l
  · rw [Fin.append_left]
    simp only [ptOf, Fin.coe_castAdd, hp, if_pos (show i.val < mC 6 (kindOfC es) by
      unfold mC; omega), zrL_getD4 es i.val (by unfold mC; omega), zLo]
    split_ifs with h
    · rfl
    · rw [hr 0 (by omega)]; congr 1; omega
  · rw [Fin.append_right]
    simp only [ptOf, Fin.coe_natAdd, hp, Rev4.blkOf]
    split_ifs with h
    · rw [zrL_getD4 es _ h, dif_neg (by omega), hr (1 + i.val) (by unfold mC at h; omega)]
      congr 1; omega
    · exact hz (1 + i.val) (by unfold mC at h; omega) (by omega)

/-- **A segment's `P^e` is `targetSSegS`** at the verifier's operand (Z1's coordinates, zeros to
entry 18, `L`'s bits from 19; B-12's range factor). -/
theorem peL_seg {indN : Rev4.NodeKind → Fin 9 → ℕ → F} {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F}
    {es : Log} (hn : (kindOfC es).isNode = false) {r : Array F}
    (hr : ∀ l < (kindOfC es).m - 13, r.getD l 0 = coordAt es 2 l)
    (hz : ∀ l, (kindOfC es).m - 13 ≤ l → l < 19 → r.getD l 0 = 0)
    (hL : Rev4.lastAt r 19 = lastL es) :
    Rev4.targetSSegS r = Array.ofFn (peL (zlm4 indN etN) es) := by
  have hm := CKind.m_mem (kindOfC es)
  unfold Rev4.targetSSegS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [targetS_range _ _ σ (fun u => if u / 256 ≤ Rev4.lastAt r 19 then chainE (σ + 64 * (u % 256))
      else 0) fun _ => rfl, segPt_eq hr hz, peL_range4]
  rw [sum_eqAtR_padN (show mC 6 (kindOfC es) ≤ 8 + 18 by unfold mC; omega) _ (zrL_length es), hL]
  refine sum_congr rfl fun u _ => ?_
  generalize hκ : kindOfC es = κ at hn
  rcases κ with κ | κ
  · simp only [zlm4, EtSeg, pAt]
  · simp [CKind.isNode] at hn

end FR.Snd.P4a
