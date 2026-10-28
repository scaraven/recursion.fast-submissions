-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.9 `finSh` (i), A.10 S1/S2; stage P4a pass 2).
import FRSoundness4P4aCtrl
import FRSoundness4TailFold

/-!
# A segment's S bridges: `L`'s bits, S2's initial claim, S2's true sum

* **`testBit_lastL`**: bit `k < 18` of `lastL es` is `lastOps`' `L_k` (`lb`); so `lastBits` are the
  cube bits of `lastL` (**`lastBits_getD`**).
* **`eq_pad_last`**: `eq` at an 18-coordinate point zero-padded from `nb` and the bits of `L < 2^nb`
  is `eqAtR τ L`.
* **`c0S_seg`**: a segment's S2 initial claim (`shiftTargetS` on `bnd ‖ L`) is
  `eq(τ, L)·h̃(θ) + κ_s·s̃(θ)` (3.x's `c0S_eq` with the end at `L`).
-/

namespace FR.Snd.P4a
open RecursionFast Finset FR.Impl

/-! ## The bits of `L` -/

theorem sum_bits_lt (b : ℕ → Bool) : ∀ n, (∑ k ∈ range n, if b k then 2 ^ k else 0) < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, pow_succ]; have := sum_bits_lt b n; split_ifs <;> omega

theorem testBit_sum_bits (b : ℕ → Bool) : ∀ n j,
    (∑ k ∈ range n, if b k then 2 ^ k else 0).testBit j = (decide (j < n) && b j)
  | 0, j => by simp
  | n + 1, j => by
    have e : (∑ k ∈ range (n + 1), if b k then 2 ^ k else 0) =
        2 ^ n * (if b n then 1 else 0) + ∑ k ∈ range n, if b k then 2 ^ k else 0 := by
      rw [sum_range_succ]; split_ifs <;> ring
    rw [e, Nat.testBit_two_pow_mul_add _ (sum_bits_lt b n), testBit_sum_bits b n]
    by_cases h : j < n
    · rw [if_pos h]; simp [h, show j < n + 1 by omega]
    · rw [if_neg h]
      obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by omega⟩
      rw [Nat.add_sub_cancel_left]
      rcases d with _ | d
      · cases b n <;> simp
      · cases b n <;> simp [Nat.testBit_succ]

/-- **Bit `k` of `L` is `lastOps`' `L_k`.** -/
theorem testBit_lastL (es : Log) {k : ℕ} (hk : k < 18) : (lastL es).testBit k = lb (nStmt es) k := by
  have h := testBit_sum_bits (fun j => lb (nStmt es) j) 18 k
  rw [decide_eq_true hk, Bool.true_and, ← lastL_sum] at h
  exact h

theorem lastL_lt (es : Log) : lastL es < 2 ^ 18 := Nat.mod_lt _ (by norm_num)

/-- `lastBits` are the cube bits of `lastL`. -/
theorem lastBits_getD (es : Log) {k : ℕ} (hk : k < 18) :
    (lastBits es).getD k 0 = if (lastL es).testBit k then 1 else 0 := by
  rw [testBit_lastL es hk, lastBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rfl

/-! ## `eq` at the padded point and `L` -/

theorem pad_getD {nb : ℕ} (τ : List F) (hτ : τ.length = nb) (l : ℕ) :
    (τ ++ List.replicate (18 - nb) 0).getD l 0 = if l < nb then τ.getD l 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
    split_ifs <;> rfl

/-- **`eq((τ ‖ 0), bits L) = eq(τ, L)`** for `L < 2^nb`. -/
theorem eq_pad_last {nb : ℕ} (hnb : nb ≤ 18) (τ : List F) (hτ : τ.length = nb) {Lb : ℕ}
    (hL : Lb < 2 ^ nb) :
    eq (ptOf 18 (τ ++ List.replicate (18 - nb) 0))
        (fun l : Fin 18 => if Lb.testBit l then 1 else 0) = eqAtR (ptOf nb τ) Lb := by
  set g : ℕ → F := fun l => (τ ++ List.replicate (18 - nb) 0).getD l 0 *
      (if Lb.testBit l then 1 else 0) +
    (1 - (τ ++ List.replicate (18 - nb) 0).getD l 0) * (1 - if Lb.testBit l then 1 else 0)
  set h : ℕ → F := fun l => if Lb.testBit l then τ.getD l 0 else 1 - τ.getD l 0
  calc eq (ptOf 18 (τ ++ List.replicate (18 - nb) 0)) (fun l : Fin 18 => if Lb.testBit l then 1 else 0)
      = ∏ l : Fin 18, g l := rfl
    _ = ∏ l ∈ range 18, g l := Fin.prod_univ_eq_prod_range g 18
    _ = ∏ l ∈ range nb, g l := by
        rw [← prod_range_mul_prod_Ico _ hnb]
        have h1 : ∏ l ∈ Ico nb 18, g l = 1 := by
          refine prod_eq_one fun l hl => ?_
          have hl' := (mem_Ico.1 hl).1
          have ht : Lb.testBit l = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) hl'))
          simp only [g, pad_getD τ hτ, ht, if_neg (show ¬ l < nb by omega)]; simp
        rw [h1, mul_one]
    _ = ∏ l ∈ range nb, h l := by
        refine prod_congr rfl fun l hl => ?_
        have hl' := mem_range.1 hl
        simp only [g, h, pad_getD τ hτ, if_pos hl']
        split_ifs <;> ring
    _ = eqAtR (ptOf nb τ) Lb := (Fin.prod_univ_eq_prod_range h nb).symm

/-! ## S2's initial claim at a segment -/

theorem nbC_le (κ : CKind) : nbC κ ≤ 18 := by
  unfold nbC; rcases κ.m_mem with h | h | h <;> omega

/-- **A segment's S2 initial claim**: `eq(τ, L)·h̃(θ) + κ_s·s̃(θ)` (the end at block `L`). -/
theorem c0S_seg {es : Log} (hn : (kindOfC es).isNode = false)
    (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    c0S es = eqAtR (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (lastL es) *
        thS (ptOf 10 (thL es)) (hbL (kindOfC es) es) +
      ksL es * thS (ptOf 10 (thL es)) (sbL (kindOfC es) es) := by
  rw [c0S, pad18, shiftTargetS, shiftTargetAt, ptA_toArray, ptA_toArray, mle_digTbl, mle_digTbl]
  generalize hκ : kindOfC es = κ at hn hL ⊢
  have hb : (bndL κ es).length = 4 := by unfold bndL; split_ifs <;> rfl
  have hg : ∀ j < 4, (bndL κ es ++ endBits κ es).toArray.getD j 0 = (bndL κ es).getD j 0 :=
    fun j hj => by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show j < (bndL κ es).length by omega)]
  have hlast : lastOf (bndL κ es ++ endBits κ es).toArray =
      fun l : Fin 18 => if (lastL es).testBit l then 1 else 0 := by
    funext l
    rw [lastOf, ← lastBits_getD es l.isLt]
    simp only [endBits, hn, Bool.false_eq_true, if_false, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show (bndL κ es).length ≤ 4 + l.val by omega), hb,
      Nat.add_sub_cancel_left]
  have htau : (tauL κ es).length = nbC κ := by simp [tauL]
  rw [hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num), hlast,
    eq_pad_last (nbC_le κ) _ htau hL]
  rfl

/-! ## T4's witness is the dooms' `zw` -/

/-- **T4's decoded witness is Boolean** (`segHolds_of_truths`' `hbool` at `zw := T4.zW`). -/
theorem zW_bool (κ : CKind) (L es : Log) (b : ℕ) : BlockR1CS.IsBool (T4.zW κ L es b) :=
  unpack_boolean _ _

end FR.Snd.P4a
