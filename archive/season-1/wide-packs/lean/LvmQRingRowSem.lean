-- New for lvm2 E2F (slice S1, E2F-QH2): the row switch's auxiliary rows are sound: where they hold, the free row
-- words are V's `rowWordD` of the slices (the bit transpose).
import LvmQRingCrt
import LvmTypedLHolds
import LvmDecideE2

/-!
# The row switch's auxiliary rows (`rowAux_sound`)

On the memory read off the words (`memOf lay z`), if every row of `rowAux bw tB qs` holds, then for `j < 128` the
free cell `tB + j` holds `rowWordD sv j`, `sv` the 64 slices at lanes `qs + 2 i` (`re`) and `qs + 2 i + 1` (`im`).

* `bitsum`: `Σ_{i<n} x^i·b_i` for `0/1` words `b` has bit `k` iff `k < n ∧ b_k = 1` (`testBit_bitsum`);
* `natsum`: the same for `rowWordD`'s `Nat` sum (`testBit_natsum`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Typed

/-! ## Bit sums -/

/-- `Σ_{i<n} x^i·b_i` in `K`. -/
def bitsum (b : Nat → FK) (n : Nat) : FK := ((List.range n).map fun i => xPowK i * b i).sum

theorem xPowK_toNat {i : Nat} (hi : i < 64) : (xPowK i).val.toNat = 2 ^ i := by
  simp only [xPowK, UInt64.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi)

theorem testBit_bitsum (b : Nat → FK) (hb : ∀ i < 64, b i = 0 ∨ b i = 1) :
    ∀ n ≤ 64, ∀ k, (bitsum b n).val.toNat.testBit k = (decide (k < n) && decide (b k = 1))
  | 0, _, k => by
    simp only [bitsum, List.range_zero, List.map_nil, List.sum_nil]
    show (0 : Nat).testBit k = _
    simp
  | n + 1, hn, k => by
    have ih := testBit_bitsum b hb n (by (clear * - n hn; omega)) k
    have e : bitsum b (n + 1) = bitsum b n + xPowK n * b n := by
      simp only [bitsum, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [e]
    rcases hb n (by (clear * - n hn; omega)) with h | h
    · rw [h, mul_zero, add_zero, ih]
      by_cases hk : k = n
      · subst hk; simp [h]
      · by_cases hk' : k < n
        · simp [hk', show k < n + 1 by (clear * - k n hk'; omega)]
        · simp [hk', show ¬ k < n + 1 by (clear * - k n hk hk'; omega)]
    · rw [h, mul_one]
      change ((_ : UInt64) ^^^ _).toNat.testBit k = _
      rw [UInt64.toNat_xor, Nat.testBit_xor, ih, xPowK_toNat (by (clear * - n hn; omega)), Nat.testBit_two_pow]
      by_cases hk : k = n
      · subst hk; simp [h]
      · by_cases hk' : k < n
        · simp [hk', show k < n + 1 by (clear * - k n hk'; omega), hk, Ne.symm hk]
        · simp [hk', show ¬ k < n + 1 by (clear * - k n hk hk'; omega), Ne.symm hk]

/-- `rowWordD`'s sum: `Σ_{i<n, B i} 2^i`. -/
def natsum (B : Nat → Bool) (n : Nat) : Nat := (List.range n).foldl (fun acc i => if B i then acc + 2 ^ i else acc) 0

theorem natsum_lt (B : Nat → Bool) : ∀ n, natsum B n < 2 ^ n
  | 0 => by simp [natsum]
  | n + 1 => by
    have ih := natsum_lt B n
    simp only [natsum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    split <;> rw [pow_succ] <;> (clear * - B n ih; omega)

theorem testBit_natsum (B : Nat → Bool) : ∀ n k, (natsum B n).testBit k = (decide (k < n) && B k)
  | 0, k => by simp [natsum]
  | n + 1, k => by
    have ih := testBit_natsum B n k
    have hl := natsum_lt B n
    have e : natsum B (n + 1) = if B n then natsum B n + 2 ^ n else natsum B n := by
      simp only [natsum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e]
    split
    · rename_i hB
      rw [Nat.add_comm]
      by_cases hk : k < n
      · rw [Nat.testBit_two_pow_add_gt hk, ih]; simp [hk, show k < n + 1 by (clear * - k n B hk; omega)]
      · by_cases hkn : k = n
        · subst hkn; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hl]; simp [hB]
        · have : 2 ^ n + natsum B n < 2 ^ k := by
            have : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by (clear * - n k B hk hkn; omega))
            rw [pow_succ] at this; (clear * - n B k hl this; omega)
          rw [Nat.testBit_lt_two_pow this]; simp [show ¬ k < n + 1 by (clear * - k n B hk hkn; omega)]
    · rename_i hB
      rw [ih]
      by_cases hkn : k = n
      · subst hkn; simp [hB]
      · by_cases hk : k < n
        · simp [hk, show k < n + 1 by (clear * - k n B hk; omega)]
        · simp [hk, show ¬ k < n + 1 by (clear * - k n B hkn hk; omega)]

theorem fk_eq_of_testBit {a b : FK} (h : ∀ k, a.val.toNat.testBit k = b.val.toNat.testBit k) : a = b := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  congr 1
  exact UInt64.toNat_inj.mp (Nat.eq_of_testBit_eq h)

/-! ## The rows -/

/-- An auxiliary `D`-only row `cell + Σ w_i·word_i = 0` gives the cell's word as the sum. -/
theorem drow_val (lay : Lay) (z : ℕ → FK) {n : ℕ} {ws : List (FE × ℕ)}
    (h : ARowHolds lay z 0 ⟨(2, .cell ⟨.K, n, []⟩, 1) :: ws.map fun e => (2, .word e.2 0, e.1)⟩) :
    FE.ofK ((memOf lay z).k n) = (ws.map fun e => e.1 * FE.ofK (z e.2)).sum := by
  simp only [ARowHolds, aRowMat, List.filter_cons, List.filter_map, List.map_cons, List.map_map] at h
  simp [Function.comp_def, aopVal, Addr.at, dot, Mem.rd, memOf] at h
  have := lh_c2 h
  simpa [aopVal, Addr.at, Lvm.Loop.dot, Mem.rd, memOf] using this.symm

/-- The slices at lanes `qs + 2 i`, `qs + 2 i + 1` of a memory. -/
def slicesOf (M : Mem) (qs : Nat) : List FE2 :=
  (List.range 64).map fun i => (⟨M.k (qs + 2 * i), M.k (qs + 2 * i + 1)⟩ : FE2)

theorem bit_of_row {lay : Lay} {z : ℕ → FK} {w : ℕ}
    (h : ARowHolds lay z 0 ⟨[(0, .word w 0, 1), (1, .word w 0, 1), (2, .word w 0, 1)]⟩) : z w = 0 ∨ z w = 1 := by
  simp only [ARowHolds, aRowMat, List.filter_cons, List.filter_nil] at h
  simp only [beq_self_eq_true, if_true, Nat.reduceBEq, Bool.false_eq_true, if_false, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, aopVal, Nat.mul_zero, Nat.add_zero] at h
  apply pr_bit
  have h2 : FE.ofKRingHom (z w * z w + z w) = FE.ofKRingHom 0 := by
    rw [map_add, map_mul, map_zero]; exact h
  exact congrArg FE.c₀ h2

theorem ofK_bitsum (b : Nat → FK) (n : Nat) :
    FE.ofK (bitsum b n) = ((List.range n).map fun i => xPowW i * FE.ofK (b i)).sum := by
  rw [bitsum, show FE.ofK (((List.range n).map fun i => xPowK i * b i).sum) =
    FE.ofKRingHom (((List.range n).map fun i => xPowK i * b i).sum) from rfl, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, map_mul]; rfl

theorem ofK_inj {a b : FK} (h : FE.ofK a = FE.ofK b) : a = b := congrArg FE.c₀ h

/-- A `D`-only aux row over 64 bit words with weights `x^i`: the cell's word is the bit sum. -/
theorem drow_bitsum (lay : Lay) (z : ℕ → FK) {n : ℕ} (w : ℕ → ℕ)
    (h : ARowHolds lay z 0 ⟨(2, .cell ⟨.K, n, []⟩, 1) :: (List.range 64).map fun i => (2, .word (w i) 0, xPowW i)⟩) :
    (memOf lay z).k n = bitsum (fun i => z (w i)) 64 := by
  have e := drow_val lay z (n := n) (ws := (List.range 64).map fun i => (xPowW i, w i)) (by
    simpa only [List.map_map, Function.comp_def] using h)
  apply ofK_inj
  rw [e, ofK_bitsum, List.map_map]
  rfl

/-- **The row switch's auxiliary rows are sound**: the free row words are `rowWordD` of the slices. -/
theorem rowAux_sound (lay : Lay) (z : ℕ → FK) {bw tB qs : ℕ}
    (h : ∀ r ∈ (rowAux bw tB qs).rows, ARowHolds lay z 0 r) {j : ℕ} (hj : j < 128) :
    (memOf lay z).k (tB + j) = rowWordD (slicesOf (memOf lay z) qs) j := by
  have hrows : (rowAux bw tB qs).rows = rowBoolRows bw ++ (List.range 128).map (rowRecRow bw tB) ++
      (List.range 2).flatMap (fun h => (List.range 64).map (rowTrRow bw qs h)) := rfl
  have hB : ∀ j < 128, ∀ i < 64, z (bw + 64 * j + i) = 0 ∨ z (bw + 64 * j + i) = 1 := fun j hj i hi =>
    bit_of_row (w := bw + 64 * j + i) (h _ (by
      rw [hrows]; exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩))))
  have hR : (memOf lay z).k (tB + j) = bitsum (fun i => z (bw + 64 * j + i)) 64 :=
    drow_bitsum lay z (fun i => bw + 64 * j + i) (h _ (by
      rw [hrows]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
  have hT : ∀ hh < 2, ∀ i < 64, (memOf lay z).k (qs + 2 * i + hh) =
      bitsum (fun j' => z (bw + 64 * (j' + 64 * hh) + i)) 64 := fun hh hh2 i hi =>
    drow_bitsum lay z (fun j' => bw + 64 * (j' + 64 * hh) + i) (h _ (by
      rw [hrows]; exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨hh, List.mem_range.mpr hh2, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩)))
  apply fk_eq_of_testBit
  intro k
  rw [hR, testBit_bitsum _ (fun i hi => hB j hj i hi) 64 le_rfl k]
  have hlt := natsum_lt (fun i => bitFE2 ((slicesOf (memOf lay z) qs).getD i 0) j) 64
  show _ = ((natsum (fun i => bitFE2 ((slicesOf (memOf lay z) qs).getD i 0) j) 64).toUInt64).toNat.testBit k
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt, testBit_natsum]
  by_cases hk : k < 64
  · simp only [hk, decide_true, Bool.true_and]
    have hs : (slicesOf (memOf lay z) qs).getD k 0 =
        (⟨(memOf lay z).k (qs + 2 * k), (memOf lay z).k (qs + 2 * k + 1)⟩ : FE2) := by
      simp [slicesOf, List.getD_eq_getElem?_getD, hk]
    rw [hs, bitFE2]
    split
    · rename_i hj64
      have := hT 0 (by norm_num) k hk
      rw [Nat.add_zero] at this
      rw [this, testBit_bitsum _ (fun i hi => by have := hB i (by (clear * - i lay z qs j k hi; omega)) k hk; simpa using this) 64 le_rfl j]
      simp [hj64]
    · rename_i hj64
      have := hT 1 (by norm_num) k hk
      rw [this, testBit_bitsum _ (fun i hi => hB (i + 64) (by (clear * - i lay z qs j k hi; omega)) k hk) 64 le_rfl (j - 64)]
      simp [show j - 64 < 64 by (clear * - j lay z qs hj k hj64; omega), show j - 64 + 64 = j by (clear * - j lay z qs hj k hj64; omega)]
  · simp [hk]

end Lvm.Q2
