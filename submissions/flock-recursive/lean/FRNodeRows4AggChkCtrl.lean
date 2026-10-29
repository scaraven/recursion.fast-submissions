-- New for `flock-recursive` (stage B4, track L-circ): the controls of the aggregate check rows.
import FRNodeRows4AggChkG

/-!
# Controls for `aggChk`'s rows and readings

Positive (the rows are satisfiable by the honest values) and negative (a bad witness breaks a row):

| definition | (+) | (−) |
|---|---|---|
| `decRowsI`/`decRowsA` (`pkO` at offset 0) | `pkO_unpack`: every element is its own packed bits | `pkO_bits_ctl`: packs that differ in a cell differ |
| the adder rows (`full_add`) | `full_add_complete`: Boolean `a, b, c` with `p = ab`, `c' = ab + (a + b)c` meet both rows, `c'` Boolean | `full_add_neg`: `1 + 1` with carry `0` breaks the carry row |
| `rngRowsI`'s inverse row | `inv_ctl` (+): a nonzero length has an inverse | `inv_ctl` (−): length `0` on an active sub-slot breaks it |
| `rngRowsI`'s cap rows | `cap_ctl` (+): bit `c` alone meets them | `cap_ctl` (−): bits `c` and `0` (`2^c + 1`) break the product row |
| `chnRowsI` | `chain_ctl` (+): an inactive sub-slot meets it whatever its start | `chain_ctl` (−): an active one whose start differs from the shifted end breaks it |
| `aggChecks_of` | `aggChecks_ctl`: two chaining views of total `3` are accepted | FRAgg's `ctrlA_bad_start`, `ctrlA_bad_sum`, `ctrlA_bad_end` (`V_A` rejects) |
| `PfView` | `pfView_ctl`: the decoder copying `hdr`/`stmt` from the two queries meets it | `pfView_ctl`: the empty decoder does not |
| `capE` | `cap_segAt`: `cap (segAt ι) = 2^{capE ι}` | `capE_ne`: the `L31` exponent is not `L30`'s |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Finset

/-- (+) **Every element is its packed bits** (the decomposition rows' completeness). -/
theorem pkO_unpack (x : F) (w : Asg) (c : ℕ → ℕ) (hc : ∀ q (hq : q < 128), w (c q) = unpack x ⟨q, hq⟩) :
    (pkO c 0 128).ev w = x := by
  have hb : BoolC w c 128 := fun q hq => by rw [hc q hq]; exact unpack_boolean _ _
  refine eq_of_bitF fun j => ?_
  rw [bitF_pkO w (by norm_num) hb, hc _ (by omega)]
  simp only [Nat.zero_le, Nat.sub_zero, true_and, Nat.zero_add, j.isLt, unpack, Fin.eta]
  split_ifs with h <;> simp [h]

/-- (−) Packs that differ in one Boolean cell differ. -/
theorem pkO_bits_ctl (w : Asg) (c₁ c₂ : ℕ → ℕ) (h₁ : BoolC w c₁ 8) (h₂ : BoolC w c₂ 8)
    (h0 : w (c₁ 0) = 1) (h0' : w (c₂ 0) = 0) : (pkO c₁ 0 8).ev w ≠ (pkO c₂ 0 8).ev w := fun h => by
  have := (pkO_bits_eq w (by norm_num) h₁ h₂ h (q := 0) (by norm_num)).1 h0
  rw [h0'] at this; exact zero_ne_one this

/-- (+) **The adder's rows are met by the honest carry** `c' = ab + (a + b)c`, which is Boolean. -/
theorem full_add_complete {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    a * b = a * b ∧ (a + b) * c = (a * b + (a + b) * c) - a * b ∧
      (a * b + (a + b) * c = 0 ∨ a * b + (a + b) * c = 1) := by
  refine ⟨rfl, by ring, (full_add ha hb hc rfl (by ring)).2.1⟩

/-- (−) `1 + 1` with a zero carry-out breaks the carry row. -/
theorem full_add_neg : ¬ ((1 + 1 : F) * 0 = 0 - 1 * 1) := by
  rw [F_two]; simp

/-- (±) **The inverse row** `n · inv = S`: a nonzero length has its inverse; length `0` on an active
sub-slot has none. -/
theorem inv_ctl (n : F) (hn : n ≠ 0) : n * n⁻¹ = 1 ∧ ∀ inv : F, ¬ ((0 : F) * inv = 1) :=
  ⟨mul_inv_cancel₀ hn, fun inv h => by simp at h⟩

/-- (±) **The cap rows** at exponent `c` (`c ≤ 18`): bit `c` alone (`n = 2^c`) meets
`x·Σ_{t<c} E_t n_t = 0`; bits `c` and `0` (`n = 2^c + 1`) break it. -/
theorem cap_ctl (c : ℕ) (hc : 1 ≤ c) (hc' : c ≤ 18) (w : Asg) (cell : ℕ → ℕ) (x : ℕ)
    (hb : BoolC w cell c) (hx : w x = 1) :
    ((∀ t < c, w (cell t) = 0) → (gateR (Lin.cell x) (pkO cell 0 c)).Holds w) ∧
      (w (cell 0) = 1 → ¬ (gateR (Lin.cell x) (pkO cell 0 c)).Holds w) := by
  refine ⟨fun h0 => ?_, fun h1 hr => ?_⟩
  · simp only [Row.Holds, gateR, Lin.ev_cell, hx, one_mul, Lin.ev_nil]
    rw [pkO_ev]; exact sum_eq_zero fun t ht => by rw [h0 t (mem_range.1 ht), mul_zero]
  · have := pkO_zero w (by omega) hb (gate_one hr (by simpa using hx)) (q := 0) (by omega)
    rw [h1] at this; exact one_ne_zero this

/-- (±) **The chaining row** `S·(x − y) = 0`: an inactive sub-slot meets it whatever `x`; an active
one with `x ≠ y` breaks it. -/
theorem chain_ctl (w : Asg) (S : Lin) (x : ℕ) (y : Lin) :
    (S.ev w = 0 → (gateR S ((Lin.cell x).sub y)).Holds w) ∧
      (S.ev w = 1 → w x ≠ y.ev w → ¬ (gateR S ((Lin.cell x).sub y)).Holds w) := by
  refine ⟨fun h0 => by simp [Row.Holds, gateR, h0], fun h1 hne hr => hne ?_⟩
  have := gate_one hr h1
  simpa [sub_eq_zero] using this

/-- (+) **`aggChecks_of`**: two chaining views `0 → 1` (1 step, `L31`) and `1 → 2` (2 steps, `L31`),
total `3`, end `2`, against `leafStmt 2 3`. -/
theorem aggChecks_ctl :
    aggChecks (leafStmtF (dC 2) 3) 3 (dC 2) ((List.range 2).map fun i =>
      if i = 0 then (⟨.L31, dC 0, dC 1, 1⟩ : SegView) else ⟨.L31, dC 1, dC 2, 2⟩) = true :=
  aggChecks_of rfl ⟨by norm_num, by norm_num⟩
    (fun i hi => by interval_cases i <;> simp [SegKind.cap, SegKind.m])
    (by simp [sum_range_succ]) (by simp) (fun i h1 h2 => by
      obtain rfl : i = 1 := by omega
      simp)

/-- (±) **`PfView`**: the decoder copying `hdr` from the seed query and `stmt` from the second query
(bytes `0 … 175`) meets it; the empty decoder does not. -/
theorem pfView_ctl :
    PfView (fun tr => ⟨((List.range 176).map fun p =>
      if p < 48 then byteAt (tr.headD (ByteArray.empty, default)).1 (71 + p)
      else byteAt ((tr.drop 1).headD (ByteArray.empty, default)).1 (40 + (p - 48))).toArray⟩) ∧
      ¬ PfView (fun _ => ByteArray.empty) := by
  refine ⟨fun e₀ e₁ tr => ⟨fun j hj => ?_, fun j hj => ?_⟩, fun h => ?_⟩
  · rw [byteAt_mk, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, if_pos hj, List.headD_cons]
  · rw [byteAt_mk, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, if_neg (show ¬ 48 + j < 48 by omega), List.drop_one,
      List.tail_cons, List.headD_cons]
    congr 1; omega
  · have := (h (⟨(List.replicate 87 (0 : UInt8) ++ [1]).toArray⟩, default) (ByteArray.empty, default) []).1 16
      (by norm_num)
    have h2 : byteAt (⟨(List.replicate 87 (0 : UInt8) ++ [1]).toArray⟩ : ByteArray) 87 = 1 := by
      rw [byteAt_mk]; decide
    have h3 : byteAt ByteArray.empty 16 = 0 := rfl
    change byteAt ByteArray.empty 16 = byteAt (⟨(List.replicate 87 (0 : UInt8) ++ [1]).toArray⟩ : ByteArray) 87 at this
    rw [h2, h3] at this
    exact absurd this (by decide)

/-- (−) The capacity exponents differ by kind. -/
theorem capE_ne : capE .N30 ≠ capE .P30 ∧ (segAt .N30).cap = 2 ^ 17 := ⟨by decide, rfl⟩

end N4s
end FR
