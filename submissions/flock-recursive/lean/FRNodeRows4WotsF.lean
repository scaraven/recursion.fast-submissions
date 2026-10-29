-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.wots_sound`.
import FRNodeRows4WotsD

/-!
# A 4.1 `wots_sound`: the checksum and the signature

* **`csum`**: the checksum rows (`R_{i+1} = R_i · f_i` from `1` to `1`) make the checksum digits the
  base-4 digits of `Σ (3 − dᵢ)`: `wotsDigits_mD`;
* **`wots_sound4`**: the WOTS rows of signed child `σ` (but the digest's mux, `digRows`), the node's Z
  and S truths, its L rows and `PubCells4` give the contract's `SigOk vk (mD κ σ w) σ'` for the
  signature `σ' = readSig4 κ σ w` the reader reads.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## L's bits -/

/-- **A declared L bit is Boolean** (`lRows4`). -/
theorem lbit {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hL : ∀ r ∈ lRows4 κ, r.Holds w) {σ j : ℕ}
    (hσ : σ < κ.vslots) (hj : j < 266 + 399 + 7552 + 3) : w (Lc κ σ (299 + j)) = 0 ∨ w (Lc κ σ (299 + j)) = 1 := by
  refine boolR_val hone (hL (boolR κ (Lc κ σ (299 + j))) (List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨σ,
    List.mem_range.2 hσ, List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩⟩, rfl⟩))
  simp [Lc, Nat.add_assoc]

/-! ## The checksum -/

theorem fac_ev {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {c u v : F} {b₀ b₁ s : ℕ}
    (hs : w s = 1 - w b₀ * w b₁) : (fac κ c u v b₀ b₁ s).ev w = c * (1 + u * w b₀) * (1 + v * w b₁) := by
  simp only [fac, Lin.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hone, hs]
  ring

theorem bit_pow {x : F} (hx : x = 0 ∨ x = 1) (a : F) : 1 + (a - 1) * x = a ^ (if x = 1 then 1 else 0) := by
  rcases hx with rfl | rfl <;> simp

/-- **Digit `i`'s factor**: `g^3 · g⁻¹^{dᵢ}` (message digit), `g⁻¹^{4^t dᵢ}` (checksum digit `t`). -/
theorem facI_ev {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ i : ℕ} (hi : i < wotsLen)
    (hb₀ : w (digC κ σ (2 * i)) = 0 ∨ w (digC κ σ (2 * i)) = 1)
    (hb₁ : w (digC κ σ (2 * i + 1)) = 0 ∨ w (digC κ σ (2 * i + 1)) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) :
    (facI κ σ i).ev w = if i < 128 then gW ^ 3 * gW⁻¹ ^ digV κ σ w i else gW⁻¹ ^ (4 ^ (i - 128) * digV κ σ w i) := by
  have r2 := hsel ⟨Lin.cell (digC κ σ (2 * i)), Lin.cell (digC κ σ (2 * i + 1)), (one κ).sub (Lin.cell (selC κ σ i 2))⟩
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩)
  simp only [Row.Holds, one, Lin.ev_cell, Lin.ev_sub, hone] at r2
  have hs : w (selC κ σ i 2) = 1 - w (digC κ σ (2 * i)) * w (digC κ σ (2 * i + 1)) := by
    linear_combination r2
  unfold facI
  split_ifs with h
  · rw [fac_ev hone hs]; unfold digV bv
    rcases hb₀ with h0 | h0 <;> rcases hb₁ with h1 | h1 <;> simp [h0, h1] <;> ring
  · rw [fac_ev hone hs]; unfold digV bv
    rcases hb₀ with h0 | h0 <;> rcases hb₁ with h1 | h1 <;> simp [h0, h1] <;> ring

/-- **The checksum rows telescope**: `Π_{i<133} fᵢ = 1`. -/
theorem prod_fac {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hsum : ∀ r ∈ sumRows κ σ, r.Holds w) : ∏ i ∈ Finset.range wotsLen, (facI κ σ i).ev w = 1 := by
  have key : ∀ n ≤ wotsLen, ∏ i ∈ Finset.range n, (facI κ σ i).ev w = (prL κ σ n).ev w := by
    intro n
    induction n with
    | zero => intro _; simp [prL, one, hone]
    | succ n ih =>
      intro hn
      have hr := hsum _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
      simp only [Row.Holds] at hr
      rw [Finset.prod_range_succ, ih (by omega), hr]
  rw [key _ le_rfl]
  simp [prL, one, hone]

theorem lsum_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **The checksum**: `Σ_{i<128} (3 − dᵢ) = Σ_{t<5} 4^t d_{128+t}`. -/
theorem csum {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hb : ∀ p < 266, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) (hsum : ∀ r ∈ sumRows κ σ, r.Holds w) :
    ∑ i ∈ Finset.range 128, (3 - digV κ σ w i) = ∑ t ∈ Finset.range 5, 4 ^ t * digV κ σ w (128 + t) := by
  have hp := prod_fac hone hsum
  rw [show wotsLen = 128 + 5 from rfl, Finset.prod_range_add] at hp
  have hfa : ∀ i < wotsLen, (facI κ σ i).ev w = _ := fun i hi =>
    facI_ev hone hi (hb _ (by unfold wotsLen at hi; omega)) (hb _ (by unfold wotsLen at hi; omega)) hsel
  rw [Finset.prod_congr rfl fun i hi => (hfa i (by simp at hi; unfold wotsLen; omega)).trans
      (if_pos (Finset.mem_range.1 hi)),
    Finset.prod_congr rfl fun t ht => (hfa (128 + t) (by simp at ht; unfold wotsLen; omega)).trans
      (if_neg (by omega))] at hp
  have h3 : ∀ i, gW ^ 3 * gW⁻¹ ^ digV κ σ w i = gW ^ (3 - digV κ σ w i) := fun i => by
    have hd := digV_le κ σ w i
    conv_lhs => rw [show 3 = (3 - digV κ σ w i) + digV κ σ w i by omega, pow_add, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ gW_ne, one_pow, mul_one]
  simp only [h3, Finset.prod_pow_eq_pow_sum, show ∀ t, 128 + t - 128 = t from fun t => by omega] at hp
  rw [inv_pow] at hp
  have := gW_inj (a := ∑ i ∈ Finset.range 128, (3 - digV κ σ w i))
    (b := ∑ t ∈ Finset.range 5, 4 ^ t * digV κ σ w (128 + t)) ?_ ?_ (mul_inv_eq_one₀ (pow_ne_zero _ gW_ne) |>.1 hp)
  · exact this
  · calc ∑ i ∈ Finset.range 128, (3 - digV κ σ w i) ≤ ∑ _i ∈ Finset.range 128, 3 :=
          Finset.sum_le_sum fun i _ => by omega
      _ < 1024 := by simp
  · have d0 := digV_le κ σ w 128; have d1 := digV_le κ σ w 129; have d2 := digV_le κ σ w 130
    have d3 := digV_le κ σ w 131; have d4 := digV_le κ σ w 132
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reducePow, zero_add]
    omega

/-- **The WOTS digits of `mD` are the circuit's.** -/
theorem wotsDigits_mD {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hb : ∀ p < 266, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) (hsum : ∀ r ∈ sumRows κ σ, r.Holds w) {i : ℕ} (hi : i < wotsLen) :
    (wotsDigits (mD κ σ w)).getD i 0 = digV κ σ w i := by
  have hm : msgDigits (mD κ σ w) = (List.range 128).map (digV κ σ w) := by
    refine List.ext_getElem (by simp [Wots.msgDigits_length]) fun j h1 h2 => ?_
    have := msgDigits_mD (fun p hp => hb p (by omega)) (i := j) (by simpa [Wots.msgDigits_length] using h1)
    simpa [List.getD_eq_getElem?_getD, h1] using this
  unfold wotsDigits
  rw [hm]
  by_cases h : i < 128
  · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, List.length_range, List.map_map]
    rw [List.getD_eq_getElem _ _ (by simp; unfold wotsLen at hi; omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [show (fun x => 3 - x) ∘ digV κ σ w = fun x => 3 - digV κ σ w x from rfl, lsum_range,
      csum hone hb hsel hsum]
    have d0 := digV_le κ σ w 128; have d1 := digV_le κ σ w 129; have d2 := digV_le κ σ w 130
    have d3 := digV_le κ σ w 131; have d4 := digV_le κ σ w 132
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reducePow, zero_add]
    rcases (by unfold wotsLen at hi; omega : i = 128 ∨ i = 129 ∨ i = 130 ∨ i = 131 ∨ i = 132) with
      rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-! ## `wots_sound` at 4.1 -/

/-- **A 4.1 `wots_sound`**: on the node's Z and S truths, its L rows and `PubCells4`, the WOTS rows
of signed child `σ` (the index, selectors, chains, key leaf, path, root and checksum rows) make the
signature the reader reads (`readSig4`) sign the digest of the digit bits `mD`. -/
theorem wots_sound4 {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hZ : truthZ4 κ w) (hS : truthS4 κ w)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hP : PubCells4 κ w vk c₁ c₂) {σ : ℕ} (hσ : σ < 2) {S : ℕ → Lin}
    (hW : ∀ r ∈ wotsRows κ σ S, r.Holds w) :
    SigOk vk (mD κ σ w) (N4s.readSig4 κ σ w) = true := by
  have hone : w κ.oneCell = 1 := by
    have := congrArg List.head? hP
    simpa [cells4, Node.pubVals] using this
  have hv : 2 ≤ κ.vslots := by cases κ <;> decide
  have hb : ∀ p < 266, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1 := fun p hp =>
    lbit hone hL (by omega) (by omega)
  have hix : ∀ r ∈ idxRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inl h))
  have hsel : ∀ r ∈ selRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inr (.inl h)))
  have hch : ∀ r ∈ chainRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inr (.inr (.inl h))))
  have hlf : ∀ r ∈ leafRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inl h)))))
  have hpa : ∀ r ∈ pathRows κ σ, r.Holds w := fun r h =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inl h))))))
  have hro : ∀ r ∈ rootRows κ σ, r.Holds w := fun r h =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
  have hsu : ∀ r ∈ sumRows κ σ, r.Holds w := fun r h =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))
  have hj := j_mirror hone hix
  have hidx : (N4s.readSig4 κ σ w).idx = idxOf κ σ w := rfl
  refine Wots.wots_sound (by rw [hidx]; exact idx_lt hone hix) (by simp [N4s.readSig4])
    (by simp [N4s.readSig4]) (ends := endsD κ σ w) (by simp [endsD]) (fun i hi => ?_)
    (cur := curD κ σ w) ?_ (fun t ht => ?_) (root_vk hone hP hσ hro)
  · have hd := wotsDigits_mD hone hb hsel hsu hi
    rw [List.getD_eq_getElem _ _ (by rw [Wots.wotsDigits_length]; exact hi)] at hd
    simp only [hd, endsD, List.getElem_map, List.getElem_range, hidx]
    rw [chain_end hone hZ hS hσ hi hj (hb _ (by unfold wotsLen at hi; omega))
      (hb _ (by unfold wotsLen at hi; omega)) hsel hch]
    have ho : Read.digestOf w (N4s.sigCell κ σ (1 + 2 * i)) (N4s.sigCell κ σ (2 + 2 * i)) = otsD κ σ w i := by
      unfold otsD otsC N4s.sigCell Lc; rw [show 1 + 2 * i + 1 = 2 + 2 * i by omega, Nat.add_zero]
    simp only [N4s.readSig4, List.getElem_map, List.getElem_range, ho]
  · rw [hidx]
    have : curB κ σ 0 = wb κ σ 465 := rfl
    simp only [curD, this]
    exact leaf_out hone hZ hS hσ hj hlf
  · have ht' : t < sigHeight := by simpa [N4s.readSig4] using ht
    rw [path_out hone hZ hS hσ ht' hix hpa, hidx]
    have hs : Read.digestOf w (N4s.sigCell κ σ (1 + 2 * wotsLen + 2 * t))
        (N4s.sigCell κ σ (2 + 2 * wotsLen + 2 * t)) = sibD κ σ w t := by
      unfold sibD sibC N4s.sigCell Lc
      rw [show 1 + 2 * wotsLen + 2 * t + 1 = 2 + 2 * wotsLen + 2 * t by omega, Nat.add_zero]
    simp only [N4s.readSig4, List.getElem_map, List.getElem_range, hs]

end W4
end FR
