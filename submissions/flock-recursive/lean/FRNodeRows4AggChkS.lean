-- New for `flock-recursive` (PACK-4.4.1 §4.3; stage B4, track L-circ): what the check rows give.
import FRNodeRows4AggChkB

/-!
# What aggregate `a`'s check rows give

On `one = 1` and the rows `aggRowsC κ a S` (`S i`: sub-slot `i`'s activity, `0` or `1`, `1` exactly
below the segment count `k`), in terms of the stream's elements (`sE`) and `cAB`'s message:

* **`chain_sub`**: an active sub-slot `i ≥ 1` starts (`dg2` of its elements `6, 7`) at sub-slot
  `i − 1`'s end (`sh1` of its `13, 14, 15`);
* **`end_sub`**: at `[k = j]`, sub-slot `j − 1`'s end is `cAB`'s `e` (`sh1` of its `4, 5, 6`);
* **`rng_sub`**: an active sub-slot of selected kind `ι` has `1 ≤ n ≤ 2^{capE ι}` (`n8` of its
  element `15`);
* **`sum_sub`**: `Σ_{i<k} nᵢ = n8 (cAB's element 6)`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Finset

section Rows
variable {κ : NodeKind} {a : ℕ} {S : ℕ → Lin} {w : Asg}

/-! ## Membership -/

theorem mem_sub {i : ℕ} (hi : i < κ.maxK) {r : Row} (h : r ∈ subRows κ a S i) : r ∈ aggRowsC κ a S := by
  unfold aggRowsC
  simp only [List.mem_append]
  exact .inl (.inl (.inl (.inl (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, h⟩))))

theorem mem_decA {r : Row} (h : r ∈ decRowsA κ (aggChild κ a) a) : r ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr h)))

theorem mem_end {j : ℕ} (hj : j < κ.maxK) {r : Row}
    (h : r ∈ endRowsJ κ (aggChild κ a) a (ind κ S (j + 1)) (j + 1)) : r ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp only [List.mem_append]
  exact .inl (.inl (.inr (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, h⟩)))

theorem mem_add {i : ℕ} (hi : i + 1 < κ.maxK) {r : Row} (h : r ∈ addRowsI κ (aggChild κ a) (i + 1)) :
    r ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp only [List.mem_append]
  exact .inl (.inr (List.mem_flatMap.2 ⟨i, List.mem_range.2 (by omega), h⟩))

theorem mem_sum : sumRow κ (aggChild κ a) ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp

/-! ## Row values -/

theorem gate_ev {s x : Lin} (h : (gateR s x).Holds w) : s.ev w * x.ev w = 0 := by
  simpa [Row.Holds, gateR] using h

theorem gate_one {s x : Lin} (h : (gateR s x).Holds w) (hs : s.ev w = 1) : x.ev w = 0 := by
  simpa [hs] using gate_ev h

theorem row_ev {x y z : Lin} (h : (⟨x, y, z⟩ : Row).Holds w) : x.ev w * y.ev w = z.ev w := h

variable (hone : w κ.oneCell = 1) (hR : ∀ r ∈ aggRowsC κ a S, r.Holds w)
include hone hR

/-! ## The decompositions -/

/-- **Elements `13 + u` of sub-slot `i` are their Boolean bits.** -/
theorem bits_sub {i u : ℕ} (hi : i < κ.maxK) (hu : u < 3) :
    BoolC w (bC κ (aggChild κ a) i u) 128 ∧
      w (sE κ (aggChild κ a) i (13 + u)) = (pkO (bC κ (aggChild κ a) i u) 0 128).ev w := by
  have hm : ∀ r ∈ decRowsI κ (aggChild κ a) i, r.Holds w := fun r hr =>
    hR r (mem_sub hi (by unfold subRows; simp only [List.mem_append]; exact .inl (.inl (.inl hr))))
  have hu' : ∀ r, r ∈ (eqR κ (Lin.cell (sE κ (aggChild κ a) i (13 + u))) (pkO (bC κ (aggChild κ a) i u) 0 128) ::
      (List.range 128).map fun q => boolR κ (bC κ (aggChild κ a) i u q)) → r.Holds w := fun r hr =>
    hm r (List.mem_flatMap.2 ⟨u, List.mem_range.2 hu, hr⟩)
  refine ⟨fun q hq => boolR_val hone (hu' _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))), ?_⟩
  simpa using eqR_val hone (hu' _ List.mem_cons_self)

/-- **`cAB`'s elements `4 + 2u` are their Boolean bits.** -/
theorem bits_A {u : ℕ} (hu : u < 2) :
    BoolC w (aC κ (aggChild κ a) u) 128 ∧ w (hc (cAB κ a) (4 + 2 * u)) = (pkO (aC κ (aggChild κ a) u) 0 128).ev w := by
  have hu' : ∀ r, r ∈ (eqR κ (Lin.cell (hc (cAB κ a) (4 + 2 * u))) (pkO (aC κ (aggChild κ a) u) 0 128) ::
      (List.range 128).map fun q => boolR κ (aC κ (aggChild κ a) u q)) → r.Holds w := fun r hr =>
    hR r (mem_decA (List.mem_flatMap.2 ⟨u, List.mem_range.2 hu, hr⟩))
  refine ⟨fun q hq => boolR_val hone (hu' _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))), ?_⟩
  simpa using eqR_val hone (hu' _ List.mem_cons_self)

/-- **The string `13 ‖ 14 ‖ 15` of sub-slot `i` is its bits.** -/
theorem catBit_sub {i Q : ℕ} (hi : i < κ.maxK) (hQ : Q < 384) :
    catBit (w (sE κ (aggChild κ a) i 13)) (w (sE κ (aggChild κ a) i 14)) (w (sE κ (aggChild κ a) i 15)) Q =
      decide (w (bC κ (aggChild κ a) i (Q / 128) (Q % 128)) = 1) := by
  have hq := Nat.mod_lt Q (show 0 < 128 by norm_num)
  obtain ⟨hb, he⟩ := bits_sub hone hR hi (show Q / 128 < 3 by omega)
  rw [catBit, bitN_mod, ← bitN_dec w hb he hq]
  rcases (by omega : Q / 128 = 0 ∨ Q / 128 = 1 ∨ Q / 128 = 2) with h | h | h <;> rw [h] <;> rfl

/-! ## The chaining -/

/-- **An active later sub-slot starts at its predecessor's end.** -/
theorem chain_sub {i : ℕ} (hi1 : 1 ≤ i) (hi : i < κ.maxK) (hS : (S i).ev w = 1) :
    dg2 (w (sE κ (aggChild κ a) i 6)) (w (sE κ (aggChild κ a) i 7)) =
      sh1 (w (sE κ (aggChild κ a) (i - 1) 13)) (w (sE κ (aggChild κ a) (i - 1) 14))
        (w (sE κ (aggChild κ a) (i - 1) 15)) := by
  set σ := aggChild κ a
  have hc : ∀ u < 2, w (sE κ σ i (6 + u)) = (pkO (shC κ σ (i - 1) u) 0 128).ev w := fun u hu => by
    have hr := hR _ (mem_sub hi (r := gateR (S i) ((Lin.cell (sE κ σ i (6 + u))).sub (pkO (shC κ σ (i - 1) u) 0 128)))
      (by unfold subRows; simp only [List.mem_append, if_neg (show i ≠ 0 by omega)]
          exact .inr (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩)))
    have := gate_one hr hS
    simpa [sub_eq_zero] using this
  have hb : ∀ u < 2, BoolC w (shC κ σ (i - 1) u) 128 := fun u hu q hq => by
    unfold shC; split_ifs
    · exact (bits_sub hone hR (by omega) (by omega : u < 3)).1 _ (by omega)
    · exact (bits_sub hone hR (by omega) (by omega : u + 1 < 3)).1 _ (by omega)
  refine Vector.ext fun j hj => ?_
  simp only [dg2, sh1, Vector.getElem_ofFn]
  refine catByte_congr fun b hb8 => ?_
  rw [catBit_sub hone hR (by omega) (by omega)]
  have hP : 8 * j + b < 256 := by omega
  have hL : catBit (w (sE κ σ i 6)) (w (sE κ σ i 7)) 0 (8 * j + b) =
      decide (w (shC κ σ (i - 1) ((8 * j + b) / 128) ((8 * j + b) % 128)) = 1) := by
    have hm := Nat.mod_lt (8 * j + b) (show 0 < 128 by norm_num)
    rcases (by omega : (8 * j + b) / 128 = 0 ∨ (8 * j + b) / 128 = 1) with h | h
    · rw [catBit, h, bitN_mod]; exact bitN_dec w (hb 0 (by norm_num)) (hc 0 (by norm_num)) hm
    · rw [catBit, h, bitN_mod]; exact bitN_dec w (hb 1 (by norm_num)) (hc 1 (by norm_num)) hm
  rw [hL]
  unfold shC
  split_ifs with h
  · rw [show (8 * (1 + j) + b) / 128 = (8 * j + b) / 128 by omega,
      show (8 * (1 + j) + b) % 128 = (8 * j + b) % 128 + 8 by omega]
  · rw [show (8 * (1 + j) + b) / 128 = (8 * j + b) / 128 + 1 by omega,
      show (8 * (1 + j) + b) % 128 = (8 * j + b) % 128 - 120 by omega]

/-! ## The end -/

/-- **At `[k = j]`, sub-slot `j − 1` ends at `cAB`'s `e`.** -/
theorem end_sub {j : ℕ} (hj : j < κ.maxK) (hind : (ind κ S (j + 1)).ev w = 1) :
    sh1 (w (sE κ (aggChild κ a) j 13)) (w (sE κ (aggChild κ a) j 14)) (w (sE κ (aggChild κ a) j 15)) =
      sh1 (w (hc (cAB κ a) 4)) (w (hc (cAB κ a) 5)) (w (hc (cAB κ a) 6)) := by
  set σ := aggChild κ a
  have hE : ∀ r ∈ endRowsJ κ σ a (ind κ S (j + 1)) (j + 1), r.Holds w := fun r hr => hR r (mem_end hj hr)
  simp only [endRowsJ, Nat.add_sub_cancel, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq] at hE
  obtain ⟨h1, h2, h3⟩ := hE
  have e1 := gate_one h1 hind
  have e2 := gate_one h2 hind
  have e3 := gate_one h3 hind
  simp only [Lin.ev_sub, Lin.ev_cell, sub_eq_zero] at e1 e2 e3
  obtain ⟨b0, d0⟩ := bits_sub hone hR hj (show 0 < 3 by norm_num)
  obtain ⟨b2, d2⟩ := bits_sub hone hR hj (show 2 < 3 by norm_num)
  obtain ⟨a0, da0⟩ := bits_A hone hR (show 0 < 2 by norm_num)
  obtain ⟨a1, da1⟩ := bits_A hone hR (show 1 < 2 by norm_num)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one] at d0 d2 da0 da1
  refine Vector.ext fun i hi => ?_
  simp only [sh1, Vector.getElem_ofFn]
  refine catByte_congr fun b hb => ?_
  set Q := 8 * (1 + i) + b
  by_cases hQ1 : Q < 128
  · rw [catBit_lt _ _ _ hQ1, catBit_lt _ _ _ hQ1, bitN_dec w b0 d0 hQ1, bitN_dec w a0 da0 hQ1]
    have := pkO_bits_eq w (by norm_num) (fun q hq => b0 _ (by omega)) (fun q hq => a0 _ (by omega)) e1
      (q := Q - 8) (by omega)
    simp only [Nat.sub_add_cancel (show 8 ≤ Q by omega)] at this
    exact decide_eq_decide.2 this
  by_cases hQ2 : Q < 256
  · rw [catBit_mid _ _ _ (by omega) hQ2, catBit_mid _ _ _ (by omega) hQ2, e2]
  · have hQ3 : Q < 264 := by omega
    rw [catBit_hi _ _ _ (by omega) (by omega), catBit_hi _ _ _ (by omega) (by omega),
      bitN_dec w b2 d2 (by omega), bitN_dec w a1 da1 (by omega)]
    exact decide_eq_decide.2 (pkO_bits_eq w (by norm_num) (fun q hq => b2 _ (by omega))
      (fun q hq => a1 _ (by omega)) e3 (by omega))

/-! ## The lengths' range -/

theorem rng_rows {i : ℕ} (hi : i < κ.maxK) :
    ∀ r ∈ rngRowsI κ (aggChild κ a) (N4c.sub κ a i) i (S i), r.Holds w := fun r hr =>
  hR r (mem_sub hi (by unfold subRows; simp only [List.mem_append]; exact .inl (.inl (.inr hr))))

/-- **An active sub-slot's length bits from 19 on are clear.** -/
theorem hi_zero {i : ℕ} (hi : i < κ.maxK) (hS : (S i).ev w = 1) {t : ℕ} (h1 : 19 ≤ t) (h2 : t < 64) :
    w (nb κ (aggChild κ a) i t) = 0 := by
  have hb := (bits_sub hone hR hi (show 2 < 3 by norm_num)).1
  have h := gate_one (rng_rows hone hR hi _ (List.mem_append_left _ (List.mem_cons_self ..))) hS
  have := pkO_zero w (c := fun t => nb κ (aggChild κ a) i (19 + t)) (by norm_num)
    (fun q hq => hb _ (by omega)) h (q := t - 19) (by omega)
  simpa [Nat.add_sub_cancel' h1] using this

/-- **An active sub-slot of selected kind `ι` has `1 ≤ n ≤ 2^{capE ι}`.** -/
theorem rng_sub {i : ℕ} (hi : i < κ.maxK) (hS : (S i).ev w = 1) {ι : Kind}
    (hsel : ∀ ι', w (selc κ (N4c.sub κ a i) ι') = if ι' = ι then 1 else 0) :
    1 ≤ n8 (w (sE κ (aggChild κ a) i 15)) ∧ n8 (w (sE κ (aggChild κ a) i 15)) ≤ 2 ^ capE ι := by
  set σ := aggChild κ a
  obtain ⟨b2, d2⟩ := bits_sub hone hR hi (show 2 < 3 by norm_num)
  have hnb : BoolC w (nb κ σ i) 64 := fun t ht => b2 (8 + t) (by omega)
  set f : ℕ → Bool := fun t => decide (w (nb κ σ i t) = 1) with hf
  have hn : n8 (w (sE κ σ i 15)) = nOfBits f 64 := by
    rw [n8_bits]; exact nOfBits_congr fun t ht => bitN_dec w b2 d2 (by omega)
  have hR' := rng_rows hone hR hi
  have hk : ∀ r ∈ [gateR (Lin.cell (selc κ (N4c.sub κ a i) ι))
      (pkO (fun t => nb κ σ i (capE ι + 1 + t)) 0 (18 - capE ι)),
      ⟨Lin.cell (selc κ (N4c.sub κ a i) ι), Lin.cell (nb κ σ i (capE ι)), Lin.cell (xC κ σ i ι)⟩,
      gateR (Lin.cell (xC κ σ i ι)) (pkO (nb κ σ i) 0 (capE ι))], r.Holds w := fun r hr =>
    hR' r (List.mem_append_right _ (List.mem_flatMap.2 ⟨ι, kinds_mem ι, hr⟩))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k2, k3, k4⟩ := hk
  have hs1 : w (selc κ (N4c.sub κ a i) ι) = 1 := by rw [hsel ι, if_pos rfl]
  have hc := capE_le ι
  set c := capE ι
  -- bits above `c` are clear
  have hz2 := gate_one k2 (by simpa using hs1)
  have hhi : ∀ t, c + 1 ≤ t → t < 64 → f t = false := fun t h1 h2 => by
    simp only [hf, decide_eq_false_iff_not]
    by_cases h19 : t < 19
    · have := pkO_zero w (c := fun t => nb κ σ i (c + 1 + t)) (by omega) (fun q hq => hnb _ (by omega)) hz2
        (q := t - (c + 1)) (by omega)
      simp only [Nat.add_sub_cancel' h1] at this
      rw [this]; exact zero_ne_one
    · rw [hi_zero hone hR hi hS (by omega) h2]; exact zero_ne_one
  have hv : nOfBits f 64 = nOfBits f c + 2 ^ c * (if f c then 1 else 0) := by
    rw [nOfBits_high (m' := c + 1) (by omega) hhi, nOfBits_add, nOfBits_one, Nat.add_zero]
  have hx : w (xC κ σ i ι) = w (nb κ σ i c) := by
    have := row_ev k3; simp only [Lin.ev_cell, hs1, one_mul] at this; exact this.symm
  rw [hn]
  refine ⟨?_, ?_⟩
  · -- `n ≠ 0`: the inverse row
    have h4 := row_ev (hR' _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    simp only [Lin.ev_cell, hS] at h4
    by_contra hlt
    have h0 : nOfBits f 64 = 0 := by omega
    have hall : ∀ t < 19, w (nb κ σ i t) = 0 := fun t ht => by
      rcases hnb t (by omega) with h | h
      · exact h
      · have := nOfBits_ge (f := f) (m := 64) (t := t) (by omega) (by simp [hf, h]); have := Nat.two_pow_pos t; omega
    have : (pkO (nb κ σ i) 0 19).ev w = 0 := by
      rw [pkO_ev]; exact sum_eq_zero fun t ht => by rw [hall t (mem_range.1 ht), mul_zero]
    rw [this, zero_mul] at h4
    exact zero_ne_one h4
  · rw [hv]
    by_cases hfc : f c = true
    · -- bit `c` set: the bits below are clear
      have hw : w (nb κ σ i c) = 1 := by simpa [hf] using hfc
      have hz4 := gate_one k4 (by simpa [hx] using hw)
      have hlo : nOfBits f c = 0 := nOfBits_zero fun t ht => by
        simp only [hf, decide_eq_false_iff_not]
        rw [pkO_zero w (by omega) (fun q hq => hnb _ (by omega)) hz4 ht]; exact zero_ne_one
      rw [hlo, if_pos hfc]; omega
    · rw [if_neg hfc]; have := nOfBits_lt f c; omega

end Rows

section Sum
variable {κ : NodeKind} {a : ℕ} {S : ℕ → Lin} {w : Asg}

/-- **The ripple-carry adder** (bits `t < N`): Boolean `a`, `b`, carries `c` with `c₀ = 0`, the rows of
each bit; the sum bits `a + b + c` are Boolean and `Σ a + Σ b = Σ (a + b + c) + 2^T c_T`. -/
theorem ripple (N : ℕ) (A B C P : ℕ → F) (ha : ∀ t < N, A t = 0 ∨ A t = 1) (hb : ∀ t < N, B t = 0 ∨ B t = 1)
    (hc0 : C 0 = 0) (hp : ∀ t < N, A t * B t = P t) (hc : ∀ t < N, (A t + B t) * C t = C (t + 1) - P t) :
    ∀ T ≤ N, (C T = 0 ∨ C T = 1) ∧ (∀ t < T, A t + B t + C t = 0 ∨ A t + B t + C t = 1) ∧
      nOfBits (fun t => dv (A t)) T + nOfBits (fun t => dv (B t)) T =
        nOfBits (fun t => dv (A t + B t + C t)) T + 2 ^ T * nv (C T)
  | 0, _ => ⟨.inl hc0, fun t ht => absurd ht (Nat.not_lt_zero _), by simp [nOfBits_dv, hc0, nv_zero]⟩
  | T + 1, hT => by
    obtain ⟨hcT, hs, ih⟩ := ripple N A B C P ha hb hc0 hp hc T (by omega)
    obtain ⟨hsT, hcT', e⟩ := full_add (ha T (by omega)) (hb T (by omega)) hcT (hp T (by omega)) (hc T (by omega))
    refine ⟨hcT', fun t ht => ?_, ?_⟩
    · rcases Nat.lt_or_ge t T with h | h
      · exact hs t h
      · rw [show t = T by omega]; exact hsT
    · simp only [nOfBits_dv, sum_range_succ] at ih ⊢
      rw [pow_succ]
      have e' : (nv (A T) + nv (B T)) * 2 ^ T + nv (C T) * 2 ^ T =
          (nv (A T + B T + C T) + 2 * nv (C (T + 1))) * 2 ^ T := by
        rw [← add_mul, e]
      nlinarith [ih, e']

variable (hone : w κ.oneCell = 1) (hR : ∀ r ∈ aggRowsC κ a S, r.Holds w)
include hone hR

/-- **The lengths add up**: `Σ_{i<k} nᵢ` is `cAB`'s `n` (bits `8–71` of its element `6`). -/
theorem sum_sub {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ κ.maxK)
    (hP : ∀ i < κ.maxK, (S i).ev w = if i < k then 1 else 0) :
    ∑ i ∈ range k, n8 (w (sE κ (aggChild κ a) i 15)) = n8 (w (hc (cAB κ a) 6)) := by
  set σ := aggChild κ a
  have hm2 : 2 ≤ κ.maxK := by cases κ <;> decide
  -- the masks
  have hmask : ∀ i < κ.maxK, ∀ t < 19, w (mC κ σ i t) = (S i).ev w * w (nb κ σ i t) := fun i hi t ht => by
    have hr := hR _ (mem_sub hi (r := ⟨S i, Lin.cell (nb κ σ i t), Lin.cell (mC κ σ i t)⟩)
      (by unfold subRows; simp only [List.mem_append]
          exact .inl (.inr (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩))))
    simpa using (row_ev hr).symm
  have hnb : ∀ i < κ.maxK, ∀ t < 64, w (nb κ σ i t) = 0 ∨ w (nb κ σ i t) = 1 := fun i hi t ht =>
    (bits_sub hone hR hi (show 2 < 3 by norm_num)).1 (8 + t) (by omega)
  have hmB : ∀ i < κ.maxK, ∀ t, (mL κ σ i t).ev w = 0 ∨ (mL κ σ i t).ev w = 1 := fun i hi t => by
    rw [mL_ev]
    split_ifs with ht
    · rw [hmask i hi t ht, hP i hi]
      split_ifs
      · rw [one_mul]; exact hnb i hi t (by omega)
      · left; exact zero_mul _
    · exact .inl rfl
  -- each sub-slot's masked value
  have hmval : ∀ i < κ.maxK, nOfBits (fun t => dv ((mL κ σ i t).ev w)) 21 =
      if i < k then n8 (w (sE κ σ i 15)) else 0 := fun i hi => by
    split_ifs with hik
    · have hS : (S i).ev w = 1 := by rw [hP i hi, if_pos hik]
      obtain ⟨b2, d2⟩ := bits_sub hone hR hi (show 2 < 3 by norm_num)
      set f : ℕ → Bool := fun t => decide (w (nb κ σ i t) = 1)
      have h1 : n8 (w (sE κ σ i 15)) = nOfBits f 19 := by
        rw [n8_bits, nOfBits_congr (g := f) fun t ht => bitN_dec w b2 d2 (by omega)]
        exact nOfBits_high (by norm_num) fun t h1 h2 => by
          simp only [f, decide_eq_false_iff_not]; rw [hi_zero hone hR hi hS h1 h2]; exact zero_ne_one
      rw [h1, nOfBits_high (m' := 19) (by norm_num) fun t h1 h2 => by
        simp only [mL_ev, if_neg (show ¬ t < 19 by omega), dv, decide_eq_false_iff_not]; exact zero_ne_one]
      refine nOfBits_congr fun t ht => ?_
      simp only [mL_ev, if_pos ht, hmask i hi t ht, hS, one_mul, dv, f]
    · have hS : (S i).ev w = 0 := by rw [hP i hi, if_neg hik]
      refine nOfBits_zero fun t ht => ?_
      simp only [mL_ev, dv, decide_eq_false_iff_not]
      split_ifs with h
      · rw [hmask i hi t h, hS, zero_mul]; exact zero_ne_one
      · exact zero_ne_one
  -- the adder, addition by addition
  have hacc : ∀ i < κ.maxK, (∀ t < adW, (accL κ σ i t).ev w = 0 ∨ (accL κ σ i t).ev w = 1) ∧
      nOfBits (fun t => dv ((accL κ σ i t).ev w)) adW =
        ∑ i' ∈ range (i + 1), nOfBits (fun t => dv ((mL κ σ i' t).ev w)) 21 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨fun t _ => hmB 0 (by omega) t, by simp [accL, adW]⟩
    | succ i ih =>
      intro hi
      obtain ⟨ihb, ihv⟩ := ih (by omega)
      have hA : ∀ r ∈ addRowsI κ σ (i + 1), r.Holds w := fun r hr => hR r (mem_add hi hr)
      simp only [addRowsI, Nat.add_sub_cancel, List.mem_append, List.mem_flatMap, List.mem_range,
        List.mem_cons, List.mem_nil_iff, or_false, List.mem_singleton] at hA
      have hp : ∀ t < adW, (accL κ σ i t).ev w * (mL κ σ (i + 1) t).ev w = w (pC κ σ (i + 1) t) := fun t ht => by
        simpa using row_ev (hA _ (.inl ⟨t, ht, .inl rfl⟩))
      have hc : ∀ t < adW, ((accL κ σ i t).ev w + (mL κ σ (i + 1) t).ev w) * (cL κ σ (i + 1) t).ev w =
          (cL κ σ (i + 1) (t + 1)).ev w - w (pC κ σ (i + 1) t) := fun t ht => by
        have := row_ev (hA _ (.inl ⟨t, ht, .inr rfl⟩))
        simpa [cL_ev, Lin.ev_append] using this
      have h21 : (cL κ σ (i + 1) adW).ev w = 0 := by
        have := gate_one (hA _ (.inr rfl)) (by simpa [one] using hone)
        simpa [cL_ev, adW] using this
      obtain ⟨-, hsb, e⟩ := ripple adW (fun t => (accL κ σ i t).ev w) (fun t => (mL κ σ (i + 1) t).ev w)
        (fun t => (cL κ σ (i + 1) t).ev w) (fun t => w (pC κ σ (i + 1) t)) ihb
        (fun t _ => hmB (i + 1) hi t) (by simp [cL_ev]) hp hc adW le_rfl
      simp only [h21, nv_zero, mul_zero, add_zero] at e
      refine ⟨fun t ht => by rw [accL_succ_ev]; exact hsb t ht, ?_⟩
      simp only [accL_succ_ev]
      rw [← e, ihv, sum_range_succ _ (i + 1)]; rfl
  -- the sum row
  have hlast := hacc (κ.maxK - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ κ.maxK)] at hlast
  obtain ⟨hlb, hlv⟩ := hlast
  have hs := eqR_val hone (hR _ mem_sum)
  have hP1 : (accP κ σ (κ.maxK - 1)).ev w = ∑ q ∈ range 21, E (q + 0) * (accL κ σ (κ.maxK - 1) q).ev w := by
    simp [accP, ev_flatMap_range, adW]
  rw [hP1, pkO_ev] at hs
  obtain ⟨a1, da1⟩ := bits_A hone hR (show 1 < 2 by norm_num)
  have hbit : ∀ t < 64, decide (w (aC κ σ 1 (8 + t)) = 1) = decide (t < 21 ∧ (accL κ σ (κ.maxK - 1) t).ev w = 1) := by
    intro t ht
    have := congrArg (fun x => bitF x ⟨t, by omega⟩) hs
    rw [bitF_sumO (v := fun q => (accL κ σ (κ.maxK - 1) q).ev w) (d := 0) (n := 21) (by norm_num)
        (fun q hq => hlb q hq),
      bitF_sumO (v := fun q => w (aC κ σ 1 (8 + q))) (d := 0) (n := 64) (by norm_num)
        (fun q hq => a1 _ (by omega))] at this
    simp only [Nat.sub_zero, Nat.zero_le, true_and, Nat.zero_add] at this
    rw [this]; simp [ht]
  rw [n8_bits]
  rw [nOfBits_congr (g := fun t => decide (t < 21 ∧ (accL κ σ (κ.maxK - 1) t).ev w = 1)) fun t ht => by
    rw [bitN_dec w a1 da1 (by omega), hbit t ht]]
  rw [nOfBits_high (m' := 21) (by norm_num) fun t h1 _ => by simp; omega]
  rw [nOfBits_congr (g := fun t => dv ((accL κ σ (κ.maxK - 1) t).ev w)) fun t ht => by simp [dv, ht]]
  rw [show (21 : ℕ) = adW from rfl, hlv, sum_congr rfl fun i hi => hmval i (mem_range.1 hi),
    ← sum_range_add_sum_Ico _ hkm]
  rw [sum_congr rfl fun i hi => if_pos (mem_range.1 hi), sum_eq_zero fun i hi => if_neg (by
    have := (mem_Ico.1 hi).1; omega), add_zero]

end Sum


end W4
end FR
