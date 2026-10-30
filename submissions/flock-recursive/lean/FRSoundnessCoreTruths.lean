-- G6: this module also holds the former modules `FRRSEval` (one section each, in import order).
import FRRS
import FRSoundnessCoreSteps

section G6_FRRSEval

-- New for `flock-recursive` (BLUEPRINT §2.1, §7 `FRRSEval`, BP-E-m6). Computable twins of the
-- novel-basis values, `Enc` and the tensor weights, proved equal to `FRRS`'s definitions.

/-!
# Computable twins: `Ŵ_v(D[j])`, `Enc`, the tensor weights (BLUEPRINT §2.1, §7)

Over a field `L` of characteristic 2 with a domain `pt` that is additive in the bits
(`pt (a xor b) = pt a + pt b`) and injective on `[0, 2^N)`:

* `wRow pt N v` is the table row `(Ŵ_v(pt 2^i))_{i<N}`, computed by the LCH recursion
  `Ŵ_{v+1}(y) = Ŵ_v(y)(Ŵ_v(y) − 1) / (Ŵ_v(p)(Ŵ_v(p) − 1))`, `p = pt 2^{v+1}` (`normW_succ`); all
  rows cost `O(N²)` field operations;
* `wAt pt N v j` is `Ŵ_v(pt j)` by additivity over the bits of `j` (`W_linear`), proved equal to
  `(normW pt v).eval (pt j)` (`wAt_eq`);
* `encTwin` (the computable `Enc_{2^ℓ}`) and `tensorTwin` (the verifier's `tensorW`,
  `∏_v (1 − r_v + r_v Ŵ_v(D[j]))`), proved equal to `enc` (`encTwin_eq`) and to
  `Σ_x eq(r, x) X_x(D[j])` (`tensorTwin_eq`).

The protocol instance is `pt = D`, `N = 20` (`wAtD`, `encD`).
-/

namespace FR

open Polynomial Finset

section Twin

variable {L : Type*} [Field L]

/-- **The basis table row** `v`: `(Ŵ_v(pt 2^i))_{i<N}`, by the LCH recursion on values. -/
def wRow (pt : ℕ → L) (N : ℕ) : ℕ → List L
  | 0 => (List.range N).map fun i => (pt (2 ^ i) - pt 0) / (pt 1 - pt 0)
  | v + 1 =>
    let r := wRow pt N v
    let b := r.getD (v + 1) 0
    r.map fun a => a * (a - 1) / (b * (b - 1))

/-- **`Ŵ_v(pt j)`** from the table: the sum over the set bits `i` of `j` of `Ŵ_v(pt 2^i)`. -/
def wAt (pt : ℕ → L) (N v j : ℕ) : L :=
  ∑ i ∈ range N, if j.testBit i then (wRow pt N v).getD i 0 else 0

theorem wRow_length (pt : ℕ → L) (N : ℕ) : ∀ v, (wRow pt N v).length = N
  | 0 => by simp [wRow]
  | v + 1 => by simp [wRow, wRow_length pt N v]

theorem normW_zero_eval (pt : ℕ → L) (y : L) :
    (normW pt 0).eval y = (y - pt 0) / (pt 1 - pt 0) := by
  simp [normW, eval_subW, div_eq_mul_inv, mul_comm]

variable [CharP L 2] {pt : ℕ → L} {N : ℕ}

/-- The table holds the values of `Ŵ_v` at the basis points. -/
theorem wRow_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ v, v < N → ∀ i, i < N → (wRow pt N v).getD i 0 = (normW pt v).eval (pt (2 ^ i)) := by
  intro v
  induction v with
  | zero =>
    intro _ i hi
    simp [wRow, List.getD_eq_getElem?_getD, hi, normW_zero_eval]
  | succ v ih =>
    intro hv i hi
    have hlen := wRow_length pt N v
    rw [wRow, List.getD_eq_getElem _ _ (by simpa [hlen]), List.getElem_map,
      ← List.getD_eq_getElem _ 0, ih (by omega) i hi, ih (by omega) (v + 1) hv,
      normW_succ hadd hpt hv]

omit [CharP L 2] in
/-- `pt j` is the sum of `pt 2^i` over the set bits `i` of `j < 2^ℓ`. -/
theorem pt_bits (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) :
    ∀ ℓ j, j < 2 ^ ℓ → pt j = ∑ i ∈ range ℓ, if j.testBit i then pt (2 ^ i) else 0 := by
  have h0 : pt 0 = 0 := by simpa using hadd 0 0
  apply bit_induction
  · simp [h0]
  · intro ℓ j hj ih
    rw [sum_range_succ, Nat.testBit_lt_two_pow hj, ih]; simp
  · intro ℓ j hj ih
    rw [two_pow_add_eq_xor hj, hadd, ← two_pow_add_eq_xor hj, sum_range_succ,
      Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj, ih]
    simp only [Bool.not_false, ite_true]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i hi => by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hi)]

theorem normW_eval_sum (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) {ι : Type*}
    (s : Finset ι) (g : ι → L) :
    (normW pt v).eval (∑ i ∈ s, g i) = ∑ i ∈ s, (normW pt v).eval (g i) := by
  classical
  have h0 : (normW pt v).eval 0 = 0 := by simpa using normW_add hadd v 0 0
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, normW_add hadd, ih]

/-- **`wAt_eq`**: the table value is `Ŵ_v(pt j)` (`v < N`, `j < 2^N`). -/
theorem wAt_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (hpt : Set.InjOn pt (Set.Iio (2 ^ N)))
    {v j : ℕ} (hv : v < N) (hj : j < 2 ^ N) : wAt pt N v j = (normW pt v).eval (pt j) := by
  rw [pt_bits hadd N j hj, normW_eval_sum hadd, wAt]
  refine sum_congr rfl fun i hi => ?_
  split_ifs
  · exact wRow_spec hadd hpt v hv i (mem_range.1 hi)
  · simpa using (normW_eval_sum hadd v (∅ : Finset ℕ) fun _ => (0 : L)).symm

variable {M : Type*} [Field M] [Algebra L M]

/-- **The computable `Enc_{2^ℓ}`**: `Σ_x c_x ∏_{v ∈ bits x} Ŵ_v(pt j)` from the table. -/
def encTwin (pt : ℕ → L) (N ℓ : ℕ) {n : ℕ} (c : Fin (2 ^ ℓ) → M) (j : Fin n) : M :=
  ∑ x : Fin (2 ^ ℓ), c x * bitProd (fun v => algebraMap L M (wAt pt N v j)) ℓ x

/-- **The verifier's tensor weight** `∏_{v<ℓ} (1 − r_v + r_v Ŵ_v(pt j))` (`tensorW`, A.5). -/
def tensorTwin (pt : ℕ → L) (N ℓ : ℕ) (r : ℕ → M) (j : ℕ) : M :=
  ∏ v ∈ range ℓ, (1 - r v + r v * algebraMap L M (wAt pt N v j))

theorem bitProd_map {R S : Type*} [CommMonoid R] [CommMonoid S] (φ : R →* S) (f : ℕ → R)
    (ℓ x : ℕ) : φ (bitProd f ℓ x) = bitProd (fun v => φ (f v)) ℓ x := by
  simp only [bitProd, bitSel, map_prod]
  exact prod_congr rfl fun v _ => by split_ifs <;> simp

/-- `X_x(pt j)` from the table. -/
theorem novelX_eval_twin (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ x j : ℕ} (hℓ : ℓ ≤ N) (hx : x < 2 ^ ℓ)
    (hj : j < 2 ^ N) :
    algebraMap L M ((novelX pt x).eval (pt j)) =
      bitProd (fun v => algebraMap L M (wAt pt N v j)) ℓ x := by
  rw [novelX_eq_bitProd pt hx, bitProd, bitSel, eval_prod, map_prod, bitProd, bitSel]
  refine prod_congr rfl fun v hv => ?_
  split_ifs
  · rw [wAt_eq hadd hpt (by have := mem_range.1 hv; omega) hj]
  · simp

/-- **`encTwin_eq`**: the computable encoding is `Enc_{2^ℓ}` (`ℓ ≤ N`, `n ≤ 2^N`). -/
theorem encTwin_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ n : ℕ} (hℓ : ℓ ≤ N) (hn : n ≤ 2 ^ N)
    (c : Fin (2 ^ ℓ) → M) (j : Fin n) : encTwin pt N ℓ c j = enc pt n (2 ^ ℓ) c j := by
  refine sum_congr rfl fun x _ => ?_
  rw [novelX_eval_twin hadd hpt hℓ x.2 (j.2.trans_le hn)]

/-- **`tensorTwin_eq`** (the tensor identity, computed): `tensorTwin = Σ_x eq(r, x) X_x(pt j)`. -/
theorem tensorTwin_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ j : ℕ} (hℓ : ℓ ≤ N) (hj : j < 2 ^ N) (r : ℕ → M) :
    tensorTwin pt N ℓ r j =
      ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * algebraMap L M ((novelX pt x).eval (pt j)) := by
  rw [tensorTwin, ← tensor_identity]
  exact sum_congr rfl fun x hx => by rw [novelX_eval_twin hadd hpt hℓ (mem_range.1 hx) hj]

/-! ## Values to coefficients, interpolation (S-D2; BLUEPRINT §6.2) -/

/-- `Enc` as a word indexed by `ℕ`: `encN pt c j = Σ_x c_x X_x(pt j)` (`enc pt n k c j` for
`j < n`, `enc_eq_encN`). -/
noncomputable def encN (pt : ℕ → L) {k : ℕ} (c : Fin k → M) (j : ℕ) : M :=
  ∑ x : Fin k, c x * algebraMap L M ((novelX pt x).eval (pt j))

omit [CharP L 2] in
theorem enc_eq_encN (pt : ℕ → L) {n k : ℕ} (c : Fin k → M) (j : Fin n) :
    enc pt n k c j = encN pt c j := rfl

omit [CharP L 2] in
theorem novelX_two_pow_add (pt : ℕ → L) {ℓ x : ℕ} (hx : x < 2 ^ ℓ) :
    novelX pt (2 ^ ℓ + x) = novelX pt x * normW pt ℓ := by
  rw [novelX_eq_bitProd pt (show 2 ^ ℓ + x < 2 ^ (ℓ + 1) by rw [pow_succ]; omega),
    bitProd_succ_hi _ hx, ← novelX_eq_bitProd pt hx]

/-- **The inverse additive NTT** on the coset `pt s + pt [0, 2^ℓ)`: from the values `y j` at
`pt (s + j)`, `j < 2^ℓ`, the novel-basis coefficients (`coeffsAt_spec`). One level: with
`α = Ŵ_ℓ(pt s)`, the halves give `u = c_lo + α c_hi` and `w = c_lo + (α + 1) c_hi`. -/
def coeffsAt (pt : ℕ → L) (N : ℕ) : ℕ → ℕ → (ℕ → M) → ℕ → M
  | 0, _, y => y
  | ℓ + 1, s, y => fun x =>
    let u := coeffsAt pt N ℓ s y
    let w := coeffsAt pt N ℓ (s + 2 ^ ℓ) fun j => y (2 ^ ℓ + j)
    let α := algebraMap L M (wAt pt N ℓ s)
    if x < 2 ^ ℓ then u x - α * (w x - u x) else w (x - 2 ^ ℓ) - u (x - 2 ^ ℓ)

omit [CharP L 2] in
theorem sum_novel_succ (pt : ℕ → L) (ℓ : ℕ) (c : ℕ → M) (P : L) :
    ∑ x ∈ range (2 ^ (ℓ + 1)), c x * algebraMap L M ((novelX pt x).eval P) =
      ∑ x ∈ range (2 ^ ℓ), (c x + c (2 ^ ℓ + x) * algebraMap L M ((normW pt ℓ).eval P)) *
        algebraMap L M ((novelX pt x).eval P) := by
  rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  rw [novelX_two_pow_add pt (mem_range.1 hx), eval_mul, map_mul]
  ring

/-- **`coeffsAt_spec`**: on a coset `pt s + pt [0, 2^ℓ)` (`pt (s + j) = pt s + pt j`), the
coefficients reproduce the values. -/
theorem coeffsAt_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ ℓ s (y : ℕ → M), ℓ ≤ N → s + 2 ^ ℓ ≤ 2 ^ N → (∀ j < 2 ^ ℓ, pt (s + j) = pt s + pt j) →
      ∀ j < 2 ^ ℓ, ∑ x ∈ range (2 ^ ℓ),
        coeffsAt pt N ℓ s y x * algebraMap L M ((novelX pt x).eval (pt (s + j))) = y j := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s y _ _ _ j hj
    obtain rfl : j = 0 := by simpa using hj
    simp [coeffsAt, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro s y hN hs H j hj
    have hsN : s < 2 ^ N := by have := Nat.one_le_two_pow (n := ℓ + 1); omega
    have hα : (normW pt ℓ).eval (pt s) = wAt pt N ℓ s := (wAt_eq hadd hpt (by omega) hsN).symm
    have hpow : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hW : ∀ i < 2 ^ ℓ, (normW pt ℓ).eval (pt i) = 0 := fun i hi => normW_eval_lt pt hi
    have hup : ∀ j' < 2 ^ ℓ, pt (2 ^ ℓ + j') = pt (2 ^ ℓ) + pt j' := fun j' h' => by
      rw [two_pow_add_eq_xor h', hadd]
    rw [sum_novel_succ]
    simp only [coeffsAt]
    by_cases hlo : j < 2 ^ ℓ
    · rw [H j (by omega), normW_add hadd, hW j hlo, add_zero, hα, ← H j (by omega)]
      rw [← ih s y (by omega) (by omega) (fun i hi => H i (by omega)) j hlo]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      simp only [hx', ite_true, show ¬ (2 ^ ℓ + x < 2 ^ ℓ) by omega, ite_false,
        Nat.add_sub_cancel_left]
      ring
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlo)
      have hj' : j' < 2 ^ ℓ := by omega
      have hP : pt (s + (2 ^ ℓ + j')) = pt (s + 2 ^ ℓ + j') := by rw [Nat.add_assoc]
      have H' : ∀ i < 2 ^ ℓ, pt (s + 2 ^ ℓ + i) = pt (s + 2 ^ ℓ) + pt i := fun i hi => by
        rw [Nat.add_assoc, H _ (by omega), H _ (by omega), hup i hi, add_assoc]
      have hWv : (normW pt ℓ).eval (pt (s + (2 ^ ℓ + j'))) = wAt pt N ℓ s + 1 := by
        rw [H _ (by omega), normW_add hadd, hup j' hj', normW_add hadd, hW j' hj',
          normW_eval_self hpt (by omega), add_zero, hα]
      rw [hWv, hP]
      rw [← ih (s + 2 ^ ℓ) (fun i => y (2 ^ ℓ + i)) (by omega) (by omega) H' j' hj']
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      simp only [hx', ite_true, show ¬ (2 ^ ℓ + x < 2 ^ ℓ) by omega, ite_false,
        Nat.add_sub_cancel_left, map_add, map_one]
      ring

/-- **`coeffs_of_values`**: the novel-basis message of the codeword whose values on
`pt 0, …, pt (2^ℓ − 1)` are `y` (the inverse additive NTT, `O(ℓ 2^ℓ)` butterflies). -/
def coeffsOfValues (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) : Fin (2 ^ ℓ) → M :=
  fun x => coeffsAt pt N ℓ 0 y x

/-- **`coeffs_spec`**: `Enc(coeffs_of_values y)` takes the values `y` on `pt [0, 2^ℓ)`. -/
theorem coeffs_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) (y : ℕ → M) {j : ℕ}
    (hj : j < 2 ^ ℓ) : encN pt (coeffsOfValues pt N ℓ y) j = y j := by
  have h0 : pt 0 = 0 := by simpa using hadd 0 0
  have := coeffsAt_spec hadd hpt ℓ 0 y hℓ (by simpa using Nat.pow_le_pow_right two_pos hℓ)
    (fun i _ => by simp [h0]) j hj
  rw [zero_add] at this
  rw [encN, ← this]
  exact Fin.sum_univ_eq_sum_range (fun x => coeffsAt pt N ℓ 0 y x *
    algebraMap L M ((novelX pt x).eval (pt j))) _

/-- The message is determined by the values on `pt [0, 2^ℓ)`: `coeffs_of_values` inverts
`Enc`. -/
theorem coeffs_unique (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) (y : ℕ → M)
    (c : Fin (2 ^ ℓ) → M) (hc : ∀ j < 2 ^ ℓ, encN pt c j = y j) :
    coeffsOfValues pt N ℓ y = c := by
  have hk : 2 ^ ℓ ≤ 2 ^ N := Nat.pow_le_pow_right two_pos hℓ
  refine enc_injective (n := 2 ^ ℓ) hpt hk hk le_rfl (funext fun j => ?_)
  rw [enc_eq_encN, enc_eq_encN, coeffs_spec hadd hpt hℓ y j.2, hc j j.2]

/-- **`interpF`**: Lagrange interpolation through the values `y i` at `pt i`, `i ∈ J`, evaluated at
`pt j`: `Σ_{i∈J} y_i ∏_{m ∈ J∖i} (pt j − pt m)/(pt i − pt m)`. -/
def interpF (pt : ℕ → L) (J : Finset ℕ) (y : ℕ → M) (j : ℕ) : M :=
  ∑ i ∈ J, y i * ∏ m ∈ J.erase i,
    (algebraMap L M (pt j) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m))

omit [CharP L 2] in
theorem interpF_congr (pt : ℕ → L) (J : Finset ℕ) {y y' : ℕ → M} (h : ∀ i ∈ J, y i = y' i)
    (j : ℕ) : interpF pt J y j = interpF pt J y' j :=
  sum_congr rfl fun i hi => by rw [h i hi]

omit [CharP L 2] in
/-- **`interpF_eq`**: on distinct points, `interpF` evaluates every polynomial of degree `< |J|`
from its values on `J`. -/
theorem interpF_eq {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) {p : M[X]}
    (hp : p.degree < J.card) (j : ℕ) :
    interpF pt J (fun i => p.eval (algebraMap L M (pt i))) j = p.eval (algebraMap L M (pt j)) := by
  have hv : Set.InjOn (fun i => algebraMap L M (pt i)) J := fun a ha b hb h =>
    hJ ha hb ((algebraMap L M).injective h)
  conv_rhs => rw [Lagrange.eq_interpolate hv hp]
  simp [interpF, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    eval_finsetSum, eval_prod, div_eq_inv_mul]

/-- **Erasure decoding of a row** (BLUEPRINT §6.2): if the word `u` agrees with `Enc(c)` on a set
`J` of `2^ℓ` distinct points, interpolating on `J` and taking coefficients returns `c`. -/
theorem decode_row (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) {J : Finset ℕ}
    (hJ : Set.InjOn pt J) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → M) (u : ℕ → M)
    (hu : ∀ i ∈ J, u i = encN pt c i) :
    coeffsOfValues pt N ℓ (interpF pt J u) = c := by
  refine coeffs_unique hadd hpt hℓ _ c fun j _ => ?_
  have hdeg : (encPoly pt c).degree < J.card := by
    rw [hJc]; exact mem_degreeLT.1 (encPoly_mem hpt (Nat.pow_le_pow_right two_pos hℓ) c)
  have he : ∀ i, encN pt c i = (encPoly pt c).eval (algebraMap L M (pt i)) := fun i =>
    (encPoly_eval pt (i + 1) _ c ⟨i, by omega⟩).symm
  rw [interpF_congr pt J hu, funext he, interpF_eq hJ hdeg]

end Twin

/-! ## The protocol instance: `D`, `N = logNMax = 20` -/

/-- `Ŵ_v(D[j])` from the table (`v < 20`, `j < 2^20`). -/
def wAtD (v j : ℕ) : F := wAt D logNMax v j

/-- The computable `Enc_{2^ℓ}` over `M ∈ {F, K}` on `D`. -/
def encD {M : Type*} [Field M] [Algebra F M] (ℓ : ℕ) {n : ℕ} (c : Fin (2 ^ ℓ) → M) (j : Fin n) :
    M := encTwin D logNMax ℓ c j

theorem D_injOn20 : Set.InjOn D (Set.Iio (2 ^ 20)) := D_injOn_nMax

theorem wAtD_eq {v j : ℕ} (hv : v < logNMax) (hj : j < nMax) :
    wAtD v j = (normW D v).eval (D j) :=
  wAt_eq D_xor D_injOn_nMax hv hj

theorem encD_eq {M : Type*} [Field M] [Algebra F M] {ℓ n : ℕ} (hℓ : ℓ ≤ logNMax) (hn : n ≤ nMax)
    (c : Fin (2 ^ ℓ) → M) (j : Fin n) : encD ℓ c j = enc D n (2 ^ ℓ) c j :=
  encTwin_eq D_xor D_injOn_nMax hℓ hn c j

/-- **`encF`**: the computable `Enc_{2^ℓ}` on `D` as an `ℕ`-indexed word (from the table). -/
def encF {M : Type*} [Field M] [Algebra F M] (ℓ : ℕ) (c : Fin (2 ^ ℓ) → M) (j : ℕ) : M :=
  ∑ x : Fin (2 ^ ℓ), c x * bitProd (fun v => algebraMap F M (wAtD v j)) ℓ x

theorem encF_eq {M : Type*} [Field M] [Algebra F M] {ℓ j : ℕ} (hℓ : ℓ ≤ logNMax) (hj : j < nMax)
    (c : Fin (2 ^ ℓ) → M) : encF ℓ c j = encN D c j :=
  sum_congr rfl fun x _ => by rw [novelX_eval_twin D_xor D_injOn_nMax hℓ x.2 hj]; rfl

/-- `coeffs_of_values` on `D` (`ℓ ≤ 20`): values on `D[0, 2^ℓ)` to the message. -/
def coeffsOfValuesD {M : Type*} [Field M] [Algebra F M] (ℓ : ℕ) (y : ℕ → M) : Fin (2 ^ ℓ) → M :=
  coeffsOfValues D logNMax ℓ y

/-- **The extractor's row decoding on `D`** (BLUEPRINT §6.2): `2^ℓ` agreement positions
`J ⊆ [0, 2^20)` of a word `u` with `Enc(c)` give back `c`. -/
theorem decode_row_D {M : Type*} [Field M] [Algebra F M] {ℓ : ℕ} (hℓ : ℓ ≤ logNMax)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < nMax) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → M)
    (u : ℕ → M) (hu : ∀ i ∈ J, u i = encN D c i) :
    coeffsOfValuesD ℓ (interpF D J u) = c :=
  decode_row D_xor D_injOn_nMax hℓ (fun _ ha _ hb h => D_injOn_nMax (hJN _ ha) (hJN _ hb) h)
    hJc c u hu

end FR

end G6_FRRSEval

section G6_FRSoundnessCoreTruths

-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessStepA` (10), `FRSoundnessStepB` (10),
-- `FRSoundnessStepC` (3), `FRSoundnessTruths` (18). Content: 3.x positions and readers (`phStart`,
-- `capPos`, `wordOf`), the level parameters (`lvN`, `lvK`, `lvE`) and the per-level truths the
-- decoder reads (`wordK`, `foldAt`, `sAt`, `msgOf`, `decodeL`, `farL`, `consSet`, …). The 3.x
-- modules import this one.

/-! ## From `FRSoundnessStepA` (10 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

/-- **The kind of a chain**: the header's first byte (byte 71 of the seed query
`"FRSEED0" ‖ vk ‖ c ‖ hdr`); `L32` if it is not a kind byte. -/
def kindOf (es : Log) : Kind := (((entAt es 0).1.data[71]?).bind Kind.ofByte?).getD .L32

theorem kindOf_congr {es es' : Log} (h : Agree es es' 1) : kindOf es = kindOf es' := by
  simp only [kindOf, h 0 one_pos]

/-- The Fiat–Shamir position of each phase's first item, in the order of `phases` (a phase with
no Fiat–Shamir item, `Q`, gets the position of the next one). -/
def fsStarts : List ℕ :=
  (phases.foldl (fun (acc : ℕ × List ℕ) p =>
    (acc.1 + (p.shape.items.filter Item.isFS).length, acc.2 ++ [acc.1])) (0, [])).2

/-- The first Fiat–Shamir position of phase `k` of `phases`. -/
def phStart (k : ℕ) : ℕ := fsStarts.getD k 0

/-- Control: the phase starts (A.4; `piopPhases` are phases `0 … 25` (revision 3.12: E4 at 24), level `i`'s
`P1, C, P2, Q, P3` are `26 + 5i … 30 + 5i`, `Pf` is `51`). -/
theorem fsStarts_eq : fsStarts = [0, 1, 2, 3, 13, 15, 67, 68, 69, 97, 98, 99, 114, 170, 178, 208,
    209, 210, 221, 263, 264, 265, 311, 312, 313, 317, 318, 330, 331, 356, 356, 361, 369, 370, 383,
    383, 388, 396, 397, 407, 407, 412, 420, 421, 429, 429, 434, 442, 443, 449, 449, 454] := by
  decide +kernel

/-- The position of level `i`'s cap absorb: `cap₀` (phase 2), else `C.(i − 1)` (phase `22 + 5i`). -/
def capPos (i : ℕ) : ℕ := if i = 0 then phStart 2 else phStart (22 + 5 * i)

/-- Cap entry `c` of level `i`: the 32 bytes at offset `32c` of the cap's message (A.2). -/
def capDig (es : Log) (i c : ℕ) : Digest := bytesAt (msgAt es (capPos i)) (32 * c) 32

/-- **The column of level `i` at position `p`** for kind `k`, read off `L` top-down from its cap
entry (`p / 2^sib`) along the bits of `p` (`colL (frEnc i)`, height `sib = log₂ n − cap`). -/
def colOf (k : Kind) (L es : Log) (i p : ℕ) : Option ByteArray :=
  colL (frEnc i) L (capDig es i (p / 2 ^ (lvl k i).sib)) (lvl k i).sib p

/-- **The committed word of level `i`**: row `r` at position `p` is the column's F element `r`
(16 bytes each, row 0 first, A.2); `0` where `L` reads no column. -/
def wordOf (k : Kind) (L es : Log) (i : ℕ) : Fin (lvl k i).rows → Fin (2 ^ (lvl k i).logN) → F :=
  fun r p => ((colOf k L es i p).map fun col => readF col (16 * r)).getD 0

/-- The column depends on the entries up to the cap's absorb only. -/
theorem colOf_congr (k : Kind) (L : Log) {es es' : Log} (i p : ℕ)
    (h : Agree es es' (capPos i + 1)) : colOf k L es i p = colOf k L es' i p := by
  simp only [colOf, capDig, msgAt, h (capPos i) (by omega)]

end FR.Snd

end

/-! ## From `FRSoundnessStepB` (10 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

section Rounds3

variable (b : ℕ)

variable (c0 : Log → Log → F)

variable (nr : Kind → ℕ)

/-- The rounds answered by the entries `es`: `min (nr (kindOf es)) ⌊(|es| − b)/2⌋`. -/
def ans3 (es : Log) : ℕ := min (nr (kindOf es)) ((es.length - b) / 2)

variable (e : Expr) (T : Log → Log → Array (Array F))

/-- The claim after `l` rounds is not the true sum of the tables bound at the first `l`
challenges. -/
def Wrong3 (L es : Log) (l : ℕ) : Prop :=
  clR b c0 L es l ≠ trueSum e (bindAll (T L es) (rchs b es l)) (nr (kindOf es) - l)

/-- **The round doom** (§5.2 row Z3): past the phase's first absorb, the running claim after the
answered rounds is false. -/
def D3 (L es : Log) : Prop := b < es.length ∧ Wrong3 b c0 nr e T L es (ans3 b nr es)

variable {b c0 nr e T}

theorem wrong3_congr (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) : Wrong3 b c0 nr e T L es l ↔ Wrong3 b c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong3, clR_congr hc h, rchs_congr h, hT, kindOf_congr (hb.mono hb1)]

theorem kindOf_append {es : Log} (x : ByteArray × Digest) (h : 0 < es.length) :
    kindOf (es ++ [x]) = kindOf es :=
  kindOf_congr (agree_append es [x] h)

/-- When the next position is not a real round's squeeze, appending keeps the answered rounds and
the doom. -/
theorem D3_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2) :
    D3 b c0 nr e T L (es ++ [x]) ↔ D3 b c0 nr e T L es := by
  have hk := kindOf_append x (show 0 < es.length by omega)
  have ha : ans3 b nr (es ++ [x]) = ans3 b nr es := by
    simp only [ans3, hk, List.length_append, List.length_singleton]
    rcases hc with hc | hc
    · rw [show (es.length + 1 - b) / 2 = (es.length - b) / 2 by omega]
    · rw [min_eq_left hc, min_eq_left (le_trans hc (Nat.div_le_div_right (by omega)))]
  have hle : b + 2 * ans3 b nr es ≤ es.length := by
    have : ans3 b nr es ≤ (es.length - b) / 2 := min_le_right _ _
    omega
  simp only [D3, ha, List.length_append, List.length_singleton]
  rw [wrong3_congr hb1 hTc (agree_append es [x] hle)]
  exact ⟨fun h => ⟨hlen, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem not_D3_short {L es : Log} (h : es.length ≤ b) : ¬ D3 b c0 nr e T L es :=
  fun hd => by have := hd.1; omega

/-- At a real round's squeeze, the extension answers one more round, and its claim and truth
are the round polynomial and the bound tables at the answer's first F coordinate. -/
theorem wrong3_ext1 (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (L es : Log) (a : Digest) {j : ℕ}
    (hj : es.length = b + 2 * j + 1) :
    Wrong3 b c0 nr e T L (ext1 es a) (j + 1) ↔
      peval (g3At b es j (clR b c0 L es j)) (chF a 0) ≠
        trueSum e ((bindAll (T L es) (rchs b es j)).map (bind0 · (chF a 0)))
          (nr (kindOf es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
  have hr : rch b (ext1 es a) j = chF a 0 := by
    simp only [rch, fAt, ansAt]
    rw [← hj, entAt_ext1]
  obtain ⟨hT, hc0⟩ := hTc L (ext1 es a) es (hA.mono (by omega))
  have hcl : clR b c0 L (ext1 es a) j = clR b c0 L es j :=
    clR_congr (l := j) hc0 (hA.mono (by omega))
  have hg : g3At b (ext1 es a) j (clR b c0 L es j) = g3At b es j (clR b c0 L es j) := by
    simp only [g3At, msgAt, hA (b + 2 * j) (by omega)]
  have hrs : rchs b (ext1 es a) j = rchs b es j := rchs_congr (l := j) (hA.mono (by omega))
  simp only [Wrong3, clR, hcl, hg, hr, rchs_succ, hrs, hT, hk, bindAll_append]

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **The round row** (§5.2 Z3): from a doomed claim, at most `3·2^128` answers make the next
claim true. -/
theorem D3_single (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (he : e.deg = 3)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOf es)) (L es : Log) :
    (Finset.univ.filter fun a => D3 b c0 nr e T L es ∧ ¬ D3 b c0 nr e T L (ext1 es a)).card ≤
      3 * 2 ^ 128 := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D3_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2 ((D3_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOf es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong3 b c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs b es j), t.size = 2 ^ (nr (kindOf es) - j - 1 + 1) := by
    refine bindAll_size (rchs b es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs b es j)) hts
    (claim := clR b c0 L es j) (by
      rw [show nr (kindOf es) - j - 1 + 1 = nr (kindOf es) - j by omega]; exact hw)
    (g3At b es j (clR b c0 L es j))
  refine le_trans (Finset.card_le_card (t := Finset.univ.filter fun a : Digest => chF a 0 ∈ _)
    fun a ha => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  have hnd : ¬ D3 b c0 nr e T L (ext1 es a) := by
    rw [Finset.mem_filter] at ha; exact ha.2.2
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong3 b c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong3_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨by rw [he]; rfl, g3_check es j _⟩, ?_⟩
  rw [hnw, show nr (kindOf es) - (j + 1) = nr (kindOf es) - j - 1 by omega]

theorem D3_log_congr {L L' X : Log} (hT : T L' X = T L X) (hc : c0 L' X = c0 L X) :
    D3 b c0 nr e T L' X ↔ D3 b c0 nr e T L X := by
  simp only [D3, Wrong3, clR_log_congr hc, hT]

end Rounds3

end FR.Snd

end

/-! ## From `FRSoundnessStepC` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- The proximity parameters of level `i` of kind `κ`: `n = 2^log₂n`, `k = n/2^(i+1)`,
`e = ⌊(n − k)/2⌋` (§2.2). -/
def lvN (κ : Kind) (i : ℕ) : ℕ := 2 ^ (lvl κ i).logN

def lvK (κ : Kind) (i : ℕ) : ℕ := lvN κ i / 2 ^ (i + 1)

def lvE (κ : Kind) (i : ℕ) : ℕ := (lvN κ i - lvK κ i) / 2

end FR.Snd

end

/-! ## From `FRSoundnessTruths` (18 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- Level `i`'s word in K. -/
noncomputable def wordK (κ : Kind) (L es : Log) (i : ℕ) :
    Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K :=
  fun r p => algebraMap F K (wordOf κ L es i r p)

/-- Level `i`'s code: `RS[K, D, kᵢ]` on the `nᵢ` points `D j` (`encCode_eq_rsCode`). -/
noncomputable def codeK (κ : Kind) (i : ℕ) : Submodule K (Fin (2 ^ (lvl κ i).logN) → K) :=
  rsCode (Dpts (2 ^ (lvl κ i).logN)) (lvK κ i)

/-- **`far_i`**: no agreement set makes level `i`'s word jointly `eᵢ`-close to the code. -/
def farL (κ : Kind) (L es : Log) (i : ℕ) : Prop :=
  ∀ A, ¬ JointClose (codeK κ i) (lvE κ i) (wordK κ L es i) A

theorem not_farL_iff {κ : Kind} {L es : Log} {i : ℕ} :
    ¬ farL κ L es i ↔ ∃ V : Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K,
      (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (lvl κ i).logN - lvE κ i ≤ (jointAgree (wordK κ L es i) V).card := by
  simp only [farL, JointClose, not_forall, not_not]
  constructor
  · rintro ⟨A, hA, V, hV, rfl⟩; exact ⟨V, hV, hA⟩
  · rintro ⟨V, hV, hA⟩; exact ⟨_, hA, V, hV, rfl⟩

open Classical in
/-- **`decodeL`**: the codeword rows of a close word (A.10's `f⁽ⁱ⁾`, before `interp_F` /
`coeffs_of_values`); `0` when far. -/
noncomputable def decodeL (κ : Kind) (L es : Log) (i : ℕ) :
    Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K :=
  if h : ¬ farL κ L es i then Classical.choose (not_farL_iff.mp h) else 0

theorem decodeL_spec {κ : Kind} {L es : Log} {i : ℕ} (h : ¬ farL κ L es i) :
    (∀ r, decodeL κ L es i r ∈ codeK κ i) ∧
      2 ^ (lvl κ i).logN - lvE κ i ≤ (jointAgree (wordK κ L es i) (decodeL κ L es i)).card := by
  rw [decodeL, dite_eq_left h]
  exact Classical.choose_spec (not_farL_iff.mp h)

/-- P1.i's fold challenge `l` (K): the answer of round `l`'s squeeze. -/
def sAt (es : Log) (i l : ℕ) : K := kAt es (phStart (26 + 5 * i) + 2 * l + 1)

/-- **The column fold `y_j`** of level `i` at position `j`: `Σ_r eq(sᵢ, r)·W⁽ⁱ⁾[r][j]`. -/
noncomputable def foldAt (κ : Kind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (lvl κ i).logN)) : K :=
  ∑ r : Fin (lvl κ i).rows, eqBits (sAt es i) (lvl κ i).ell r * wordK κ L es i r j

/-- `log₂ kᵢ`: level `i`'s message length is `kᵢ = nᵢ / 2^(i+1) = 2^mLog`. -/
def mLog (κ : Kind) (i : ℕ) : ℕ := (lvl κ i).logN - (i + 1)

/-- **Row `r`'s message** of level `i`'s decoded word (`f⁽ⁱ⁾`'s row `r`: novel-basis
coefficients by `coeffs_of_values` on `D[0, kᵢ)`); `0` past the rows or the message. -/
noncomputable def msgOf (κ : Kind) (L es : Log) (i r : ℕ) : ℕ → K := fun x =>
  if hr : r < (lvl κ i).rows then
    if hx : x < 2 ^ mLog κ i then
      coeffsOfValuesD (mLog κ i) (fun j => if hj : j < 2 ^ (lvl κ i).logN then
        decodeL κ L es i ⟨r, hr⟩ ⟨j, hj⟩ else 0) ⟨x, hx⟩
    else 0
  else 0

/-- `f⁽ⁱ⁾` as a table over level `i`'s variables (row bits first, as P1.i folds them). -/
noncomputable def fTab (κ : Kind) (L es : Log) (i y : ℕ) : K :=
  msgOf κ L es i (y % (lvl κ i).rows) (y / (lvl κ i).rows)

/-- The final message's element `x` (absorbed at C.4, phase 46). -/
def finalAt (es : Log) (x : ℕ) : K := readK (msgAt es (phStart 47)) (32 * x)

/-- **`f⁽ⁱ⁺¹⁾` as level `i`'s folded message**: K element `x` from level `i + 1`'s rows
`2(x mod 8)` and `2(x mod 8) + 1`, column `x div 8` (`i < 4`); the final message (`i = 4`). -/
noncomputable def nextMsg (κ : Kind) (L es : Log) (i x : ℕ) : K :=
  if i + 1 < nLevels then
    msgOf κ L es (i + 1) (2 * (x % 8)) (x / 8) +
      K.u * msgOf κ L es (i + 1) (2 * (x % 8) + 1) (x / 8)
  else finalAt es x

/-- Level `i`'s encoding of a message at position `j` (`Enc_{kᵢ}` in the novel basis on `D`). -/
noncomputable def encAt (κ : Kind) (i : ℕ) (m : ℕ → K) (j : ℕ) : K :=
  encF (mLog κ i) (fun x => m x) j

/-- **P2.i's consistency set `A_c`** (A.10): the positions where the column fold agrees with the
next level's codeword. -/
noncomputable def consSet (κ : Kind) (L es : Log) (i : ℕ) : Finset (Fin (2 ^ (lvl κ i).logN)) :=
  univ.filter fun j => foldAt κ L es i j = encAt κ i (nextMsg κ L es i) j

/-- The level parameters the uniqueness argument uses (checked per level and kind). -/
theorem lv_params (κ : Kind) {i : ℕ} (hi : i < 5) :
    2 * lvE κ i + lvK κ i ≤ lvN κ i ∧ lvN κ i ≤ nMax ∧ mLog κ i ≤ logNMax ∧
      lvK κ i = 2 ^ mLog κ i ∧ lvN κ i = 2 ^ (lvl κ i).logN := by
  cases κ <;> interval_cases i <;> decide

/-- A codeword of level `i`'s code is `Enc` of a message of `2^mLog` coefficients. -/
theorem exists_msg {κ : Kind} {i : ℕ} (hi : i < 5) {v : Fin (2 ^ (lvl κ i).logN) → K}
    (hv : v ∈ codeK κ i) : ∃ c : Fin (2 ^ mLog κ i) → K, enc D _ _ c = v := by
  obtain ⟨-, hN, -, hk, hn⟩ := lv_params κ hi
  rw [codeK, hk, ← encCode_D (by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN)]
    at hv
  exact LinearMap.mem_range.mp hv

/-- `coeffs_of_values` gives back the message of a codeword. -/
theorem msgOf_eq {κ : Kind} {L es : Log} {i : ℕ} (hi : i < 5) {r : Fin (lvl κ i).rows}
    {c : Fin (2 ^ mLog κ i) → K} (hc : enc D _ _ c = decodeL κ L es i r) (x : Fin (2 ^ mLog κ i)) :
    msgOf κ L es i r x = c x := by
  obtain ⟨-, hN, hm, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (lvl κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  simp only [msgOf, r.2, x.2, dite_true]
  rw [coeffsOfValuesD, coeffs_unique D_xor D_injOn_nMax hm _ c fun j hj => ?_]
  simp only [show j < 2 ^ (lvl κ i).logN from lt_of_lt_of_le hj hkn, dite_true]
  rw [← hc, enc_eq_encN]

end FR.Snd

end

end G6_FRSoundnessCoreTruths
