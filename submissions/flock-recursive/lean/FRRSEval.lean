-- New for `flock-recursive` (BLUEPRINT §2.1, §7 `FRRSEval`, BP-E-m6). Computable twins of the
-- novel-basis values, `Enc` and the tensor weights, proved equal to `FRRS`'s definitions.
import FRRS

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
    (algebraMap L M (pt j) - algebraMap L M (pt m)) / (algebraMap L M (pt i) - algebraMap L M (pt m))

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
