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

end Twin

/-! ## The protocol instance: `D`, `N = 20` -/

/-- `Ŵ_v(D[j])` from the table (`v < 20`, `j < 2^20`). -/
def wAtD (v j : ℕ) : F := wAt D 20 v j

/-- The computable `Enc_{2^ℓ}` over `M ∈ {F, K}` on `D`. -/
def encD {M : Type*} [Field M] [Algebra F M] (ℓ : ℕ) {n : ℕ} (c : Fin (2 ^ ℓ) → M) (j : Fin n) :
    M := encTwin D 20 ℓ c j

theorem D_injOn20 : Set.InjOn D (Set.Iio (2 ^ 20)) :=
  D_injOn.mono (Set.Iio_subset_Iio (by norm_num))

theorem wAtD_eq {v j : ℕ} (hv : v < 20) (hj : j < 2 ^ 20) : wAtD v j = (normW D v).eval (D j) :=
  wAt_eq D_xor D_injOn20 hv hj

theorem encD_eq {M : Type*} [Field M] [Algebra F M] {ℓ n : ℕ} (hℓ : ℓ ≤ 20) (hn : n ≤ 2 ^ 20)
    (c : Fin (2 ^ ℓ) → M) (j : Fin n) : encD ℓ c j = enc D n (2 ^ ℓ) c j :=
  encTwin_eq D_xor D_injOn20 hℓ hn c j

end FR
