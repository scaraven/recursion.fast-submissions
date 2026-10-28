-- New for `flock-recursive` (BLUEPRINT §6.2 step 4: `Enc(g⁽ⁱ⁺¹⁾)`; stage S-H2, track L-ext).
import FRXDecodeB

/-!
# The forward butterflies: `Enc` on the machine's array (pure half)

BLUEPRINT §6.2 step 4 needs `Enc(f⁽ⁱ⁺¹⁾)` at every position of level `i`. S-D2's `encF` is the
sum `Σ_x c_x X_x(D j)`. A machine computes it as the forward additive NTT. That is the inverse of
`FRXDecodeB.bflyRun`, run top-down and in place. Level `l` maps the halves `u` (low) and `w` (high)
of each block of `2^(l+1)` to `u + α w` and `u + α w + w`, with `α = Ŵ_l(D base)`.

* `fwdRun_block`: after the levels `ℓ − 1, …, 0`, block `b` of size `2^ℓ` holds the values of
  its own coefficients on `D[b·2^ℓ, (b+1)·2^ℓ)`.
* **`fwdRun_enc`**: from a message of `2^m` coefficients zero-padded to `2^n`, the run of `n`
  levels gives `encF m c j` at every `j < 2^n`. One run covers all `2^(n−m)` cosets, so no coset
  offset is needed.
-/

namespace FR.X

open FR Finset Polynomial

/-- `b·2^k + j = b·2^k ⊕ j` for `j < 2^k`. -/
theorem mul_two_pow_add_eq_xor {b k j : ℕ} (hj : j < 2 ^ k) : b * 2 ^ k + j = b * 2 ^ k ^^^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hj, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : i < k
  · simp [h, show ¬ (k ≤ i) by omega]
  · rw [if_neg h, Nat.testBit_lt_two_pow (hj.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    simp [show k ≤ i by omega]

/-- `D` is additive on an aligned block: `D (b·2^k + j) = D (b·2^k) + D j` (`j < 2^k`). -/
theorem D_block {b k j : ℕ} (hj : j < 2 ^ k) : D (b * 2 ^ k + j) = D (b * 2 ^ k) + D j := by
  rw [mul_two_pow_add_eq_xor hj, D_xor]

section Fwd

variable {M : Type*} [Field M] [Algebra F M]

/-- **One forward level** `l`: in each block of `2^(l+1)` at `base`, the halves `u` (low) and
`w` (high) become `u + α w` (low) and `u + α w + w` (high), `α = Ŵ_l(D base)` (`bflyLevel`'s
inverse). -/
def fwdLevel (l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap F M (wAtD l base)
  if x < 2 ^ l then u + α * w else u + α * w + w

/-- **The forward iteration**: levels `ℓ − 1, ℓ − 2, …, 0`. -/
def fwdRun : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => fwdRun l (fwdLevel l A)

/-- `Ŵ_ℓ` on the block `b` of size `2^(ℓ+1)`: `Ŵ_ℓ(D(b·2^(ℓ+1) + j))` is `α` on the low half and
`α + 1` on the high half. -/
theorem normW_block {ℓ b j : ℕ} (hN : (b + 1) * 2 ^ (ℓ + 1) ≤ nMax) (hj : j < 2 ^ (ℓ + 1)) :
    (normW D ℓ).eval (D (b * 2 ^ (ℓ + 1) + j)) =
      wAtD ℓ (b * 2 ^ (ℓ + 1)) + if j < 2 ^ ℓ then 0 else 1 := by
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hℓ : ℓ < logNMax := by
    by_contra h
    have : 2 ^ (logNMax + 1) ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (ℓ + 1) ≤ (b + 1) * 2 ^ (ℓ + 1) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [nMax, logNMax] at hN this; omega
  have hb : b * 2 ^ (ℓ + 1) < nMax := by
    have : 0 < 2 ^ (ℓ + 1) := by positivity
    nlinarith
  rw [D_block hj, normW_add D_xor, wAtD_eq hℓ hb]
  congr 1
  split_ifs with h
  · exact normW_eval_lt D h
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    rw [two_pow_add_eq_xor (show j' < 2 ^ ℓ by omega), D_xor, normW_add D_xor,
      normW_eval_lt D (show j' < 2 ^ ℓ by omega), add_zero]
    exact normW_eval_self D_injOn_nMax hℓ

/-- **The block invariant**: after the levels `ℓ − 1, …, 0`, position `j` of block `b` holds the
value at `D(b·2^ℓ + j)` of the block's coefficients. -/
theorem fwdRun_block : ∀ (ℓ : ℕ) (A : ℕ → M) (b j : ℕ), j < 2 ^ ℓ → (b + 1) * 2 ^ ℓ ≤ nMax →
    fwdRun ℓ A (b * 2 ^ ℓ + j) = ∑ x ∈ range (2 ^ ℓ),
      A (b * 2 ^ ℓ + x) * algebraMap F M ((novelX D x).eval (D (b * 2 ^ ℓ + j))) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro A b j hj _
    obtain rfl : j = 0 := by simpa using hj
    simp [fwdRun, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro A b j hj hN
    have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ ℓ := by positivity
    -- the level's value at the two halves
    have hval : ∀ x < 2 ^ ℓ, ∀ e < 2, fwdLevel ℓ A ((2 * b + e) * 2 ^ ℓ + x) =
        A (b * 2 ^ (ℓ + 1) + x) + algebraMap F M (wAtD ℓ (b * 2 ^ (ℓ + 1))) *
          A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) + if e = 0 then 0 else A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) := by
      intro x hx e he
      have hi : (2 * b + e) * 2 ^ ℓ + x = b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x) := by rw [hp]; ring
      have hlt : e * 2 ^ ℓ + x < 2 ^ (ℓ + 1) := by
        rw [hp]; interval_cases e <;> omega
      have hdiv : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) / 2 ^ (ℓ + 1) = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
      have hmod : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) % 2 ^ (ℓ + 1) = e * 2 ^ ℓ + x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      have hxm : (e * 2 ^ ℓ + x) % 2 ^ ℓ = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [hi, fwdLevel]
      simp only [hdiv, hmod, hxm]
      interval_cases e
      · simp [hx]
      · rw [if_neg (by omega), if_neg (by omega)]
    -- the target, split by the top coefficient bit
    have hN' : (2 * b + 1 + 1) * 2 ^ ℓ ≤ nMax := by
      have : (2 * b + 1 + 1) * 2 ^ ℓ = (b + 1) * 2 ^ (ℓ + 1) := by rw [hp]; ring
      omega
    have key : ∀ e < 2, ∀ j' < 2 ^ ℓ, j = e * 2 ^ ℓ + j' →
        fwdRun (ℓ + 1) A (b * 2 ^ (ℓ + 1) + j) = ∑ x ∈ range (2 ^ (ℓ + 1)),
          A (b * 2 ^ (ℓ + 1) + x) * algebraMap F M ((novelX D x).eval (D (b * 2 ^ (ℓ + 1) + j))) := by
      intro e he j' hj' hjj
      have hpos2 : b * 2 ^ (ℓ + 1) + j = (2 * b + e) * 2 ^ ℓ + j' := by rw [hjj, hp]; ring
      rw [fwdRun, hpos2, ih (fwdLevel ℓ A) (2 * b + e) j' hj' (by
        have : (2 * b + e + 1) * 2 ^ ℓ ≤ (2 * b + 1 + 1) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ (by omega)
        omega)]
      rw [← hpos2, sum_novel_succ, normW_block (by rwa [show (b + 1) * 2 ^ (ℓ + 1) =
        (2 * b + 1 + 1) * 2 ^ ℓ by rw [hp]; ring]) hj]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      rw [hval x hx' e he]
      have hjlt : (j < 2 ^ ℓ) ↔ e = 0 := by
        constructor
        · intro h; by_contra h'; have : e = 1 := by omega
          subst this; omega
        · intro h; subst h; omega
      by_cases h0 : e = 0
      · rw [if_pos h0, if_pos (hjlt.2 h0), Nat.add_assoc, add_zero, add_zero]; ring
      · rw [if_neg h0, if_neg (fun h => h0 (hjlt.1 h)), Nat.add_assoc, map_add, map_one]; ring
    by_cases hlo : j < 2 ^ ℓ
    · exact key 0 (by norm_num) j hlo (by ring)
    · exact key 1 (by norm_num) (j - 2 ^ ℓ) (by rw [hp] at hj; omega) (by omega)

/-- **The forward run is `Enc`**: on a message `c` of `2^m` coefficients zero-padded to `2^n`
(`m ≤ n ≤ 20`), the `n` forward levels give `encF m c j` at every position `j < 2^n`. -/
theorem fwdRun_enc {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ logNMax) (c : Fin (2 ^ m) → M)
    (A : ℕ → M) (hA : ∀ x, A x = if h : x < 2 ^ m then c ⟨x, h⟩ else 0) {j : ℕ} (hj : j < 2 ^ n) :
    fwdRun n A j = encF m c j := by
  have hnN : 2 ^ n ≤ nMax := Nat.pow_le_pow_right (by norm_num) hn
  have hN : (0 + 1) * 2 ^ n ≤ nMax := by omega
  have h := fwdRun_block n A 0 j hj hN
  simp only [Nat.zero_mul, Nat.zero_add] at h
  have hm : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmn
  rw [h, encF_eq (hmn.trans hn) (hj.trans_le hnN), encN,
    ← sum_range_add_sum_Ico _ hm, sum_eq_zero (s := Ico _ _) (fun x hx => by
      rw [hA x, dif_neg (by have := (mem_Ico.1 hx).1; omega), zero_mul]), add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun x => A x * algebraMap F M ((novelX D x).eval (D j)))]
  exact sum_congr rfl fun x _ => by rw [hA x, dif_pos x.2]

end Fwd

/-! ## Controls -/

/-- **Positive control**: one level on two points is `(u + α w, u + α w + w)`, `α = Ŵ₀(D 0)`. -/
theorem fwdRun_one (A : ℕ → F) :
    fwdRun 1 A 0 = A 0 + wAtD 0 0 * A 1 ∧ fwdRun 1 A 1 = A 0 + wAtD 0 0 * A 1 + A 1 := by
  simp [fwdRun, fwdLevel]

/-- **Inverse control**: on two points the forward level undoes `bflyRun`'s (so the forward
butterflies invert the decoder's, they are not a second inverse NTT). -/
theorem fwd_bfly_one (Y : ℕ → F) :
    fwdRun 1 (bflyRun D logNMax 0 1 Y) 0 = Y 0 ∧ fwdRun 1 (bflyRun D logNMax 0 1 Y) 1 = Y 1 := by
  obtain ⟨h0, h1⟩ := bflyRun_one (M := F) D logNMax 0 Y
  obtain ⟨f0, f1⟩ := fwdRun_one (bflyRun D logNMax 0 1 Y)
  rw [f0, f1, h0, h1]
  simp only [wAtD, Algebra.algebraMap_self, RingHom.id_apply]
  constructor <;> ring

end FR.X
