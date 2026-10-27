-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, §6.5 `coeffs_spec`; stage S-H2, track L-ext).
import FRRSEval

/-!
# The butterfly inverse NTT, iterative (phase 5, pure half)

S-D2's `coeffsAt` (`FRRSEval`) is the inverse additive NTT written top-down: the coefficients
on a coset of `2^(ℓ+1)` points are merged from those of its two halves. A machine runs it
bottom-up, in place: level `l = 0, 1, …` merges adjacent blocks of `2^l` into blocks of
`2^(l+1)`, `O(ℓ · 2^ℓ)` butterflies in all. This module defines that iteration on an array
(`bflyLevel`, `bflyRun`) and proves it equal to `coeffsAt` (`bflyRun_block`, `bflyRun_eq`), hence
to `coeffsOfValues` and, through `decode_row_D`, to the message of a codeword on `2^ℓ` agreeing
positions (`bfly_decode_D`). The machine program and its simulation are the next step.

The array is indexed from `0`; block `b` of level `l` covers `[b·2^l, (b+1)·2^l)` and holds the
coefficients on the coset at `s₀ + b·2^l` (`s₀` the array's domain offset).
-/

namespace FR.X

open FR Finset

section Bfly

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **One butterfly level** `l`: in each block of `2^(l+1)` at `base`, the halves' coefficients
`u` (low) and `w` (high) merge into `u − α (w − u)` (low) and `w − u` (high), with
`α = Ŵ_l(pt (s₀ + base))` (`coeffsAt`'s step). -/
def bflyLevel (pt : ℕ → L) (N s0 l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap L M (wAt pt N l (s0 + base))
  if x < 2 ^ l then u - α * (w - u) else w - u

/-- **The iteration**: levels `0, …, ℓ − 1`. -/
def bflyRun (pt : ℕ → L) (N s0 : ℕ) : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => bflyLevel pt N s0 l (bflyRun pt N s0 l A)

/-- **The block invariant**: after `l` levels, block `b` holds `coeffsAt` of its coset. -/
theorem bflyRun_block (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) :
    ∀ l b x, x < 2 ^ l → bflyRun pt N s0 l y (b * 2 ^ l + x) =
      coeffsAt pt N l (s0 + b * 2 ^ l) (fun j => y (b * 2 ^ l + j)) x := by
  intro l
  induction l with
  | zero =>
    intro b x hx
    obtain rfl : x = 0 := by simpa using hx
    simp [bflyRun, coeffsAt]
  | succ l ih =>
    intro b x hx
    have hp : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := by positivity
    have hdiv : (b * 2 ^ (l + 1) + x) / 2 ^ (l + 1) = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx,
        Nat.zero_add]
    have hmod : (b * 2 ^ (l + 1) + x) % 2 ^ (l + 1) = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    have hu := ih (2 * b) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have hw := ih (2 * b + 1) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have e1 : 2 * b * 2 ^ l = b * 2 ^ (l + 1) := by rw [hp]; ring
    have e2 : (2 * b + 1) * 2 ^ l = b * 2 ^ (l + 1) + 2 ^ l := by rw [hp]; ring
    rw [e1] at hu
    rw [e2] at hw
    simp only [bflyRun, bflyLevel, hdiv, hmod, coeffsAt]
    rw [hu, hw]
    have hY : (fun j => y (b * 2 ^ (l + 1) + 2 ^ l + j)) =
        fun j => (fun j => y (b * 2 ^ (l + 1) + j)) (2 ^ l + j) := by
      funext j; rw [Nat.add_assoc]
    rw [hY, ← Nat.add_assoc]
    by_cases hx' : x < 2 ^ l
    · rw [if_pos hx', if_pos hx', Nat.mod_eq_of_lt hx']
    · rw [if_neg hx', if_neg hx', show x % 2 ^ l = x - 2 ^ l by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]

/-- **The iteration is `coeffsAt`** on the array's first `2^ℓ` entries. -/
theorem bflyRun_eq (pt : ℕ → L) (N s0 ℓ : ℕ) (y : ℕ → M) {i : ℕ} (hi : i < 2 ^ ℓ) :
    bflyRun pt N s0 ℓ y i = coeffsAt pt N ℓ s0 y i := by
  simpa using bflyRun_block pt N s0 y ℓ 0 i hi

/-- From offset `0`, the iteration is `coeffsOfValues`. -/
theorem bflyRun_coeffs (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) (i : Fin (2 ^ ℓ)) :
    bflyRun pt N 0 ℓ y i = coeffsOfValues pt N ℓ y i :=
  bflyRun_eq pt N 0 ℓ y i.2

end Bfly

/-- **The extractor's row decoding, iterative** (`decode_row_D`): if the word `u` agrees with
`Enc(c)` on a set `J` of `2^ℓ` positions below `2^20`, the butterflies run on the values that
`interpF` gives at `D[0, 2^ℓ)` return the message `c`. -/
theorem bfly_decode_D {M : Type*} [Field M] [Algebra F M] {ℓ : ℕ} (hℓ : ℓ ≤ logNMax)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < nMax) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → M)
    (u : ℕ → M) (hu : ∀ i ∈ J, u i = encN D c i) (i : Fin (2 ^ ℓ)) :
    bflyRun D logNMax 0 ℓ (interpF D J u) i = c i := by
  rw [bflyRun_coeffs, ← decode_row_D hℓ hJN hJc c u hu]
  rfl

/-! ## The agreement set's first `k` positions (§6.2 step 4: `P = A[0…k)`) -/

/-- **The first `k` positions of `A` below `n`**, in increasing order: the scan a machine makes
over the positions `0, …, n − 1`. -/
def firstK (n : ℕ) (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (((List.range n).filter (· ∈ A)).take k).toFinset

theorem firstK_subset (n : ℕ) (A : Finset ℕ) (k : ℕ) : firstK n A k ⊆ A := fun i hi => by
  rw [firstK, List.mem_toFinset] at hi
  simpa using (List.mem_filter.1 (List.mem_of_mem_take hi)).2

theorem firstK_lt (n : ℕ) (A : Finset ℕ) (k : ℕ) : ∀ i ∈ firstK n A k, i < n := fun i hi => by
  rw [firstK, List.mem_toFinset] at hi
  exact List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_take hi)).1

theorem firstK_card {n : ℕ} {A : Finset ℕ} (hA : ∀ i ∈ A, i < n) {k : ℕ} (hk : k ≤ A.card) :
    (firstK n A k).card = k := by
  have hnd : ((List.range n).filter (· ∈ A)).Nodup := (List.nodup_range).filter _
  have hlen : ((List.range n).filter (· ∈ A)).length = A.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hA i h, h⟩⟩
  rw [firstK, List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _)), List.length_take,
    hlen, Nat.min_eq_left hk]

/-- **Decoding on an agreement set** (phases 4–5, pure): if the word `u` agrees with `Enc(c)` on
a set `A` of at least `2^ℓ` positions below `n ≤ 2^20`, interpolating on its first `2^ℓ`
positions and running the butterflies returns `c`. -/
theorem decode_agree {M : Type*} [Field M] [Algebra F M] {ℓ : ℕ} (hℓ : ℓ ≤ logNMax)
    {n : ℕ} (hn : n ≤ nMax) {A : Finset ℕ} (hA : ∀ i ∈ A, i < n) (hcard : 2 ^ ℓ ≤ A.card)
    (c : Fin (2 ^ ℓ) → M) (u : ℕ → M) (hu : ∀ i ∈ A, u i = encN D c i) (i : Fin (2 ^ ℓ)) :
    bflyRun D logNMax 0 ℓ (interpF D (firstK n A (2 ^ ℓ)) u) i = c i :=
  bfly_decode_D hℓ (fun j hj => lt_of_lt_of_le (firstK_lt n A _ j hj) hn) (firstK_card hA hcard)
    c u (fun j hj => hu j (firstK_subset n A _ hj)) i

/-! ## Controls -/

section Controls

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **Positive control**: one level on two points is the explicit merge
`(y₀ − α (y₁ − y₀), y₁ − y₀)`, `α = Ŵ₀(pt s₀)`. -/
theorem bflyRun_one (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) :
    bflyRun pt N s0 1 y 0 = y 0 - algebraMap L M (wAt pt N 0 s0) * (y 1 - y 0) ∧
    bflyRun pt N s0 1 y 1 = y 1 - y 0 := by
  simp [bflyRun, bflyLevel]

/-- **Negative control**: zero levels change nothing, so the decoding needs all `ℓ` levels
(the first coefficient of a two-point row is not its first value unless `α (y₁ − y₀) = 0`). -/
theorem bflyRun_zero (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) : bflyRun pt N s0 0 y = y := rfl

end Controls

/-- **Controls of `firstK`**: the first two of `{5, 1, 3}` are `{1, 3}`; asking for more than the
set holds gives the whole set (so `decode_agree` needs `2^ℓ ≤ |A|`). -/
theorem firstK_ctl : firstK 8 {5, 1, 3} 2 = {1, 3} ∧ firstK 8 {5, 1, 3} 7 = {1, 3, 5} := by
  decide

end FR.X
