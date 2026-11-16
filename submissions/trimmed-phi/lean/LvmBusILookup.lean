-- adapted from leanerVM/LeanerVM/Parameters/Generator.lean@25da57d32 (the order certificate of `g`)
-- and leanerVM/LeanerVM/Arithmetization/Bus.lean@25da57d32 (`eq_zero_of_perm_map_mul_g`,
-- `lookup_sound`) for lvm (WP-9): namespaces `LeanVM.Parameters` / `LeanVM.Arithmetization`
-- (WP-2's port), non-`module` file; new here: the transfer of the order to `Lvm.FK.x`
-- (`orderOf_FKx`, `FKx_pow_inj`).
import LvmFieldFacts
import LvmFieldKCorrect
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# The generator's order and the offline memory-checking argument

**The order of `g`** (leanerVM `Parameters/Generator`, leanVM `Parameters/Generator`): `g = x`,
the word `0x2` of `K = GF(2^64)`, has order `2^64 - 1`. `g^(2^64-1) = 1` is Lagrange; the seven
checks `g^((2^64-1)/p) ≠ 1` are one `decide +kernel` on the fast field `Lvm.FK`, transported to
`BF64` through `toBF64`; Mathlib's `orderOf_eq_of_pow_and_pow_div_prime` combines them. The fast field `Lvm.FK` (WP-1) is the same
field through `ringEquivBF64`, which sends `FK.x` to `g`, so `FK.x` has the same order
(`orderOf_FKx`) and its powers below `2^64 - 1` are distinct (`FKx_pow_inj`): the exponent
addressing of the LoopIR memories (`Lvm.Loop.GInj`).

**The lookup argument** (specification Lemma 6.3 and Theorem 6.4, leanerVM's generic form): if
the pushes (the bumped reads and the seeds) are a permutation of the pulls (the reads and the
finalizes), every read count is nonzero, there are fewer than `2^64 - 1` reads, and every seed and
finalize has a good key, then every read has a good key.

## Wrong readings excluded (leanerVM)

* Lemma 6.3 concludes that every count is `0`, not that the list is empty: a read with count `0`
  pulls and pushes the same tuple and balances itself; only the count product rejects it.
* Balance is a permutation counted in `ℕ`: a field sum over `K`, of characteristic `2`, would
  cancel any message pushed twice.
-/

namespace LeanVM.Parameters

/-! ## The order certificate (leanerVM `Parameters/Generator`) -/

/-- `|K^×| = 2^64 - 1`, factored into its seven primes. -/
theorem card_sub_one_factorization :
    (2 : ℕ) ^ 64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 := by norm_num

/-- `g` is nonzero, so it lies in `K^×`. -/
theorem g_ne_zero : g ≠ 0 := by decide

/-- Lagrange: `g^(2^64-1) = 1`. -/
theorem g_pow_card_sub_one : g ^ (2 ^ 64 - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one g g_ne_zero
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h

/-! Addition chains for the seven powers (proof help): `2^64 - 1 = ∏_{i<6} (2^(2^i) + 1)` and
`2^32 + 1 = 641 · 6700417`, so each power is a few `frob`s (squarings) and products of shared
terms, `x^3`, `x^15`, `x^255`, `x^65535`, `x^(2^32 - 1)`. -/
private def pc3 : Lvm.FK := Lvm.FK.frob 1 Lvm.FK.x * Lvm.FK.x
private def pc15 : Lvm.FK := Lvm.FK.frob 2 pc3 * pc3
private def pc255 : Lvm.FK := Lvm.FK.frob 4 pc15 * pc15
private def pc65535 : Lvm.FK := Lvm.FK.frob 8 pc255 * pc255
private def pcG : Lvm.FK := Lvm.FK.frob 16 pc65535 * pc65535
private def pa2 : Lvm.FK := Lvm.FK.frob 2 Lvm.FK.x * Lvm.FK.x
private def pa4 : Lvm.FK := Lvm.FK.frob 4 pa2 * pa2
private def pa8 : Lvm.FK := Lvm.FK.frob 8 pa4 * pa4
private def pa16 : Lvm.FK := Lvm.FK.frob 16 pa8 * pa8
private def pb2 : Lvm.FK := Lvm.FK.frob 4 pc3 * pc3
private def pb4 : Lvm.FK := Lvm.FK.frob 8 pb2 * pb2
private def pb8 : Lvm.FK := Lvm.FK.frob 16 pb4 * pb4
private def pd2 : Lvm.FK := Lvm.FK.frob 8 pc15 * pc15
private def pd4 : Lvm.FK := Lvm.FK.frob 16 pd2 * pd2
private def pe2 : Lvm.FK := Lvm.FK.frob 16 pc255 * pc255

open Lvm.FK in
/-- The seven checks on the fast field `Lvm.FK` (WP-1), in one kernel evaluation: `FK`'s
word arithmetic costs the kernel about a tenth of `BF64`'s, and the powers are rewritten (`frob_eq_pow`,
`pow_mul`, `pow_add`) into the addition chains above, about 35 products instead of 220. -/
private theorem FKx_pow_checks : Lvm.FK.x ^ ((2 ^ 64 - 1) / 3) ≠ 1 ∧
    Lvm.FK.x ^ ((2 ^ 64 - 1) / 5) ≠ 1 ∧ Lvm.FK.x ^ ((2 ^ 64 - 1) / 17) ≠ 1 ∧
    Lvm.FK.x ^ ((2 ^ 64 - 1) / 257) ≠ 1 ∧ Lvm.FK.x ^ ((2 ^ 64 - 1) / 641) ≠ 1 ∧
    Lvm.FK.x ^ ((2 ^ 64 - 1) / 65537) ≠ 1 ∧ Lvm.FK.x ^ ((2 ^ 64 - 1) / 6700417) ≠ 1 := by
  have e3 : x ^ ((2 ^ 64 - 1) / 3) = frob 32 pa16 * pa16 := by
    simp only [pa16, pa8, pa4, pa2, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  have e5 : x ^ ((2 ^ 64 - 1) / 5) = frob 32 pb8 * pb8 := by
    simp only [pb8, pb4, pb2, pc3, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  have e17 : x ^ ((2 ^ 64 - 1) / 17) = frob 32 pd4 * pd4 := by
    simp only [pd4, pd2, pc15, pc3, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  have e257 : x ^ ((2 ^ 64 - 1) / 257) = frob 32 pe2 * pe2 := by
    simp only [pe2, pc255, pc15, pc3, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  have e641 : x ^ ((2 ^ 64 - 1) / 641) = pcG ^ 6700417 := by
    simp only [pcG, pc65535, pc255, pc15, pc3, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  have e65537 : x ^ ((2 ^ 64 - 1) / 65537) = frob 32 pc65535 * pc65535 := by
    simp only [pc65535, pc255, pc15, pc3, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  have e6700417 : x ^ ((2 ^ 64 - 1) / 6700417) = pcG ^ 641 := by
    simp only [pcG, pc65535, pc255, pc15, pc3, frob_eq_pow, ← pow_mul, ← pow_add, ← pow_succ]; norm_num
  rw [e3, e5, e17, e257, e641, e65537, e6700417]
  -- on the words as natural numbers (GOLF3: `FK`'s word operations cost the kernel 3-4 times more)
  simp only [ne_eq, eq_iff_toNat, mul_toNat, frob_toNat, pow_toNat, pa16, pa8, pa4, pa2, pb8, pb4, pb2, pc3,
    pc15, pc255, pc65535, pcG, pd4, pd2, pe2]
  decide +kernel

/-- `Lvm.FK.toBF64` sends `FK.x` to `g` (stated again as `Lvm.FK.toBF64_x` below). -/
private theorem toBF64_FKx : Lvm.FK.toBF64 Lvm.FK.x = g := by decide

/-- A power of `g` is `1` only if the same power of `FK.x` is. -/
private theorem g_pow_ne_one_of {n : ℕ} (h : Lvm.FK.x ^ n ≠ 1) : g ^ n ≠ 1 := by
  rw [← toBF64_FKx, ← Lvm.FK.toBF64_npow, ← Lvm.FK.toBF64_one]
  exact fun e ↦ h (Lvm.FK.toBF64_injective e)

/-- The prime-`3` check of the certificate. -/
theorem g_pow_div_three_ne_one : g ^ ((2 ^ 64 - 1) / 3) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.1

/-- The prime-`5` check of the certificate. -/
theorem g_pow_div_five_ne_one : g ^ ((2 ^ 64 - 1) / 5) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.2.1

/-- The prime-`17` check of the certificate. -/
theorem g_pow_div_seventeen_ne_one : g ^ ((2 ^ 64 - 1) / 17) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.2.2.1

/-- The prime-`257` check of the certificate. -/
theorem g_pow_div_257_ne_one : g ^ ((2 ^ 64 - 1) / 257) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.2.2.2.1

/-- The prime-`641` check of the certificate. -/
theorem g_pow_div_641_ne_one : g ^ ((2 ^ 64 - 1) / 641) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.2.2.2.2.1

/-- The prime-`65537` check of the certificate. -/
theorem g_pow_div_65537_ne_one : g ^ ((2 ^ 64 - 1) / 65537) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.2.2.2.2.2.1

/-- The prime-`6700417` check of the certificate. -/
theorem g_pow_div_6700417_ne_one : g ^ ((2 ^ 64 - 1) / 6700417) ≠ 1 :=
  g_pow_ne_one_of FKx_pow_checks.2.2.2.2.2.2

/-- `g` generates `K^×`: its order is exactly `2^64 - 1`. -/
theorem orderOf_g : orderOf g = 2 ^ 64 - 1 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) g_pow_card_sub_one
    fun p hp hdvd ↦ ?_
  rw [card_sub_one_factorization] at hdvd
  simp only [Nat.Prime.dvd_mul hp, or_assoc] at hdvd
  rcases hdvd with h | h | h | h | h | h | h <;>
    rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]
  exacts [g_pow_div_three_ne_one, g_pow_div_five_ne_one, g_pow_div_seventeen_ne_one,
    g_pow_div_257_ne_one, g_pow_div_641_ne_one, g_pow_div_65537_ne_one,
    g_pow_div_6700417_ne_one]

/-- Distinct indices below `2^64 - 1` are distinct addresses. -/
theorem gpow_injOn : Set.InjOn addressOfIndex (Set.Iio (2 ^ 64 - 1)) := by
  rw [← orderOf_g]
  exact pow_injOn_Iio_orderOf

end LeanVM.Parameters

namespace Lvm.FK

open LeanVM.Parameters

/-- `FK.x` is `g` through the ring isomorphism. -/
theorem toBF64_x : toBF64 x = g := by decide

/-- **`FK.x` has order `2^64 - 1`** (new, lvm WP-9): the ring isomorphism keeps orders. -/
theorem orderOf_FKx : orderOf x = 2 ^ 64 - 1 := by
  rw [← orderOf_g, ← toBF64_x]
  exact (orderOf_injective ringEquivBF64.toMonoidHom ringEquivBF64.injective x).symm

/-- **Distinct exponents below `2^64 - 1` give distinct powers of `FK.x`.** -/
theorem FKx_pow_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1)
    (h : x ^ a = x ^ b) : a = b := by
  rw [← orderOf_FKx] at ha hb
  exact pow_injOn_Iio_orderOf ha hb h

end Lvm.FK

namespace LeanVM.Arithmetization

open LeanVM.Parameters

/-! ## Invariant count lists (leanerVM `Arithmetization/Bus`) -/

/-- Specification Lemma 6.3 (invariant count multisets): a list of counts that is a permutation
of itself multiplied by `g`, with fewer than `2^64 - 1` elements, holds only `0`. -/
theorem eq_zero_of_perm_map_mul_g {C : List K} (h : (C.map (g * ·)).Perm C)
    (hlen : C.length < 2 ^ 64 - 1) : ∀ c ∈ C, c = 0 := by
  have hcount : ∀ x, C.count (g * x) = C.count x := fun x ↦ by
    rw [← h.count_eq (g * x), List.count_map_of_injective _ _ (mul_right_injective₀ g_ne_zero)]
  have hpow : ∀ k x, C.count (g ^ k * x) = C.count x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, one_mul]
    | succ k ih => intro x; rw [pow_succ', mul_assoc, hcount, ih]
  intro c hc
  by_contra hc0
  have hnodup : ((List.range (2 ^ 64 - 1)).map fun k ↦ g ^ k * c).Nodup :=
    List.Nodup.map_on (fun a ha b hb hab ↦ gpow_injOn (List.mem_range.mp ha)
      (List.mem_range.mp hb) (mul_right_cancel₀ hc0 hab)) List.nodup_range
  have hsub : ((List.range (2 ^ 64 - 1)).map fun k ↦ g ^ k * c) ⊆ C := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
    rw [← List.count_pos_iff, hpow]
    exact List.count_pos_iff.mpr hc
  have hle := (List.subperm_of_subset hnodup hsub).length_le
  rw [List.length_map, List.length_range] at hle
  omega

/-! ## The generic lookup theorem -/

/-- Specification Theorem 6.4 (lookup correctness), for any messages with a key, a count and a
bump that keeps the key and multiplies the count by `g`: if the pushes (the bumped reads and
the seeds) are a permutation of the pulls (the reads and the finalizes), every read count is
nonzero, there are fewer than `2^64 - 1` reads, and every seed and finalize has a good key,
then every read has a good key. -/
theorem lookup_sound {M κ : Type} [DecidableEq κ] {key : M → κ} {count : M → K}
    {bump : M → M} (key_bump : ∀ m, key (bump m) = key m)
    (count_bump : ∀ m, count (bump m) = g * count m) {Good : κ → Prop}
    {reads seeds fins : List M} (balanced : (reads.map bump ++ seeds).Perm (reads ++ fins))
    (seeds_good : ∀ m ∈ seeds, Good (key m)) (fins_good : ∀ m ∈ fins, Good (key m))
    (counts_ne : ∀ m ∈ reads, count m ≠ 0) (length_lt : reads.length < 2 ^ 64 - 1) :
    ∀ m ∈ reads, Good (key m) := by
  intro m hm
  by_contra hbad
  let p : M → Bool := fun m' ↦ decide (key m' = key m)
  have hnil : ∀ l : List M, (∀ m' ∈ l, Good (key m')) → l.filter p = [] := fun l hl ↦
    List.filter_eq_nil_iff.mpr fun m' hm' hpm ↦ hbad (by
      rw [← of_decide_eq_true hpm]; exact hl m' hm')
  have hbal := balanced.filter p
  rw [List.filter_append, List.filter_append, hnil seeds seeds_good, hnil fins fins_good,
    List.append_nil, List.append_nil, List.filter_map,
    show p ∘ bump = p from funext fun m' ↦ by simp only [Function.comp_apply, p, key_bump]]
    at hbal
  have hC := hbal.map count
  rw [List.map_map, show count ∘ bump = (g * ·) ∘ count from funext count_bump,
    ← List.map_map] at hC
  have hzero := eq_zero_of_perm_map_mul_g hC
    (by rw [List.length_map]; exact lt_of_le_of_lt (List.length_filter_le _ _) length_lt)
  exact counts_ne m hm (hzero _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, by simp [p]⟩)))

end LeanVM.Arithmetization
