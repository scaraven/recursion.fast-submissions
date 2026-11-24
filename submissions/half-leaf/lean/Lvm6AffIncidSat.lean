-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- New for lvm2 (WP AC-THM). STATEMENT FROZEN 2026-11-13; proved [AC-THM-INC-A] with `Lvm6AffHF`.
-- Not imported by any submission root until the integration roll. Part of the bespoke replacement for
-- ArkLib's incidence count; see `Lvm6AffIncid` and docs/lvm2/stages/AC-THM.md §2.
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Lvm6AffHF

/-! # Refined Bézout on a curve of `K³` (affine Hilbert functions) -/

namespace LeanVM.Protocol.Whir.AffineCombiner.Incid

open MvPolynomial Finset

variable {K : Type*} [Field K]

/-- `K[Y, V, Z]_{≤ t}` has dimension `C(t + 3, 3)`: `6 · dim = (t + 1)(t + 2)(t + 3)`. -/
theorem six_mul_finrank_restrictTotalDegree (t : ℕ) :
    6 * Module.finrank K (restrictTotalDegree (Fin 3) K t) = (t + 1) * (t + 2) * (t + 3) := by
  classical
  have hcard : Module.finrank K (restrictTotalDegree (Fin 3) K t) =
      Nat.card {n : Fin 3 →₀ ℕ | (n.sum fun _ e => e) ≤ t} :=
    Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)
  have hset : {n : Fin 3 →₀ ℕ | (n.sum fun _ e => e) ≤ t} =
      ↑((range (t + 1)).biUnion fun u => (univ : Finset (Fin 3)).finsuppAntidiag u) := by
    ext n
    simp only [Set.mem_ofPred_eq, coe_biUnion, coe_range, Set.mem_iUnion, Set.mem_Iio, mem_coe,
      mem_finsuppAntidiag, subset_univ, and_true, exists_prop, exists_eq_right',
      Finsupp.sum_fintype n (fun _ e => e) (fun _ => rfl), Nat.lt_succ_iff]
  have hsum : Module.finrank K (restrictTotalDegree (Fin 3) K t) =
      ∑ u ∈ range (t + 1), (u + 2).choose u := by
    rw [hcard, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_biUnion]
    · refine sum_congr rfl fun u _ => ?_
      rw [card_finsuppAntidiag_nat_eq_choose, card_univ, Fintype.card_fin, Nat.add_comm 3 u]
      rfl
    · intro u _ v _ huv
      refine disjoint_left.2 fun f hu hv => huv ?_
      rw [mem_finsuppAntidiag] at hu hv
      exact hu.1.symm.trans hv.1
  rw [hsum]
  clear hcard hset hsum
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [sum_range_succ, Nat.mul_add, ih, Nat.choose_symm_add]
    have h := Nat.add_one_mul_choose_eq (t + 2) 1
    rw [Nat.choose_one_right] at h
    have h6 : 6 * (t + 1 + 2).choose 2 = 3 * ((t + 2 + 1) * (t + 2)) := by
      rw [h]; ring_nf
    rw [h6]
    ring

/-- The second difference of `dim K[Y, V, Z]_{≤ s}`, with slack: the Hilbert function of a complete
intersection of degrees `a`, `b` is at most `a b (s + 2)`. -/
theorem finrank_restrictTotalDegree_second_diff {a b s : ℕ} (h : a + b ≤ s) :
    Module.finrank K (restrictTotalDegree (Fin 3) K s) +
        Module.finrank K (restrictTotalDegree (Fin 3) K (s - b - a)) ≤
      Module.finrank K (restrictTotalDegree (Fin 3) K (s - a)) +
        Module.finrank K (restrictTotalDegree (Fin 3) K (s - b)) + a * b * (s + 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have e3 : a + b + k - b = a + k := by rw [Nat.add_right_comm, Nat.add_sub_cancel]
  have e1 : a + b + k - b - a = k := by rw [e3, Nat.add_sub_cancel_left]
  have e2 : a + b + k - a = b + k := by rw [Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [e1, e2, e3]
  have h0 := six_mul_finrank_restrictTotalDegree (K := K) (a + b + k)
  have h1 := six_mul_finrank_restrictTotalDegree (K := K) k
  have h2 := six_mul_finrank_restrictTotalDegree (K := K) (b + k)
  have h3 := six_mul_finrank_restrictTotalDegree (K := K) (a + k)
  have key : (a + b + k + 1) * (a + b + k + 2) * (a + b + k + 3) + (k + 1) * (k + 2) * (k + 3) +
      3 * (a * b * (a + b)) = (b + k + 1) * (b + k + 2) * (b + k + 3) +
      (a + k + 1) * (a + k + 2) * (a + k + 3) + 6 * (a * b * (a + b + k + 2)) := by ring
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos 5)
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, h0, h1, h2, h3, ← key]
  exact Nat.le_add_right _ _

/-- **Refined Bézout on a curve of `K³`** [AC-THM-INC-A]. Let `r` be irreducible with `r ∤ G`. Every
finite set of points on `G' = 0` that lie on the saturation `(r, G) : G'^∞` (every `y` with
`G'^N y ∈ (r, G)` for some `N` vanishes there) has at most `deg r · deg G · deg G'` points. In
particular the points lie on `r = G = 0` (take `y = r`, `y = G`, `N = 0`). Proof: the affine Hilbert
function `s ↦ dim K[x]_{≤s} / I_{≤s}` of `I = (r, G)` is at most `a b (s + 2)`; it can only drop on
passing to the saturation `J`; `G'` is a non-zero-divisor modulo `J`, so the Hilbert function of
`J + (G')` is at most `HF_J(s) − HF_J(s − b')`, which is at most `a b b'` for infinitely many `s`;
and `m` distinct points impose independent conditions on polynomials of degree `≥ m − 1`. -/
theorem card_le_of_sat (r G G' : MvPolynomial (Fin 3) K) (hr : Irreducible r) (hrG : ¬ r ∣ G)
    {a b b' : ℕ} (ha : r.totalDegree ≤ a) (hb : G.totalDegree ≤ b) (hb' : G'.totalDegree ≤ b')
    (S : Finset (Fin 3 → K))
    (hS : ∀ x ∈ S, eval x G' = 0 ∧
      ∀ y : MvPolynomial (Fin 3) K, (∃ N : ℕ, G' ^ N * y ∈ Ideal.span {r, G}) → eval x y = 0) :
    S.card ≤ a * b * b' := by
  classical
  by_cases hG'0 : G' = 0
  · have hS0 : S = ∅ := eq_empty_of_forall_notMem fun x hx => by
      have := (hS x hx).2 1 ⟨1, by rw [hG'0, pow_one, zero_mul]; exact Ideal.zero_mem _⟩
      rw [RingHom.map_one] at this
      exact one_ne_zero this
    rw [hS0, card_empty]
    exact Nat.zero_le _
  have hr0 : r ≠ 0 := hr.ne_zero
  have hG0 : G ≠ 0 := fun h => hrG (h ▸ dvd_zero r)
  have hrp : Prime r := hr.prime
  have hregG : ∀ y, G * y ∈ Ideal.span {r} → y ∈ Ideal.span {r} := by
    intro y hy
    rw [Ideal.mem_span_singleton] at hy ⊢
    exact (hrp.dvd_or_dvd hy).resolve_left hrG
  have hregG' :
      ∀ y, G' * y ∈ HF.sat (Ideal.span {r, G}) G' → y ∈ HF.sat (Ideal.span {r, G}) G' := by
    rintro y ⟨N, hN⟩
    exact ⟨N + 1, by rw [pow_succ, mul_assoc]; exact hN⟩
  have hIJ : Ideal.span {r, G} ≤ HF.sat (Ideal.span {r, G}) G' := fun y hy =>
    ⟨0, by rw [pow_zero, one_mul]; exact hy⟩
  -- `J = (r, G) : G'^∞`; Hilbert functions of `J` and `J + (G')` (`HF.card_le_of_hilbert`).
  refine HF.card_le_of_hilbert (s₁ := r.totalDegree + b)
    (fun t => Module.finrank K (restrictTotalDegree (Fin 3) K t))
    (fun t => Module.finrank K (HF.low (HF.sat (Ideal.span {r, G}) G') t))
    (fun t => Module.finrank K (HF.low (HF.sat (Ideal.span {r, G}) G' ⊔ Ideal.span {G'}) t))
    (fun t => HF.finrank_low_le _ t)
    (fun t ht => HF.finrank_low_sup_span _ hG'0 hb' ht hregG') (fun s hs => ?_) (fun s hs => ?_)
  · -- `HF_{(r, G)}(s) ≤ HF_{(r)}(s) − HF_{(r)}(s − b)`, with `HF_{(r)}` exact.
    have h1 := HF.finrank_low_sup_span (Ideal.span {r}) hG0 hb (s := s)
      ((Nat.le_add_left b _).trans hs) hregG
    rw [← Ideal.span_insert,
      HF.finrank_low_span_singleton hr0 (t := s) ((Nat.le_add_right _ b).trans hs),
      HF.finrank_low_span_singleton hr0 (t := s - b) (Nat.le_sub_of_add_le hs)] at h1
    have h2 := HF.finrank_low_mono hIJ s
    have h3 := finrank_restrictTotalDegree_second_diff (K := K) (a := r.totalDegree) (b := b) hs
    have h4 : r.totalDegree * b * (s + 2) ≤ a * b * (s + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ha)
    exact Nat.le_of_add_le_add_right (h3.trans ((Nat.add_le_add_right h1 _).trans
      ((Nat.add_le_add (Nat.add_le_add_right h2 _) h4).trans_eq (Nat.add_right_comm _ _ _))))
  · -- The points of `S` lie on the zero set of `J + (G')`.
    refine HF.card_add_finrank_low_le _ S (fun x hx y hy => ?_) hs
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy₂
    rw [eval_add, eval_mul, (hS x hx).1, mul_zero, add_zero]
    exact (hS x hx).2 y₁ hy₁

end LeanVM.Protocol.Whir.AffineCombiner.Incid
