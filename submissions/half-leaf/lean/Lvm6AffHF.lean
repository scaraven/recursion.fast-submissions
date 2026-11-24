-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- New for lvm2 (WP AC-THM, AC-THM-INC-A). Affine Hilbert functions over a field, by linear algebra
-- only (no Hilbert polynomials), for `Lvm6AffIncidSat`. Generic in the variables `σ`.
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine Hilbert functions

For an ideal `I` of `K[σ]`, `low I s = I ∩ K[σ]_{≤ s}` is a subspace of the finite-dimensional space
`restrictTotalDegree σ K s` of polynomials of total degree `≤ s`; the affine Hilbert function is
`dim K[σ]_{≤ s} − dim low I s`. All statements below are inequalities between the dimensions:
* `card_add_finrank_low_le`: `m` points on the zero set of `I` impose independent conditions in
  degree `≥ m − 1`;
* `finrank_low_sup_span`: if `deg G ≤ b` and `G` is a non-zero-divisor modulo `I`, then
  `HF_{I + (G)}(s) ≤ HF_I(s) − HF_I(s − b)`;
* `finrank_low_span_singleton`: `(r) ∩ K[σ]_{≤ t} = r · K[σ]_{≤ t − deg r}`;
* `card_le_of_hilbert`: the telescoping count that turns these into a bound on the number of points.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner.HF

open MvPolynomial Module

variable {σ K : Type*} [Field K]

/-- `I ∩ K[σ]_{≤ s}` as a `K`-subspace. -/
noncomputable def low (I : Ideal (MvPolynomial σ K)) (s : ℕ) : Submodule K (MvPolynomial σ K) :=
  I.restrictScalars K ⊓ restrictTotalDegree σ K s

theorem mem_low {I : Ideal (MvPolynomial σ K)} {s : ℕ} {p : MvPolynomial σ K} :
    p ∈ low I s ↔ p ∈ I ∧ p.totalDegree ≤ s := by
  rw [low, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_restrictTotalDegree]

theorem low_le (I : Ideal (MvPolynomial σ K)) (s : ℕ) : low I s ≤ restrictTotalDegree σ K s :=
  inf_le_right

/-- The saturation `I : f^∞ = {y | ∃ N, f^N y ∈ I}`. -/
def sat {R : Type*} [CommSemiring R] (I : Ideal R) (f : R) : Ideal R where
  carrier := {y | ∃ N : ℕ, f ^ N * y ∈ I}
  add_mem' := by
    rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, ?_⟩
    rw [pow_add, mul_add, mul_comm (f ^ N), mul_assoc, mul_assoc]
    exact I.add_mem (I.mul_mem_left _ hN) (by rw [mul_left_comm]; exact I.mul_mem_left _ hM)
  zero_mem' := ⟨0, by rw [mul_zero]; exact I.zero_mem⟩
  smul_mem' := by
    rintro c y ⟨N, hN⟩
    exact ⟨N, by rw [smul_eq_mul, mul_left_comm]; exact I.mul_mem_left c hN⟩

theorem mem_sat {R : Type*} [CommSemiring R] {I : Ideal R} {f y : R} :
    y ∈ sat I f ↔ ∃ N : ℕ, f ^ N * y ∈ I :=
  Iff.rfl

/-- A polynomial of degree `≤ S.card − 1` that is `1` at `p ∈ S` and `0` on the rest of `S`. -/
theorem exists_indicator (S : Finset (σ → K)) {p : σ → K} (hp : p ∈ S) :
    ∃ f : MvPolynomial σ K, f.totalDegree ≤ S.card - 1 ∧ eval p f = 1 ∧
      ∀ q ∈ S, q ≠ p → eval q f = 0 := by
  classical
  have hne : ∀ q ∈ S.erase p, ∃ i, p i ≠ q i := fun q hq =>
    Function.ne_iff.mp (Finset.ne_of_mem_erase hq).symm
  choose i hi using hne
  refine ⟨∏ q ∈ (S.erase p).attach,
    C (p (i q.1 q.2) - q.1 (i q.1 q.2))⁻¹ * (X (i q.1 q.2) - C (q.1 (i q.1 q.2))), ?_, ?_, ?_⟩
  · refine (totalDegree_finsetProd _ _).trans ?_
    rw [← Finset.card_erase_of_mem hp, ← Finset.card_attach]
    refine (Finset.sum_le_card_nsmul _ _ 1 fun q _ => ?_).trans (by rw [smul_eq_mul, mul_one])
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_sub_C_le _ _).trans (totalDegree_X _).le
  · rw [eval_prod]
    refine Finset.prod_eq_one fun q _ => ?_
    rw [eval_mul, eval_C, eval_sub, eval_X, eval_C]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hi q.1 q.2))
  · intro q hq hqp
    rw [eval_prod]
    refine Finset.prod_eq_zero (i := ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩⟩) (Finset.mem_attach _ _) ?_
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]

theorem mulLeft_injective {G : MvPolynomial σ K} (hG : G ≠ 0) :
    Function.Injective (LinearMap.mulLeft K G) :=
  fun _ _ h => mul_left_cancel₀ hG h

/-- **Principal ideals.** `(r) ∩ K[σ]_{≤ t} = r · K[σ]_{≤ t − deg r}`. -/
theorem low_span_singleton {r : MvPolynomial σ K} (hr : r ≠ 0) {t : ℕ} (ht : r.totalDegree ≤ t) :
    low (Ideal.span {r}) t =
      (restrictTotalDegree σ K (t - r.totalDegree)).map (LinearMap.mulLeft K r) := by
  ext x
  rw [mem_low, Ideal.mem_span_singleton', Submodule.mem_map]
  constructor
  · rintro ⟨⟨y, rfl⟩, hx⟩
    refine ⟨y, (mem_restrictTotalDegree _ _ _).2 ?_, mul_comm _ _⟩
    rcases eq_or_ne y 0 with rfl | hy
    · rw [totalDegree_zero]; exact Nat.zero_le _
    · rw [totalDegree_mul_of_isDomain hy hr] at hx; exact Nat.le_sub_of_add_le hx
  · rintro ⟨y, hy, rfl⟩
    rw [mem_restrictTotalDegree] at hy
    exact ⟨⟨y, mul_comm _ _⟩,
      (totalDegree_mul _ _).trans ((Nat.add_le_add_left hy _).trans (Nat.add_sub_of_le ht).le)⟩

theorem finrank_low_span_singleton {r : MvPolynomial σ K} (hr : r ≠ 0) {t : ℕ}
    (ht : r.totalDegree ≤ t) :
    finrank K (low (Ideal.span {r}) t) =
      finrank K (restrictTotalDegree σ K (t - r.totalDegree)) := by
  rw [low_span_singleton hr ht]
  exact (Submodule.equivMapOfInjective _ (mulLeft_injective hr) _).finrank_eq.symm

variable [Finite σ]

instance (I : Ideal (MvPolynomial σ K)) (s : ℕ) : FiniteDimensional K (low I s) :=
  Submodule.finiteDimensional_of_le (low_le I s)

theorem finrank_low_le (I : Ideal (MvPolynomial σ K)) (s : ℕ) :
    finrank K (low I s) ≤ finrank K (restrictTotalDegree σ K s) :=
  Submodule.finrank_mono (low_le I s)

theorem finrank_low_mono {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (s : ℕ) :
    finrank K (low I s) ≤ finrank K (low J s) :=
  Submodule.finrank_mono fun _ hx => mem_low.2 ⟨h (mem_low.1 hx).1, (mem_low.1 hx).2⟩

/-- **Points impose independent conditions.** If every polynomial of `I` vanishes on the finite set
`S` and `S.card ≤ s + 1`, then `S.card ≤ HF_I(s)`. -/
theorem card_add_finrank_low_le (I : Ideal (MvPolynomial σ K)) (S : Finset (σ → K))
    (hS : ∀ x ∈ S, ∀ y ∈ I, eval x y = 0) {s : ℕ} (hs : S.card ≤ s + 1) :
    S.card + finrank K (low I s) ≤ finrank K (restrictTotalDegree σ K s) := by
  classical
  let ev : restrictTotalDegree σ K s →ₗ[K] (S → K) :=
    { toFun := fun f x => eval x.1 f.1
      map_add' := fun f g => funext fun x => by
        rw [Submodule.coe_add, eval_add, Pi.add_apply]
      map_smul' := fun c f => funext fun x => by
        rw [Submodule.coe_smul, smul_eval, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_comm] }
  have hsurj : LinearMap.range ev = ⊤ := by
    refine LinearMap.range_eq_top.2 fun c => ?_
    have hind : ∀ x : S, ∃ f ∈ restrictTotalDegree σ K s,
        eval x.1 f = 1 ∧ ∀ y : S, y ≠ x → eval y.1 f = 0 := by
      intro x
      obtain ⟨f, hdeg, h1, h0⟩ := exists_indicator S x.2
      exact ⟨f, (mem_restrictTotalDegree _ _ _).2 (hdeg.trans (Nat.sub_le_iff_le_add.2 hs)), h1,
        fun y hy => h0 y.1 y.2 fun e => hy (Subtype.ext e)⟩
    choose f hf hf1 hf0 using hind
    refine ⟨∑ x, c x • ⟨f x, hf x⟩, funext fun y => ?_⟩
    change eval y.1 (↑(∑ x, c x • (⟨f x, hf x⟩ : restrictTotalDegree σ K s))) = c y
    rw [Submodule.coe_sum, eval_sum, Finset.sum_eq_single y]
    · rw [Submodule.coe_smul, smul_eval, hf1, mul_one]
    · intro x _ hxy
      rw [Submodule.coe_smul, smul_eval, hf0 x y (Ne.symm hxy), mul_zero]
    · intro h; exact absurd (Finset.mem_univ y) h
  have hker : Submodule.comap (restrictTotalDegree σ K s).subtype (low I s) ≤ LinearMap.ker ev :=
    fun f hf => funext fun x => hS x.1 x.2 f.1 (mem_low.1 hf).1
  have h1 := LinearMap.finrank_range_add_finrank_ker ev
  rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
  have h2 := Submodule.finrank_mono hker
  rw [(Submodule.comapSubtypeEquivOfLe (low_le I s)).finrank_eq] at h2
  exact (Nat.add_le_add_left h2 _).trans h1.le

/-- **Non-zero-divisor step.** If `G ≠ 0`, `deg G ≤ b ≤ s` and `G` is a non-zero-divisor modulo `I`,
then `HF_{I + (G)}(s) + HF_I(s − b) ≤ HF_I(s)`, stated without subtraction. -/
theorem finrank_low_sup_span (I : Ideal (MvPolynomial σ K)) {G : MvPolynomial σ K} (hG : G ≠ 0)
    {b s : ℕ} (hb : G.totalDegree ≤ b) (hbs : b ≤ s) (hreg : ∀ y, G * y ∈ I → y ∈ I) :
    finrank K (low I s) + finrank K (restrictTotalDegree σ K (s - b)) ≤
      finrank K (low (I ⊔ Ideal.span {G}) s) + finrank K (low I (s - b)) := by
  let m := LinearMap.mulLeft K G
  have hB : (restrictTotalDegree σ K (s - b)).map m ≤ restrictTotalDegree σ K s := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hy
    rw [mem_restrictTotalDegree]
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add hb hy).trans (Nat.add_sub_of_le hbs).le)
  have : FiniteDimensional K ((restrictTotalDegree σ K (s - b)).map m) :=
    Submodule.finiteDimensional_of_le hB
  have hsup : low I s ⊔ (restrictTotalDegree σ K (s - b)).map m ≤ low (I ⊔ Ideal.span {G}) s := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact mem_low.2 ⟨Ideal.mem_sup_left (mem_low.1 hx).1, (mem_low.1 hx).2⟩
    · exact mem_low.2 ⟨by
        obtain ⟨y, -, rfl⟩ := hx
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self G)),
        (mem_restrictTotalDegree _ _ _).1 (hB hx)⟩
  have hinf : low I s ⊓ (restrictTotalDegree σ K (s - b)).map m ≤ (low I (s - b)).map m := by
    rintro x ⟨hxA, y, hy, rfl⟩
    exact ⟨y, mem_low.2 ⟨hreg y (mem_low.1 hxA).1, (mem_restrictTotalDegree _ _ _).1 hy⟩, rfl⟩
  have e1 :=
    Submodule.finrank_sup_add_finrank_inf_eq (low I s) ((restrictTotalDegree σ K (s - b)).map m)
  have e2 := (Submodule.equivMapOfInjective m (mulLeft_injective hG) (restrictTotalDegree σ K (s - b))).finrank_eq
  have e3 := (Submodule.finrank_mono hinf).trans (Submodule.finrank_map_le m (low I (s - b)))
  have e4 := Submodule.finrank_mono hsup
  rw [e2, ← e1]
  exact Nat.add_le_add e4 e3

/-- **Telescoping.** Abstract form of the count: `D`, `dJ`, `dJ'` stand for `dim K[σ]_{≤ s}`,
`dim J ∩ K[σ]_{≤ s}` and `dim (J + (G')) ∩ K[σ]_{≤ s}`. `hreg` is the non-zero-divisor step for `G'`
of degree `≤ b'`, `hlin` bounds the Hilbert function of `J` by `c (s + 2)` from `s₁` on, and `hpts`
says that `n` points on the zero set of `J + (G')` impose independent conditions. Then `n ≤ c b'`:
otherwise the Hilbert function of `J` would grow by `c b' + 1` per step of `b'`. -/
theorem card_le_of_hilbert {n c b' s₁ : ℕ} (D dJ dJ' : ℕ → ℕ) (hJ : ∀ s, dJ s ≤ D s)
    (hreg : ∀ s, b' ≤ s → dJ s + D (s - b') ≤ dJ' s + dJ (s - b'))
    (hlin : ∀ s, s₁ ≤ s → D s ≤ dJ s + c * (s + 2))
    (hpts : ∀ s, n ≤ s + 1 → n + dJ' s ≤ D s) : n ≤ c * b' := by
  refine Nat.le_of_not_lt fun hn => ?_
  -- From `n + s₁` on, each step of `b'` raises the Hilbert function of `J` by at least `c b' + 1`.
  have key : ∀ t, t * (c * b' + 1) + dJ (n + s₁ + t * b') ≤ D (n + s₁ + t * b') := by
    intro t
    induction t with
    | zero => rw [Nat.zero_mul, Nat.zero_add, Nat.zero_mul, Nat.add_zero]; exact hJ _
    | succ t ih =>
      have hu : n ≤ n + s₁ + t * b' := Nat.le_add_right_of_le (Nat.le_add_right n s₁)
      rw [Nat.succ_mul, Nat.succ_mul, ← Nat.add_assoc (n + s₁) (t * b') b']
      generalize n + s₁ + t * b' = u at ih hu ⊢
      have h1 := hreg (u + b') (Nat.le_add_left b' u)
      rw [Nat.add_sub_cancel] at h1
      have h2 := hpts (u + b') (Nat.le_succ_of_le (Nat.le_add_right_of_le hu))
      have h3 : t * (c * b' + 1) + dJ (u + b') ≤ dJ' (u + b') :=
        Nat.le_of_add_le_add_right (b := dJ u) <|
          ((Nat.add_right_comm _ _ _).trans (Nat.add_comm _ _)).trans_le
            ((Nat.add_le_add_left ih _).trans h1)
      exact ((congrArg (· + dJ (u + b')) (Nat.add_comm _ _)).trans (Nat.add_assoc _ _ _)).trans_le
        ((Nat.add_le_add (Nat.succ_le_of_lt hn) h3).trans h2)
  have h1 := key (c * (n + s₁ + 2) + 1)
  have h2 := hlin (n + s₁ + (c * (n + s₁ + 2) + 1) * b')
    (Nat.le_add_right_of_le (Nat.le_add_left s₁ n))
  have e1 : (c * (n + s₁ + 2) + 1) * (c * b' + 1) =
      c * b' * (c * (n + s₁ + 2) + 1) + (c * (n + s₁ + 2) + 1) := by ring
  have e2 : c * (n + s₁ + (c * (n + s₁ + 2) + 1) * b' + 2) =
      c * b' * (c * (n + s₁ + 2) + 1) + c * (n + s₁ + 2) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h := h1.trans h2
  generalize c * b' * (c * (n + s₁ + 2) + 1) = X at h
  generalize c * (n + s₁ + 2) = Y at h
  exact Nat.not_succ_le_self Y
    (Nat.le_of_add_le_add_left (Nat.le_of_add_le_add_right (h.trans_eq (Nat.add_comm _ _))))

end LeanVM.Protocol.Whir.AffineCombiner.HF
