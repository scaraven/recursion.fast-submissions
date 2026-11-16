/- `LvmTensorSwitchOff` (GOLF2 off-path move, group 29 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmTensorSwitch,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmTensorSwitch

-- ===== from `LvmTensorSwitch` =====

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section Eq
variable {S : Type*} [CommRing S] {m : ℕ}

theorem map_eqPt {T : Type*} [CommRing T] (f : S →+* T) (z : Fin m → S) (u : Fin m → Bool) :
    f (eqPt z u) = eqPt (fun l ↦ f (z l)) u := by
  simp only [eqPt, map_prod]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  split <;> simp

/-- `Σ_u eq(a, u)·eq(b, u) = Π_l (a_l b_l + (1 − a_l)(1 − b_l))`. -/
theorem sum_eqPt_mul (a b : Fin m → S) :
    ∑ u, eqPt a u * eqPt b u = ∏ l, (a l * b l + (1 - a l) * (1 - b l)) := by
  have h : ∀ l, a l * b l + (1 - a l) * (1 - b l) =
      ∑ x : Bool, (if x then a l else 1 - a l) * (if x then b l else 1 - b l) := fun l ↦ by
    simp
  rw [Finset.prod_congr rfl fun l _ ↦ h l, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [eqPt, eqPt, ← Finset.prod_mul_distrib]

end Eq
end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section Word
variable {K : Type*} [CommRing K] {t : K} {m : ℕ}

/-- `Σ_u eq(z, u)·f(u)` in coordinates. -/
theorem wordClaim_eq (z : Fin m → Quad K t) (f : (Fin m → Bool) → K) :
    ∑ u, eqPt z u * Quad.C (f u) =
      ⟨∑ u, (eqPt z u).re * f u, ∑ u, (eqPt z u).im * f u⟩ := by
  ext
  · rw [← QuadraticAlgebra.reₗ_apply (R := K), map_sum]
    exact Finset.sum_congr rfl fun u _ ↦ Quad.re_mul_C _ _
  · rw [← QuadraticAlgebra.imₗ_apply (R := K), map_sum]
    exact Finset.sum_congr rfl fun u _ ↦ Quad.im_mul_C _ _

/-- **Prop 7.1 (1)**: a word claim `f̃(z) = v` is the pair of `K`-linear claims
`Σ_u w_k(u) f(u) = v_k`. -/
theorem wordClaim_iff (z : Fin m → Quad K t) (f : (Fin m → Bool) → K) (v : Quad K t) :
    ∑ u, eqPt z u * Quad.C (f u) = v ↔
      (∑ u, (eqPt z u).re * f u = v.re ∧ ∑ u, (eqPt z u).im * f u = v.im) := by
  rw [wordClaim_eq, QuadraticAlgebra.ext_iff]

/-- **Prop 7.1 (2), the tensor switch**: the extensions at `r ∈ F^m` of the two weights are the
coordinates of `Π_l (z_l r_l + (1 − z_l)(1 − r_l))` in `Quad F t'`, for any `φ : K →+* F`. -/
theorem tensorSwitch {F : Type*} [CommRing F] (φ : K →+* F) {t' : F} (h : φ t = t')
    (z : Fin m → Quad K t) (r : Fin m → F) :
    ∏ l, (Quad.map φ t' h (z l) * Quad.C (r l) +
        (1 - Quad.map φ t' h (z l)) * (1 - Quad.C (r l))) =
      ⟨∑ u, eqPt r u * φ (eqPt z u).re, ∑ u, eqPt r u * φ (eqPt z u).im⟩ := by
  rw [← sum_eqPt_mul]
  have e : ∀ u, eqPt (fun l ↦ Quad.map φ t' h (z l)) u * eqPt (fun l ↦ (Quad.C (r l) : Quad F t')) u =
      Quad.map φ t' h (eqPt z u) * Quad.C (eqPt r u) := fun u ↦ by
    rw [map_eqPt, Quad.C_eq_algebraMap, map_eqPt]
    rfl
  rw [Finset.sum_congr rfl fun u _ ↦ e u]
  ext
  · rw [← QuadraticAlgebra.reₗ_apply (R := F), map_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [QuadraticAlgebra.reₗ_apply, Quad.re_mul_C, Quad.map_re, mul_comm]
  · rw [← QuadraticAlgebra.imₗ_apply (R := F), map_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [QuadraticAlgebra.imₗ_apply, Quad.im_mul_C, Quad.map_im, mul_comm]

/-- **Prop 7.1 (3)**: a false pair `(a, b) ≠ 0` of claim differences survives the batching
`a + λ·b` for one `λ` at most. -/
theorem card_batch2_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] (a b : F)
    (hab : a ≠ 0 ∨ b ≠ 0) : (univ.filter fun l : F ↦ a + l * b = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun x hx y hy ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  by_cases hb : b = 0
  · rw [hb, mul_zero, add_zero] at hx
    exact absurd hx (hab.resolve_right (not_not.mpr hb))
  · have : (x - y) * b = 0 := by linear_combination hx - hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)

end Word
end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct

/-- **The tensor switch at `E2 → Quad Ext3`** (ARCH-7 §2.1): `V` computes
`Π_l (z_l r_l + (1 + z_l)(1 + r_l))` in `E6` and reads the two weights off its coordinates. -/
theorem tensorSwitch_E2 {m : ℕ} (z : Fin m → LeanVM.Parameters.E2) (r : Fin m → LeanVM.Parameters.E) :
    ∏ l, (LeanVM.Parameters.e2ToE6 (z l) * Quad.C (r l) +
        (1 - LeanVM.Parameters.e2ToE6 (z l)) * (1 - Quad.C (r l))) =
      ⟨∑ u, eqPt r u * LeanVM.Parameters.ofK (eqPt z u).re,
        ∑ u, eqPt r u * LeanVM.Parameters.ofK (eqPt z u).im⟩ :=
  tensorSwitch _ rfl z r

end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section Slice
variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R A)
  {Kw : Type*} [CommRing Kw] [Algebra R Kw] {κ : Type*} [Fintype κ] [DecidableEq κ] (γ : Module.Basis κ R Kw)
  {B : Type*} [CommRing B] [Algebra R B] [Algebra Kw B] [IsScalarTower R Kw B]
  {m : ℕ} (z : Fin m → A) (q : (Fin m → Bool) → Kw)

/-- **The rows** of the slice values: `t_j = Σ_i (β.repr s_i)_j · γ_i` (the transpose). -/
noncomputable def rowsOf (s : κ → A) (j : ι) : Kw := ∑ i, β.repr (s i) j • γ i

/-- **The true row** `j`: `Σ_u ε_j(u)·q(u)`, `ε_j(u) = (β.repr eq(z, u))_j`. -/
noncomputable def trueRow (j : ι) : Kw := ∑ u, β.repr (eqPt z u) j • q u

private theorem repr_sum_smul {M : Type*} [AddCommGroup M] [Module R M] {ι' : Type*} (b : Module.Basis ι' R M)
    {α : Type*} (s : Finset α) (c : α → R) (e : α → M) (j : ι') :
    b.repr (∑ u ∈ s, c u • e u) j = ∑ u ∈ s, c u * b.repr (e u) j := by
  simp [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- **Transposition**: the slice claims hold iff every row is its true value. Both say
`(β.repr s_i)_j = Σ_u q_i(u)·ε_j(u)` for every bit `i` and coordinate `j`. -/
theorem slicesTrue_iff (s : κ → A) :
    SlicesTrue γ z q s ↔ ∀ j, rowsOf β γ s j = trueRow β z q j := by
  have hrow : ∀ j i, γ.repr (rowsOf β γ s j) i = β.repr (s i) j := fun j i ↦ by
    rw [rowsOf, Module.Basis.repr_sum_self]
  have htrue : ∀ j i, γ.repr (trueRow β z q j) i = ∑ u, γ.repr (q u) i * β.repr (eqPt z u) j :=
    fun j i ↦ by
      rw [trueRow, repr_sum_smul]
      exact Finset.sum_congr rfl fun u _ ↦ mul_comm _ _
  constructor
  · intro hs j
    refine γ.ext_elem fun i ↦ ?_
    rw [hrow, htrue, hs i, repr_sum_smul]
  · intro hr i
    refine β.ext_elem fun j ↦ ?_
    rw [← hrow, hr j, htrue, repr_sum_smul]

end Slice
end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section Slice
variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R A)
  {Kw : Type*} [CommRing Kw] [Algebra R Kw] {κ : Type*} [Fintype κ] [DecidableEq κ] (γ : Module.Basis κ R Kw)
  {B : Type*} [CommRing B] [Algebra R B] [Algebra Kw B] [IsScalarTower R Kw B]
  {m : ℕ} (z : Fin m → A) (q : (Fin m → Bool) → Kw)

omit [DecidableEq ι] in
/-- The true rows give the true target: `Σ_u W(u) q(u) = Σ_j ρ_j·trueRow j`. -/
theorem weight_sum (ρ : ι → B) :
    ∑ u, weight β z ρ u * algebraMap Kw B (q u) = target ρ (trueRow β z q) := by
  simp only [weight, target, trueRow, map_sum, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
  ring

omit [DecidableEq ι] in
/-- **The switched claim** holds iff the batched row errors vanish. -/
theorem claim_iff (ρ : ι → B) (t : ι → Kw) :
    ∑ u, weight β z ρ u * algebraMap Kw B (q u) = target ρ t ↔
      ∑ j, ρ j * algebraMap Kw B (t j - trueRow β z q j) = 0 := by
  rw [weight_sum, target, target, eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [map_sub, mul_sub]

omit [Fintype ι] [DecidableEq ι] in
/-- **The verifier's weight**: in `B ⊗_R A` with the basis `1 ⊗ β_j` (`Algebra.TensorProduct.basis`),
the coordinates of `Π_l (r_l ⊗ z_l + (1 − r_l) ⊗ (1 − z_l))` are `Σ_u eq(r, u)·ε_j(u)`. -/
theorem tensor_repr (r : Fin m → B) (j : ι) :
    (Algebra.TensorProduct.basis B β).repr
        (∏ l, (r l ⊗ₜ[R] z l + (1 - r l) ⊗ₜ[R] (1 - z l))) j =
      ∑ u, eqPt r u * algebraMap R B (β.repr (eqPt z u) j) := by
  let iL : B →ₐ[R] B ⊗[R] A := Algebra.TensorProduct.includeLeft
  let iR : A →ₐ[R] B ⊗[R] A := Algebra.TensorProduct.includeRight
  have hfac : ∀ l, r l ⊗ₜ[R] z l + (1 - r l) ⊗ₜ[R] (1 - z l) =
      iL (r l) * iR (z l) + (1 - iL (r l)) * (1 - iR (z l)) := fun l ↦ by
    have e1 : (1 : B ⊗[R] A) - iL (r l) = iL (1 - r l) := by rw [map_sub, map_one]
    have e2 : (1 : B ⊗[R] A) - iR (z l) = iR (1 - z l) := by rw [map_sub, map_one]
    rw [e1, e2]
    simp only [iL, iR, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Finset.prod_congr rfl fun l _ ↦ hfac l, ← sum_eqPt_mul]
  have e : ∀ u, eqPt (fun l ↦ iL (r l)) u * eqPt (fun l ↦ iR (z l)) u = eqPt r u ⊗ₜ[R] eqPt z u :=
    fun u ↦ by
      rw [show eqPt (fun l ↦ iL (r l)) u = iL (eqPt r u) from
          (map_eqPt (iL : B →+* B ⊗[R] A) r u).symm,
        show eqPt (fun l ↦ iR (z l)) u = iR (eqPt z u) from
          (map_eqPt (iR : A →+* B ⊗[R] A) z u).symm]
      simp only [iL, iR, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Finset.sum_congr rfl fun u _ ↦ e u, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

omit [DecidableEq ι] in
/-- **`V` evaluates the weight's extension**: `Σ_j ρ_j·(coordinate j of the product)` is
`Σ_u eq(r, u)·W(u)`, the multilinear extension of `W` at `r`. -/
theorem weight_ext (ρ : ι → B) (r : Fin m → B) :
    ∑ j, ρ j * (Algebra.TensorProduct.basis B β).repr
        (∏ l, (r l ⊗ₜ[R] z l + (1 - r l) ⊗ₜ[R] (1 - z l))) j =
      ∑ u, eqPt r u * weight β z ρ u := by
  simp only [tensor_repr, weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end Slice
end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section SZ
variable {T : Type*} [CommRing T] {Sm : Type*} [Fintype Sm] [DecidableEq Sm] (σ : Sm → T)

open Classical in
/-- The number of sample points `s ∈ Sm^n` at which `Σ_b eq(σ∘s, b)·δ(b)` vanishes. -/
noncomputable def zeroCount {n : ℕ} (δ : (Fin n → Bool) → T) : ℕ :=
  (univ.filter fun s : Fin n → Sm ↦ ∑ b, eqPt (fun l ↦ σ (s l)) b * δ b = 0).card

/-- The table with its first variable bound to `c`. -/
def fold1 {n : ℕ} (δ : (Fin (n + 1) → Bool) → T) (c : T) (b : Fin n → Bool) : T :=
  (1 - c) * δ (Fin.cons false b) + c * δ (Fin.cons true b)

private theorem sum_split {n : ℕ} (r : Fin (n + 1) → T) (δ : (Fin (n + 1) → Bool) → T) :
    ∑ b, eqPt r b * δ b = ∑ b, eqPt (Fin.tail r) b * fold1 δ (r 0) b := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, eqPt, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    fold1, Fin.tail, ite_true, Bool.false_eq_true, ite_false]
  ring

omit [DecidableEq Sm] in
open Classical in
private theorem zeroCount_succ {n : ℕ} (δ : (Fin (n + 1) → Bool) → T) :
    zeroCount σ δ = ∑ c, zeroCount σ (fold1 δ (σ c)) := by
  simp only [zeroCount, Finset.card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ Sm).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  have ht : (Fin.tail fun l ↦ σ ((Fin.cons c s : Fin (n + 1) → Sm) l)) = fun l ↦ σ (s l) := by
    funext l
    simp [Fin.tail]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, sum_split, Fin.cons_zero, ht]

omit [DecidableEq Sm] in
open Classical in
private theorem zeroCount_le_card {n : ℕ} (δ : (Fin n → Bool) → T) :
    zeroCount σ δ ≤ Fintype.card Sm ^ n := by
  calc zeroCount σ δ ≤ (univ : Finset (Fin n → Sm)).card := Finset.card_filter_le _ _
    _ = Fintype.card Sm ^ n := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

open Classical in
/-- **Schwartz–Zippel over a ring on a product set**: if `σ` is injective with regular
differences (`(σ a − σ b)·x = 0 → x = 0` for `a ≠ b`), a nonzero table `δ` on `{0,1}^n` has
`Σ_b eq(σ∘s, b)·δ(b) = 0` for at most `n·|Sm|^(n−1)` sample points `s`. For a field `T` take
`σ = id`; for `T = Quad Ext3` and challenges in `E3`, `σ = algebraMap`. -/
theorem card_sz_le (hσ : ∀ a b : Sm, a ≠ b → ∀ x : T, (σ a - σ b) * x = 0 → x = 0) :
    ∀ {n : ℕ} (δ : (Fin n → Bool) → T), δ ≠ 0 → zeroCount σ δ ≤ n * Fintype.card Sm ^ (n - 1)
  | 0, δ, hδ => by
    have h0 : ∀ s : Fin 0 → Sm, ∑ b, eqPt (fun l ↦ σ (s l)) b * δ b ≠ 0 := by
      intro s hs
      apply hδ
      funext b
      have hb : ∀ b' : Fin 0 → Bool, b' = b := fun b' ↦ funext fun i ↦ i.elim0
      rw [Fintype.sum_subsingleton _ b, eqPt, Finset.univ_eq_empty, Finset.prod_empty, one_mul] at hs
      exact hs
    rw [zero_mul, Nat.le_zero, zeroCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun s _ ↦ h0 s
  | n + 1, δ, hδ => by
    rw [zeroCount_succ]
    -- at most one `c` makes the folded table zero
    have hone : (univ.filter fun c : Sm ↦ fold1 δ (σ c) = 0).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_contra hne
      have hd : ∀ x, δ (Fin.cons true x) - δ (Fin.cons false x) = 0 := fun x ↦ by
        refine hσ a b hne _ ?_
        have h1 := congrFun ha x
        have h2 := congrFun hb x
        simp only [fold1, Pi.zero_apply] at h1 h2
        linear_combination h1 - h2
      apply hδ
      funext y
      refine Fin.consCases (fun y0 x ↦ ?_) y
      have hx := congrFun ha x
      simp only [fold1, Pi.zero_apply] at hx
      have h1 := hd x
      cases y0
      · show δ (Fin.cons false x) = 0
        linear_combination hx - σ a * h1
      · show δ (Fin.cons true x) = 0
        linear_combination hx + (1 - σ a) * h1
    have hterm : ∀ c, zeroCount σ (fold1 δ (σ c)) ≤
        n * Fintype.card Sm ^ (n - 1) + (if fold1 δ (σ c) = 0 then Fintype.card Sm ^ n else 0) := by
      intro c
      by_cases hc : fold1 δ (σ c) = 0
      · have e : (if fold1 δ (σ c) = 0 then Fintype.card Sm ^ n else 0) = Fintype.card Sm ^ n :=
          ite_eq_left_iff.mpr fun h ↦ absurd hc h
        rw [e]
        exact (zeroCount_le_card σ _).trans (Nat.le_add_left _ _)
      · have e : (if fold1 δ (σ c) = 0 then Fintype.card Sm ^ n else 0) = 0 :=
          ite_eq_right_iff.mpr fun h ↦ absurd h hc
        rw [e, add_zero]
        exact card_sz_le hσ _ hc
    calc ∑ c, zeroCount σ (fold1 δ (σ c))
        ≤ ∑ c, (n * Fintype.card Sm ^ (n - 1) +
            (if fold1 δ (σ c) = 0 then Fintype.card Sm ^ n else 0)) := Finset.sum_le_sum fun c _ ↦ hterm c
      _ = Fintype.card Sm * (n * Fintype.card Sm ^ (n - 1)) +
            (univ.filter fun c : Sm ↦ fold1 δ (σ c) = 0).card * Fintype.card Sm ^ n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
            ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ ≤ n * Fintype.card Sm ^ n + 1 * Fintype.card Sm ^ n := by
          refine Nat.add_le_add ?_ (Nat.mul_le_mul_right _ hone)
          rcases n with _ | n
          · simp
          · rw [Nat.add_sub_cancel]
            exact (by ring : Fintype.card Sm * ((n + 1) * Fintype.card Sm ^ n) =
              (n + 1) * Fintype.card Sm ^ (n + 1)).le
      _ = (n + 1) * Fintype.card Sm ^ (n + 1 - 1) := by
          rw [Nat.add_sub_cancel]
          ring

end SZ
end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section Sound
variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R A)
  {Kw : Type*} [CommRing Kw] [Algebra R Kw] {κ : Type*} [Fintype κ] [DecidableEq κ] (γ : Module.Basis κ R Kw)
  {B : Type*} [CommRing B] [Algebra R B] [Algebra Kw B] [IsScalarTower R Kw B]
  {Sm : Type*} [Fintype Sm] [DecidableEq Sm] (σ : Sm → B)
  {m n : ℕ} (z : Fin m → A) (q : (Fin m → Bool) → Kw) (e : ι ≃ (Fin n → Bool))

omit [DecidableEq ι] [DecidableEq κ] in
open Classical in
/-- **Soundness of the bit-slice switch** (gate G-S): if the slice claims are false, the switched
claim with the row-batching weights `ρ_j = eq(σ∘s, e j)` holds for at most `n·|Sm|^(n−1)` of the
`|Sm|^n` batching points `s` (`7·|E3|^6` of `|E3|^7` at `E2`: escape `7/|E3|`). -/
theorem switch_sound (hσ : ∀ a b : Sm, a ≠ b → ∀ x : B, (σ a - σ b) * x = 0 → x = 0)
    (hinj : Function.Injective (algebraMap Kw B)) (s : κ → A) (hs : ¬ SlicesTrue γ z q s) :
    (univ.filter fun p : Fin n → Sm ↦
        ∑ u, weight β z (fun j ↦ eqPt (fun l ↦ σ (p l)) (e j)) u * algebraMap Kw B (q u) =
          target (fun j ↦ eqPt (fun l ↦ σ (p l)) (e j)) (rowsOf β γ s)).card ≤
      n * Fintype.card Sm ^ (n - 1) := by
  let δ : (Fin n → Bool) → B := fun b ↦ algebraMap Kw B (rowsOf β γ s (e.symm b) - trueRow β z q (e.symm b))
  have hδ : δ ≠ 0 := by
    intro h0
    apply hs
    rw [slicesTrue_iff β γ z q]
    intro j
    have := congrFun h0 (e j)
    simp only [δ, Equiv.symm_apply_apply, Pi.zero_apply] at this
    exact sub_eq_zero.mp (hinj (this.trans (map_zero _).symm))
  refine le_trans (le_of_eq ?_) (card_sz_le σ hσ δ hδ)
  rw [zeroCount]
  congr 1
  refine Finset.filter_congr fun p _ ↦ ?_
  rw [claim_iff, ← e.sum_comp]
  simp only [δ, Equiv.symm_apply_apply]

end Sound
end Lvm.TS
end

section
set_option autoImplicit false
namespace Lvm.TS
open Finset
open scoped TensorProduct
section Concrete
open LeanVM.Parameters

/-- A bit as an element of `GF(2)`. -/
def bit2 (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bit2_xor (x y : Bool) : bit2 (x ^^ y) = bit2 x + bit2 y := by
  cases x <;> cases y <;> decide

/-- The bits of a word of `K` (bit `i` = the coefficient of `x^i`), an `F₂`-linear map. -/
noncomputable def bitsLin : K →ₗ[ZMod 2] (Fin 64 → ZMod 2) where
  toFun a i := bit2 (a.toBitVec.getLsbD i)
  map_add' a b := by
    funext i
    simp only [BF64.add_def, BF64.toBitVec_ofBitVec, BitVec.getLsbD_xor, bit2_xor, Pi.add_apply]
  map_smul' r a := by
    funext i
    rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
    · rw [zero_smul]
      simp only [RingHom.id_apply, zero_smul, Pi.zero_apply]
      rw [show BF64.toBitVec 0 = 0 from rfl]
      simp [bit2]
    · simp only [one_smul, RingHom.id_apply]

private theorem bitsLin_bijective : Function.Bijective bitsLin := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a b h ↦ ?_, ?_⟩
  · apply BF64.toBitVec_injective
    refine BitVec.eq_of_getLsbD_eq fun i hi ↦ ?_
    have := congrFun h ⟨i, hi⟩
    simp only [bitsLin, LinearMap.coe_mk, AddHom.coe_mk, bit2] at this
    revert this
    cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> decide
  · rw [BF64.card_bf64, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **The bit basis of `K` over `F₂`**: coordinate `i` is bit `i` (`bitsK_repr`). -/
noncomputable def bitsK : Module.Basis (Fin 64) (ZMod 2) K :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective bitsLin bitsLin_bijective)

theorem bitsK_repr (a : K) (i : Fin 64) : bitsK.repr a i = bit2 (a.toBitVec.getLsbD i) := by
  rw [bitsK, Module.Basis.ofEquivFun_repr_apply]
  rfl

/-- **The `128` coordinates of `E2` over `F₂`**: bit `i` of `re` (`(i, 0)`) and of `im` (`(i, 1)`). -/
noncomputable def bitsE2 : Module.Basis (Fin 64 × Fin 2) (ZMod 2) E2 :=
  bitsK.smulTower (QuadraticAlgebra.basis 1 g)

theorem bitsE2_repr (y : E2) (i : Fin 64) :
    bitsE2.repr y (i, 0) = bit2 (y.re.toBitVec.getLsbD i) ∧
      bitsE2.repr y (i, 1) = bit2 (y.im.toBitVec.getLsbD i) := by
  simp [bitsE2, Module.Basis.smulTower_repr, bitsK_repr]

/-- The slice claims at `E2` in v1's form (`slicesTrue`): `s_i = Σ_u [bit i of q(u)]·eq(z, u)`. -/
theorem slicesTrue_bits {m : ℕ} (z : Fin m → E2) (q : (Fin m → Bool) → K) (s : Fin 64 → E2) :
    SlicesTrue bitsK z q s ↔
      ∀ i, s i = ∑ u, if (q u).toBitVec.getLsbD i then eqPt z u else 0 := by
  refine forall_congr' fun i ↦ ?_
  have e : ∀ u, bitsK.repr (q u) i • eqPt z u =
      if (q u).toBitVec.getLsbD i then eqPt z u else 0 := fun u ↦ by
    rw [bitsK_repr, bit2]
    split <;> simp
  rw [Finset.sum_congr rfl fun u _ ↦ e u]

/-- **The row order** (pinned for prover, V and L-B): row `(i, h)` (bit `i` of the `X^h` coordinate) is
`j = i + 64·h`, whose 7 bits, least significant first, are the cube point (`eRow_val`). -/
def eRow : Fin 64 × Fin 2 ≃ (Fin 7 → Bool) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans ((finCongr (by norm_num : 2 * 64 = 2 ^ 7)).trans
    (finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv))))

theorem eRow_val (i : Fin 64) (h : Fin 2) :
    (finFunctionFinEquiv (fun l ↦ finTwoEquiv.symm (eRow (i, h) l)) : ℕ) = i + 64 * h := by
  simp [eRow, Equiv.arrowCongr, finProdFinEquiv]

open Classical in
/-- **The bit-slice switch at `E2 ⊗_{F₂} E3` is sound** (gate G-S): false slice claims at an `E2`
point make the switched `E3` claim hold for at most `7·|E3|^6` of the `|E3|^7` row-batching
points `r''` (`ρ_j = eq(r'', e j)`, `128 = 2^7` rows): escape `7/|E3| = 7·2^-192`. -/
theorem switch_sound_E2 {m : ℕ} (z : Fin m → E2) (q : (Fin m → Bool) → K) (s : Fin 64 → E2)
    (e : Fin 64 × Fin 2 ≃ (Fin 7 → Bool)) (hs : ¬ SlicesTrue bitsK z q s) :
    (univ.filter fun p : Fin 7 → E ↦
        ∑ u, weight bitsE2 z (fun j ↦ eqPt (fun l ↦ p l) (e j)) u * algebraMap K E (q u) =
          target (fun j ↦ eqPt (fun l ↦ p l) (e j)) (rowsOf bitsE2 bitsK s)).card ≤
      7 * Fintype.card E ^ (7 - 1) := by
  convert switch_sound bitsE2 bitsK (σ := fun x : E ↦ x) z q e
    (fun a b hab x h ↦ (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab))
    (algebraMap K E).injective s hs using 8

end Concrete
end Lvm.TS
end
