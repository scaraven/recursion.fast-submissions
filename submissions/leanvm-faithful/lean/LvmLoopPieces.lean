import LvmLoopInterp
import LvmE2QFieldCorrect

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmQAsmHar47Off`, outside its import closure.)

-- ===== merged from `LvmLoopRows` (GOLF module merge: `LvmLoopRows.lean` is now a stub importing `LvmLoopPieces`) =====
section

/-!
# LoopIR tables: the constraint polynomials state the row relations

`Shape.Rel σ v` is a shape's operation as a relation between the values a table row holds: the
result and operand values assembled from their limb columns (`valOf`), and the fixed constants.
`constraints_sound`: on a well-typed shape, if every constraint polynomial vanishes at a row, the
relation holds (`constraints_complete`: and conversely, for the honest prover). The algebra is the
limb formula of the product in `FE = FK[y]/(y^3 + y + 1)` (`mul_c₀`, `mul_c₁`, `mul_c₂`, from
`LvmFieldE`'s Karatsuba product in characteristic 2).
-/

namespace Lvm.Loop

open FE Program

/-! ## Limbs -/

/-- Limb `l` of an `E` value (`c₂` from `l = 2` on). -/
def limb (x : FE) : Nat → FK
  | 0 => x.c₀
  | 1 => x.c₁
  | _ => x.c₂

theorem two_eq_zero_FK : (2 : FK) = 0 := CharTwo.two_eq_zero

theorem mul_c₀ (x y : FE) : (x * y).c₀ = x.c₀ * y.c₀ + x.c₁ * y.c₂ + x.c₂ * y.c₁ := by
  show (FE.mul x y).c₀ = _
  simp only [FE.mul]
  linear_combination (x.c₁ * y.c₁ + x.c₂ * y.c₂) * two_eq_zero_FK

theorem mul_c₁ (x y : FE) :
    (x * y).c₁ = x.c₀ * y.c₁ + x.c₁ * y.c₀ + x.c₁ * y.c₂ + x.c₂ * y.c₁ + x.c₂ * y.c₂ := by
  show (FE.mul x y).c₁ = _
  simp only [FE.mul]
  linear_combination (x.c₀ * y.c₀ + x.c₁ * y.c₁) * two_eq_zero_FK

theorem mul_c₂ (x y : FE) :
    (x * y).c₂ = x.c₀ * y.c₂ + x.c₁ * y.c₁ + x.c₂ * y.c₀ + x.c₂ * y.c₂ := by
  show (FE.mul x y).c₂ = _
  simp only [FE.mul]
  linear_combination (x.c₀ * y.c₀) * two_eq_zero_FK

@[simp] theorem add_c₀ (x y : FE) : (x + y).c₀ = x.c₀ + y.c₀ := rfl
@[simp] theorem add_c₁ (x y : FE) : (x + y).c₁ = x.c₁ + y.c₁ := rfl
@[simp] theorem add_c₂ (x y : FE) : (x + y).c₂ = x.c₂ + y.c₂ := rfl

theorem FE.ext_limb {x y : FE} (h : ∀ l < 3, limb x l = limb y l) : x = y := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  cases x; cases y; simp only [limb] at h0 h1 h2; subst h0 h1 h2; rfl

theorem FK.eq_of_add_eq_zero {a b : FK} (h : a + b = 0) : a = b := by
  linear_combination h - b * two_eq_zero_FK

/-! ## Polynomial evaluation -/

theorem Poly2.ev_append (P R : Poly2) (v : Var → FK) : (P ++ R).ev v = P.ev v + R.ev v := by
  induction P with
  | nil => simp only [ev, List.nil_append, List.foldr_nil, zero_add]
  | cons m P ih =>
    simp only [List.cons_append, Poly2.ev, List.foldr_cons] at ih ⊢
    rw [ih]; ring

@[simp] theorem Poly2.ev_nil (v : Var → FK) : Poly2.ev [] v = 0 := rfl

@[simp] theorem Poly2.ev_var (u : Var) (v : Var → FK) : (Poly2.var u).ev v = v u := by
  simp only [ev, var, List.foldr_cons, List.map_cons, List.map_nil, prodK, mul_one, one_mul,
      List.foldr_nil, add_zero]

@[simp] theorem Poly2.ev_const (c : FK) (v : Var → FK) : (Poly2.const c).ev v = c := by
  simp only [ev, const, List.foldr_cons, List.map_nil, prodK, mul_one, List.foldr_nil, add_zero]

theorem valOf_limb_E (u : Nat → FK) {l : Nat} (hl : l < 3) : limb (valOf .E u) l = u l := by
  interval_cases l <;> rfl

theorem valOf_limb_K (u : Nat → FK) (l : Nat) : limb (valOf .K u) l = if l = 0 then u 0 else 0 := by
  rcases l with _ | _ | l <;> rfl

/-- Limb `l` of an operand column group is the value's limb. -/
theorem limbPoly_ev (τ : Ty) (u : Nat → Var) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (limbPoly u τ.limbs l).ev v = limb (valOf τ (fun i => v (u i))) l := by
  cases τ
  · rw [valOf_limb_K]; simp only [limbPoly, Ty.limbs]
    by_cases h : l = 0
    · subst h; simp only [Order.lt_one_iff, ↓reduceIte, Poly2.ev_var]
    · simp only [show ¬l < 1 by omega, ↓reduceIte, Poly2.ev_nil, h]
  · simp only [limbPoly, Ty.limbs, hl, ↓reduceIte, Poly2.ev_var, valOf_limb_E _ hl]

theorem limbFix_ev (c : FCol) (τ : Ty) (u : Nat → Var) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (limbFix c u τ.limbs l).ev v = v (.fix c) * limb (valOf τ (fun i => v (u i))) l := by
  cases τ
  · rw [valOf_limb_K]; simp only [limbFix, Ty.limbs]
    by_cases h : l = 0
    · subst h; simp only [Poly2.ev, Order.lt_one_iff, ↓reduceIte, List.foldr_cons, List.map_cons,
        List.map_nil, prodK, mul_one, one_mul, List.foldr_nil, add_zero]
    · simp only [show ¬l < 1 by omega, ↓reduceIte, Poly2.ev_nil, h, mul_zero]
  · simp only [Poly2.ev, limbFix, Ty.limbs, hl, ↓reduceIte, List.foldr_cons, List.map_cons,
      List.map_nil, prodK, mul_one, one_mul, List.foldr_nil, add_zero, valOf_limb_E _ hl]

theorem prodTerms_110 : prodTerms 1 1 0 = ([(0, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_111 : prodTerms 1 1 1 = ([] : List (Nat × Nat)) := rfl
theorem prodTerms_112 : prodTerms 1 1 2 = ([] : List (Nat × Nat)) := rfl
theorem prodTerms_310 : prodTerms 3 1 0 = ([(0, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_311 : prodTerms 3 1 1 = ([(1, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_312 : prodTerms 3 1 2 = ([(2, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_130 : prodTerms 1 3 0 = ([(0, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_131 : prodTerms 1 3 1 = ([(0, 1)] : List (Nat × Nat)) := rfl
theorem prodTerms_132 : prodTerms 1 3 2 = ([(0, 2)] : List (Nat × Nat)) := rfl
theorem prodTerms_330 : prodTerms 3 3 0 = ([(0, 0), (1, 2), (2, 1)] : List (Nat × Nat)) := rfl
theorem prodTerms_331 : prodTerms 3 3 1 = ([(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)] : List (Nat × Nat)) := rfl
theorem prodTerms_332 : prodTerms 3 3 2 = ([(0, 2), (1, 1), (2, 0), (2, 2)] : List (Nat × Nat)) := rfl

/-- **The product limb formula**: limb `l` of `a·b` from the limb columns of `a` and `b`. -/
theorem prodPoly_ev (τa τb : Ty) (u w : Nat → Var) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (prodPoly u w τa.limbs τb.limbs l).ev v =
      limb (valOf τa (fun i => v (u i)) * valOf τb (fun i => v (w i))) l := by
  cases τa <;> cases τb <;> interval_cases l <;>
    simp only [Poly2.ev, prodPoly, Ty.limbs, prodTerms_110, List.map_cons, List.map_nil, List.foldr_cons, prodK, mul_one, one_mul, List.foldr_nil, add_zero, limb, valOf, ofK, mul_c₀, mul_zero, prodTerms_111, mul_c₁, zero_mul, prodTerms_112, mul_c₂, prodTerms_130, prodTerms_131, prodTerms_132, prodTerms_310, prodTerms_311, zero_add, prodTerms_312, prodTerms_330, prodTerms_331, prodTerms_332] <;> ring

/-! ## The relation of a shape -/

namespace Shape

variable (σ : Shape)

/-- Operand `o`'s value at a row. -/
def argV (v : Var → FK) (o : Nat) : FE := valOf (σ.args.getD o .K) fun l => v (.arg o l)

/-- The result's value at a row. -/
def resV (v : Var → FK) : FE := valOf σ.ty fun l => v (.res l)

/-- **The relation a row of the shape states.** -/
def Rel (v : Var → FK) : Prop :=
  match σ.kind with
  | .muladd => σ.resV v = σ.argV v 0 * σ.argV v 1 + σ.argV v 2
  | .lin => σ.resV v = σ.argV v 0 + FE.ofK (v (.fix .k)) * σ.argV v 1 + FE.ofK (v (.fix .k'))
  | .assert0 => σ.argV v 1 * σ.argV v 0 = 0
  | .loadE => σ.resV v = σ.argV v 0 + FE.y * σ.argV v 1 + FE.y * FE.y * σ.argV v 2
  | .fixmul => σ.resV v = FE.ofK (v (.fix .F)) * σ.argV v 0 + σ.argV v 1
  | .readd => True
  | .e2mul h => σ.resV v = FE.ofK ((E2Fn.mul.val fun o => v (.arg o 0)).coord h)
  | .e2lin h =>
    -- the `k'` column holds `k_h` (`fvalBasic`), the only constant coordinate `h` reads: `k₀ = k₁ = k'` here
    σ.resV v = FE.ofK (((E2Fn.lin (v (.fix .k)) (v (.fix .k')) (v (.fix .k'))).val fun o => v (.arg o 0)).coord h)

/-- A well-typed shape: arities, and a `K` result only from `K` operands. -/
def TypeOk : Prop :=
  match σ.kind with
  | .muladd => σ.args.length = 3 ∧ (σ.ty = .E ∨ ∀ t ∈ σ.args, t = .K)
  | .lin => σ.args.length = 2 ∧ (σ.ty = .E ∨ ∀ t ∈ σ.args, t = .K)
  | .assert0 => σ.args.length = 2
  | .loadE => σ.args = [.K, .K, .K] ∧ σ.ty = .E
  | .fixmul => σ.args.length = 2 ∧ (σ.ty = .E ∨ ∀ t ∈ σ.args, t = .K)
  | .readd => σ.args = [.K]
  | .e2mul _ => σ.args.length = 6 ∧ (∀ t ∈ σ.args, t = .K) ∧ σ.ty = .K
  | .e2lin _ => σ.args.length = 4 ∧ (∀ t ∈ σ.args, t = .K) ∧ σ.ty = .K

end Shape

theorem argLimbs_eq (σ : Shape) (o : Nat) : σ.argLimbs o = (σ.args.getD o .K).limbs := rfl

theorem isK_valOf_K (u : Nat → FK) : IsK (valOf .K u) := rfl

theorem argV_isK {σ : Shape} (h : ∀ t ∈ σ.args, t = .K) (v : Var → FK) (o : Nat) :
    IsK (σ.argV v o) := by
  unfold Shape.argV
  by_cases ho : o < σ.args.length
  · rw [show σ.args.getD o .K = .K by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho, Option.getD_some]
      exact h _ (List.getElem_mem ho)]
    exact isK_valOf_K _
  · rw [List.getD_eq_default _ _ (by omega)]; exact isK_valOf_K _

theorem isK_limb_pos {x : FE} (h : IsK x) {l : Nat} (hl : 0 < l) : limb x l = 0 := by
  rw [← h]; rcases l with _ | _ | l
  · omega
  · rfl
  · rfl

/-- The result value is `rhs` when its limb columns are `rhs`'s (and `rhs` is a `K` value when the
result is a `K` cell). -/
theorem resV_eq (σ : Shape) (v : Var → FK) (rhs : FE)
    (h : ∀ l < σ.ty.limbs, v (.res l) = limb rhs l) (hK : σ.ty = .K → IsK rhs) :
    σ.resV v = rhs := by
  apply FE.ext_limb
  intro l hl
  unfold Shape.resV
  cases hσ : σ.ty
  · rw [valOf_limb_K]
    rw [hσ] at h
    by_cases h0 : l = 0
    · subst h0; simp only [if_true]; exact h 0 (by simp only [Ty.limbs, Order.lt_one_iff])
    · rw [if_neg h0, isK_limb_pos (hK hσ) (by omega)]
  · rw [valOf_limb_E _ hl]; rw [hσ] at h; exact h l (by simpa [Ty.limbs] using hl)

theorem mem_constraints_map {f : Nat → Poly2} {n : Nat} {v : Var → FK}
    (h : ∀ C ∈ (List.range n).map f, C.ev v = 0) : ∀ l < n, (f l).ev v = 0 :=
  fun l hl => h _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)

theorem limbs_le (τ : Ty) : τ.limbs ≤ 3 := by cases τ <;> simp only [Ty.limbs, Nat.one_le_ofNat,
    Std.le_refl]

theorem limb_add (x y : FE) (l : Nat) : limb (x + y) l = limb x l + limb y l := by
  rcases l with _ | _ | l <;> rfl

theorem limb_ofK_mul (c : FK) (x : FE) (l : Nat) : limb (FE.ofK c * x) l = c * limb x l := by
  rcases l with _ | _ | l <;> simp only [limb, ofK, mul_c₀, zero_mul, add_zero, zero_add, mul_c₁,
      mul_c₂]

theorem limb_ofK (c : FK) (l : Nat) : limb (FE.ofK c) l = if l = 0 then c else 0 := by
  rcases l with _ | _ | l <;> rfl

theorem Shape.ev_limbArg (σ : Shape) (v : Var → FK) (o : Nat) {l : Nat} (hl : l < 3) :
    (limbPoly (Var.arg o) (σ.argLimbs o) l).ev v = limb (σ.argV v o) l := limbPoly_ev _ _ _ hl

theorem Shape.ev_fixArg (σ : Shape) (c : FCol) (v : Var → FK) (o : Nat) {l : Nat} (hl : l < 3) :
    (limbFix c (Var.arg o) (σ.argLimbs o) l).ev v = v (.fix c) * limb (σ.argV v o) l :=
  limbFix_ev _ _ _ _ hl

theorem Shape.ev_prodArg (σ : Shape) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (prodPoly (Var.arg 0) (Var.arg 1) (σ.argLimbs 0) (σ.argLimbs 1) l).ev v =
      limb (σ.argV v 0 * σ.argV v 1) l := prodPoly_ev _ _ _ _ _ hl

theorem argV_K {σ : Shape} {o : Nat} (h : σ.args.getD o .K = .K) (v : Var → FK) :
    σ.argV v o = FE.ofK (v (.arg o 0)) := by
  unfold Shape.argV; rw [h]; rfl

/-- **The constraints state the relation.** -/
theorem constraints_sound (σ : Shape) (hσ : σ.TypeOk) (v : Var → FK)
    (h : ∀ C ∈ σ.constraints, C.ev v = 0) : σ.Rel v := by
  have h3 := limbs_le σ.ty
  rcases hk : σ.kind with _ | _ | _ | _ | _ | _ | hh | hh
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => isK_add (isK_mul (argV_isK
      (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _) (argV_isK (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _))
      (argV_isK (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _))
    have hl3 : l < 3 := by omega
    have e := hl l hlt
    rw [Poly2.ev_append, Poly2.ev_append, Poly2.ev_var, σ.ev_prodArg v hl3, σ.ev_limbArg v 2 hl3] at e
    rw [limb_add]
    apply FK.eq_of_add_eq_zero; linear_combination e
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => isK_add (isK_add (argV_isK
      (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _) (isK_mul (isK_ofK _)
      (argV_isK (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _))) (isK_ofK _))
    have hl3 : l < 3 := by omega
    have e := hl l hlt
    rw [Poly2.ev_append, Poly2.ev_append, Poly2.ev_append, Poly2.ev_var, σ.ev_limbArg v 0 hl3,
      σ.ev_fixArg .k v 1 hl3] at e
    rw [limb_add, limb_add, limb_ofK_mul, limb_ofK]
    apply FK.eq_of_add_eq_zero
    by_cases h0 : l = 0
    · simp only [h0, if_true, Poly2.ev_var] at e ⊢; linear_combination e
    · simp only [h0, if_false, Poly2.ev_nil] at e ⊢; linear_combination e
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    simp only [Shape.Rel, hk]
    rw [mul_comm]
    apply FE.ext_limb
    intro l hl3
    have hl := mem_constraints_map h
    by_cases hb : σ.argLimbs 0 = 1 ∧ σ.argLimbs 1 = 1
    · have hK : ∀ t : Ty, t.limbs = 1 → t = .K := fun t ht => by
        cases t
        · rfl
        · exact absurd ht (by decide)
      have hK0 : (σ.args.getD 0 .K) = .K := hK _ hb.1
      have hK1 : (σ.args.getD 1 .K) = .K := hK _ hb.2
      have hisK : IsK (σ.argV v 0 * σ.argV v 1) := isK_mul (by rw [argV_K hK0]; rfl)
        (by rw [argV_K hK1]; rfl)
      rcases l with _ | l
      · have e := hl 0 (by simp only [hb, and_self, ↓reduceIte, Order.lt_one_iff])
        rw [σ.ev_prodArg v (by omega)] at e
        exact e
      · rw [isK_limb_pos hisK (by omega)]; rcases l with _ | _ <;> rfl
    · have e := hl l (by simp only [hb, ↓reduceIte, hl3])
      rw [σ.ev_prodArg v hl3] at e
      exact e.trans (by interval_cases l <;> rfl)
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => by simp only [hσ.2, reduceCtorEq] at hK)
    rw [hσ.2] at hlt
    have hl3 : l < 3 := by simpa [Ty.limbs] using hlt
    have e := hl l hl3
    rw [Poly2.ev_append, Poly2.ev_var, Poly2.ev_var] at e
    rw [FK.eq_of_add_eq_zero e]
    have hg : ∀ o < 3, σ.args.getD o .K = .K := fun o ho => by
      rw [hσ.1]; interval_cases o <;> rfl
    rw [argV_K (hg 0 (by omega)), argV_K (hg 1 (by omega)), argV_K (hg 2 (by omega))]
    interval_cases l <;> simp only [limb, ofK, y, add_c₀, mul_c₀, zero_mul, mul_zero, add_zero,
        mul_one, mul_c₁, mul_c₂, zero_add, add_c₁, one_mul, add_c₂]
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => isK_add (isK_mul (isK_ofK _)
      (argV_isK (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _))
      (argV_isK (hσ.2.resolve_left (by simp only [hK, reduceCtorEq, not_false_eq_true])) _ _))
    have hl3 : l < 3 := by omega
    have e := hl l hlt
    rw [Poly2.ev_append, Poly2.ev_append, Poly2.ev_var, σ.ev_fixArg .F v 0 hl3,
      σ.ev_limbArg v 1 hl3] at e
    rw [limb_add, limb_ofK_mul]
    apply FK.eq_of_add_eq_zero; linear_combination e
  · simp only [Shape.Rel, hk]
  · simp only [Shape.TypeOk, hk] at hσ
    simp only [Shape.constraints, hk] at h
    simp only [Shape.Rel, hk, Shape.resV, hσ.2.2, valOf]
    congr 1
    cases hh
    · have e := h _ (List.mem_singleton_self _)
      simp only [Poly2.ev_append, Poly2.ev_var] at e
      simp only [Poly2.ev, prodK, List.map, List.foldr] at e
      simp only [E2Fn.val, E2Fn.opd, FE2.mul_def, FE2.add_def, FE2.coord_false]
      apply FK.eq_of_add_eq_zero; linear_combination e
    · have e := h _ (List.mem_singleton_self _)
      simp only [Poly2.ev_append, Poly2.ev_var] at e
      simp only [Poly2.ev, prodK, List.map, List.foldr] at e
      simp only [E2Fn.val, E2Fn.opd, FE2.mul_def, FE2.add_def, FE2.coord_true]
      apply FK.eq_of_add_eq_zero; linear_combination e
  · simp only [Shape.TypeOk, hk] at hσ
    simp only [Shape.constraints, hk] at h
    simp only [Shape.Rel, hk, Shape.resV, hσ.2.2, valOf]
    congr 1
    have e := h _ (List.mem_singleton_self _)
    simp only [Poly2.ev_append, Poly2.ev_var] at e
    simp only [Poly2.ev, prodK, List.map, List.foldr] at e
    cases hh <;>
    · simp only [E2Fn.val, E2Fn.opd, FE2.mul_def, FE2.add_def, FE2.ofK, FE2.coord_false, FE2.coord_true,
        if_true, if_false, Bool.false_eq_true] at e ⊢
      apply FK.eq_of_add_eq_zero; linear_combination e

end Lvm.Loop
end
-- ===== end of `LvmLoopRows` =====

/-!
# Pieces partition the instances

A block's template rows are cut by shape (`Block.shapes`, `Block.rowsOf`) and each shape's rows by
the binary decomposition of their count (`binParts`, `chunks`): every template row lies in exactly
one piece, at one position, and a piece has `2^a` rows. So the piece rows `(n, p, x)` of the program
(`Program.prows`) and its instances are in bijection by `Program.pinst`:

* `prow_inst`: a piece row is an instance of the program, of the piece's shape;
* `inst_prow`: every instance is a piece row (`pinst p x`);
* `prow_inj`: two piece rows with one instance are one piece row.

Proof-help for `LvmLoopSound` (one seed per cell, and every row relation from a table row).
-/

namespace Lvm.Loop

/-! ## Binary decomposition and chunks -/

theorem bitsUp_sum : ∀ (f k n : Nat), n < 2 ^ f → ((bitsUp f k n).map (2 ^ ·)).sum = 2 ^ k * n
  | 0, k, n, h => by simp only [pow_zero, Order.lt_one_iff] at h; subst h; simp only [bitsUp, List.map_nil, List.sum_nil, mul_zero]
  | f + 1, k, n, h => by
    have ih := bitsUp_sum f (k + 1) (n / 2) (by rw [Nat.pow_succ] at h; omega)
    simp only [bitsUp, List.map_append, List.sum_append, ih]
    split
    · have hn : n = 2 * (n / 2) + 1 := by (clear h ih; omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      conv_rhs => rw [hn]
      ring
    · have hn : n = 2 * (n / 2) := by (clear h ih; omega)
      simp only [List.map_nil, List.sum_nil, Nat.zero_add]
      conv_rhs => rw [hn]
      ring

theorem binParts_sum (n : Nat) : ((binParts n).map (2 ^ ·)).sum = n := by
  have h : n < 2 ^ (n + 1) := Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by omega) (by omega))
  rw [binParts, List.map_reverse, List.sum_reverse, bitsUp_sum _ _ _ h]; simp only [pow_zero,
      one_mul]

theorem chunks_spec : ∀ (as l : List Nat), (as.map (2 ^ ·)).sum = l.length →
    (chunks as l).flatMap (·.2) = l ∧ ∀ c ∈ chunks as l, c.2.length = 2 ^ c.1
  | [], l, h => by simp only [List.map_nil, List.sum_nil] at h; simp only [chunks, List.flatMap_nil, List.eq_nil_of_length_eq_zero h.symm, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self]
  | a :: as, l, h => by
    simp only [List.map_cons, List.sum_cons] at h
    obtain ⟨ih1, ih2⟩ := chunks_spec as (l.drop (2 ^ a)) (by simp only [List.length_drop]; omega)
    refine ⟨by simp only [chunks, List.flatMap_cons, ih1, List.take_append_drop], fun c hc => ?_⟩
    simp only [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [List.length_take, inf_eq_left]; (clear * - h; omega)
    · exact ih2 c hc

/-! ## Distinct shapes -/

/-! ## The pieces of a block -/

namespace Block

variable (B : Block)

theorem mem_pieces {b : Nat} {p : Piece} (hp : p ∈ B.pieces b) :
    p.blk = b ∧ p.ts.length = 2 ^ p.a ∧
      ∀ t ∈ p.ts, t < B.tpl.length ∧ (B.tpl.getD t default).shape = p.shape := by
  simp only [pieces, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨σ, -, ⟨a, ts⟩, hc, rfl⟩ := hp
  refine ⟨rfl, (chunks_spec _ _ (binParts_sum _)).2 _ hc, fun t ht => ?_⟩
  have : t ∈ B.rowsOf σ := by
    rw [← (chunks_spec (binParts (B.rowsOf σ).length) (B.rowsOf σ) (binParts_sum _)).1,
      List.mem_flatMap]
    exact ⟨_, hc, ht⟩
  simp only [rowsOf, List.mem_filter, List.mem_range, decide_eq_true_eq] at this
  exact this

end Block

/-! ## The pieces of a program -/

namespace Program

variable (Q : Program)

theorem mem_pieces {p : Piece} (hp : p ∈ Q.pieces) :
    p.blk < Q.blocks.length ∧ p.ts.length = 2 ^ p.a ∧
      ∀ t ∈ p.ts, t < (Q.blk p.blk).tpl.length ∧ ((Q.blk p.blk).tpl.getD t default).shape = p.shape := by
  simp only [pieces, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨b, hb, hp⟩ := hp
  obtain ⟨h1, h2, h3⟩ := (Q.blk b).mem_pieces hp
  subst h1
  exact ⟨hb, h2, h3⟩

theorem mem_ipieces {n : Nat} {p : Piece} : (n, p) ∈ Q.ipieces ↔ Q.pieces[n]? = some p := by
  simp only [ipieces, List.mem_map, List.mem_zipIdx_iff_getElem?, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨p', n'⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨(p, n), h, rfl, rfl⟩

theorem mem_prows {n x : Nat} {p : Piece} :
    (n, p, x) ∈ Q.prows ↔ Q.pieces[n]? = some p ∧ x < 2 ^ Q.height p := by
  simp only [prows, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨n', p'⟩, hm, x', hx, rfl, rfl, rfl⟩
    exact ⟨(Q.mem_ipieces).mp hm, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨(n, p), (Q.mem_ipieces).mpr h, x, hx, rfl, rfl, rfl⟩

theorem height_eq (p : Piece) : 2 ^ Q.height p = 2 ^ p.a * (Q.blk p.blk).size := by
  simp only [height, pow_add, Block.size]

/-- **A piece row is an instance of the program, of the piece's shape.** -/
theorem prow_inst {n x : Nat} {p : Piece} (h : (n, p, x) ∈ Q.prows) :
    Q.pinst p x ∈ Q.insts ∧ (Q.pinst p x).row.shape = p.shape := by
  obtain ⟨hn, hx⟩ := (Q.mem_prows).mp h
  have hp : p ∈ Q.pieces := List.mem_of_getElem? hn
  obtain ⟨hb, hlen, hts⟩ := Q.mem_pieces hp
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  rw [Q.height_eq] at hx
  have hi : x / (Q.blk p.blk).size < p.ts.length := by
    rw [hlen, Nat.div_lt_iff_lt_mul hsz]; exact hx
  have hmem : p.ts.getD (x / (Q.blk p.blk).size) 0 ∈ p.ts := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  obtain ⟨ht, hsh⟩ := hts _ hmem
  refine ⟨(Q.mem_insts _).mpr ⟨p.blk, hb, _, Nat.mod_lt _ hsz, _, ht, rfl⟩, ?_⟩
  simpa [pinst, inst] using hsh

end Program

end Lvm.Loop
