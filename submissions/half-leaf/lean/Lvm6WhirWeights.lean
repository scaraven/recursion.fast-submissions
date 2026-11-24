-- New for lvm6 (WP W1). The deployed verifier's weights (FORMAT6 v2.2.1 §6.6) as a `WtIface E2`:
-- a weight is `(κ, Φ)`, meaning the claim `Σ_u Σ_c Φ(u ++ c) · lowMsg_κ(U_u)(c)` on a tuple `U`
-- (leanVM `tclaim`); a fold evaluates `Φ`'s first variable at `α` (as `foldFn`); the glue adds the
-- OOD weight `λ·eq(z, ·)` and the queries' weights `λ^(k+2)·∏_i ((1 − y_i) + y_i Ŵ_i(x_k))`
-- (leanVM `eqEval`, `colFactor`/`inducedWeight`). The level's admitted weights are those with its
-- `κ` and `Φ` affine in each variable (`wokE`); with them the ladder's weight facts hold
-- (`hWH`, `hglue`, `den_wGlue`). After leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/
-- {Weights,State,Tuple}.lean` @ fdb317982.
import Lvm6WhirCode
import Lvm6WhirSum
import Lvm6WhirLadder

/-!
# The deployed weights (W1)

* `bl u`: a cube point as a list of `0`/`1`; `sum_cube_succ`.
* `denE κ Φ`, **`WtE`**: the weights, `den_wFold` (folding = `foldFn`).
* `prodL a n y = ∏_{i<n} a_i(y_i)`; `MA_prodL`; `eqL z`, `colL h x`: the OOD and query weights.
* `wGlueE`: the verifier's glue at a deployed level; **`den_wGlueE`**: it means `glued (tailE2 …)`.
* `wokE κ m w`: `w.1 = κ` and `w.2` affine in each of its `m + κ` variables; `hWH_E`, `hglue_E`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Whir Polynomial Finset

/-! ## Cube points as lists -/

/-- A cube point as a list of `0`/`1` values. -/
noncomputable def bl {n : ℕ} (u : Fin n → Bool) : List E2 := List.ofFn fun i ↦ if u i then 1 else 0

theorem bl_cons {n : ℕ} (b : Bool) (u : Fin n → Bool) :
    bl (Fin.cons b u : Fin (n + 1) → Bool) = (if b then 1 else 0) :: bl u := by
  simp [bl, List.ofFn_succ]

theorem bl_zero (u : Fin 0 → Bool) : bl u = [] := rfl

theorem sum_cube_succ {M : Type*} [AddCommMonoid M] {m : ℕ} (f : (Fin (m + 1) → Bool) → M) :
    ∑ v, f v = ∑ u, f (Fin.cons false u) + ∑ u, f (Fin.cons true u) := by
  rw [← (Fin.consEquiv fun _ ↦ Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

/-! ## The weights -/

/-- **A deployed weight's meaning**: `U ↦ Σ_u Σ_c Φ(u ++ c)·lowMsg_κ(U_u)(c)`. -/
noncomputable def denE {m : ℕ} (κ : ℕ) (Φ : List E2 → E2) : Tup E2 m →ₗ[E2] E2 where
  toFun U := ∑ u : Fin m → Bool, ∑ c : Fin κ → Bool, Φ (bl u ++ bl c) * lowMsgF κ (U u) c
  map_add' U V := by
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' a U := by
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The verifier's fold of a weight's table by `α`. -/
noncomputable def foldTab (Φ : List E2 → E2) (α : E2) : List E2 → E2 :=
  fun x ↦ (1 - α) * Φ (0 :: x) + α * Φ (1 :: x)

theorem denE_join {m : ℕ} (κ : ℕ) (Φ : List E2 → E2) (P G : Tup E2 m) :
    denE (m := m + 1) κ Φ (joinT P G) =
      ∑ u : Fin m → Bool, ∑ c : Fin κ → Bool, (Φ (0 :: (bl u ++ bl c)) * lowMsgF κ (P u) c +
        Φ (1 :: (bl u ++ bl c)) * lowMsgF κ (G u) c) := by
  show (∑ v : Fin (m + 1) → Bool, ∑ c : Fin κ → Bool,
    Φ (bl v ++ bl c) * lowMsgF κ (joinT P G v) c) = _
  rw [sum_cube_succ (fun v ↦ ∑ c : Fin κ → Bool, Φ (bl v ++ bl c) * lowMsgF κ (joinT P G v) c),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [joinT_false, joinT_true, bl_cons, bl_cons]
  simp only [Bool.false_eq_true, if_false, if_true, List.cons_append]

theorem denE_fold {m : ℕ} (κ : ℕ) (Φ : List E2 → E2) (α : E2) :
    denE (m := m) κ (foldTab Φ α) = foldFn (denE (m := m + 1) κ Φ) α := by
  refine LinearMap.ext fun P ↦ ?_
  rw [foldFn_apply]
  have hl : (inlT P : Tup E2 (m + 1)) = joinT P 0 := rfl
  have hr : (inrT P : Tup E2 (m + 1)) = joinT 0 P := rfl
  rw [hl, hr, denE_join, denE_join]
  show (∑ u : Fin m → Bool, ∑ c : Fin κ → Bool,
    foldTab Φ α (bl u ++ bl c) * lowMsgF κ (P u) c) = _
  simp only [Pi.zero_apply, map_zero, Pi.zero_apply, mul_zero, add_zero, zero_add, Finset.mul_sum,
    ← Finset.sum_add_distrib, foldTab]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  ring

/-- **The deployed weights** as the verifier holds them. -/
noncomputable def WtE : WtIface E2 where
  Wt _ := ℕ × (List E2 → E2)
  den w := denE w.1 w.2
  wFold w α := (w.1, foldTab w.2 α)
  den_wFold w α := denE_fold w.1 w.2 α

theorem wFolds_fst {m : ℕ} : ∀ (j : ℕ) (rs : List (Rnd E2)) (w : WtE.Wt (m + j)),
    (wFolds WtE j rs w).1 = w.1
  | 0, _, _ => rfl
  | j + 1, rs, w => wFolds_fst (m := m) j rs.tail _

/-! ## Multiaffine tables -/

theorem MA_add : ∀ {n : ℕ} {f g : List E2 → E2}, MA n f → MA n g → MA n fun x ↦ f x + g x
  | 0, _, _, _, _ => trivial
  | n + 1, _, _, hf, hg => ⟨fun X x ↦ by simp only []; rw [hf.1 X x, hg.1 X x]; ring,
      fun X ↦ MA_add (hf.2 X) (hg.2 X)⟩

theorem MA_mul_const : ∀ {n : ℕ} {f : List E2 → E2} (a : E2), MA n f → MA n fun x ↦ a * f x
  | 0, _, _, _ => trivial
  | n + 1, _, a, hf => ⟨fun X x ↦ by simp only []; rw [hf.1 X x]; ring,
      fun X ↦ MA_mul_const a (hf.2 X)⟩

theorem MA_zero : ∀ (n : ℕ), MA n fun _ : List E2 ↦ (0 : E2)
  | 0 => trivial
  | n + 1 => ⟨fun _ _ ↦ by ring, fun _ ↦ MA_zero n⟩

theorem MA_sum {ι : Type} (s : Finset ι) {n : ℕ} (f : ι → List E2 → E2)
    (hf : ∀ i ∈ s, MA n (f i)) : MA n fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MA_zero n
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact MA_add (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem MA.fold {n : ℕ} {Φ : List E2 → E2} (h : MA (n + 1) Φ) (α : E2) : MA n (foldTab Φ α) := by
  have : foldTab Φ α = fun x ↦ Φ (α :: x) := funext fun x ↦ (h.1 α x).symm
  rw [this]
  exact h.2 α

/-- `∏_{i<n} a_i(y_i)`. -/
noncomputable def prodL (a : ℕ → E2 → E2) : ℕ → List E2 → E2
  | 0, _ => 1
  | n + 1, y => a 0 (y.headD 0) * prodL (fun i ↦ a (i + 1)) n y.tail

/-- A product of affine factors is multiaffine. -/
theorem MA_prodL : ∀ (n : ℕ) (a : ℕ → E2 → E2), (∀ i X, a i X = (1 - X) * a i 0 + X * a i 1) →
    MA n (prodL a n)
  | 0, _, _ => trivial
  | n + 1, a, ha => ⟨fun X x ↦ by simp only [prodL, List.headD_cons, List.tail_cons]; rw [ha 0 X]; ring,
      fun X ↦ by
        simp only [prodL, List.headD_cons, List.tail_cons]
        exact MA_mul_const _ (MA_prodL n _ fun i ↦ ha (i + 1))⟩

theorem bl_succ {n : ℕ} (w : Fin (n + 1) → Bool) :
    bl w = (if w 0 then 1 else 0) :: bl (fun i : Fin n ↦ w i.succ) := by
  simp [bl, List.ofFn_succ]

theorem prodL_bl : ∀ (n : ℕ) (a : ℕ → E2 → E2) (w : Fin n → Bool),
    prodL a n (bl w) = ∏ i : Fin n, a i (if w i then 1 else 0)
  | 0, _, _ => by simp [prodL]
  | n + 1, a, w => by
    rw [bl_succ, prodL, List.headD_cons, List.tail_cons, prodL_bl n _ _, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]

/-! ## The OOD and query weights -/

/-- The OOD weight `eq(z, y) = ∏_i (z_i y_i + (1 − z_i)(1 − y_i))`. -/
noncomputable def eqL {ν : ℕ} (z : Fin ν → E2) : List E2 → E2 :=
  prodL (fun i X ↦ (if h : i < ν then z ⟨i, h⟩ else 0) * X +
    (1 - if h : i < ν then z ⟨i, h⟩ else 0) * (1 - X)) ν

/-- The query weight at position `x`: `∏_{i<κ} ((1 − y_i) + y_i Ŵ_i(K(x)))`. -/
noncomputable def colL (κ : ℕ) (x : ℕ) : List E2 → E2 :=
  prodL (fun i X ↦ (1 - X) + X * algebraMap K E2 (normVanishingAt i (K.ofBits x))) κ

theorem MA_eqL {ν : ℕ} (z : Fin ν → E2) : MA ν (eqL z) :=
  MA_prodL ν _ fun i X ↦ by ring

theorem MA_colL (κ x : ℕ) : MA κ (colL κ x) :=
  MA_prodL κ _ fun i X ↦ by ring

/-! ## The glue -/

theorem lowMsgF_msgPolyF {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E2) :
    lowMsgF κ (msgPolyF κ g) = g := by
  have := lowMsgF_msgPolyF_add hκ g 0
  rwa [mul_zero, add_zero] at this

/-- The current level's weight on a next tuple's polynomial reads its message. -/
theorem denE_phiE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (hko : ko + 1 ≤ 64)
    (Φ : List E2 → E2) (U : Tup E2 (0 + ℓ')) :
    denE (m := 0) (ko + 1) Φ (phiE κ' ℓ' ko hκ U) =
      ∑ w : Fin (ko + 1) → Bool, Φ (bl w) * keyE κ' ℓ' ko hκ U w := by
  simp only [denE, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_unique, bl_zero, List.nil_append,
    phiE_apply, lowMsgF_msgPolyF hko]

/-- The OOD functional is the weight `eqL z` on the message. -/
theorem mleEval_eq_sum {ν : ℕ} (z : Fin ν → E2) (g : (Fin ν → Bool) → E2) :
    mleEval z g = ∑ w, g w * eqL z (bl w) := by
  simp only [mleEval, mlePoly, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [eqL, prodL_bl]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [i.isLt, ↓reduceDIte, Fin.eta]
  by_cases hw : w i <;> simp [hw]

/-- A query's functional is the weight `colL` on the message. -/
theorem evx_phiE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (hko : ko + 1 ≤ 64) (h : ℕ)
    (hh : h ≤ 64) (x : Fin (2 ^ h)) (U : Tup E2 (0 + ℓ')) :
    evx (domE h hh) x (phiE κ' ℓ' ko hκ U) =
      ∑ w : Fin (ko + 1) → Bool, keyE κ' ℓ' ko hκ U w * colL (ko + 1) x (bl w) := by
  simp only [evx, LinearMap.coe_mk, AddHom.coe_mk, phiE_apply, msgPolyF, eval_finsetSum,
    eval_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  congr 1
  rw [colL, prodL_bl]
  show (Polynomial.map (algebraMap K E2) (novel (bitsToNat w))).eval
      (algebraMap K E2 (K.ofBits x)) = _
  rw [eval_map, eval₂_at_apply, eval_novel, novelAt_bitsToNat hko, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hw : w i <;> simp [hw]

/-- The next tuples' lanes and messages as one message (`keyE`'s order). -/
def splitE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) :
    (Fin (0 + ℓ') → Bool) × (Fin κ' → Bool) ≃ (Fin (ko + 1) → Bool) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
    (Equiv.arrowCongr (finSumFinEquiv.trans (finCongr hκ)) (Equiv.refl Bool))

theorem keyE_splitE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (U : Tup E2 (0 + ℓ'))
    (p : (Fin (0 + ℓ') → Bool) × (Fin κ' → Bool)) :
    keyE κ' ℓ' ko hκ U (splitE κ' ℓ' ko hκ p) = lowMsgF κ' (U p.1) p.2 := by
  obtain ⟨u, c⟩ := p
  simp [keyE, splitE, Equiv.arrowCongr_apply]

theorem splitE_apply (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (u : Fin (0 + ℓ') → Bool)
    (c : Fin κ' → Bool) (j : Fin (ko + 1)) :
    splitE κ' ℓ' ko hκ (u, c) j =
      if h : (j : ℕ) < 0 + ℓ' then u ⟨j, h⟩ else c ⟨j - (0 + ℓ'), by have := j.isLt; omega⟩ := by
  simp only [splitE, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_apply,
    Function.comp_apply, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply]
  by_cases h : (j : ℕ) < 0 + ℓ'
  · rw [dif_pos h, show (Fin.cast hκ.symm j : Fin (0 + ℓ' + κ')) = Fin.castAdd κ' ⟨j, h⟩ from
      Fin.ext rfl, finSumFinEquiv_symm_apply_castAdd]
    rfl
  · rw [dif_neg h, show (Fin.cast hκ.symm j : Fin (0 + ℓ' + κ')) =
      Fin.natAdd (0 + ℓ') ⟨j - (0 + ℓ'), by have := j.isLt; omega⟩ from Fin.ext (by simp; omega),
      finSumFinEquiv_symm_apply_natAdd]
    rfl

theorem bl_splitE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1)
    (p : (Fin (0 + ℓ') → Bool) × (Fin κ' → Bool)) :
    bl (splitE κ' ℓ' ko hκ p) = bl p.1 ++ bl p.2 := by
  obtain ⟨u, c⟩ := p
  refine List.ext_getElem (by simp only [bl, List.length_ofFn, List.length_append]; omega)
    fun i h1 h2 ↦ ?_
  have hlen : (bl u).length = 0 + ℓ' := by simp [bl]
  simp only [bl, List.length_ofFn] at h1
  rw [show (bl (splitE κ' ℓ' ko hκ (u, c)))[i] =
      if splitE κ' ℓ' ko hκ (u, c) ⟨i, h1⟩ then 1 else 0 by simp only [bl, List.getElem_ofFn],
    splitE_apply]
  by_cases hi : i < 0 + ℓ'
  · rw [dif_pos hi, List.getElem_append_left (by rw [hlen]; exact hi)]
    simp [bl]
  · rw [dif_neg hi, List.getElem_append_right (by rw [hlen]; omega)]
    simp only [bl, List.getElem_ofFn, List.length_ofFn]

/-- A weight on next tuples, reindexed by the one message. -/
theorem denE_eq_sum_key (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (Ψ : List E2 → E2)
    (U : Tup E2 (0 + ℓ')) :
    denE (m := 0 + ℓ') κ' Ψ U = ∑ w : Fin (ko + 1) → Bool, Ψ (bl w) * keyE κ' ℓ' ko hκ U w := by
  rw [← (splitE κ' ℓ' ko hκ).sum_comp, Fintype.sum_prod_type]
  simp only [denE, LinearMap.coe_mk, AddHom.coe_mk, keyE_splitE, bl_splitE]

/-- **The verifier's glue** at a deployed level: the running weight, the OOD weight, the queries'. -/
noncomputable def wGlueE (κ' ℓ' ko t h : ℕ) (w : WtE.Wt 0) (o : TailOut E2 ko t (2 ^ h)) :
    WtE.Wt (0 + ℓ') :=
  (κ', fun y ↦ w.2 y + o.lam * eqL o.z y +
    ∑ k : Fin t, o.lam ^ ((k : ℕ) + 2) * colL (ko + 1) (o.ps k) y)

/-- **The glue means `glued`** for a weight of the level's `κ = ko + 1`. -/
theorem den_wGlueE (ko ℓ h κ' ℓ' h' kq t c : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (w : WtE.Wt 0) (hw : w.1 = ko + 1)
    (o : TailOut E2 ko t (2 ^ h)) :
    WtE.den (wGlueE κ' ℓ' ko t h w o) =
      glued (tailE2 ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht) (WtE.den w) o.z
        o.lam o.ps := by
  obtain ⟨κw, Φ⟩ := w
  simp only at hw
  subst hw
  refine LinearMap.ext fun U ↦ ?_
  show denE κ' _ U = _
  rw [denE_eq_sum_key κ' ℓ' ko hκ]
  simp only [glued, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.sum_apply, smul_eq_mul]
  show _ = denE (m := 0) (ko + 1) Φ (phiE κ' ℓ' ko hκ U) + o.lam * mleEval o.z (keyE κ' ℓ' ko hκ U) +
    ∑ k : Fin t, o.lam ^ ((k : ℕ) + 2) * evx (domE h hh) (o.ps k) (phiE κ' ℓ' ko hκ U)
  rw [denE_phiE κ' ℓ' ko hκ hko.le, mleEval_eq_sum]
  simp only [evx_phiE κ' ℓ' ko hκ hko.le h hh, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [wGlueE, add_mul, Finset.sum_mul]
  ring_nf

/-! ## The admitted weights -/

/-- **The weights a level admits**: its `κ`, and a table affine in each of the `m + κ` variables. -/
def wokE (κ m : ℕ) (w : WtE.Wt (0 + m)) : Prop := w.1 = κ ∧ MA (m + κ) w.2

end Lvm6.Whir
