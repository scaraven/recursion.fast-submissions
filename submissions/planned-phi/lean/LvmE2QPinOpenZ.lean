-- New for lvm2 E2-FT (E2F-QH5): the small shape's `E2` claims at S2GF: V_S's small claim (`onStackZB` =
-- `onStackZBN 23`) of a word half on regular blocks (`halfB_small`: the parts moved down), of a `D` word half
-- (`halfD_small`: `κ` times the half at `D`'s small point, through `LvmE2QPinOpenG.zWR_D` over `Quad Ext3`), of a
-- regular row claim (`onStackZB_reg`), at the rotated point.
import LvmE2QPinOpenF
import LvmE2QPinOpenG

/-!
# The small shape's `E2` claims

* `R6 = Quad Ext3` as a ring (`Quad FE x`), `q6 : FE6 → R6` multiplicative (`q6_mul`), `e2q : E2 → R6`,
  `q6_wordWD`: V's word weight is `pR` over `R6`; `L6 h`: coordinate `h` as an `E3`-linear map;
* **`halfB_small`**: on regular parts, the small claim is the sum of the parts' claims moved down, at `x^σ`;
* **`halfD_small`**: on `D` (one part, coefficient `1`), the small claim is `eqAbove_D(x^σ)` times coordinate `h` of
  `wordW(dzE z, x^σ)·κ(z)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape

/-! ## `Quad Ext3` as a ring -/

/-- `Quad Ext3 = E3[X]/(X² + xX + 1)` as a commutative ring. -/
abbrev R6 := Quad FE FE6.xE

/-- A `FE6` value in the ring. -/
def q6 (a : FE6) : R6 := ⟨a.re, a.im⟩

theorem q6_mul (a b : FE6) : q6 (FE6.mul a b) = q6 a * q6 b := by
  rw [fe6_mul]
  apply QuadraticAlgebra.ext
  · rw [Quad.re_mul]; rfl
  · rw [Quad.im_mul]
    show a.re * b.im + a.im * b.re + FE6.xE * (a.im * b.im) = a.re * b.im + a.im * b.re + FE6.xE * a.im * b.im
    ring

/-- `E2 → Quad Ext3`. -/
def e2q (z : FE2) : R6 := q6 (FE6.ofE2 z)

theorem e2q_mul (a b : FE2) : e2q (a * b) = e2q a * e2q b := by
  apply QuadraticAlgebra.ext
  · rw [Quad.re_mul]
    show FE.ofK (a * b).re = FE.ofK a.re * FE.ofK b.re + FE.ofK a.im * FE.ofK b.im
    rw [FE2.mul_def]
    show FE.ofKRingHom _ = FE.ofKRingHom _ * FE.ofKRingHom _ + FE.ofKRingHom _ * FE.ofKRingHom _
    rw [map_add, map_mul, map_mul]
  · rw [Quad.im_mul]
    show FE.ofK (a * b).im = FE.ofK a.re * FE.ofK b.im + FE.ofK a.im * FE.ofK b.re + FE6.xE * FE.ofK a.im * FE.ofK b.im
    rw [FE2.mul_def]
    show FE.ofKRingHom _ = FE.ofKRingHom _ * FE.ofKRingHom _ + FE.ofKRingHom _ * FE.ofKRingHom _ +
      FE.ofKRingHom FK.x * FE.ofKRingHom _ * FE.ofKRingHom _
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul]
    ring

theorem e2q_one : e2q 1 = 1 := by apply QuadraticAlgebra.ext <;> rfl

theorem e2q_zero : e2q 0 = 0 := by apply QuadraticAlgebra.ext <;> rfl

theorem e2q_add (a b : FE2) : e2q (a + b) = e2q a + e2q b := by
  apply QuadraticAlgebra.ext
  · show FE.ofKRingHom (a.re + b.re) = _; rw [map_add]; rfl
  · show FE.ofKRingHom (a.im + b.im) = _; rw [map_add]; rfl

theorem q6_ofE (e : FE) : q6 (FE6.ofE e) = algebraMap FE R6 e := rfl

theorem q6_factorV (z : FE2) (r : FE) : q6 (factorV z r) = fR (e2q z) r := by
  rw [wordFactor_eq]
  apply QuadraticAlgebra.ext
  · show r + FE.ofK z.re + 1 = (1 + e2q z + algebraMap FE R6 r).re
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_one, QuadraticAlgebra.algebraMap_eq]
    show _ = 1 + FE.ofK z.re + r
    ring
  · show FE.ofK z.im = (1 + e2q z + algebraMap FE R6 r).im
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_one, QuadraticAlgebra.algebraMap_eq]
    show _ = 0 + FE.ofK z.im + 0
    ring

/-- **V's word weight is `pR` over `Quad Ext3`.** -/
theorem q6_wordWD : ∀ (z : List FE2) (y : List FE), q6 (wordWD z y) = pR (z.map e2q) y := by
  have hgen : ∀ (z : List FE2) (y : List FE) (acc : FE6),
      q6 ((List.zip z y).foldl (fun acc (p : FE2 × FE) => FE6.mul acc (factorV p.1 p.2)) acc) =
        q6 acc * pR (z.map e2q) y := by
    intro z
    induction z with
    | nil => intro y acc; simp [pR]
    | cons a z ih =>
      intro y acc
      cases y with
      | nil => simp [pR]
      | cons b y => rw [List.zip_cons_cons, List.foldl_cons, ih, q6_mul, q6_factorV, List.map_cons, pR_cons]; ring
  intro z y
  have e : wordWD z y = (List.zip z y).foldl (fun acc (p : FE2 × FE) => FE6.mul acc (factorV p.1 p.2)) ⟨1, 0⟩ := rfl
  rw [e, hgen, show q6 ⟨1, 0⟩ = 1 from rfl, one_mul]

/-- Coordinate `h` as an `E3`-linear map. -/
def L6 (h : Bool) : R6 →ₗ[FE] FE where
  toFun q := if h then q.im else q.re
  map_add' a b := by cases h <;> simp
  map_smul' c a := by cases h <;> simp [smul_eq_mul]

theorem c6_eq (h : Bool) (a : FE6) : c6 h a = L6 h (q6 a) := by cases h <;> rfl

/-! ## Word halves on regular parts -/

/-- A part of a half as a block claim: `coord_h(wordW(z, ·)·c)` on its block. -/
def partH (h : Bool) (e : FE2 × Placement × List FE2) : BlockClaim :=
  ⟨e.2.1, fun y => c6 h (FE6.mul (wordWD e.2.2 y) (FE6.ofE2 e.1)), 0⟩

theorem halfB_parts (h : Bool) (P : List (FE2 × Placement × List FE2)) (v : FE) (y : List FE)
    (hy : y.length = CMain.nu20) :
    (halfB CMain.nu20 h P v).onStack.1 y = (P.map fun e => 1 * (partH h e).onStack.1 y).sum := by
  simp only [BlockClaim.onStack, halfB]
  rw [eqAbove_top _ y hy, one_mul, List.take_of_length_le (by omega), c6_sumW6D]
  exact congrArg List.sum (List.map_congr_left fun e _ => by rw [c6_part, one_mul]; rfl)

/-- **The small claim of a half on regular parts**: its parts moved down, at `x^σ`. -/
theorem halfB_small (h : Bool) (P : List (FE2 × Placement × List FE2)) (hP : ∀ e ∈ P, RegP e.2.1) (v t : FE)
    (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB (halfB CMain.nu20 h P v) t).1 x = (P.map fun e => (shiftB (partH h e)).onStack.1 (rotZ x)).sum := by
  have e1 : (onStackZB (halfB CMain.nu20 h P v) t).1 x = zW x (halfB CMain.nu20 h P v).onStack.1 := by
    unfold zW onStackZB
    rw [show (halfB CMain.nu20 h P v).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  rw [e1, zW_congr x hx (halfB_parts h P v), zW_sum]
  exact congrArg List.sum (List.map_congr_left fun e he => by
    rw [one_mul, zW_eq_zb (partH h e) 0 (hP e he) x hx, onStackZB_reg _ 0 (hP e he) x hx])

/-! ## `D` word halves -/

/-- `D`'s small point over `E2`: `z₀…z₁₇ ‖ z₂₀ z₂₁ ‖ 0 0`. -/
def dzE (z : List FE2) : List FE2 := z.take 18 ++ [z.getD 20 0, z.getD 21 0, 0, 0]

/-- `D`'s scale over `E2`: `(1 + z₁₈)(1 + z₁₉)`. -/
def kapE (z : List FE2) : FE2 := (1 + z.getD 18 0) * (1 + z.getD 19 0)

theorem getD_map_e2q (z : List FE2) (i : ℕ) : (z.map e2q).getD i 0 = e2q (z.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases z[i]? with
  | none => exact e2q_zero.symm
  | some a => rfl

theorem kapR_map (z : List FE2) : kapR (z.map e2q) = e2q (kapE z) := by
  rw [kapR, kapE, e2q_mul, e2q_add, e2q_add, e2q_one, getD_map_e2q, getD_map_e2q]

theorem dzR_map (z : List FE2) : dzR (z.map e2q) = (dzE z).map e2q := by
  rw [dzR, dzE, List.map_append, List.map_take, getD_map_e2q, getD_map_e2q]
  simp [e2q_zero]

/-- **The small claim of a `D` half** (one part on `⟨22, 0⟩`, coefficient `1`): `eqAbove_D(x^σ)` times coordinate
`h` of `wordW(dzE z, x^σ)·κ(z)`. -/
theorem halfD_small (h : Bool) (z : List FE2) (hz : z.length = 22) (v t : FE) (x : List FE)
    (hx : x.length = CMain.nu20) :
    (onStackZB (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v) t).1 x =
      (⟨22, 0⟩ : Placement).eqAbove (rotZ x) *
        c6 h (FE6.mul (wordWD (dzE z) ((rotZ x).take 22)) (FE6.ofE2 (kapE z))) := by
  have e1 : (onStackZB (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v) t).1 x =
      zW x (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v).onStack.1 := by
    unfold zW onStackZB
    rw [show (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  have hw : ∀ y : List FE, y.length = CMain.nu20 → (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v).onStack.1 y =
      L6 h (algebraMap FE R6 ((⟨22, 0⟩ : Placement).eqAbove y) * pR (z.map e2q) (y.take 22)) := by
    intro y hy
    rw [halfB_parts h _ v y hy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    simp only [partH, BlockClaim.onStack]
    have hs : ∀ (e : FE) (q : R6), e * L6 h q = L6 h (algebraMap FE R6 e * q) := fun e q => by
      rw [← Algebra.smul_def, (L6 h).map_smul, smul_eq_mul]
    rw [c6_eq, q6_mul, show q6 (FE6.ofE2 1) = 1 from e2q_one, mul_one, q6_wordWD, hs]
  rw [e1, zW_congr x hx hw, zW_lin, zWR_D _ (by simp [hz]) x hx, kapR_map, dzR_map, ← q6_wordWD]
  rw [show algebraMap FE R6 ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) * (e2q (kapE z) *
      q6 (wordWD (dzE z) ((rotZ x).take 22))) = ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) •
        q6 (FE6.mul (wordWD (dzE z) ((rotZ x).take 22)) (FE6.ofE2 (kapE z))) by
    rw [Algebra.smul_def, q6_mul]; unfold e2q; ring, (L6 h).map_smul, smul_eq_mul, ← c6_eq]

/-! ## The row claim by components -/

/-- Component `k`'s ring: `E3[X]/(X² + x^(2^k) X + 1)`. -/
abbrev Rk (k : ℕ) := Quad FE (twK k)

/-- A pair in component `k`'s ring. -/
def qk (k : ℕ) (p : FE × FE) : Rk k := ⟨p.1, p.2⟩

/-- `E2 → ` component `k`: `a ↦ σ^k(a_re) + σ^k(a_im) X`. -/
def zk (k : ℕ) (a : FE2) : Rk k := ⟨FE.ofK (a.re ^ 2 ^ k), FE.ofK (a.im ^ 2 ^ k)⟩

theorem qk_qm (k : ℕ) (a b : FE × FE) : qk k (qm (twK k) a b) = qk k a * qk k b := by
  apply QuadraticAlgebra.ext
  · rw [Quad.re_mul]; rfl
  · rw [Quad.im_mul]
    show (qm (twK k) a b).2 = a.1 * b.2 + a.2 * b.1 + twK k * a.2 * b.2
    simp only [qm]
    ring

theorem qk_fct (k : ℕ) (zr : FE2 × FE) : qk k (fct k zr) = fR (zk k zr.1) zr.2 := by
  apply QuadraticAlgebra.ext
  · show 1 + FE.ofK (zr.1.re ^ 2 ^ k) + zr.2 = (1 + zk k zr.1 + algebraMap FE (Rk k) zr.2).re
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_one, QuadraticAlgebra.algebraMap_eq]; rfl
  · show FE.ofK (zr.1.im ^ 2 ^ k) = (1 + zk k zr.1 + algebraMap FE (Rk k) zr.2).im
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_one, QuadraticAlgebra.algebraMap_eq]
    show _ = 0 + FE.ofK (zr.1.im ^ 2 ^ k) + 0
    ring

theorem zk_mul (k : ℕ) (a b : FE2) : zk k (a * b) = zk k a * zk k b := by
  have h := crd_mul_frob k a b
  simp only [crd, Bool.false_eq_true, if_false, if_true] at h
  rw [show zk k (a * b) = qk k (FE.ofK ((a * b).re ^ 2 ^ k), FE.ofK ((a * b).im ^ 2 ^ k)) from rfl, h, qk_qm]
  rfl

theorem zk_add (k : ℕ) (a b : FE2) : zk k (a + b) = zk k a + zk k b := by
  apply QuadraticAlgebra.ext
  · show FE.ofK ((a.re + b.re) ^ 2 ^ k) = FE.ofK (a.re ^ 2 ^ k) + FE.ofK (b.re ^ 2 ^ k)
    rw [← frobK_apply, map_add, frobK_apply, frobK_apply]
    exact map_add FE.ofKRingHom _ _
  · show FE.ofK ((a.im + b.im) ^ 2 ^ k) = FE.ofK (a.im ^ 2 ^ k) + FE.ofK (b.im ^ 2 ^ k)
    rw [← frobK_apply, map_add, frobK_apply, frobK_apply]
    exact map_add FE.ofKRingHom _ _

theorem zk_one (k : ℕ) : zk k 1 = 1 := by
  apply QuadraticAlgebra.ext
  · show FE.ofK ((1 : FK) ^ 2 ^ k) = 1; rw [one_pow]; rfl
  · show FE.ofK ((0 : FK) ^ 2 ^ k) = 0; rw [zero_pow (pow_ne_zero k two_ne_zero)]; rfl

theorem zk_zero (k : ℕ) : zk k 0 = 0 := by
  apply QuadraticAlgebra.ext <;>
  · show FE.ofK ((0 : FK) ^ 2 ^ k) = 0; rw [zero_pow (pow_ne_zero k two_ne_zero)]; rfl

/-- **Component `k` of V's tensor coordinates is `pR` over component `k`'s ring.** -/
theorem qk_phiA (k : ℕ) (z : List FE2) (y : List FE) : qk k (phiA k (tensorWD z y)) = pR (z.map (zk k)) y := by
  rw [phiA_tensorWD]
  have hgen : ∀ (z : List FE2) (y : List FE) (P : FE × FE),
      qk k ((List.zip z y).foldl (fun P zr => qm (twK k) P (fct k zr)) P) = qk k P * pR (z.map (zk k)) y := by
    intro z
    induction z with
    | nil => intro y P; simp [pR]
    | cons a z ih =>
      intro y P
      cases y with
      | nil => simp [pR]
      | cons b y => rw [List.zip_cons_cons, List.foldl_cons, ih, qk_qm, qk_fct, List.map_cons, pR_cons]; ring
  rw [hgen, show qk k (1, 0) = 1 from rfl, one_mul]

/-- The `ν`-pairing of component `k` as an `E3`-linear map. -/
def Lk (ρ : ℕ → FE) (k : ℕ) : Rk k →ₗ[FE] FE where
  toFun q := nuH ρ false k * q.re + nuH ρ true k * q.im
  map_add' a b := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
  map_smul' c a := by simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul, RingHom.id_apply]; ring

/-- **V's row weight by components**: `rowW eqR z y = Σ_k L_k(pR (σ^k z) y)`. -/
theorem rowW_comp (eqR : List FE) (z : List FE2) (y : List FE) :
    rowW eqR z y = ∑ k ∈ Finset.range 64, Lk (fun j => eqR.getD j 0) k (pR (z.map (zk k)) y) := by
  rw [rowW, sumE_eq, lsum_range, show ∑ j ∈ Finset.range 128, eqR.getD j 0 * (tensorWD z y).getD j 0 =
    ∑ j ∈ Finset.range 128, (fun j => eqR.getD j 0) j * (tensorWD z y).getD j 0 from rfl, weight_crt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← qk_phiA]
  rfl

theorem zW_fsum1 (x : List FE) (n : ℕ) (g : ℕ → List FE → FE) :
    zW x (fun y ↦ ∑ i ∈ Finset.range n, g i y) = ∑ i ∈ Finset.range n, zW x (g i) := by
  have := zW_fsum x n (fun _ => 1) g
  simp only [one_mul] at this
  exact this

theorem pR_last {R : Type} [CommRing R] [Algebra FE R] (z : List R) (hz : z.length = 23) (hz22 : z.getD 22 0 = 0)
    (y : List FE) (hy : y.length = 23) :
    pR z y = algebraMap FE R ((⟨22, 0⟩ : Placement).eqAbove y) * pR (z.take 22) (y.take 22) := by
  conv_lhs => rw [← List.take_append_drop 22 z, ← List.take_append_drop 22 y]
  have hz' : z.drop 22 = [0] := by
    apply List.ext_getElem (by simp [hz])
    intro i h1 _
    have : i = 0 := by simp [hz] at h1; omega
    subst this
    rw [List.getElem_drop]
    simpa [List.getD_eq_getElem?_getD, hz] using hz22
  obtain ⟨y22, hy'⟩ : ∃ y22, y.drop 22 = [y22] := by
    rcases hd : y.drop 22 with _ | ⟨a, _ | ⟨b, l⟩⟩
    · have := congrArg List.length hd; simp [hy] at this
    · exact ⟨a, rfl⟩
    · have := congrArg List.length hd; simp [hy] at this
  have hyl : y = y.take 22 ++ [y22] := by rw [← hy', List.take_append_drop]
  rw [pR_append (by simp [hz, hy]), hz', hy', pR_cons, pR_nil, mul_one, mul_comm]
  congr 1
  conv_rhs => rw [hyl]
  rw [eqAbove_app 22 0 _ _ (by simp [hy])]
  simp [selectorPoint, eqEval, Shape.eOfNat_zero, fR]

theorem getD_map_zk (k : ℕ) (z : List FE2) (i : ℕ) : (z.map (zk k)).getD i 0 = zk k (z.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases z[i]? with
  | none => exact (zk_zero k).symm
  | some a => rfl

theorem kapR_zk (k : ℕ) (z : List FE2) : kapR ((z.take 22).map (zk k)) = zk k (kapE (z.take 22)) := by
  rw [kapR, kapE, zk_mul, zk_add, zk_add, zk_one, getD_map_zk, getD_map_zk]

theorem dzR_mapZ (k : ℕ) (w : List FE2) : dzR (w.map (zk k)) = (dzE w).map (zk k) := by
  rw [dzR, dzE, List.map_append, List.map_take, getD_map_zk, getD_map_zk]
  simp [zk_zero]

theorem dzR_zk (k : ℕ) (z : List FE2) : dzR ((z.take 22).map (zk k)) = (dzE (z.take 22)).map (zk k) :=
  dzR_mapZ k (z.take 22)

/-- **The small claim of the tape's row claim** (on `⟨23, 0⟩`, its point `0` above `D`): by components,
`eqAbove_D(x^σ)·σ^k(κ(z))·pR(σ^k(dzE z), x^σ)` paired with `ν`. -/
theorem rowZ_small (eqR : List FE) (z : List FE2) (hz : z.length = 23) (hz22 : z.getD 22 0 = 0) (v t : FE)
    (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB ⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ t).1 x =
      ∑ k ∈ Finset.range 64, Lk (fun j => eqR.getD j 0) k
        (algebraMap FE (Rk k) ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) *
          (zk k (kapE (z.take 22)) * pR ((dzE (z.take 22)).map (zk k)) ((rotZ x).take 22))) := by
  have e1 : (onStackZB ⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ t).1 x =
      zW x (⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ : BlockClaim).onStack.1 := by
    unfold zW onStackZB
    rw [show (⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ : BlockClaim).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  have hw : ∀ y : List FE, y.length = CMain.nu20 → (⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ : BlockClaim).onStack.1 y =
      ∑ k ∈ Finset.range 64, Lk (fun j => eqR.getD j 0) k
        (algebraMap FE (Rk k) ((⟨22, 0⟩ : Placement).eqAbove y) * pR ((z.take 22).map (zk k)) (y.take 22)) := by
    intro y hy
    simp only [BlockClaim.onStack]
    rw [eqAbove_top _ y hy, one_mul, List.take_of_length_le (by omega), rowW_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pR_last _ (by simp [hz]) (by rw [getD_map_zk, hz22, zk_zero]) y hy, List.map_take]
  rw [e1, zW_congr x hx hw, zW_fsum1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zW_lin, zWR_D _ (by simp [hz]) x hx, kapR_zk, dzR_zk]

end Lvm.Q2
