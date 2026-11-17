-- New for lvm2 E2-FT (E2F-VP): roll 10's pending-weight Keccak layer identities (`LvmKeccakSymAdj`,
-- `LvmKeccakSymCorr`, there on `FE`) over any field `F`, for V_S's `E2` front (`FE2`).
import LvmE2VProg
import LvmKeccakSymAdj

/-!
# The Keccak layer's weights against an outer product, over a field

`linearTransposeF (outerUGF A ℓ)` is a layer's next weight vector; `weightedCF_eq` and `rcOuterF_eq` read it
without building it, `corrAF_eq` computes the correlation of two six-coordinate equality kernels by a carry
automaton. Roll 10's statements and proofs (on `FE`), restated over `F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

section

variable {F : Type} [Field F] [Algebra K F]

/-- `eq_kernel` as an array (`eqKernelF`'s values). -/
def eqKernelAF (point : List F) : Array F :=
  point.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- The outer product `u_j = A_{j mod 64}·ℓ_{j / 64}` over the 1600 bits (`verifyKeccakLayerG`'s `weights` line with
`A = eqKernelAF p`). -/
def outerUGF (A laneW : Array F) : List F :=
  (List.range keccakBits).map fun j => A.getD (j % 64) 0 * laneW.getD (j / 64) 0

/-! ## The reference expressions (verbatim from `verifyKeccakLayerG`) -/

/-- `weighted` of `verifyKeccakLayerG`: `Σ_{l<25} eqL_l·Σ_{z<64} eqZ_z·w_{64l+z}`. -/
def weightedRefF (eqZ eqL : Array F) (w : List F) : F :=
  let w := w.toArray
  sumF ((List.range 25).map fun l => eqL.getD l 0 *
    sumF ((List.range 64).map fun z => eqZ.getD z 0 * w.getD (64 * l + z) 0))

/-- One segment's round-constant sum of `iota`: `Σ_{z < 64, bit z of rc} w_z`. -/
def rcRefF (w : List F) (rc : UInt64) : F :=
  sumF ((List.range 64).filterMap fun z => if rc.toNat.testBit z then some (w.getD z 0) else none)

/-! ## The symbolic forms -/


/-- The reference correlation `corr(r) = Σ_{z<64} B_z·A_{(z + r) mod 64}`. -/
def corrGF (A B : Array F) (r : Nat) : F :=
  sumF ((List.range 64).map fun z => B.getD z 0 * A.getD ((z + r) % 64) 0)

/-- `⟨eqL ⊗ B, T(A ⊗ ℓ)⟩` from the correlations (`corr r = corrGF A B r`): with `x = l mod 5` and
`S_c = Σ_y eqL_{c + 5y}`, `Σ_l ℓ_{π l}·((eqL_l + S_{x−1})·corr(ρ_l) + S_{x+1}·corr(ρ_l + 1))`. -/
def weightedCF (corr : Nat → F) (eqL laneW : Array F) : F := Id.run do
  let S : Array F := (Array.range 5).map fun c =>
    eqL.getD c 0 + eqL.getD (c + 5) 0 + eqL.getD (c + 10) 0 + eqL.getD (c + 15) 0 + eqL.getD (c + 20) 0
  let mut acc : F := 0
  for l in [:25] do
    let x := l % 5
    let rl := rhoA.getD l 0
    acc := acc + laneW.getD (keccakPi l) 0 *
      ((eqL.getD l 0 + S.getD ((x + 4) % 5) 0) * corr rl + S.getD ((x + 1) % 5) 0 * corr ((rl + 1) % 64))
  return acc

/-- One segment's round-constant sum on `T(A ⊗ ℓ)`: lane 0 of the transpose is
`g_{0,z} + C_{1,z} + C_{4,z+1}`, `g_{l,z} = A_{(z + ρ_l) mod 64}·ℓ_{π l}`, `C_{c,z} = Σ_y g_{c+5y,z}`. -/
def rcOuterF (A laneW : Array F) (rc : UInt64) : F := Id.run do
  let zs := (List.range 64).filter fun z => rc.toNat.testBit z
  let sh (l off : Nat) : F := sumF (zs.map fun z => A.getD ((z + off + rhoA.getD l 0) % 64) 0)
  let mut acc : F := laneW.getD (keccakPi 0) 0 * sh 0 0
  for y in [:5] do
    acc := acc + laneW.getD (keccakPi (1 + 5 * y)) 0 * sh (1 + 5 * y) 0 +
      laneW.getD (keccakPi (4 + 5 * y)) 0 * sh (4 + 5 * y) 1
  return acc

/-! ## Proof helpers: the loops and the transpose in closed form

Adapted from leanVM `LvmKeccakLinear` (`outer_loop`, `inner_loop`, `flatMap_getD`, `columns_getD`),
restated on `Lvm.FE`. -/

section Helpers

open Finset

private theorem sumE_eq_sum (l : List F) : sumF l = l.sum := by
  unfold sumF
  suffices h : ∀ a : F, l.foldl (· + ·) a = a + l.sum by simpa using h 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

private theorem list_sum_range (f : ℕ → F) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ Finset.range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem sumE_range (f : ℕ → F) (n : ℕ) :
    sumF ((List.range n).map f) = ∑ y ∈ Finset.range n, f y := by
  rw [sumE_eq_sum, list_sum_range]

private theorem foldl_add_sum (g : ℕ → F) : ∀ (l : List ℕ) (a : F),
    l.foldl (fun acc k => acc + g k) a = a + (l.map g).sum
  | [], a => by simp
  | k :: l, a => by rw [List.foldl_cons, foldl_add_sum g l]; simp [add_assoc]

private theorem foldl_add2_sum (g h : ℕ → F) (l : List ℕ) (a : F) :
    l.foldl (fun acc k => acc + g k + h k) a = a + (l.map fun k => g k + h k).sum := by
  rw [← foldl_add_sum]; simp only [add_assoc]

private theorem sum_filter_range (p : ℕ → Bool) (f : ℕ → F) (n : ℕ) :
    (((List.range n).filter p).map f).sum =
      ∑ z ∈ (Finset.range n).filter (fun z => p z = true), f z := by
  rw [Finset.sum_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases h : p n = true <;> simp [h]

private theorem filterMap_ite (p : ℕ → Bool) (f : ℕ → F) (l : List ℕ) :
    l.filterMap (fun z => if p z then some (f z) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a = true <;> simp [h, ih]

private theorem array_getD_toArray (l : List F) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem rhoA_getD (l : ℕ) : rhoA.getD l 0 = keccakRho.getD l 0 := by
  simp [rhoA, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem setIfInBounds_getD (a : Array F) (i p : ℕ) (x : F) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

private theorem flatMap_getD (F : ℕ → ℕ → F) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).getD (m * x + z) 0 = F x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getD F m n x z hxn hz
    · have : x = n := by (clear * - hx hxn; omega)
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

/-- θ's input weights after ρπ (`gOf` of `LvmKeccakLinear`). -/
private def gW (w : List F) (p : ℕ) : F :=
  w.getD (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) 0

/-- A column sum of `gW`. -/
private def colW (w : List F) (x z : ℕ) : F := ∑ y ∈ Finset.range 5, gW w (64 * (x + 5 * y) + z)

private theorem inner_loop (W : ℕ → F) (lane : ℕ) (g : Array F) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := inner_loop W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getD, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; (clear hg hs; omega))

private theorem outer_loop (w : List F) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gW w p else 0
  | 0, _ => ⟨by simp [keccakBits], fun p ↦ by
      simp [Array.getD_eq_getD_getElem?, keccakBits, Array.getElem?_replicate]
      split_ifs <;> rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := outer_loop w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_loop
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by (clear * - h1; omega)), array_getD_toArray, gW]
      have e1 : p / 64 = L := by (clear * - h1; omega)
      have e2 : p % 64 = p - 64 * L := by (clear * - h1 e1; omega)
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by (clear * - h2; omega))]
      · rw [ite_eq_right h2, ite_eq_right (by (clear * - hL h1 h2; omega))]

private theorem columns_getD (A : Array F) (w : List F) (hA : ∀ p < 1600, A.getD p 0 = gW w p)
    {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumF ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colW w x z := by
  rw [array_getD_toArray, flatMap_getD (fun x z ↦
    sumF ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_range]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  simp only [Finset.mem_range] at hy
  exact hA _ (by (clear * - hx hz hy; omega))

/-- **`linearTransposeF` in closed form.** -/
private theorem klt_getD (w : List F) {p : ℕ} (hp : p < 1600) :
    (linearTransposeF w).getD p 0 =
      gW w p + colW w ((p / 64 % 5 + 1) % 5) (p % 64) + colW w ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) := by
  obtain ⟨-, hg⟩ := outer_loop w 25 le_rfl
  have hA : ∀ q < 1600, _ := fun q hq ↦ (hg q).trans (ite_eq_left (by omega : q < 64 * 25))
  unfold linearTransposeF
  simp only []
  have hp' : p = 64 * (p / 64) + p % 64 := by (clear * -; omega)
  conv_lhs => rw [hp']
  rw [flatMap_getD _ 64 25 (p / 64) (p % 64) (by (clear * - hp; omega)) (Nat.mod_lt _ (by (clear * -; omega)))]
  rw [columns_getD _ w hA (by (clear * -; omega)) (Nat.mod_lt _ (by (clear * -; omega))),
    columns_getD _ w hA (by (clear * -; omega)) (Nat.mod_lt _ (by (clear * -; omega))), ← hp', hA p hp]

private theorem keccakPi_lt {l : ℕ} (hl : l < 25) : keccakPi l < 25 := by
  unfold keccakPi; omega

private theorem outerUG_getD (A laneW : Array F) {j : ℕ} (hj : j < 1600) :
    (outerUGF A laneW).getD j 0 = A.getD (j % 64) 0 * laneW.getD (j / 64) 0 := by
  simp [outerUGF, List.getD_eq_getElem?_getD, keccakBits, hj]

/-- `gW` of the outer product: `g_{l,z} = A_{(z + ρ_l) mod 64}·ℓ_{π l}`. -/
private theorem gW_outer (A laneW : Array F) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    gW (outerUGF A laneW) (64 * l + z) =
      A.getD ((z + keccakRho.getD l 0) % 64) 0 * laneW.getD (keccakPi l) 0 := by
  have e1 : (64 * l + z) / 64 = l := by (clear * - hz; omega)
  have e2 : (64 * l + z) % 64 = z := by (clear * - e1; omega)
  have hπ := keccakPi_lt hl
  rw [gW, e1, e2, outerUG_getD _ _ (by (clear * - hπ; omega))]
  congr 2 <;> (clear * -; omega)

/-- `S_c = Σ_y eqL_{c + 5y}`. -/
private def colS (eqL : Array F) (c : ℕ) : F := ∑ y ∈ Finset.range 5, eqL.getD (c + 5 * y) 0

private theorem weightedC_sum (corr : ℕ → F) (eqL laneW : Array F) :
    weightedCF corr eqL laneW = ∑ l ∈ Finset.range 25, laneW.getD (keccakPi l) 0 *
      ((eqL.getD l 0 + colS eqL ((l % 5 + 4) % 5)) * corr (keccakRho.getD l 0) +
        colS eqL ((l % 5 + 1) % 5) * corr ((keccakRho.getD l 0 + 1) % 64)) := by
  simp only [weightedCF, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, foldl_add_sum, pure_bind, zero_add]
  have hS : ∀ c < 5, ((Array.range 5).map fun c => eqL.getD c 0 + eqL.getD (c + 5) 0 + eqL.getD (c + 10) 0 +
      eqL.getD (c + 15) 0 + eqL.getD (c + 20) 0).getD c 0 = colS eqL c := by
    intro c hc
    simp [Array.getD_eq_getD_getElem?, hc, colS, Finset.sum_range_succ]
  show ((List.range' 0 25).map _).sum = _
  rw [← List.range_eq_range', list_sum_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hS _ (by (clear * -; omega)), hS _ (by (clear * -; omega)), rhoA_getD]

/-- `Σ_l S_{(x+k') mod 5}·f_l = Σ_l e_l·Σ_y f_{(x+k) mod 5 + 5y}` for `{k, k'} = {1, 4}`. -/
private theorem regroup (e f : ℕ → F) (k k' : ℕ) (hk : (k = 1 ∧ k' = 4) ∨ (k = 4 ∧ k' = 1)) :
    ∑ l ∈ Finset.range 25, (∑ y ∈ Finset.range 5, e ((l % 5 + k') % 5 + 5 * y)) * f l =
      ∑ l ∈ Finset.range 25, e l * ∑ y ∈ Finset.range 5, f ((l % 5 + k) % 5 + 5 * y) := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceMod, zero_add]
    ring

/-- `g_{l,z}` of the outer product. -/
private def gO (A laneW : Array F) (l z : ℕ) : F :=
  A.getD ((z + keccakRho.getD l 0) % 64) 0 * laneW.getD (keccakPi l) 0

private theorem colW_outer (A laneW : Array F) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    colW (outerUGF A laneW) x z = ∑ y ∈ Finset.range 5, gO A laneW (x + 5 * y) z := by
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [Finset.mem_range] at hy
  exact gW_outer A laneW (by (clear * - hx hy; omega)) hz

/-- Position `64 l + z` of `T(A ⊗ ℓ)`. -/
private theorem klt_outer (A laneW : Array F) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    (linearTransposeF (outerUGF A laneW)).getD (64 * l + z) 0 =
      gO A laneW l z + ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 1) % 5 + 5 * y) z +
        ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 4) % 5 + 5 * y) ((z + 1) % 64) := by
  have e1 : (64 * l + z) / 64 = l := by (clear * - hz; omega)
  have e2 : (64 * l + z) % 64 = z := by (clear * - e1; omega)
  rw [klt_getD _ (by (clear * - hl e1; omega)), gW_outer A laneW hl hz, e1, e2,
    colW_outer A laneW (by (clear * - e1; omega)) hz, colW_outer A laneW (by (clear * - e1; omega)) (by (clear * -; omega))]
  rfl

private theorem weightedRef_closed (A B eqL laneW : Array F) :
    weightedRefF B eqL (linearTransposeF (outerUGF A laneW)) =
      ∑ l ∈ Finset.range 25, eqL.getD l 0 * ∑ z ∈ Finset.range 64, B.getD z 0 *
        (gO A laneW l z + ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 1) % 5 + 5 * y) z +
          ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 4) % 5 + 5 * y) ((z + 1) % 64)) := by
  simp only [weightedRefF, sumE_range]
  refine Finset.sum_congr rfl fun l hl => congrArg (eqL.getD l 0 * ·) ?_
  refine Finset.sum_congr rfl fun z hz => congrArg (B.getD z 0 * ·) ?_
  simp only [Finset.mem_range] at hl hz
  rw [array_getD_toArray, klt_outer A laneW hl hz]

/-- `ℓ_{π l}·corr(ρ_l)`. -/
private def pO (A B laneW : Array F) (l : ℕ) : F :=
  laneW.getD (keccakPi l) 0 * corrGF A B (keccakRho.getD l 0)

/-- `ℓ_{π l}·corr(ρ_l + 1)`. -/
private def qO (A B laneW : Array F) (l : ℕ) : F :=
  laneW.getD (keccakPi l) 0 * corrGF A B ((keccakRho.getD l 0 + 1) % 64)

private theorem sumB_gO (A B laneW : Array F) (l : ℕ) :
    ∑ z ∈ Finset.range 64, B.getD z 0 * gO A laneW l z = pO A B laneW l := by
  rw [pO, corrGF, sumE_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [gO]; ring

private theorem sumB_gO1 (A B laneW : Array F) (l : ℕ) :
    ∑ z ∈ Finset.range 64, B.getD z 0 * gO A laneW l ((z + 1) % 64) = qO A B laneW l := by
  rw [qO, corrGF, sumE_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have : ((z + 1) % 64 + keccakRho.getD l 0) % 64 = (z + (keccakRho.getD l 0 + 1) % 64) % 64 := by omega
  simp only [gO, this]; ring

private theorem inner_closed (A B laneW : Array F) (l : ℕ) :
    ∑ z ∈ Finset.range 64, B.getD z 0 *
        (gO A laneW l z + ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 1) % 5 + 5 * y) z +
          ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 4) % 5 + 5 * y) ((z + 1) % 64)) =
      pO A B laneW l + ∑ y ∈ Finset.range 5, pO A B laneW ((l % 5 + 1) % 5 + 5 * y) +
        ∑ y ∈ Finset.range 5, qO A B laneW ((l % 5 + 4) % 5 + 5 * y) := by
  have h2 : ∑ z ∈ Finset.range 64, ∑ y ∈ Finset.range 5,
      B.getD z 0 * gO A laneW ((l % 5 + 1) % 5 + 5 * y) z =
      ∑ y ∈ Finset.range 5, pO A B laneW ((l % 5 + 1) % 5 + 5 * y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => sumB_gO A B laneW _
  have h3 : ∑ z ∈ Finset.range 64, ∑ y ∈ Finset.range 5,
      B.getD z 0 * gO A laneW ((l % 5 + 4) % 5 + 5 * y) ((z + 1) % 64) =
      ∑ y ∈ Finset.range 5, qO A B laneW ((l % 5 + 4) % 5 + 5 * y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => sumB_gO1 A B laneW _
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h2, h3, sumB_gO]

end Helpers

/-! ## The statements -/

/-- **The adjoint identity** (θ, ρ, π transposed, then the inner product): for any arrays. -/
theorem weightedCF_eq (A B eqL laneW : Array F) :
    weightedCF (corrGF A B) eqL laneW = weightedRefF B eqL (linearTransposeF (outerUGF A laneW)) := by
  rw [weightedC_sum, weightedRef_closed]
  simp only [inner_closed]
  have hL : ∀ l, laneW.getD (keccakPi l) 0 *
      ((eqL.getD l 0 + colS eqL ((l % 5 + 4) % 5)) * corrGF A B (keccakRho.getD l 0) +
        colS eqL ((l % 5 + 1) % 5) * corrGF A B ((keccakRho.getD l 0 + 1) % 64)) =
      eqL.getD l 0 * pO A B laneW l + colS eqL ((l % 5 + 4) % 5) * pO A B laneW l +
        colS eqL ((l % 5 + 1) % 5) * qO A B laneW l := by
    intro l; simp only [pO, qO]; ring
  have r1 : ∑ l ∈ Finset.range 25, colS eqL ((l % 5 + 4) % 5) * pO A B laneW l =
      ∑ l ∈ Finset.range 25, eqL.getD l 0 *
        ∑ y ∈ Finset.range 5, pO A B laneW ((l % 5 + 1) % 5 + 5 * y) :=
    regroup (fun i => eqL.getD i 0) (pO A B laneW) 1 4 (Or.inl ⟨rfl, rfl⟩)
  have r2 : ∑ l ∈ Finset.range 25, colS eqL ((l % 5 + 1) % 5) * qO A B laneW l =
      ∑ l ∈ Finset.range 25, eqL.getD l 0 *
        ∑ y ∈ Finset.range 5, qO A B laneW ((l % 5 + 4) % 5 + 5 * y) :=
    regroup (fun i => eqL.getD i 0) (qO A B laneW) 4 1 (Or.inr ⟨rfl, rfl⟩)
  rw [Finset.sum_congr rfl fun l _ => hL l]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [r1, r2]

/-- **Lane 0 of the transpose**, summed over a round constant's bits: for any arrays. -/
theorem rcOuterF_eq (A laneW : Array F) (rc : UInt64) :
    rcOuterF A laneW rc = rcRefF (linearTransposeF (outerUGF A laneW)) rc := by
  have hR : rcRefF (linearTransposeF (outerUGF A laneW)) rc =
      ∑ z ∈ (Finset.range 64).filter (fun z => rc.toNat.testBit z = true),
        (gO A laneW 0 z + ∑ y ∈ Finset.range 5, gO A laneW (1 + 5 * y) z +
          ∑ y ∈ Finset.range 5, gO A laneW (4 + 5 * y) ((z + 1) % 64)) := by
    simp only [rcRefF, filterMap_ite, sumE_eq_sum, sum_filter_range]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z < 64 := by simp only [Finset.mem_filter, Finset.mem_range] at hz; exact hz.1
    have := klt_outer A laneW (l := 0) (by (clear * -; omega)) hz'
    simp only [mul_zero, zero_add, Nat.zero_mod] at this
    exact this
  simp only [rcOuterF, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, foldl_add2_sum, pure_bind, sumE_eq_sum, sum_filter_range, rhoA_getD]
  show (_ : F) + ((List.range' 0 5).map _).sum = _
  rw [← List.range_eq_range', list_sum_range, hR]
  set F := (Finset.range 64).filter (fun z => rc.toNat.testBit z = true)
  have t1 : ∑ z ∈ F, gO A laneW 0 z =
      laneW.getD (keccakPi 0) 0 * ∑ z ∈ F, A.getD ((z + 0 + keccakRho.getD 0 0) % 64) 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [gO, add_zero]; ring
  have t2 : ∑ z ∈ F, ∑ y ∈ Finset.range 5, gO A laneW (1 + 5 * y) z =
      ∑ y ∈ Finset.range 5, laneW.getD (keccakPi (1 + 5 * y)) 0 *
        ∑ z ∈ F, A.getD ((z + 0 + keccakRho.getD (1 + 5 * y) 0) % 64) 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [gO, add_zero]; ring
  have t3 : ∑ z ∈ F, ∑ y ∈ Finset.range 5, gO A laneW (4 + 5 * y) ((z + 1) % 64) =
      ∑ y ∈ Finset.range 5, laneW.getD (keccakPi (4 + 5 * y)) 0 *
        ∑ z ∈ F, A.getD ((z + 1 + keccakRho.getD (4 + 5 * y) 0) % 64) 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have : ((z + 1) % 64 + keccakRho.getD (4 + 5 * y) 0) % 64 =
        (z + 1 + keccakRho.getD (4 + 5 * y) 0) % 64 := by (clear * -; omega)
    simp only [gO, this]; ring
  simp only [Finset.sum_add_distrib]
  rw [t1, t2, t3, add_assoc]



/-! ## The correlation automaton -/


/-- Per bit `k`: `(m₀₁, m₁₀, m₀₀ + m₁₁)` with `m_{zo} = eq(q_k, z)·eq(p_k, o)`. -/
def corrTabF (q p : List F) : Array (F × F × F) :=
  ((List.range 6).map fun k =>
    let qk := q.getD k 0
    let pk := p.getD k 0
    ((1 + qk) * pk, qk * (1 + pk), (1 + qk) * (1 + pk) + qk * pk)).toArray

/-- `corr(r)` by the carry of `z + r`, low bit first. State `(v₀, v₁)` = carry `0`, `1`. On a bit of `r` equal to 0:
`(v₀ (m₀₀ + m₁₁) + v₁ m₀₁, v₁ m₁₀)`. On a 1: `(v₀ m₀₁, v₀ m₁₀ + v₁ (m₀₀ + m₁₁))`. The carry out of bit 5 is
dropped (mod 64). -/
def corrAF (t : Array (F × F × F)) (r : Nat) : F := Id.run do
  let mut v0 : F := 1
  let mut v1 : F := 0
  for k in [:6] do
    let (m01, m10, d) := t.getD k (0, 0, 0)
    if (r >>> k) % 2 == 0 then
      (v0, v1) := (v0 * d + v1 * m01, v1 * m10)
    else
      (v0, v1) := (v0 * m01, v0 * m10 + v1 * d)
  return v0 + v1

/-! ## Proof helpers -/

open Finset

private theorem eqKernelA_snoc (l : List F) (x : F) :
    eqKernelAF (l ++ [x]) = (eqKernelAF l).map (· * (1 + x)) ++ (eqKernelAF l).map (· * x) := by
  simp only [eqKernelAF, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem size_eqKernelA' (l : List F) : (eqKernelAF l).size = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [eqKernelA_snoc, Array.size_append, Array.size_map, Array.size_map, ih]
    simp [pow_succ, mul_two]

/-- `eq(x, b)` for a bit `b`. -/
private def eqB (x : F) (b : Nat) : F := if b = 0 then 1 + x else x

private theorem getD_snoc (l : List F) (x : F) {n e o : Nat} (hn : l.length = n) (he : e < 2 ^ n)
    (ho : o < 2) : (eqKernelAF (l ++ [x])).getD (e + 2 ^ n * o) 0 = (eqKernelAF l).getD e 0 * eqB x o := by
  have hs := size_eqKernelA' l
  rw [hn] at hs
  rw [eqKernelA_snoc]
  rcases (by (clear * - ho; omega) : o = 0 ∨ o = 1) with rfl | rfl
  · simp [eqB, Array.getElem?_append_left, hs, he]
  · simp [eqB, hs, he]

/-- The carry-`c` part of the `k`-bit correlation: `z < 2^k` with `⌊(z + ρ) / 2^k⌋ = c`. -/
private def S (qs ps : List F) (ρ c : Nat) : F :=
  ∑ z ∈ range (2 ^ qs.length), if (z + ρ) / 2 ^ qs.length = c then
    (eqKernelAF qs).getD z 0 * (eqKernelAF ps).getD ((z + ρ) % 2 ^ qs.length) 0 else 0

/-- One bit's transfer weight from carry `c` to carry `c'` on a bit `rk` of `r`. -/
private def T (x y : F) (rk c c' : Nat) : F :=
  ∑ b ∈ range 2, if (c + b + rk) / 2 = c' then eqB x b * eqB y ((c + b + rk) % 2) else 0

private theorem idx {N w m : Nat} (hN : 0 < N) :
    (w + N * m) / (2 * N) = (w / N + m) / 2 ∧ (w + N * m) % (2 * N) = w % N + N * ((w / N + m) % 2) := by
  rw [Nat.div_mod_unique (by omega)]
  have h1 := Nat.div_add_mod w N
  have h2 := Nat.div_add_mod (w / N + m) 2
  have h3 := Nat.mod_lt w hN
  have h4 := Nat.mod_lt (w / N + m) (by (clear * -; omega) : 0 < 2)
  constructor
  · calc w % N + N * ((w / N + m) % 2) + 2 * N * ((w / N + m) / 2)
        = w % N + N * (2 * ((w / N + m) / 2) + (w / N + m) % 2) := by ring
      _ = w + N * m := by rw [h2, mul_add]; (clear * - h1; omega)
  · have : N * ((w / N + m) % 2) ≤ N * 1 := Nat.mul_le_mul_left _ (by (clear * -; omega))
    (clear * - h3 this; omega)

private theorem S_step (qs ps : List F) (x y : F) {n : Nat} (hq : qs.length = n) (hp : ps.length = n)
    {ρ rk : Nat} (hρ : ρ < 2 ^ n) (hrk : rk < 2) (c' : Nat) :
    S (qs ++ [x]) (ps ++ [y]) (ρ + 2 ^ n * rk) c' =
      S qs ps ρ 0 * T x y rk 0 c' + S qs ps ρ 1 * T x y rk 1 c' := by
  have hl : (qs ++ [x]).length = n + 1 := by simp [hq]
  unfold S
  rw [hl, hq, pow_succ, mul_two, Finset.sum_range_add, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz := mem_range.mp hz
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have key : ∀ b, b < 2 → (if (z + 2 ^ n * b + (ρ + 2 ^ n * rk)) / (2 ^ n + 2 ^ n) = c' then
      (eqKernelAF (qs ++ [x])).getD (z + 2 ^ n * b) 0 *
        (eqKernelAF (ps ++ [y])).getD ((z + 2 ^ n * b + (ρ + 2 ^ n * rk)) % (2 ^ n + 2 ^ n)) 0 else 0) =
      if ((z + ρ) / 2 ^ n + (b + rk)) / 2 = c' then
        (eqKernelAF qs).getD z 0 * eqB x b *
          ((eqKernelAF ps).getD ((z + ρ) % 2 ^ n) 0 * eqB y (((z + ρ) / 2 ^ n + (b + rk)) % 2)) else 0 := by
    intro b hb
    have he : z + 2 ^ n * b + (ρ + 2 ^ n * rk) = (z + ρ) + 2 ^ n * (b + rk) := by ring
    obtain ⟨i1, i2⟩ := idx (w := z + ρ) (m := b + rk) hN
    rw [he, ← two_mul, i1, i2, getD_snoc qs x hq hz hb,
      getD_snoc ps y hp (Nat.mod_lt _ hN) (Nat.mod_lt _ (by (clear * -; omega)))]
  have k0 := key 0 (by (clear * -; omega))
  have k1 := key 1 (by (clear * -; omega))
  simp only [mul_zero, add_zero] at k0
  rw [show 2 ^ n + z = z + 2 ^ n * 1 by ring, k0, k1]
  have hc : (z + ρ) / 2 ^ n < 2 := by
    rw [Nat.div_lt_iff_lt_mul hN]; (clear * - hρ hz; omega)
  generalize (z + ρ) / 2 ^ n = c at *
  generalize (eqKernelAF qs).getD z 0 = B
  generalize (eqKernelAF ps).getD ((z + ρ) % 2 ^ n) 0 = A
  unfold T
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  clear key k0 k1
  rcases (by (clear * - hc; omega) : c = 0 ∨ c = 1) with rfl | rfl <;> rcases (by (clear * - hrk; omega) : rk = 0 ∨ rk = 1) with rfl | rfl <;>
    rcases c' with _ | _ | c' <;> simp [eqB] <;> ring

/-- One step of `corrAF`'s loop. -/
private def stepA (t : Array (F × F × F)) (r : Nat) (v : F × F) (k : Nat) : F × F :=
  let (m01, m10, d) := t.getD k (0, 0, 0)
  if (r >>> k) % 2 == 0 then (v.1 * d + v.2 * m01, v.2 * m10) else (v.1 * m01, v.1 * m10 + v.2 * d)

private theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private theorem corrA_foldl (t : Array (F × F × F)) (r : Nat) :
    corrAF t r = ((List.range 6).foldl (stepA t r) (1, 0)).1 + ((List.range 6).foldl (stepA t r) (1, 0)).2 := by
  simp only [corrAF, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield, List.forIn_pure_yield_eq_foldl]
  rfl

private theorem corrTab_getD (q p : List F) {k : Nat} (hk : k < 6) :
    (corrTabF q p).getD k (0, 0, 0) = ((1 + q.getD k 0) * p.getD k 0, q.getD k 0 * (1 + p.getD k 0),
      (1 + q.getD k 0) * (1 + p.getD k 0) + q.getD k 0 * p.getD k 0) := by
  simp [corrTabF, hk]

private theorem take_succ' (l : List F) {k : Nat} (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l.getD k 0] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

private theorem inv (q p : List F) (hq : q.length = 6) (hp : p.length = 6) (r : Nat) :
    ∀ k, k ≤ 6 → (List.range k).foldl (stepA (corrTabF q p) r) (1, 0) =
      (S (q.take k) (p.take k) (r % 2 ^ k) 0, S (q.take k) (p.take k) (r % 2 ^ k) 1)
  | 0, _ => by simp [S, eqKernelAF, Nat.mod_one]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, inv q p hq hp r k (by (clear * - hk; omega))]
    simp only [List.foldl_cons, List.foldl_nil]
    have hlq : (q.take k).length = k := by simp [hq]; (clear * - hk; omega)
    have hlp : (p.take k).length = k := by simp [hp]; (clear * - hk hlq; omega)
    have hρ : r % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hrk : r / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by (clear * -; omega))
    rw [take_succ' q (by (clear * - hq hk hlq hlp; omega)), take_succ' p (by (clear * - hp hk hlq hlp; omega)), Nat.mod_pow_succ,
      S_step _ _ _ _ hlq hlp hρ hrk, S_step _ _ _ _ hlq hlp hρ hrk]
    unfold stepA
    rw [corrTab_getD q p (by (clear * - hk hlq hlp; omega)), Nat.shiftRight_eq_div_pow]
    generalize r / 2 ^ k % 2 = rk at *
    generalize S (q.take k) (p.take k) (r % 2 ^ k) 0 = v0
    generalize S (q.take k) (p.take k) (r % 2 ^ k) 1 = v1
    generalize q.getD k 0 = x
    generalize p.getD k 0 = y
    unfold T
    rcases (by (clear * - hrk; omega) : rk = 0 ∨ rk = 1) with rfl | rfl <;>
      simp [Finset.sum_range_succ, eqB]

private theorem sumE_sum (l : List F) : sumF l = l.sum := by
  suffices h : ∀ a : F, l.foldl (· + ·) a = a + l.sum by rw [sumF, h, zero_add]
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-! ## The statement -/

/-- **The correlation automaton** on two six-coordinate equality kernels. -/
theorem corrAF_eq (q p : List F) (hq : q.length = 6) (hp : p.length = 6) (r : Nat) :
    corrAF (corrTabF q p) r = corrGF (eqKernelAF p) (eqKernelAF q) r := by
  rw [corrA_foldl, inv q p hq hp r 6 le_rfl, List.take_of_length_le (by (clear * - hq; omega)),
    List.take_of_length_le (by (clear * - hp; omega))]
  simp only
  unfold S corrGF
  rw [hq, show (2 : Nat) ^ 6 = 64 from rfl, ← Finset.sum_add_distrib, sumE_sum, list_sum_range]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz := mem_range.mp hz
  have hm : (z + r % 64) % 64 = (z + r) % 64 := by (clear * -; omega)
  have hc : (z + r % 64) / 64 < 2 := by (clear * - hz hm; omega)
  rw [hm]
  rcases (by (clear * - hz hm hc; omega) : (z + r % 64) / 64 = 0 ∨ (z + r % 64) / 64 = 1) with h | h <;> simp [h]


end

end Lvm.E2V
