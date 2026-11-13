-- New for lvm2 (roll 10, R10 V-slice): the adjoint identity behind `LvmKeccakSym` (θ, ρ, π transposed against
-- an outer product).
import LvmDecideTape
import LvmFieldCorrect

/-!
# The Keccak layer's weights against an outer product

`keccakLinearTranspose (outerUG A ℓ)` is the next layer's weight vector. `weightedC_eq` and `rcOuter_eq` read it
without building it. They are identities in any commutative ring; FE's is `LvmFieldCorrect.instCommRing`.
-/

set_option autoImplicit false

namespace Lvm

/-- The outer product `u_j = A_{j mod 64}·ℓ_{j / 64}` over the 1600 bits (`verifyKeccakLayerG`'s `weights` line with
`A = eqKernelA p`). -/
def outerUG (A laneW : Array FE) : List FE :=
  (List.range keccakBits).map fun j => A.getD (j % 64) 0 * laneW.getD (j / 64) 0

/-! ## The reference expressions (verbatim from `verifyKeccakLayerG`) -/

/-- `weighted` of `verifyKeccakLayerG`: `Σ_{l<25} eqL_l·Σ_{z<64} eqZ_z·w_{64l+z}`. -/
def weightedRef (eqZ eqL : Array FE) (w : List FE) : FE :=
  let w := w.toArray
  sumE ((List.range 25).map fun l => eqL.getD l 0 *
    sumE ((List.range 64).map fun z => eqZ.getD z 0 * w.getD (64 * l + z) 0))

/-- One segment's round-constant sum of `iota`: `Σ_{z < 64, bit z of rc} w_z`. -/
def rcRef (w : List FE) (rc : UInt64) : FE :=
  sumE ((List.range 64).filterMap fun z => if rc.toNat.testBit z then some (w.getD z 0) else none)

/-! ## The symbolic forms -/

/-- `KECCAK_RHO` as an array. -/
def rhoA : Array Nat := keccakRho.toArray

/-- The reference correlation `corr(r) = Σ_{z<64} B_z·A_{(z + r) mod 64}`. -/
def corrG (A B : Array FE) (r : Nat) : FE :=
  sumE ((List.range 64).map fun z => B.getD z 0 * A.getD ((z + r) % 64) 0)

/-- `⟨eqL ⊗ B, T(A ⊗ ℓ)⟩` from the correlations (`corr r = corrG A B r`): with `x = l mod 5` and
`S_c = Σ_y eqL_{c + 5y}`, `Σ_l ℓ_{π l}·((eqL_l + S_{x−1})·corr(ρ_l) + S_{x+1}·corr(ρ_l + 1))`. -/
def weightedC (corr : Nat → FE) (eqL laneW : Array FE) : FE := Id.run do
  let S : Array FE := (Array.range 5).map fun c =>
    eqL.getD c 0 + eqL.getD (c + 5) 0 + eqL.getD (c + 10) 0 + eqL.getD (c + 15) 0 + eqL.getD (c + 20) 0
  let mut acc : FE := 0
  for l in [:25] do
    let x := l % 5
    let rl := rhoA.getD l 0
    acc := acc + laneW.getD (keccakPi l) 0 *
      ((eqL.getD l 0 + S.getD ((x + 4) % 5) 0) * corr rl + S.getD ((x + 1) % 5) 0 * corr ((rl + 1) % 64))
  return acc

/-- One segment's round-constant sum on `T(A ⊗ ℓ)`: lane 0 of the transpose is
`g_{0,z} + C_{1,z} + C_{4,z+1}`, `g_{l,z} = A_{(z + ρ_l) mod 64}·ℓ_{π l}`, `C_{c,z} = Σ_y g_{c+5y,z}`. -/
def rcOuter (A laneW : Array FE) (rc : UInt64) : FE := Id.run do
  let zs := (List.range 64).filter fun z => rc.toNat.testBit z
  let sh (l off : Nat) : FE := sumE (zs.map fun z => A.getD ((z + off + rhoA.getD l 0) % 64) 0)
  let mut acc : FE := laneW.getD (keccakPi 0) 0 * sh 0 0
  for y in [:5] do
    acc := acc + laneW.getD (keccakPi (1 + 5 * y)) 0 * sh (1 + 5 * y) 0 +
      laneW.getD (keccakPi (4 + 5 * y)) 0 * sh (4 + 5 * y) 1
  return acc

/-! ## Proof helpers: the loops and the transpose in closed form

Adapted from leanVM `LvmKeccakLinear` (`outer_loop`, `inner_loop`, `flatMap_getD`, `columns_getD`),
restated on `Lvm.FE`. -/

section Helpers

open Finset

private theorem sumE_eq_sum (l : List FE) : sumE l = l.sum := by
  unfold sumE
  suffices h : ∀ a : FE, l.foldl (· + ·) a = a + l.sum by simpa using h 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

private theorem list_sum_range (f : ℕ → FE) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ Finset.range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem sumE_range (f : ℕ → FE) (n : ℕ) :
    sumE ((List.range n).map f) = ∑ y ∈ Finset.range n, f y := by
  rw [sumE_eq_sum, list_sum_range]

private theorem foldl_add_sum (g : ℕ → FE) : ∀ (l : List ℕ) (a : FE),
    l.foldl (fun acc k => acc + g k) a = a + (l.map g).sum
  | [], a => by simp
  | k :: l, a => by rw [List.foldl_cons, foldl_add_sum g l]; simp [add_assoc]

private theorem foldl_add2_sum (g h : ℕ → FE) (l : List ℕ) (a : FE) :
    l.foldl (fun acc k => acc + g k + h k) a = a + (l.map fun k => g k + h k).sum := by
  rw [← foldl_add_sum]; simp only [add_assoc]

private theorem sum_filter_range (p : ℕ → Bool) (f : ℕ → FE) (n : ℕ) :
    (((List.range n).filter p).map f).sum =
      ∑ z ∈ (Finset.range n).filter (fun z => p z = true), f z := by
  rw [Finset.sum_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases h : p n = true <;> simp [h]

private theorem filterMap_ite (p : ℕ → Bool) (f : ℕ → FE) (l : List ℕ) :
    l.filterMap (fun z => if p z then some (f z) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a = true <;> simp [h, ih]

private theorem array_getD_toArray (l : List FE) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem rhoA_getD (l : ℕ) : rhoA.getD l 0 = keccakRho.getD l 0 := by
  simp [rhoA, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem setIfInBounds_getD (a : Array FE) (i p : ℕ) (x : FE) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

private theorem flatMap_getD (F : ℕ → ℕ → FE) (m : ℕ) :
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
    · have : x = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

/-- θ's input weights after ρπ (`gOf` of `LvmKeccakLinear`). -/
private def gW (w : List FE) (p : ℕ) : FE :=
  w.getD (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) 0

/-- A column sum of `gW`. -/
private def colW (w : List FE) (x z : ℕ) : FE := ∑ y ∈ Finset.range 5, gW w (64 * (x + 5 * y) + z)

private theorem inner_loop (W : ℕ → FE) (lane : ℕ) (g : Array FE) :
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
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

private theorem outer_loop (w : List FE) :
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
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray, gW]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

private theorem columns_getD (A : Array FE) (w : List FE) (hA : ∀ p < 1600, A.getD p 0 = gW w p)
    {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colW w x z := by
  rw [array_getD_toArray, flatMap_getD (fun x z ↦
    sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_range]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  simp only [Finset.mem_range] at hy
  exact hA _ (by omega)

/-- **`keccakLinearTranspose` in closed form.** -/
private theorem klt_getD (w : List FE) {p : ℕ} (hp : p < 1600) :
    (keccakLinearTranspose w).getD p 0 =
      gW w p + colW w ((p / 64 % 5 + 1) % 5) (p % 64) + colW w ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) := by
  obtain ⟨-, hg⟩ := outer_loop w 25 le_rfl
  have hA : ∀ q < 1600, _ := fun q hq ↦ (hg q).trans (ite_eq_left (by omega : q < 64 * 25))
  unfold keccakLinearTranspose
  simp only []
  have hp' : p = 64 * (p / 64) + p % 64 := by omega
  conv_lhs => rw [hp']
  rw [flatMap_getD _ 64 25 (p / 64) (p % 64) (by omega) (Nat.mod_lt _ (by omega))]
  rw [columns_getD _ w hA (by omega) (Nat.mod_lt _ (by omega)),
    columns_getD _ w hA (by omega) (Nat.mod_lt _ (by omega)), ← hp', hA p hp]

private theorem keccakPi_lt {l : ℕ} (hl : l < 25) : keccakPi l < 25 := by
  unfold keccakPi; omega

private theorem outerUG_getD (A laneW : Array FE) {j : ℕ} (hj : j < 1600) :
    (outerUG A laneW).getD j 0 = A.getD (j % 64) 0 * laneW.getD (j / 64) 0 := by
  simp [outerUG, List.getD_eq_getElem?_getD, keccakBits, hj]

/-- `gW` of the outer product: `g_{l,z} = A_{(z + ρ_l) mod 64}·ℓ_{π l}`. -/
private theorem gW_outer (A laneW : Array FE) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    gW (outerUG A laneW) (64 * l + z) =
      A.getD ((z + keccakRho.getD l 0) % 64) 0 * laneW.getD (keccakPi l) 0 := by
  have e1 : (64 * l + z) / 64 = l := by omega
  have e2 : (64 * l + z) % 64 = z := by omega
  have hπ := keccakPi_lt hl
  rw [gW, e1, e2, outerUG_getD _ _ (by omega)]
  congr 2 <;> omega

/-- `S_c = Σ_y eqL_{c + 5y}`. -/
private def colS (eqL : Array FE) (c : ℕ) : FE := ∑ y ∈ Finset.range 5, eqL.getD (c + 5 * y) 0

private theorem weightedC_sum (corr : ℕ → FE) (eqL laneW : Array FE) :
    weightedC corr eqL laneW = ∑ l ∈ Finset.range 25, laneW.getD (keccakPi l) 0 *
      ((eqL.getD l 0 + colS eqL ((l % 5 + 4) % 5)) * corr (keccakRho.getD l 0) +
        colS eqL ((l % 5 + 1) % 5) * corr ((keccakRho.getD l 0 + 1) % 64)) := by
  simp only [weightedC, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, foldl_add_sum, pure_bind, zero_add]
  have hS : ∀ c < 5, ((Array.range 5).map fun c => eqL.getD c 0 + eqL.getD (c + 5) 0 + eqL.getD (c + 10) 0 +
      eqL.getD (c + 15) 0 + eqL.getD (c + 20) 0).getD c 0 = colS eqL c := by
    intro c hc
    simp [Array.getD_eq_getD_getElem?, hc, colS, Finset.sum_range_succ]
  show ((List.range' 0 25).map _).sum = _
  rw [← List.range_eq_range', list_sum_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hS _ (by omega), hS _ (by omega), rhoA_getD]

/-- `Σ_l S_{(x+k') mod 5}·f_l = Σ_l e_l·Σ_y f_{(x+k) mod 5 + 5y}` for `{k, k'} = {1, 4}`. -/
private theorem regroup (e f : ℕ → FE) (k k' : ℕ) (hk : (k = 1 ∧ k' = 4) ∨ (k = 4 ∧ k' = 1)) :
    ∑ l ∈ Finset.range 25, (∑ y ∈ Finset.range 5, e ((l % 5 + k') % 5 + 5 * y)) * f l =
      ∑ l ∈ Finset.range 25, e l * ∑ y ∈ Finset.range 5, f ((l % 5 + k) % 5 + 5 * y) := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceMod, zero_add]
    ring

/-- `g_{l,z}` of the outer product. -/
private def gO (A laneW : Array FE) (l z : ℕ) : FE :=
  A.getD ((z + keccakRho.getD l 0) % 64) 0 * laneW.getD (keccakPi l) 0

private theorem colW_outer (A laneW : Array FE) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    colW (outerUG A laneW) x z = ∑ y ∈ Finset.range 5, gO A laneW (x + 5 * y) z := by
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [Finset.mem_range] at hy
  exact gW_outer A laneW (by omega) hz

/-- Position `64 l + z` of `T(A ⊗ ℓ)`. -/
private theorem klt_outer (A laneW : Array FE) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    (keccakLinearTranspose (outerUG A laneW)).getD (64 * l + z) 0 =
      gO A laneW l z + ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 1) % 5 + 5 * y) z +
        ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 4) % 5 + 5 * y) ((z + 1) % 64) := by
  have e1 : (64 * l + z) / 64 = l := by omega
  have e2 : (64 * l + z) % 64 = z := by omega
  rw [klt_getD _ (by omega), gW_outer A laneW hl hz, e1, e2,
    colW_outer A laneW (by omega) hz, colW_outer A laneW (by omega) (by omega)]
  rfl

private theorem weightedRef_closed (A B eqL laneW : Array FE) :
    weightedRef B eqL (keccakLinearTranspose (outerUG A laneW)) =
      ∑ l ∈ Finset.range 25, eqL.getD l 0 * ∑ z ∈ Finset.range 64, B.getD z 0 *
        (gO A laneW l z + ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 1) % 5 + 5 * y) z +
          ∑ y ∈ Finset.range 5, gO A laneW ((l % 5 + 4) % 5 + 5 * y) ((z + 1) % 64)) := by
  simp only [weightedRef, sumE_range]
  refine Finset.sum_congr rfl fun l hl => congrArg (eqL.getD l 0 * ·) ?_
  refine Finset.sum_congr rfl fun z hz => congrArg (B.getD z 0 * ·) ?_
  simp only [Finset.mem_range] at hl hz
  rw [array_getD_toArray, klt_outer A laneW hl hz]

/-- `ℓ_{π l}·corr(ρ_l)`. -/
private def pO (A B laneW : Array FE) (l : ℕ) : FE :=
  laneW.getD (keccakPi l) 0 * corrG A B (keccakRho.getD l 0)

/-- `ℓ_{π l}·corr(ρ_l + 1)`. -/
private def qO (A B laneW : Array FE) (l : ℕ) : FE :=
  laneW.getD (keccakPi l) 0 * corrG A B ((keccakRho.getD l 0 + 1) % 64)

private theorem sumB_gO (A B laneW : Array FE) (l : ℕ) :
    ∑ z ∈ Finset.range 64, B.getD z 0 * gO A laneW l z = pO A B laneW l := by
  rw [pO, corrG, sumE_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [gO]; ring

private theorem sumB_gO1 (A B laneW : Array FE) (l : ℕ) :
    ∑ z ∈ Finset.range 64, B.getD z 0 * gO A laneW l ((z + 1) % 64) = qO A B laneW l := by
  rw [qO, corrG, sumE_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have : ((z + 1) % 64 + keccakRho.getD l 0) % 64 = (z + (keccakRho.getD l 0 + 1) % 64) % 64 := by omega
  simp only [gO, this]; ring

private theorem inner_closed (A B laneW : Array FE) (l : ℕ) :
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
theorem weightedC_eq (A B eqL laneW : Array FE) :
    weightedC (corrG A B) eqL laneW = weightedRef B eqL (keccakLinearTranspose (outerUG A laneW)) := by
  rw [weightedC_sum, weightedRef_closed]
  simp only [inner_closed]
  have hL : ∀ l, laneW.getD (keccakPi l) 0 *
      ((eqL.getD l 0 + colS eqL ((l % 5 + 4) % 5)) * corrG A B (keccakRho.getD l 0) +
        colS eqL ((l % 5 + 1) % 5) * corrG A B ((keccakRho.getD l 0 + 1) % 64)) =
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
theorem rcOuter_eq (A laneW : Array FE) (rc : UInt64) :
    rcOuter A laneW rc = rcRef (keccakLinearTranspose (outerUG A laneW)) rc := by
  have hR : rcRef (keccakLinearTranspose (outerUG A laneW)) rc =
      ∑ z ∈ (Finset.range 64).filter (fun z => rc.toNat.testBit z = true),
        (gO A laneW 0 z + ∑ y ∈ Finset.range 5, gO A laneW (1 + 5 * y) z +
          ∑ y ∈ Finset.range 5, gO A laneW (4 + 5 * y) ((z + 1) % 64)) := by
    simp only [rcRef, filterMap_ite, sumE_eq_sum, sum_filter_range]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z < 64 := by simp only [Finset.mem_filter, Finset.mem_range] at hz; exact hz.1
    have := klt_outer A laneW (l := 0) (by omega) hz'
    simp only [mul_zero, zero_add, Nat.zero_mod] at this
    exact this
  simp only [rcOuter, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, foldl_add2_sum, pure_bind, sumE_eq_sum, sum_filter_range, rhoA_getD]
  show (_ : FE) + ((List.range' 0 5).map _).sum = _
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
        (z + 1 + keccakRho.getD (4 + 5 * y) 0) % 64 := by omega
    simp only [gO, this]; ring
  simp only [Finset.sum_add_distrib]
  rw [t1, t2, t3, add_assoc]

end Lvm
