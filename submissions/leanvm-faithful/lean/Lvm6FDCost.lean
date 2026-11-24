-- lvm6 X1 (BLUEPRINT §3 `FD1`): the exact cost of the decoder programs. New.
import Lvm6FDIR

/-!
# The cost of `FD1`

`fd1_cost`: the syntactic cost (`Lvm.X.cost`, an upper bound on the machine steps by season 1's
`steps_le_cost`, here exact on every run because every loop is a constant-count `loopK`) of
`lamIR N ℓ m B` and `laneIR N ℓ m B` is the closed form `lamCost N ℓ m`, `laneCost N ℓ m`.

`fd1_fuel0`: at level 0 (`n = 2^21`, table `N = 22`, `|S| ≤ 2^21`) six rounds of `lamIR` and
130 `K`-lane decodings (62 `E`-lanes and the 6 window lanes, review RV1 §2) cost at most `2^46`
steps (`≈ 2^43.48`), half of the declared fuel's constant `2^47`.

Plumbing for the extractor's `Computes` proof: `wf_lamIR`, `wf_laneIR`, `noLoopT_*`, `outs_*`.
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

/-! ## The closed forms -/

/-- Season 1's inverse NTT cost (`cost_bflyNIR`). -/
def bflyC (N ℓ : ℕ) : ℕ := 14 + ℓ * ((67 + 20 * N) * 2 ^ (ℓ - 1) + 23)
/-- Season 1's forward NTT cost (`cost_fwdNIR`). -/
def fwdC (N ℓ : ℕ) : ℕ := 14 + ℓ * ((67 + 20 * N) * 2 ^ (ℓ - 1) + 27)
/-- Season 1's basis table cost (`cost_wtabNIR`). -/
def wtabC (N : ℕ) : ℕ := 29 + 13 * N + (N - 1) * (1077 + 45 * N)

/-- One parent of tree level `h`. -/
def parentC (N h : ℕ) : ℕ :=
  49 + 42 * 2 ^ (h + 1) + 31 * 2 ^ (h + 2) + 2 * bflyC N (h + 1) + 2 * fwdC N (h + 2)
/-- Tree level `h`. -/
def levelC (N ℓ h : ℕ) : ℕ := 12 + 2 ^ (ℓ - h - 1) * (parentC N h + 3)
/-- Tree levels `0 … h − 1`. -/
def treeC (N ℓ : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => treeC N ℓ h + levelC N ℓ h + 1
/-- **The cost of `lamIR N ℓ m B`.** -/
def lamCost (N ℓ m : ℕ) : ℕ :=
  wtabC N + (14 + 22 * 2 ^ ℓ) + (12 + 24 * m) + treeC N ℓ ℓ + (14 + 1047 * 2 ^ ℓ) + 4
/-- **The cost of `laneIR N ℓ m B`.** -/
def laneCost (N ℓ m : ℕ) : ℕ :=
  1124 + 54 * 2 ^ ℓ + 59 * m + bflyC N ℓ + fwdC N (ℓ + 1) + bflyC N (ℓ + 1)

/-! ## Proof helpers: the bodies -/

section
variable (t : ℕ)

private theorem c_leafBody : cost leafBody t = 19 := by
  simp [leafBody, cost, blkSteps]
private theorem c_dummyBody (ℓ B : ℕ) : cost (dummyBody ℓ B) t = 21 := by
  simp [dummyBody, cost, blkSteps]
private theorem c_copyBody (c : ℕ) : cost (copyBody c) t = 39 := by
  simp [copyBody, cost, blkSteps]
private theorem c_prodBody : cost prodBody t = 28 := by
  simp [prodBody, cost, blkSteps]
private theorem c_invBody : cost invBody t = 1044 := by
  simp [invBody, cost, blkSteps]
private theorem c_zeroBodyG : cost zeroBodyG t = 6 := by
  simp [zeroBodyG, cost, blkSteps]
private theorem c_synBody (ℓ B : ℕ) : cost (synBody ℓ B) t = 56 := by
  simp [synBody, cost, blkSteps]
private theorem c_corrIR (ℓ B : ℕ) : cost (corrIR ℓ B) t = 1066 := by
  simp [corrIR, cost, blkSteps]
private theorem c_cosBody : cost cosBody t = 33 := by
  simp [cosBody, cost, blkSteps]

private theorem pow_lt64 {a : ℕ} (h : a < 64) : 2 ^ a < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by norm_num) h

private theorem c_level (N ℓ B h : ℕ) (hN : N ≤ 63) (hh : h + 2 ≤ N) (hℓ : ℓ ≤ 63) :
    cost (tLevelIR N ℓ B h) t = levelC N ℓ h := by
  simp only [tLevelIR, parentBody, cost, blkSteps, List.length_cons, List.length_nil,
    c_copyBody, c_prodBody,
    cost_bflyNIR N (h + 1) _ t (by omega) (pow_lt64 (by omega)) (by omega),
    cost_fwdNIR N (h + 2) _ t (by omega) (pow_lt64 (by omega)) (by omega),
    toNat_toWord (pow_lt64 (show h + 1 < 64 by omega)), toNat_toWord (pow_lt64 (show h + 2 < 64 by omega)),
    toNat_toWord (pow_lt64 (show ℓ - h - 1 < 64 by omega)), levelC, parentC, bflyC, fwdC]
  norm_num
  ring

private theorem c_tree (N ℓ B : ℕ) (hN : N ≤ 63) (hℓ : ℓ + 1 ≤ N) :
    ∀ h ≤ ℓ, cost (treeIR N ℓ B h) t = treeC N ℓ h
  | 0, _ => rfl
  | h + 1, hh => by
    simp only [treeIR, cost, treeC, c_tree N ℓ B hN hℓ h (by omega), c_level t N ℓ B h hN (by omega) (by omega)]
end

/-! ## Exact cost -/

/-- **`fd1_cost`**: the exact cost of `lamIR` and of `laneIR`. -/
theorem fd1_cost (N ℓ m B t : ℕ) (hN : ℓ + 1 ≤ N) (hN63 : N ≤ 63) (hm : m < 2 ^ 64) :
    cost (lamIR N ℓ m B) t = lamCost N ℓ m ∧ cost (laneIR N ℓ m B) t = laneCost N ℓ m := by
  have h1 : 2 ^ ℓ < 2 ^ 64 := pow_lt64 (by omega)
  have h2 : 2 ^ (ℓ + 1) < 2 ^ 64 := pow_lt64 (by omega)
  constructor
  · simp only [lamIR, leavesIR, dummiesIR, invsIR, cost, blkSteps, List.length_cons, List.length_nil,
      c_leafBody, c_dummyBody, c_invBody, c_tree t N ℓ B hN63 hN ℓ le_rfl, cost_wtabNIR N _ t (by omega),
      toNat_toWord h1, toNat_toWord hm, lamCost, wtabC]
    norm_num
    ring
  · simp only [laneIR, zeroGIR, synIR, cosIR, cost, blkSteps, List.length_cons, List.length_nil,
      c_zeroBodyG, c_synBody, c_corrIR, c_cosBody,
      cost_bflyNIR N ℓ _ t (by omega) (pow_lt64 (by omega)) (by omega),
      cost_fwdNIR N (ℓ + 1) _ t (by omega) (pow_lt64 (by omega)) (by omega),
      cost_bflyNIR N (ℓ + 1) _ t (by omega) (pow_lt64 (by omega)) (by omega),
      toNat_toWord h1, toNat_toWord h2, toNat_toWord hm, laneCost, bflyC, fwdC]
    norm_num
    ring

/-- **`fd1_fuel0`**: level 0's six trees and 130 lane decodings fit `2^46` steps. -/
theorem fd1_fuel0 (m : ℕ) (hm : m ≤ 2 ^ 21) : 6 * lamCost 22 21 m + 130 * laneCost 22 21 m ≤ 2 ^ 46 := by
  simp only [lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num
  omega

theorem lamCost_mono {N ℓ m m' : ℕ} (h : m ≤ m') : lamCost N ℓ m ≤ lamCost N ℓ m' := by
  simp only [lamCost]; omega

theorem laneCost_mono {N ℓ m m' : ℕ} (h : m ≤ m') : laneCost N ℓ m ≤ laneCost N ℓ m' := by
  simp only [laneCost]; omega

/-! ## Plumbing: well formed, no tape loop, no output -/

theorem noLoopT_parentBody (N ℓ B h : ℕ) : NoLoopT (parentBody N ℓ B h) := by
  simp [parentBody, copyBody, prodBody, mulK, NoLoopT, noLoopT_bflyNIR, noLoopT_fwdNIR]

theorem noLoopT_treeIR (N ℓ B : ℕ) : ∀ h, NoLoopT (treeIR N ℓ B h)
  | 0 => trivial
  | h + 1 => ⟨noLoopT_treeIR N ℓ B h, trivial, noLoopT_parentBody N ℓ B h⟩

theorem noLoopT_lamIR (N ℓ m B : ℕ) : NoLoopT (lamIR N ℓ m B) :=
  ⟨noLoopT_wtabNIR N _, by simp [leavesIR, leafBody, NoLoopT],
    by simp [dummiesIR, dummyBody, NoLoopT], noLoopT_treeIR N ℓ B ℓ,
    by simp [invsIR, invBody, invK, NoLoopT]⟩

theorem noLoopT_laneIR (N ℓ m B : ℕ) : NoLoopT (laneIR N ℓ m B) := by
  simp [laneIR, zeroGIR, zeroBodyG, synIR, synBody, corrIR, cosIR, cosBody, mulK, invK, NoLoopT,
    noLoopT_bflyNIR, noLoopT_fwdNIR]

theorem outs_treeIR (N ℓ B t : ℕ) : ∀ h, outs (treeIR N ℓ B h) t = 0
  | 0 => rfl
  | h + 1 => by
    simp [treeIR, outs, outs_treeIR N ℓ B t h, tLevelIR, parentBody, copyBody, prodBody, mulK,
      outs_bflyNIR, outs_fwdNIR]

theorem outs_lamIR (N ℓ m B t : ℕ) : outs (lamIR N ℓ m B) t = 0 := by
  simp [lamIR, outs, outs_wtabNIR, outs_treeIR, leavesIR, leafBody, dummiesIR, dummyBody, invsIR,
    invBody, invK]

theorem outs_laneIR (N ℓ m B t : ℕ) : outs (laneIR N ℓ m B) t = 0 := by
  simp [laneIR, outs, zeroGIR, zeroBodyG, synIR, synBody, corrIR, cosIR, cosBody, mulK, invK,
    outs_bflyNIR, outs_fwdNIR]

end Lvm6.FD
