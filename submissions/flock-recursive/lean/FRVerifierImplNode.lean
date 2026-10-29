-- New for `flock-recursive` (BLUEPRINT revision 3.13: A.8 `targetS` and `linkW` node forms; stage-review
-- changes 20, gap 3; track S-CN, the S-F2 part).
-- RET-3: the declarations revision 4 reads moved to `FRNodeTargetCore`.
import FRNodeTarget
import FRNodeTargetCore

/-!
# The node's `targetS` and `linkW`, computed (`targetSNodeI`, `linkWI`) and `_meets`

The computable forms of `FRNodeTarget`'s specifications on the fast field `F`.

* **Two-level tables.** `eq(r_blk, x) = A[x mod 256] · B[⌊x/256⌋]` (`eqAtR_split`), `A`, `B` the
  `eq` tables of the low and high 8 block coordinates (2 × 255 products). With prefix arrays
  (`pfx`, additions only) a sum of a separable weight `R(⌊x/256⌋) · C(x mod 256)` over a block
  range costs four products (`twoF_eq`, `sepSum_eq`): every range sum of `eq(r_blk, ·)`
  (`rangeI`), and the stream counters (`ctrI`): bit `j < 8` of the counter is a mask on the
  columns, bit `j ≥ 8` a mask on the rows split by the column carry.
* **`targetSNodeI`**: the class weights, counters and the `w43` table sums, the closed form `Gc`
  at the 1,153 pinned positions (`gArr`), then `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`.
  **`targetSNode_meets`**: it is `targetSNodeS`.
* **`linkWI`**: A.8's sum per family with the two-level tables of `τ` and `r_blk` and the slot
  weights of `θ`, `r_pos` (`slotI`); **`linkW_meets`**: it is `linkWS`.
-/

namespace FR
namespace NodeI
open Finset NodeT Impl

/-! ## Two-level `eq` tables and separable range sums -/

/-! ## The block point's tables -/

section TabsLemmas
variable (rb : Fin 16 → F)

end TabsLemmas

/-! ## The stream counters -/

/-! ## `targetSNodeI` -/

section Meets
variable (rb : Fin 16 → F)

theorem hσ_bounds {σ : ℕ} (hσ : σ < 2) :
    σ * Layout.chainN + 1 + (Layout.chainN - 2) ≤ 2 ^ 16 ∧ wb σ + 400 + 65 ≤ 2 ^ 16 ∧
      wb σ + 399 ≤ 2 ^ 16 := by
  have hN : Layout.chainN = 23146 := rfl
  have hw : wb σ = 46298 + 498 * σ := rfl
  rw [hN, hw]
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> norm_num

private theorem sum_ite_c2 (c : Prop) [Decidable c] (g : ℕ → F) :
    ∑ σ ∈ range 2, (if c then g σ else 0) = if c then ∑ σ ∈ range 2, g σ else 0 := by
  split_ifs <;> simp

end Meets

/-! ## `linkWI` -/

/-- **`linkW` of a node** (A.8, revision 3.13), family `f`, computed. -/
def linkWI (f : ℕ) (τ θ rb rp : Array F) : F :=
  let T := linkTabs τ θ rb rp
  linkWOne T.1 T.2.1 T.2.2.1 T.2.2.2 f

/-- **`linkW`'s specification on arrays** (`linkWS` at the points the arrays read). -/
def linkWSA (f : ℕ) (τ θ rb rp : Array F) : F :=
  linkWS f (ptA 16 τ) (ptA 10 θ) (ptA 16 rb) (ptA 10 rp)

section LinkMeets

/-- **`linkW` meets its specification**, every family. -/
theorem linkW_meets (f : ℕ) (τ θ rb rp : Array F) : linkWI f τ θ rb rp = linkWSA f τ θ rb rp := by
  dsimp only [linkWI, linkTabs]
  exact linkWOne_eq f _ _ _ _

/-- The shared form meets it too (`f < 8`). -/
theorem linkWAll_meets {f : ℕ} (hf : f < nLinkFam) (τ θ rb rp : Array F) :
    (linkWAllI τ θ rb rp).getD f 0 = linkWSA f τ θ rb rp := by
  dsimp only [linkWAllI, linkTabs]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hf, Option.getD_some]
  exact linkWOne_eq f _ _ _ _

end LinkMeets

/-! ## `shiftMask` (revision 3.14: the node's chain-masked shift weights) -/

section MaskMeets

/-- `ptA 16` of a point padded by zeros is the point's (revision 3.15). -/
theorem ptA16_pad (xs : List F) (k : ℕ) (h : xs.length = 16) :
    ptA 16 (xs ++ List.replicate k 0).toArray = ptA 16 xs.toArray := by
  funext l
  simp [ptA, Array.getD_eq_getD_getElem?, List.getElem?_append_left (show l.val < xs.length by omega)]

/-- **`shiftMask`'s specification on 18-coordinate zero-padded block points** (revision 3.15,
ruling (c)): it reads the first 16 coordinates, so it is the 16-coordinate one. -/
theorem shiftMaskS_pad (xs ys : List F) (k : ℕ) (hx : xs.length = 16) (hy : ys.length = 16) :
    shiftMaskS (xs ++ List.replicate k 0).toArray (ys ++ List.replicate k 0).toArray =
      shiftMaskS xs.toArray ys.toArray := by
  simp only [shiftMaskS, ptA16_pad xs k hx, ptA16_pad ys k hy]

end MaskMeets

/-! ## Controls -/

section Controls

/-- (+) `linkWI`, family `x`: its first source's field bit 0 reads `1`. -/
theorem linkWI_hit : linkWI 0 (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 0))
    (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 600)) = 1 := by
  rw [linkW_meets, linkWSA]
  simp only [ptA_ofFn]
  exact linkW_hit

/-- (−) … one position off reads `0`; the mirror cell reads `−1`. -/
theorem linkWI_off_mir : linkWI 0 (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 0))
      (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 601)) = 0 ∧
    linkWI 0 (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 0))
      (Array.ofFn (cubeN 16 (mirB 0 0 0))) (Array.ofFn (cubeN 10 (mpos 0 0 0))) = -1 := by
  refine ⟨?_, ?_⟩ <;> rw [linkW_meets, linkWSA] <;> simp only [ptA_ofFn]
  · exact linkW_off
  · exact linkW_mir

/-- (−) At a `free` block point (`WM` and beyond) the node's `targetS` is zero. -/
theorem targetSNodeI_free (r : Array F) {b : ℕ} (hr : rbOf r = cubeN 16 b)
    (h1 : Layout.wmBase ≤ b) (h2 : b < 2 ^ 16) :
    targetSNodeI r = Array.ofFn (n := 64) fun _ => 0 := by
  rw [targetSNode_meets, targetSNode_blk, hr]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_eq_zero fun hi _ => ?_)
  rw [blkW_cube h2, nodeE_free h1, mul_zero]

/-- (+) At a Boolean block point `b` the node's `targetS` reads block `b`'s target. -/
theorem targetSNodeI_blk (r : Array F) {b : ℕ} (hr : rbOf r = cubeN 16 b) (h2 : b < 2 ^ 16) :
    targetSNodeI r = Array.ofFn (n := 64) fun σ =>
      ∑ hi ∈ range 256, eqAtR (zLo r) hi * nodeE b (σ + 64 * hi) := by
  rw [targetSNode_meets, targetSNode_blk, hr]
  exact congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_congr rfl fun hi _ => by
    rw [blkW_cube h2])

end Controls

end NodeI
end FR
