-- New for lvm6 (WP CD). `σ_leaf`'s copy rows: `STREAM` holds `σ_leaf` in `readSig`'s order (CD's
-- frozen layout, X2's reader), season 1's leaf walk reads it in `permC` order (`sigAtP`, roll #33).
import Lvm6QDStmt
import Lvm6QSig

/-!
# `σ_leaf`'s copy rows

**`sigLeafCopy6 dst src fg`**: 597 gated equalities, from the stream cells of `σ_leaf` (from `src`,
`readSig`'s order: index, 133 chain values, 16 siblings, 4 words each) to the cells the leaf walk
reads (from `dst`, chain `i` at `dst + 1 + 4·posC i`). **`sigLeafCopy6_spec`**: with the gate on,
`sigAtP M.k dst = sigAt' M.k src`, so `qsig6 I Il sb` with `Il.sg = dst` checks `σ_leaf` as stored.
-/

set_option autoImplicit false

namespace Lvm6.QD

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig

/-- The copies `(walk cell, stream cell)`. -/
def sigPairs6 (dst src : ℕ) : List (ℕ × ℕ) :=
  [(dst, src)] ++ (List.range wotsLen).flatMap (fun i ↦ (List.range 4).map fun l ↦
    (dst + 1 + 4 * posC i + l, src + 1 + 4 * i + l)) ++
    (List.range (4 * sigHeight)).map fun j ↦ (dst + 533 + j, src + 533 + j)

/-- **The copy rows**, gated by the cell `fg`. -/
def sigLeafCopy6 (dst src fg : ℕ) : BM Unit := do
  let _ ← seqAll ((sigPairs6 dst src).map fun pr ↦ assertEq (kc pr.1) (kc pr.2) (kc fg))
  pure ()

section
variable {c : Ctx} {M : Mem}

/-- **The copy rows give the leaf walk's signature**: `σ_leaf` as stored. -/
theorem sigLeafCopy6_spec {dst src fg : ℕ} {p : Ptr} (h : Ok c M (sigLeafCopy6 dst src fg) p)
    (hg : M.k fg = 1) : sigAtP M.k dst = sigAt' M.k src := by
  unfold sigLeafCopy6 at h
  obtain ⟨q1, h1, -⟩ := ok_bind h
  have hp : ∀ pr ∈ sigPairs6 dst src, M.k pr.1 = M.k pr.2 := fun pr hpr ↦ by
    obtain ⟨q, hq⟩ := ok_seqAll _ _ h1 _ (List.mem_map.mpr ⟨pr, hpr, rfl⟩)
    exact assertEqKK_spec hq.1 hq.2 hg
  have h0 : M.k dst = M.k src :=
    hp (dst, src) (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
  have e1 : (List.range wotsLen).map (fun i ↦ digAt M.k (dst + 1 + 4 * posC i)) =
      (List.range wotsLen).map (fun i ↦ digAt M.k (src + 1 + 4 * i)) := by
    refine List.map_congr_left fun i hi ↦ ?_
    unfold digAt
    refine Lvm.QSig.SigH.digOfW_congr fun l hl ↦ ?_
    rw [hp (dst + 1 + 4 * posC i + l, src + 1 + 4 * i + l) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩)))]
  have e2 : (List.range sigHeight).map (fun t ↦ digAt M.k (dst + 533 + 4 * t)) =
      (List.range sigHeight).map (fun t ↦ digAt M.k (src + 533 + 4 * t)) := by
    refine List.map_congr_left fun t ht ↦ ?_
    unfold digAt
    refine Lvm.QSig.SigH.digOfW_congr fun l hl ↦ ?_
    have hj : 4 * t + l < 4 * sigHeight := by have := List.mem_range.mp ht; omega
    have := hp (dst + 533 + (4 * t + l), src + 533 + (4 * t + l))
      (List.mem_append_right _ (List.mem_map.mpr ⟨4 * t + l, List.mem_range.mpr hj, rfl⟩))
    rw [show dst + 533 + 4 * t + l = dst + 533 + (4 * t + l) by ring,
      show src + 533 + 4 * t + l = src + 533 + (4 * t + l) by ring, this]
  unfold sigAtP sigAt'
  rw [h0, e1, e2]

end

end Lvm6.QD
