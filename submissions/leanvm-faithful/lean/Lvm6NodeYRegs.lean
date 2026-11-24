-- New for lvm6 (WP NODE3, STARTUP ST-2). An interval lemma for the word sources: on pairwise disjoint regions,
-- a word inside a listed region has that region's source (`TInst6.src?`), checked once per pair of regions.
import Lvm6TyProg

/-!
# Word sources by region (WP NODE3, STARTUP ST-2)

* **`yDisjB rs`**: every two listed regions are equal or disjoint (`|rs|²` comparisons, no word loop).
* **`src?_of_mem`**: with `yDisjB Ti.lay.yregs`, a word `y` inside a listed region `r` has `Ti.src? y = some r.src`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm.Typed
open Lvm6.Ty (TInst6)

/-- Word `y` lies in region `r`. -/
def yMem (r : YReg) (y : ℕ) : Bool := decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)

/-- Two regions are disjoint. -/
def yDisj (a b : YReg) : Bool := decide (a.base + 2 ^ a.log ≤ b.base ∨ b.base + 2 ^ b.log ≤ a.base)

/-- **Every two listed regions are equal or disjoint.** -/
def yDisjB (rs : List YReg) : Bool := rs.all fun a ↦ rs.all fun b ↦ decide (a = b) || yDisj a b

theorem yDisj_not {a b : YReg} (h : yDisj a b = true) {y : ℕ} (ha : yMem a y = true) (hb : yMem b y = true) :
    False := by
  simp only [yDisj, yMem, decide_eq_true_eq] at h ha hb
  omega

/-- **A word inside a listed region has the region's source**, on pairwise disjoint regions. -/
theorem src?_of_mem {Ti : TInst6} (hd : yDisjB Ti.lay.yregs = true) {r : YReg} (hr : r ∈ Ti.lay.yregs) {y : ℕ}
    (hy : r.base ≤ y ∧ y < r.base + 2 ^ r.log) : Ti.src? y = some r.src := by
  have hp : (fun r : YReg ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)) r = true := decide_eq_true hy
  obtain ⟨r', hr'⟩ : ∃ r', Ti.lay.yregs.find? (fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)) = some r' := by
    cases h : Ti.lay.yregs.find? (fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)) with
    | none => exact absurd (List.find?_eq_none.mp h r hr) (by simp [hp])
    | some r' => exact ⟨r', rfl⟩
  have hm' := List.mem_of_find?_eq_some hr'
  have hp' := List.find?_some hr'
  have he : r' = r := by
    have := List.all_eq_true.mp (List.all_eq_true.mp hd r' hm') r hr
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with e | e
    · exact e
    · exact (yDisj_not e (a := r') (b := r) (y := y) (by simpa [yMem] using hp')
        (by simpa [yMem] using hy)).elim
  unfold TInst6.src?
  rw [hr', he]
  rfl

end Lvm6.Node.Dep
