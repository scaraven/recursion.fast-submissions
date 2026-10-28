-- New for `flock-recursive` (BLUEPRINT A.6, A.8, §10 changes 21; stage S-E9, track L-circ).
import FRNodeTarget

/-!
# The `WM` mirror map: one function for the mux, the link families and the dump

BLUEPRINT A.6 (revision 3.14) pins the mirror map: source `g` of slot `σ` is block
`wmB σ + ⌊g/4⌋`, positions `256 (g mod 4) + [0, 256)`, with `g = off_f + t`. `FRNodeLayout` holds it
(`Layout.mirBlock`, `Layout.mirPos`, `Layout.mirOff`); S-C's link families (`FRNodeTarget`:
`NodeT.wmB`, `NodeT.mirB`, `NodeT.mpos`, `NodeT.fam`, as INT-3 corrected them) read the same map.
This module proves that they agree, so the mux's mirror writes, `linkWAll` and the dump use one map.
-/

namespace FR
namespace NodeT

/-- **`wmB` is the layout's.** -/
theorem wmB_eq (σ : ℕ) : wmB σ = Layout.wmB σ := rfl

/-- **Each family's mirror source is `off_f + t`** (A.6), `j`'s the single source 399. -/
theorem fam_mir (f t : ℕ) (hf : f < 8) :
    (fam f).mir t = if f = 1 then Layout.mirOff 1 else Layout.mirOff f + t := by
  interval_cases f <;> simp [fam, Layout.mirOff, add_comm]

/-- The families' source counts: `mirN` counts mirror sources (`j`: one). -/
theorem fam_n (f : ℕ) (hf : f < 8) : f ≠ 1 → (fam f).n = Layout.mirN f := by
  interval_cases f <;> simp [fam, Layout.mirN]

/-- **`mirB` is `mirBlock`** at the family's source. -/
theorem mirB_eq (σ f t : ℕ) : mirB σ f t = Layout.mirBlock σ ((fam f).mir t) := rfl

/-- **`mpos` is `mirPos`** at the family's first mirror bit `mbo` (`end41hi`: 184). -/
theorem mpos_eq (f t s : ℕ) : mpos f t s = Layout.mirPos ((fam f).mir t) ((fam f).mbo + s) := by
  simp only [mpos, Layout.mirPos, Nat.add_assoc]

/-- Every family's mirror bit lies in the pinned `WM` blocks at a position `< 1024`. -/
theorem mir_in_wm {σ f t s : ℕ} (hσ : σ < 2) (hf : f < 8) (ht : t < (fam f).n) (hs : s < fbits f) :
    Layout.wmBase ≤ mirB σ f t ∧ mirB σ f t < Layout.hEnd ∧ mpos f t s < 1024 := by
  have hg : (fam f).mir t < Layout.mirSources := by
    interval_cases f <;> simp only [fam, id] at ht ⊢ <;> simp only [Layout.mirSources] <;> omega
  have hb : (fam f).mbo + s < 256 := by
    interval_cases f <;> simp only [fam, fbits] at hs ⊢ <;> omega
  obtain ⟨h1, -, h3, -⟩ := Layout.mir_fits hσ hg
  rw [mirB_eq]
  exact ⟨by simpa [Layout.wmBase] using h1, h3, by rw [mpos_eq]; exact Layout.mirPos_lt hb⟩

end NodeT
end FR
