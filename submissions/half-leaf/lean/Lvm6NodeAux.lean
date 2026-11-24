-- New for lvm6 (WP NODE3, STARTUP ST-3). The layout's auxiliary blocks and constants by construction: `auxOf6`
-- (the PoW blocks, then `boolBlk6`, `outBlk6` per `BITS` class row, at given word bases) and `cstOf6` (the exporter's
-- `specOf`), so that a layout built as `layOfP p (auxOf6 so base) cstOf6` meets the guard's `powAuxIn`,
-- `bitsAuxIn` and `qltCst` facts by lemma.
import Lvm6NodeBits
import Lvm6NodeRun
import Lvm6QltF

/-!
# Auxiliary blocks and constants by construction (WP NODE3, STARTUP ST-3)

* **`bitsSpecsS so`**: the `BITS` classes from `qsig6`'s outputs `so` (the one build's, `famQ6o`); `bitsSpecs6 lay`
  is `bitsSpecsS` at `qsig6`'s outputs at `pS lay ⟨nK, 0⟩` (`bitsSpecs6_eq`), which is `famQ6o`'s `so`.
* **`auxOf6 so base`**, **`cstOf6`**: the exporter's `specOf` blocks (PoW, then the `BITS` rows in `bitsRowsS` order)
  and constants.
* **`powAuxIn_of`**, **`bitsAuxIn_of`**, **`qltCst_of`**: their facts for any layout with `aux = auxOf6 so base` and
  `cst = cstOf6`, in the guard's statement forms.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits Lvm.QSig Lvm.Q2
open Lvm6.Q (qsig6)

/-- The `BITS` classes of `qsig6`'s outputs `so`. -/
def bitsSpecsS (so : SigOut × WalkC) : List BSpec :=
  (SigBits.sigSpecs sigI so.1 (fun _ ↦ noPl) ++ sigSpecsC sigIl sigIl.ys so.2.pa (fun _ ↦ noPl)) ++ posSpecs6

theorem bitsSpecs6_eq (lay : Lay) : bitsSpecs6 lay = bitsSpecsS (qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)).1 := rfl

/-- The `BITS` rows `(S, x)` in order. -/
def bitsRowsS (so : SigOut × WalkC) : List (BSpec × ℕ) :=
  (bitsSpecsS so).flatMap fun S ↦ (List.range S.n).map fun x ↦ (S, x)

/-- **The auxiliary blocks** at word bases `base`: the PoW blocks, then the `BITS` rows (the exporter's `specOf`). -/
def auxOf6 (so : SigOut × WalkC) (base : ℕ → ℕ) : List ABlk :=
  ((List.range powAns.length).map fun k ↦ powBlk (powAns.getD k (0, 0)).2 (base k) (powAns.getD k (0, 0)).1) ++
    ((bitsRowsS so).zipIdx).flatMap fun (r, i) ↦
      [boolBlk6 r.1 (base (powAns.length + 2 * i)) r.2, outBlk6 r.1 (base (powAns.length + 2 * i)) r.2]

/-- **The constants** (`QLT` and the zero word; SU2: the table by `qltData6F`, `cstOf6_eq`). -/
def cstOf6 : List (ℕ × List FK) := [(zC, [0]), (qtC, Lvm6.Q.qltData6F P6 lay6)]

theorem cstOf6_eq : cstOf6 = [(zC, [0]), (qtC, Lvm6.Q.qltData6 P6 lay6)] := by
  rw [cstOf6, Lvm6.Q.qltData6F_eq]

theorem qltCst_of {lay : Lay} (h : lay.cst = cstOf6) :
    lay.cst = [(zC, [0]), (qtC, Lvm6.Q.qltData6 P6 lay6)] := h.trans cstOf6_eq

theorem powAuxIn_of {lay : Lay} {so : SigOut × WalkC} {base : ℕ → ℕ} (h : lay.aux = auxOf6 so base) :
    ∀ a ∈ powAns, ∃ bw, powBlk a.2 bw a.1 ∈ lay.aux := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  refine ⟨base k, ?_⟩
  rw [h]
  refine List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
  rw [List.getD_eq_getElem _ _ hk]

theorem bitsAuxIn_of {lay : Lay} {so : SigOut × WalkC} {base : ℕ → ℕ} (h : lay.aux = auxOf6 so base) :
    ∀ S ∈ bitsSpecsS so, ∀ x < S.n, ∃ w, boolBlk6 S w x ∈ lay.aux ∧ outBlk6 S w x ∈ lay.aux := by
  intro S hS x hx
  have hm : (S, x) ∈ bitsRowsS so :=
    List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩⟩
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hm
  have hz : ((S, x), i) ∈ (bitsRowsS so).zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hi, by simp [hix]⟩
  refine ⟨base (powAns.length + 2 * i), ?_, ?_⟩ <;> rw [h] <;>
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨((S, x), i), hz, ?_⟩) <;> simp

/-- **The guard's three aux/constant facts by construction** (STARTUP ST-3): for a layout whose `aux` is `auxOf6` at
`qsig6`'s outputs at `pS lay ⟨nK, 0⟩` (the one build's, `famQ6o_so`) and whose `cst` is `cstOf6`, the facts
`staticOk6_sound` returns from `powAuxInB`, `qltCstB` and `bitsAuxInB`, in the same statement forms. -/
theorem auxFacts_of_constr {lay : Lay} {base : ℕ → ℕ}
    (ha : lay.aux = auxOf6 (qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)).1 base) (hc : lay.cst = cstOf6) :
    (∀ a ∈ powAns, ∃ bw, powBlk a.2 bw a.1 ∈ lay.aux) ∧
      lay.cst = [(zC, [0]), (qtC, Lvm6.Q.qltData6 P6 lay6)] ∧
      (∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ w, boolBlk6 S w x ∈ lay.aux ∧ outBlk6 S w x ∈ lay.aux) :=
  ⟨powAuxIn_of ha, qltCst_of hc, fun S hS ↦ bitsAuxIn_of ha S (bitsSpecs6_eq lay ▸ hS)⟩

end Lvm6.Node.Dep
