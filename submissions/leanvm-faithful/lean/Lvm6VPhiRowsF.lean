-- New for lvm6 (ST-6, start-up speed): `rowsK`'s fast twin. The row instances over arrays (`rowIs` reads the blocks
-- and the auxiliary blocks with `List.getD`, once per row source) and the entries by LAY4's bisections
-- (`Lvm6FLB`: `rowEntsXB`, `auxEntsB`, equal to `FLF`'s searches when the chunk tables are sorted, checked once).
import Lvm6VPhiChkQ
import Lvm6FLA

/-!
# `rowsK`, fast

* `rowIsF Q lay`: `rowIs` with the blocks and auxiliary blocks read from arrays; **`rowIsF_eq`**.
* `rawXB C G`: `rawXF G` by the bisections; **`rawXB_eq`**: equal when `(SC.of G.F).okB`. `rawXA A C G`: the same
  with the chunk and row reads from arrays (`Lvm6FLA`); **`rawXA_eq`**.
* **`rowsKF Q lay`**: `rowsK`'s fold on `rowIsF` and `rawXA` when the chunk tables are sorted (`SC.okBL`), else `rowsK`;
  **`rowsKF_eq : rowsKF Q lay = rowsK Q lay`** (no hypothesis).
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-- **The row instances, over arrays** (`rowIs`'s order). -/
def rowIsF (Q : Program) (lay : Lay) : List (TSrc × ℕ) :=
  let ab := Q.blocks.toArray
  let ax := lay.aux.toArray
  ((List.range ab.size).flatMap fun b =>
      let B := ab.getD b default
      (List.range B.tpl.length).flatMap fun t => (List.range (2 ^ B.lsize)).map (TSrc.row b t, ·)) ++
    (List.range ax.size).flatMap fun k =>
      let A := ax.getD k default
      (List.range A.rows.length).flatMap fun r => (List.range (2 ^ A.l)).map (TSrc.aux k r, ·)

theorem rowIsF_eq (Q : Program) (lay : Lay) : rowIsF Q lay = rowIs Q lay := by
  unfold rowIsF rowIs rowsOf
  rw [List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  simp only [List.size_toArray, List.flatMap_map, Array.getD_eq_getD_getElem?, List.getElem?_toArray, srcL,
    Program.blk, List.getD_eq_getElem?_getD]

/-- `rawXF` by the bisections. -/
def rawXB (C : K.SC) (G : K.FLF) : TSrc → ℕ → List Ent
  | .row b t, jf => K.rowEntsXB C G b t jf
  | .aux k r, j => K.auxEntsB C G k r j

theorem rawXB_eq (G : K.FLF) (h : (K.SC.of G.F).okB = true) (s : TSrc) (jf : ℕ) :
    rawXB (K.SC.of G.F) G s jf = rawXF G s jf := by
  cases s with
  | row b t => exact K.rowEntsXB_eq G h b t jf
  | aux k r => exact K.auxEntsB_eq G h k r jf

/-- `rawXB` with the chunk and row reads from arrays. -/
def rawXA (A : K.AC) (C : K.SC) (G : K.FLF) : TSrc → ℕ → List Ent
  | .row b t, jf => K.rowEntsXA A C G b t jf
  | .aux k r, j => K.auxEntsA A C G k r j

theorem rawXA_eq (G : K.FLF) (h : (K.SC.of G.F).okB = true) (s : TSrc) (jf : ℕ) :
    rawXA (K.AC.of G.F) (K.SC.of G.F) G s jf = rawXF G s jf := by
  rw [← rawXB_eq G h]
  cases s with
  | row b t => exact K.rowEntsXA_eq _ G b t jf
  | aux k r => exact K.auxEntsA_eq _ G k r jf

/-- **`rowsK`, fast**: on sorted chunk tables, `rowsK`'s fold on the arrays and the bisections; else `rowsK`. -/
def rowsKF (Q : Program) (lay : Lay) : Array (FE2 × ℕ) :=
  let G := K.FLF.ofLay Q lay
  let C := K.SC.of G.F
  let A := K.AC.of G.F
  if C.okBL then
    (rowIsF Q lay).foldl
      (fun a r => pushL keyE a (((rawXA A C G r.1 r.2).flatMap splitEnt).filter fun e => decide (e.o < 4)))
      (Array.mkEmpty 1700000)
  else rowsK Q lay

theorem rowsKF_eq (Q : Program) (lay : Lay) : rowsKF Q lay = rowsK Q lay := by
  unfold rowsKF
  dsimp only
  by_cases hL : (K.SC.of (K.FLF.ofLay Q lay).F).okBL = true
  · have h := K.SC.okBL_okB hL
    rw [if_pos hL, rowIsF_eq]
    unfold rowsK
    simp only [rawXA_eq _ h]
  · rw [if_neg hL]

end Lvm6.V
