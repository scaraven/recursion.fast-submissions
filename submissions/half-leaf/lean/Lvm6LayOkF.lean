-- New for lvm6 (NODE3, G0 item 3): `Lay.okB`'s run-time twin. `blocksOk`/`auxOk` filter all of `lay.xs` once per
-- block (G0: 8,524 aux blocks × 9,669 chunks, 1.1 s); the twin groups the chunks by block in one pass (a hash map)
-- and reads each block's group. `okBF_eq : okBF = okB`; the guard (`staticOk6`) calls the twin. No statement
-- changes.
import LvmTypedLayout
import Std.Data.HashMap.Lemmas

/-!
# `Lay.okBF`: `Lay.okB` with the chunks grouped once

* `grpX xs`: the chunks by block (`foldr`, so each group keeps `xs`'s order); **`grpX_getD`**: block `k`'s group is
  `xs.filter (·.blk == k)`.
* `blocksOkF`, `auxOkF`: `blocksOk`, `auxOk` reading a block's chunks from a function; **`blocksOk_eq`**,
  **`auxOk_eq`**: at `fun k ↦ xs.filter (·.blk == k)` they are the originals.
* **`okBF_eq : @Lay.okBF = @Lay.okB`**.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-- The chunks grouped by block, each group in `xs`'s order. -/
def grpX (xs : List XChunk) : Std.HashMap ℕ (List XChunk) :=
  xs.foldr (fun c m ↦ m.insert c.blk (c :: m.getD c.blk [])) ∅

theorem grpX_getD (xs : List XChunk) (k : ℕ) : (grpX xs).getD k [] = xs.filter (·.blk == k) := by
  induction xs with
  | nil => simp [grpX]
  | cons c cs ih =>
    simp only [grpX, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases h : c.blk = k
    · subst h
      simp [ih]
    · simp [h, ih]

/-- `blocksOk`, each block's chunks from `G`. -/
def blocksOkF (nInK : ℕ) (G : ℕ → List XChunk) : ℕ → ℕ → ℕ → List BLay → List Block → Bool
  | _, _, _, [], [] => true
  | b, sK, sE, B :: Bs, Bq :: Bqs =>
    B.dims == Bq.dims && B.stK == sK && B.stE == sE && B.twK == Bq.tw .K && B.twE == Bq.tw .E &&
      tplOk Bq.size nInK Bq.tpl B.cr B.srcK B.srcE 0 &&
      B.chK.all (chFits B.l .K) && B.chE.all (chFits B.l .E) &&
      chunksCover B.l (G b) 0 (nCon Bq) &&
      blocksOkF nInK G (b + 1) (sK + B.twK * Bq.size) (sE + B.twE * Bq.size) Bs Bqs
  | _, _, _, _, _ => false

theorem blocksOk_eq (nInK : ℕ) (xs : List XChunk) : ∀ (b sK sE : ℕ) (Bs : List BLay) (Bqs : List Block),
    blocksOk nInK xs b sK sE Bs Bqs = blocksOkF nInK (fun k ↦ xs.filter (·.blk == k)) b sK sE Bs Bqs
  | _, _, _, [], [] => rfl
  | b, sK, sE, B :: Bs, Bq :: Bqs => by
    rw [blocksOk, blocksOkF, blocksOk_eq nInK xs (b + 1) _ _ Bs Bqs]
  | _, _, _, [], _ :: _ => rfl
  | _, _, _, _ :: _, [] => rfl

/-- `auxOk`, each aux block's chunks from `G`. -/
def auxOkF (G : ℕ → List XChunk) : ℕ → List ABlk → Bool
  | _, [] => true
  | k, A :: As =>
    A.rows.all (fun r ↦ r.ops.all fun e ↦ decide (e.1 < 4) && aopFits A.l e.2.1) &&
      chunksCover A.l (G k) 0 A.rows.length && auxOkF G (k + 1) As

theorem auxOk_eq (xs : List XChunk) : ∀ (k : ℕ) (As : List ABlk),
    auxOk xs k As = auxOkF (fun k ↦ xs.filter (·.blk == k)) k As
  | _, [] => rfl
  | k, A :: As => by rw [auxOk, auxOkF, auxOk_eq xs (k + 1) As]

namespace Lay

variable (lay : Lay)

/-- `okB` with the chunks grouped once (`grpX`). -/
def okBG (G : Std.HashMap ℕ (List XChunk)) (Q : Program) : Bool :=
  lay.nInK == Q.nInK && lay.nInE == Q.nInE && lay.blocks.length == Q.blocks.length &&
    blocksOkF lay.nInK (fun k ↦ G.getD k []) 0 Q.nInK Q.nInE lay.blocks Q.blocks &&
    auxOkF (fun k ↦ G.getD k []) lay.blocks.length lay.aux &&
    xsSorted lay.xs && yregsSorted lay.yregs &&
    lay.inp.all dregFits && lay.dense.all dregFits && decide (lay.one < 2 ^ yVars) &&
    cstOk lay.cst lay.nInK lay.blocks Q.blocks

/-- **`okB`, its chunks grouped by block in one pass.** -/
def okBF (Q : Program) : Bool := lay.okBG (grpX lay.xs) Q

theorem okBF_eq : @okBF = @okB := by
  funext lay Q
  have hG : (fun k ↦ (grpX lay.xs).getD k []) = fun k ↦ lay.xs.filter (·.blk == k) := funext (grpX_getD lay.xs)
  simp only [okBF, okBG, okB, hG, ← blocksOk_eq, ← auxOk_eq]

end Lay

end Lvm.Typed
