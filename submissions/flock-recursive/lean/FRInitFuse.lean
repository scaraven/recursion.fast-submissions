-- New for `flock-recursive` (track INIT: the badge's start-up). The plan compile and the template
-- generators' trail in one pass.
import FRNodeRows4AskPosT
import FRNodeRows4RepCFP

/-!
# One pass for the compile and the trail (`compMSXA`)

The node plan walks each prototype's ops twice at process start: `compMSX` (the compile with the
template memo, `planData4`) and `trailMS` (the ask-template generators' rows, `arOf`). Both evolve the
same compile state and memo op by op. **`compMSXA`** does both in one walk, and **`compMSXA_eq`** says
it is the pair `(compMSX …, trailMS …)`, for every extension, generator and starting state.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- **`compMSX` and `trailMS` in one pass** (`compMSXA_eq`): the compile's state, segments and memo,
and the generator `G`'s rows (reversed onto `racc`, `pre` the previous op, `k` the items so far). -/
def compMSXA (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) : List (TKey × Tpl) → CS → List Op →
    Option (ℕ × ℕ × ℕ) → List Seg → Option Op → ℕ → List Row →
    (CS × List Seg × List (TKey × Tpl)) × List Row
  | M, cs, [], _, acc, _, _, racc => ((cs, acc, M), racc)
  | M, cs, op :: ops, cur, acc, pre, k, racc =>
    let a := alignOf op ops
    let acc := match a, cur with
      | some _, some (r0, c0, b) => cutBlock r0 cs.nrows c0 b acc
      | _, _ => acc
    let cs' := cs.align a
    let cur := match a with
      | some (_, b) => some (cs'.nrows, cs'.next, b)
      | none => cur
    let acc := match op with
      | .eqTable r =>
        if (cs'.slot r).isSome && decide (8 ≤ (asAF (cs'.slot r)).length) then
          (tensorSegs P cs' (asAF (cs'.slot r))).reverse ++ acc
        else acc
      | _ => acc
    let racc := (if op.item?.isSome || G.cov op then G.rows P cs' pre op k else []).reverseAux racc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P cs' op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P cs' op
    let M := memoAdd M o.tin
    let cs2 := cs'.add op o
    let k' := if op.item?.isSome then k + 1 else k
    match op, cur with
    | .assertEq .., some (r0, c0, b) =>
      compMSXA X L P G M cs2 ops none (cutBlock r0 cs2.nrows c0 b acc) (some op) k' racc
    | _, _ => compMSXA X L P G M cs2 ops cur acc (some op) k' racc

/-- **The one pass is the two passes.** -/
theorem compMSXA_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (cur : Option (ℕ × ℕ × ℕ)) (acc : List Seg)
      (pre : Option Op) (k : ℕ) (racc : List Row),
      compMSXA X L P G M cs ops cur acc pre k racc =
        (compMSX X L P M cs ops cur acc, trailMS X L P G M cs pre k ops racc)
  | [], _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, cur, acc, pre, k, racc => by
    cases op with
    | assertEq a b act =>
      simp only [compMSXA, compMSX, trailMS]
      rcases ha : alignOf (Op.assertEq a b act) ops with _ | ⟨x, w⟩ <;> simp only [ha] <;>
        rcases cur with _ | ⟨r0, c0, w'⟩ <;> dsimp only <;> rw [compMSXA_eq X L P G ops]
    | _ => simp only [compMSXA, compMSX, trailMS]; rw [compMSXA_eq X L P G ops]; rfl

/-- (+) The pass at no ops is the starting state and accumulator. -/
theorem compMSXA_nil (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (M : List (TKey × Tpl)) (cs : CS)
    (racc : List Row) : compMSXA X L P G M cs [] none [] none 0 racc = ((cs, [], M), racc) := rfl

/-! ## The compile and the trail with replay blocks (CF2, INIT's proposal 2 for `trailMB`) -/

/-- **`compMSX` and `trailMB` in one pass** (`compMSXB_eq`): the compile's state, segments and memo,
the generator `G`'s rows and the replay template `rt`'s blocks (`bk`), each reversed onto its
accumulator. -/
def compMSXB (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) :
    List (TKey × Tpl) → CS → List Op → Option (ℕ × ℕ × ℕ) → List Seg → Option Op → ℕ → List Row → List RBlk →
    (CS × List Seg × List (TKey × Tpl)) × List Row × List RBlk
  | M, cs, [], _, acc, _, _, racc, bacc => ((cs, acc, M), racc, bacc)
  | M, cs, op :: ops, cur, acc, pre, k, racc, bacc =>
    let a := alignOf op ops
    let acc := match a, cur with
      | some _, some (r0, c0, b) => cutBlock r0 cs.nrows c0 b acc
      | _, _ => acc
    let cs' := cs.align a
    let cur := match a with
      | some (_, b) => some (cs'.nrows, cs'.next, b)
      | none => cur
    let acc := match op with
      | .eqTable r =>
        if (cs'.slot r).isSome && decide (8 ≤ (asAF (cs'.slot r)).length) then
          (tensorSegs P cs' (asAF (cs'.slot r))).reverse ++ acc
        else acc
      | _ => acc
    let racc := (if op.item?.isSome || G.cov op then G.rows P cs' pre op k else []).reverseAux racc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P cs' op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P cs' op
    let bacc := if rt.cov op then bk P cs' op o.slots :: bacc else bacc
    let M := memoAdd M o.tin
    let cs2 := cs'.add op o
    let k' := if op.item?.isSome then k + 1 else k
    match op, cur with
    | .assertEq .., some (r0, c0, b) =>
      compMSXB X L P G rt bk M cs2 ops none (cutBlock r0 cs2.nrows c0 b acc) (some op) k' racc bacc
    | _, _ => compMSXB X L P G rt bk M cs2 ops cur acc (some op) k' racc bacc

/-- **The one pass is the two passes.** -/
theorem compMSXB_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (cur : Option (ℕ × ℕ × ℕ)) (acc : List Seg)
      (pre : Option Op) (k : ℕ) (racc : List Row) (bacc : List RBlk),
      compMSXB X L P G rt bk M cs ops cur acc pre k racc bacc =
        (compMSX X L P M cs ops cur acc, trailMB X L P G rt bk M cs pre k ops racc bacc)
  | [], _, _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, cur, acc, pre, k, racc, bacc => by
    cases op with
    | assertEq a b act =>
      simp only [compMSXB, compMSX, trailMB]
      rcases ha : alignOf (Op.assertEq a b act) ops with _ | ⟨x, w⟩ <;> simp only [ha] <;>
        rcases cur with _ | ⟨r0, c0, w'⟩ <;> dsimp only <;> rw [compMSXB_eq X L P G rt bk ops]
    | _ => simp only [compMSXB, compMSX, trailMB]; rw [compMSXB_eq X L P G rt bk ops]; rfl

end Rev4
end FR
