-- New for `flock-recursive` (BLUEPRINT §10 changes 22 (a), revision 3.15: `dag_mle`; stage S-E11,
-- track L-circ).
import FRVIRTplFast

/-!
# The walk DAG's closed form `D̂` (`dag_mle`)

BLUEPRINT §10 changes 22 (a): the walk's rows are the materialised gadget DAG (`FRVIRTplDag`), laid
out as `2^gBits`-row blocks: the head, 80 `G` gadgets, the tail. Their MLE is evaluated in closed
form, never row by row: **`dagHat`** is the value of the walk instance's pieces — the `G` blocks
are instances of one key (prepared once, `kprepF`), each costing two high `eq` factors and its own
inputs, most of them in runs (`FRVIRTplRun`: one `hfac` per aligned chunk of consecutive cells); the
head, the first `G` (its accumulators start at `0`) and the tail are keys of one instance each.

**`dag_mle`**: `dagHat` is the MLE of the walk instance's indexed rows (`tinIRows`), the three
matrices at `(τ, σ)`. The pieces are found by the plan's search (`tinPP`, `groupPPs`, untrusted) and
kept only if their rows **are** the instance's rows (`mkWPlan` checks them once). This is the seam
for `R` (S-E12): `R` replays `D̂`, not the rows.
-/

namespace FR
namespace TEval
open Circ Tpl

/-- **The walk instance's plan**: its layout, row offset and instance, the keys, shared forms and
pieces of its blocks, whose rows are the instance's rows (`ok`). -/
structure WPlan where
  L : TLay
  off : ℕ
  tw : TKey × ℕ × List Lin
  keys : Array Key
  sh : Array (List Lin)
  pc : List Piece
  ok : keys.all (Key.ok 21) = true ∧ pc.flatMap (Piece.rows keys sh oneL) = tinIRows L oneL off tw
  pats : Array (Array Pat)
  pbs : List ℕ
  g : Array (List GForm)
  p : List PPc
  hg : g = sh.map (·.map (grp 4096))
  hp : p = pc.map (prepPiece pats)

def mkWPlanOf (L : TLay) (off : ℕ) (tw : TKey × ℕ × List Lin) (keys : Array Key)
    (sh : Array (List Lin)) (pc : List Piece) (pats : Array (Array Pat))
    (ok : keys.all (Key.ok 21) = true ∧ pc.flatMap (Piece.rows keys sh oneL) = tinIRows L oneL off tw) :
    WPlan :=
  ⟨L, off, tw, keys, sh, pc, ok, pats, patBits pats, sh.map (·.map (grp 4096)), pc.map (prepPiece pats),
    rfl, rfl⟩

/-- **The walk's plan** (once per node): the search's blocks, kept if their rows are the instance's,
else one sparse piece. -/
def mkWPlan (L : TLay) (off : ℕ) (tw : TKey × ℕ × List Lin) : WPlan :=
  let d := groupPPs (tinPP L oneL off tw).toArray #[]
  let tgt := tinIRows L oneL off tw
  if h : (d.1.all (Key.ok 21) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL)) tgt) = true then
    mkWPlanOf L off tw d.1 d.2.1 d.2.2.2.1 (mkPats d.1.size d.2.2.2.1) (by
      simp only [Bool.and_eq_true] at h; exact ⟨h.1, eqL_eq h.2⟩)
  else mkWPlanOf L off tw #[] #[] [.sp tgt] #[] (by simp [Piece.rows, tgt])

/-- The walk instance of a compiled slot (its `walkAB` template instance), if any. -/
def walkTin (cs : CS) : Option (TKey × ℕ × List Lin) := cs.tins.find? (isWalk ·.1)

/-- **`D̂`**: the walk rows' three matrices at `(τ, σ)` (21 and 23 coordinates), in closed form. -/
def dagHat (wp : WPlan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  let tb := tbOfK 21 t u wp.keys wp.pbs
  slotV3 (ectx3 21 tb t u wp.keys (wp.keys.map (kprep3 tb t u)) wp.g wp.pats) wp.p

/-- **`dag_mle`**: `D̂` is the MLE of the walk instance's indexed rows. -/
theorem dag_mle (wp : WPlan) (τ σ : Array F) :
    dagHat wp τ σ =
      (Eval.matMLE (entriesI .a (tinIRows wp.L oneL wp.off wp.tw)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
       Eval.matMLE (entriesI .b (tinIRows wp.L oneL wp.off wp.tw)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
       Eval.matMLE (entriesI .c (tinIRows wp.L oneL wp.off wp.tw)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ)) := by
  simp only [dagHat, tbOfK, slotV3_eq]
  rw [wp.hg, wp.hp]
  simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ wp.ok.1, wp.ok.2, rowsVal_F,
    Eval.sparse_eq]

/-! ## Controls -/

/-- (+) The sparse fallback is a plan: one piece holding the instance's rows. -/
theorem mkWPlanOf_sparse (L : TLay) (off : ℕ) (tw : TKey × ℕ × List Lin) :
    (mkWPlanOf L off tw #[] #[] [.sp (tinIRows L oneL off tw)] #[]
      (by simp [Piece.rows])).pc.flatMap (Piece.rows #[] #[] oneL) = tinIRows L oneL off tw := by
  simp [mkWPlanOf, Piece.rows]

/-- (−) `walkTin` finds no walk in a slot without template instances. -/
theorem walkTin_none (cs : CS) (h : cs.tins = []) : walkTin cs = none := by
  simp [walkTin, h]

end TEval
end FR
