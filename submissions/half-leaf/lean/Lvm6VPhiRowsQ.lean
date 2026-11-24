-- New for lvm6 (ST-4): the class table of `(Q, lay)` from its rows and the hints, `ptOfRows_ok`.
import Lvm6VPhiRows
import LvmWiringXF
import LvmE2VPhiTEqC

/-!
# `ptOfRows` and `rowsChk` on `(Q, lay)` (ST-4)

* `rowIs Q lay`: the row instances, template rows (then auxiliary rows) in `rowsOf`'s order, each at every iteration;
  `rowE`: an instance's entries, `entsE`'s (split at `E2`, `o < 4`). **`sum_entsE_rows`**: `Φ_Q` is their sum.
* `rawXF` (`rawX` on the layout's caches `FLF`, **`rawXF_eq`** on a checked layout); `rowsRes` reads a row only
  when `rowsResG` asks for it.
* **`rowsChk Q lay H`**, **`ptOfRows Q lay H`**; **`ptOfRows_ok`**: `lay.Ok Q → rowsChk Q lay H = true →
  PhiOk (ptOfRows Q lay H).eval Q lay`. `ptCheck`, `phiOk_pt` stay the reference.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop


/-- The row instances: template rows (then auxiliary rows) in `rowsOf`'s order, each at every iteration. -/
def rowIs (Q : Program) (lay : Lay) : List (TSrc × ℕ) :=
  (rowsOf Q lay).flatMap fun s => (List.range (2 ^ srcL Q lay s)).map (s, ·)

/-- **A row instance's entries**: `entsE`'s (split at `E2`, matrices `< 4`). -/
def rowE (Q : Program) (lay : Lay) (r : TSrc × ℕ) : List EntT :=
  ((rawX Q lay r.1 r.2).flatMap splitEnt).filter fun e => decide (e.o < 4)

/-- `rawX` on the layout's caches (`FLF`). -/
def rawXF (G : K.FLF) : TSrc → ℕ → List Ent
  | .row b t, jf => G.rowEntsX b t jf
  | .aux k r, j => G.srcEnts (.aux k r) j

theorem rawXF_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : TSrc) (jf : ℕ) :
    rawXF (K.FLF.ofLay Q lay) s jf = rawX Q lay s jf := by
  cases s with
  | row b t => simp only [rawXF, rawX]; rw [flf_rowEntsX, fl_rowEntsX Q lay hlay]
  | aux k r =>
    simp only [rawXF, rawX]
    rw [K.flf_srcEnts, rowEnts_eq Q lay hlay]
    rfl

/-- The row instances as an array, and one row's entries on the caches, computed when asked (`rowsResG` reads the
template rows, the rows under no hint and, in `clsRowsB`, the hinted rows). -/
def rowsRes (Q : Program) (lay : Lay) (H : Hints) : PT × Bool :=
  let G := K.FLF.ofLay Q lay
  let R := (rowIs Q lay).toArray
  rowsResG (fun g => (R[g]?.map fun r => ((rawXF G r.1 r.2).flatMap splitEnt).filter fun e => decide (e.o < 4)).getD [])
    R.size H

/-- **The start-up check** (ST-4): sorted disjoint hints, every class instance's rows the template, the covers and
the rest's kinds equal to their inputs by `normB`. -/
def rowsChk (Q : Program) (lay : Lay) (H : Hints) : Bool := (rowsRes Q lay H).2

/-- **The class table of `(Q, lay)` from the hints.** -/
def ptOfRows (Q : Program) (lay : Lay) (H : Hints) : PT := (rowsRes Q lay H).1


theorem rows_getElem? {β : Type} (l : List β) (f : β → List EntT) (F : List EntT → FE2)
    (g : β → List EntT) (hfg : ∀ b, f b = g b) :
    ((List.range l.length).map fun i => F ((l.toArray[i]?.map f).getD [])).sum = (l.map fun b => F (g b)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons, ← ih]
    simp [hfg, Function.comp_def]

/-- `Φ_Q`'s sum is the sum over the row instances. -/
theorem sum_entsE_rows (Q : Program) (lay : Lay) (pt : List FE2) :
    Lvm6.Ty.PhiQFE Q lay pt = ((rowIs Q lay).map fun r => ((rowE Q lay r).map (qval (phW pt) ∘ toQ)).sum).sum := by
  have hφ : ∀ e : EntT, e.c * eqWT pt (Lvm6.Ty.EntT.idxE e) = (qval (phW pt) ∘ toQ) e := by
    intro e; rw [eqWT_eq]; rfl
  rw [Lvm6.Ty.PhiQFE, foldr_add_eq, List.map_congr_left fun e _ => hφ e, Lvm6.Ty.entsE, entsT, List.filter_flatMap,
    sum_map_flatMap]
  rw [Lvm.Typed.KT.w_ents_rows Q lay (fun e => (((splitEnt e).filter fun e => decide (e.o < 4)).map
    (qval (phW pt) ∘ toQ)).sum)]
  rw [rowIs, sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun jf _ => ?_)
  simp only [Function.comp_apply, rowE, List.filter_flatMap, sum_map_flatMap]

/-- **The class table from the rows computes `Φ_Q`** on a checked layout once `rowsChk` passed. -/
theorem ptOfRows_ok {Q : Program} {lay : Lay} {H : Hints} (hlay : lay.Ok Q) (h : rowsChk Q lay H = true) :
    PhiOk (ptOfRows Q lay H).eval Q lay := by
  intro pt
  rw [ptOfRows, rowsRes, rowsResG_eval h, sum_entsE_rows, sum_map_flatMap, List.size_toArray]
  exact rows_getElem? (rowIs Q lay) _ (fun l => (l.map (qval (phW pt) ∘ toQ)).sum) (rowE Q lay)
    (fun r => by simp only [rowE, rawXF_eq Q lay hlay])

end Lvm6.V
