-- New for lvm6 (ST-4, STARTUP2 route (b)): `rowsK`, `phiChk`, `phiChk_ok` — the class table checked against `Q`'s rows.
import Lvm6VPhiChk
import Lvm6VPhiConsA
import Lvm6VPhiRowsQ

/-!
# `phiChk`: an untrusted class table checked against the rows

* `rowsK Q lay`: `Q`'s entries as (coefficient, index), one push per entry over the row instances through the layout's
  caches (`FLF`); **`rowsK_toList`**: on a checked layout, `((rowIs Q lay).flatMap (rowE Q lay)).map keyE`.
* **`phiChk Q lay P`**: `P.okB`, `P`'s entries on `Φ_Q`'s cube, and `cancelChk` of `P`'s entries against `rowsK`.
* **`phiChk_ok`**: `lay.Ok Q → phiChk Q lay P = true → PhiOk P.eval Q lay`, for every `P` (`P` untrusted, e.g. embedded).
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-- **`Q`'s entries as (coefficient, index)**, pushed row by row through the caches. -/
def rowsK (Q : Program) (lay : Lay) : Array (FE2 × ℕ) :=
  let G := K.FLF.ofLay Q lay
  (rowIs Q lay).foldl (fun a r => pushL keyE a (((rawXF G r.1 r.2).flatMap splitEnt).filter fun e => decide (e.o < 4)))
    (Array.mkEmpty 1700000)

theorem rowsK_toList (Q : Program) (lay : Lay) (hlay : lay.Ok Q) :
    (rowsK Q lay).toList = ((rowIs Q lay).flatMap (rowE Q lay)).map keyE := by
  unfold rowsK
  rw [foldl_app _ (fun r => (rowE Q lay r).map keyE) (fun a r => by rw [pushL_toList, rowE, rawXF_eq Q lay hlay])]
  simp [List.map_flatMap]

/-- **The start-up check of a class table** `P` against `(Q, lay)`. -/
def phiChk (Q : Program) (lay : Lay) (P : PT) : Bool :=
  let ka := rowsK Q lay
  let pe := P.ents
  P.okB && pe.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) && cancelChk ka (mkIx ka) (pe.map toIdx)

/-- **A checked class table computes `Φ_Q`.** -/
theorem phiChk_ok {Q : Program} {lay : Lay} {P : PT} (hlay : lay.Ok Q) (h : phiChk Q lay P = true) :
    PhiOk P.eval Q lay := by
  intro pt
  simp only [phiChk, Bool.and_eq_true] at h
  obtain ⟨⟨hok, hb⟩, hc⟩ := h
  rw [eval_ents P hok hb pt]
  have hs := cancelChk_sound hc (eqAtF pt)
  unfold sumL at hs
  rw [hs, rowsK_toList Q lay hlay, sum_entsE_rows, List.map_map, sum_map_flatMap]
  rfl

end Lvm6.V
