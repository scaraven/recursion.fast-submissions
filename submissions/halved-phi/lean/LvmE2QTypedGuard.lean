-- New for lvm2 E2-FT (E2F-QH3): the typed static guard at stage S2GF (twin `e2` rows, the coordinate-split cache),
-- generic in the configuration; the analogue of `LvmQTypedGuard.staticOkTC`/`StaticFactsT`.
import LvmQTypedGuard
import LvmE2QAsm
import LvmWiringXF

/-!
# The S2GF static guard (`staticOkTX`)

One `Bool` over the configuration, the frozen record, the program's segments `δ`, the program, the layout and the
instance. It decides, besides roll 11's facts (the program's well-formedness by QL's one pass, `Lay.okB`, the
regions, the mini-bus's fit, the frozen read words, QLT's constants, the cell bound), the two facts the X path needs
(E2F-LEAD's review action 1, so that neither reaches the certificate as a hypothesis):

* **`Q.twinsOk = true`** (`holds_of_wiringX`'s, `typed_soundX`'s `htw`);
* **`(cacheWX Q lay).okB Q lay = true`** (`PhiQCX_eq`'s `hc`), decided on the fast cache and check (`cacheWXF`,
  `okBF`: equal under `lay.Ok`, `LvmWiringXF`).

`staticFactsTX`: the guard gives `StaticFactsTX` (the facts in their consumers' forms).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.QTyped

/-- The S2GF static guard on a given cache `c` (the instance passes its cache, so that it is built once). -/
def staticOkTXc (C : QCfg) (F : TFrz) (δ : List Seg) (Q : Program) (lay : Typed.Lay) (N : TypedV.TNat)
    (c : PhiCacheX) : Bool :=
  Lvm.Fin.segsOkF ⟨nK C, 0⟩ δ && lay.okB Q && c.okBF Q lay && Q.twinsOk &&
    N.okB C.p.nuMain C.p.nuRec && layOkN N lay && TypedV.fitsMiniB C.p N.mbT && mbFitBF C Q lay &&
    F.mbW.all (fun e => e.2 == (layout0 C.p).t + lay.wordK e.1) && lay.cst == qltCstF C &&
    decide (max (Q.cells .K) (Q.cells .E) < 2 ^ 64 - 1)

/-- **The S2GF static guard** (`δ` the program's segments, `(qprogF C T fr pn ⟨nK C, 0⟩).2`). -/
def staticOkTX (C : QCfg) (F : TFrz) (δ : List Seg) (Q : Program) (lay : Typed.Lay) (N : TypedV.TNat) : Bool :=
  staticOkTXc C F δ Q lay N (cacheWXF Q lay)

/-- **The facts the S2GF guard gives**, in their consumers' forms. -/
structure StaticFactsTX (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TypedV.TNat) : Prop where
  /-- `typed_soundX`'s `hwf`. -/
  wf : Q.wf = true
  /-- `typed_soundX`'s `hlay`, `PhiQCX_eq`'s `hlay`. -/
  hlay : lay.Ok Q
  /-- **`PhiQCX_eq`'s `hc`** (decided). -/
  cache : (cacheWX Q lay).okB Q lay = true
  /-- **`holds_of_wiringX`'s `htw`** (decided). -/
  twins : Q.twinsOk = true
  /-- V_S's region check. -/
  regs : N.okB C.p.nuMain C.p.nuRec = true
  /-- V_S's regions are the layout's. -/
  hlayOk : layOkN N lay = true
  /-- The record is the mini-bus's. -/
  mini : TypedV.fitsMiniB C.p N.mbT = true
  /-- The layout places the read tables' cells consecutively (`MbFit`). -/
  mbFit : MbFit C fun n => (layout0 C.p).t + lay.wordK n
  /-- The frozen read words are the layout's. -/
  mbW : ∀ e ∈ F.mbW, e.2 = (layout0 C.p).t + lay.wordK e.1
  /-- QLT's cells are the layout's constants. -/
  cst : lay.cst = qltCst C
  /-- `typed_soundX`'s `hinj`. -/
  inj : GInj (max (Q.cells .K) (Q.cells .E))

theorem staticFactsTX {C : QCfg} {F : TFrz} {δ : List Seg} {Q : Program} {lay : Typed.Lay} {N : TypedV.TNat}
    {B : BM Unit} (hQ : Q = toProgram (nK C) 0 B) (hδ : δ = (B ⟨nK C, 0⟩).2)
    (h : staticOkTX C F δ Q lay N = true) : StaticFactsTX C F Q lay N := by
  unfold staticOkTX staticOkTXc at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hl⟩, hc⟩, htw⟩, hr⟩, hk⟩, hm⟩, hf⟩, hW⟩, hcs⟩, hi⟩ := h
  rw [cacheWXF_eq Q lay hl, okBF_eq Q lay hl] at hc
  refine ⟨?_, hl, hc, htw, hr, hk, hm, mbFit_of C lay ((mbFitBF_eq C Q lay hl).symm.trans hf), ?_,
    (beq_iff_eq.mp hcs).trans (qltCstF_eq C), ?_⟩
  · rw [hQ]
    exact toProgram_wf _ _ _ (by rw [← Lvm.Fin.segsOkF_eq, ← hδ]; exact hw)
  · intro e he
    simp only [List.all_eq_true, beq_iff_eq] at hW
    exact hW e he
  · have hm : max (Q.cells .K) (Q.cells .E) < 2 ^ 64 - 1 := of_decide_eq_true hi
    intro a b ha hb hab
    exact FK.FKx_pow_inj (by omega) (by omega) hab

end Lvm.E2Q
