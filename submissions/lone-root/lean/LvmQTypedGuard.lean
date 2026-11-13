-- New for lvm2 (roll 8 = B1, B1-IX): the B program's one-pass builder, the typed static guard and its facts, generic
-- in the configuration (split out of `LvmQTypedInst` so that `P8`'s instance, `LvmQTypedInst8`, does not import
-- `P20`'s closed constants: every executable initialises the closed constants of the modules it imports).
import LvmQTypedData
import LvmFinSegs
import LvmVFastQ
import LvmBusILookup
import LvmQTypedSCache
import LvmWiringKF

/-!
# The typed static guard, generic in the configuration

The B program's one-pass builder (`qprogBF`, V-PERF's phases 4–7 with `wireGadgetF`), the mini-bus read tables' fit
(`mbFitB`, `mbFitBF`), the typed static guard (`staticOkTC`, `staticOkTS`, `staticOkTOf`) and the facts it gives
(`StaticFactsT`, `staticFactsTC`/`TS`/`TOf`), the cache of a term array (`cacheOfTerms`). The instances are
`LvmQTypedInst` (`P20`, the badge's) and `LvmQTypedInst8` (`P8`); this module has no closed constants of either.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

/-! ## The B program's segments in one pass (V-PERF's phases 4–7) -/

section
open Lvm.Har Lvm.Loop.QRing Lvm.Q1

/-- QW's `wireGadget` with V-PERF's `loopF` (its text otherwise; B1-IX-S: `loop`'s ranks are quadratic in its
template, and the wiring's glue templates are long: 3.7 s of the builder's 4.5 s at P20 [measured]). -/
def wireGadgetF (P qw : Nat) (cv : Nat → Cell) (mb sb : List Cell) (b : Cell) (zE : Nat) : BM Lvm.Q1.WireOut :=
  let w := P + 5
  let D := Nat.log2 (2 * w - 1)
  let G := Lvm.Q1.preW P (fun j => gkS (cv j)) (mb.map gkS) (sb.map gkS) (gkS b) 0
  VF.loopF [] (tplOf G.2) >>= fun pre =>
  scGadget D 2 qw .plain (G.1.target.gkCell pre) >>= fun sc =>
  let σ := (List.range w).map fun i => sc.cell 2 i
  let H := Lvm.Q1.postW P (qw + 15 * w) (fun j => gkS (cv j)) (mb.map gkS) (σ.map gkS)
    (G.1.lt.map (Src.gkOut pre)) (G.1.z.gkOut pre) (G.1.one.gkOut pre) (gkS (sc.cell 5 (w - 1))) (gkS b) 0
  VF.loopF [] (tplOf H.2) >>= fun post =>
  scGadget 1 2 (qw + 15 * w + 3) .plain (H.1.gkCell post) >>= fun sl =>
  let τ := (List.range 2).map fun i => sl.cell 2 i
  VF.loopF [] (tplOf (Lvm.Q1.slotW (qw + 15 * w + 33) (G.1.om.map (Src.gkOut pre)) (τ.map gkS) (G.1.z.gkOut pre)
    (G.1.one.gkOut pre) (gkS (sl.cell 5 1)) (gkS b) 0).2) >>= fun _ =>
  ringG (qw + 15 * w + 225) (qw + 15 * w + 33) zE >>= fun rg =>
  pure ⟨σ, H.1.gkCell post, τ, rg⟩

theorem wireGadgetF_eq : wireGadgetF = Lvm.Q1.wireGadget := by
  funext P qw cv mb sb b zE
  unfold wireGadgetF
  rw [VF.loopF_eq]
  rfl

/-- V-PERF's `phases47F` with `wireGadgetF`. -/
def phases47S (C : QCfg) : BM Lvm.Har.P47Out := do
  let g := kc (pbB C)
  let p := C.p
  let r ← Lvm.Har.loadEs (QAsm.clog2 p.logN) (Lvm.Har.aLane p 0) 9
  let v ← Lvm.Har.loadEs 5 (Lvm.Har.aLane p 1) 3
  let tp ← VF.tapeGadgetF (p.logN - 5) (Lvm.Har.aLane p 2) (fun i => r.cell 0 i) (fun l => v.cell 0 l) g
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let mb ← Lvm.Har.borrow ((sigIn C).bn + 2) one.n p.logN
  let wo ← wireGadgetF (p.logN - 5) (Lvm.Har.aLane p 3) tp.cv mb (Lvm.Har.sbCells C) g z.n
  let rk ← Lvm.Har.loadEs (QAsm.clog2 p.ksLog) (Lvm.Har.aLane p 4) 9
  let vk ← Lvm.Har.loadEs 5 (Lvm.Har.aLane p 5) 3
  let kko ← VF.gkrGadgetF (p.ksLog - 4) (Lvm.Har.aLane p 6) (fun i => rk.cell 0 i) (fun l => vk.cell 0 l) g
  Lvm.Q1.ksLinkGadget p (QAsm.clog2 p.ksLog) (Lvm.Har.aLane p 7) g
  pure ⟨(List.range p.logN).map (r.cell 0), (List.range 25).map (v.cell 0), tp, mb, wo,
    (List.range p.ksLog).map (rk.cell 0), (List.range 25).map (vk.cell 0), kko⟩

theorem phases47S_eq (C : QCfg) : phases47S C = VF.phases47F C := by
  unfold phases47S VF.phases47F
  rw [wireGadgetF_eq]

end

/-- The B program's segments with V-PERF's linear-time phases 4–7 (`wireGadgetF`: B1-IX-S). -/
def qprogBF (C : QCfg) (T : TData) : BM Unit := do
  Lvm.QLink.qlink C.p (lay C)
  let _ ← Lvm.QSig.qsig (sigIn C)
  phases47S C >>= qarithB C T

theorem qprogBF_eq (C : QCfg) (T : TData) : qprogBF C T = qprogB C T := by
  unfold qprogBF qprogB
  rw [phases47S_eq, show VF.phases47F C = Lvm.Har.phases47 C by
    unfold VF.phases47F Lvm.Har.phases47; rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]]

/-- The B program from its one-pass builder. -/
theorem QB_eqF (C : QCfg) (T : TData) : QB C T = toProgram (nK C) 0 (qprogBF C T) := by
  rw [qprogBF_eq]; rfl

/-! ## The layout's fit of the mini-bus's read tables -/

/-- **`MbFit`, decided** on a word map `wk` of `K` cells (`C_main` words). -/
def mbFitBW (C : QCfg) (wk : Nat → Nat) : Bool :=
  let Q := qlinkProg C
  (capReadRows Q).all fun x =>
    (List.range (2 ^ (Q.blk x.1).lsize)).all fun jf =>
      wk (adrCell Q x.1 x.2 jf) == wk (adrCell Q x.1 x.2 0) + jf &&
        wk (resCell Q x.1 x.2 jf) == wk (resCell Q x.1 x.2 0) + jf

/-- **`MbFit`, decided** on the layout's words (`C_main` words from `T`'s offset). -/
def mbFitB (C : QCfg) (lay : Typed.Lay) : Bool := mbFitBW C fun n => (layout0 C.p).t + lay.wordK n

/-- `mbFitB` on the layout's array caches (B1-IX-S: `K.FL.wordK`'s owner is a binary search, `Lay.wordK`'s a scan of
the blocks; `mbFitBF_eq` on a checked layout). -/
def mbFitBF (C : QCfg) (Q : Program) (lay : Typed.Lay) : Bool :=
  let t := (layout0 C.p).t
  let F := K.FL.ofLay Q lay
  mbFitBW C fun n => t + F.wordK n

theorem mbFitBF_eq (C : QCfg) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) : mbFitBF C Q lay = mbFitB C lay := by
  unfold mbFitBF mbFitB
  simp only [K.fl_wordK Q lay hlay]

theorem mbFit_of (C : QCfg) (lay : Typed.Lay) (h : mbFitB C lay = true) :
    MbFit C fun n => (layout0 C.p).t + lay.wordK n := by
  intro x hx jf hjf
  simp only [mbFitB, mbFitBW, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h x hx jf hjf

/-! ## The static guard -/

/-- **The typed static guard** of a configuration on its static data, the program's segments `δ` (`segsOkF`'s
one pass; `δ` the B program's, `(qprogBF C T ⟨nK C, 0⟩).2`), program, layout, cache, instance and the verdict `ck`
of `Φ_Q`'s entry check (`K.checkTerms Q lay c.terms.toArray`: `staticFactsTC`'s `hck`; B1-IX-S: computed where the
terms are, `K.termsChecked`, or by `K.checkTermsF`). The rest of `PhiCache.okB` is `keysBF = keysB` (`okB_keys`);
QLT's constants on `qltCstF = qltCst`; `mbFitBF = mbFitB` on the checked layout. -/
def staticOkTC (C : QCfg) (F : TFrz) (δ : List Seg) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) (ck : Bool) : Bool :=
  Lvm.Fin.segsOkF ⟨nK C, 0⟩ δ && lay.okB Q && (c.keysBF Q lay && ck) &&
    N.okB C.p.nuMain C.p.nuRec && layOkN N lay && TypedV.fitsMiniB C.p N.mbT && mbFitBF C Q lay &&
    F.mbW.all (fun e => e.2 == (layout0 C.p).t + lay.wordK e.1) && lay.cst == qltCstF C &&
    decide (max (Q.cells .K) (Q.cells .E) < 2 ^ 64 - 1)

/-- The typed static guard with `Φ_Q`'s entry check on the fast entries (`K.checkTermsF = K.checkTerms`). -/
def staticOkTS (C : QCfg) (F : TFrz) (δ : List Seg) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) : Bool :=
  staticOkTC C F δ Q lay c N (K.checkTermsF Q lay c.terms.toArray)

/-- **The typed static guard** of a configuration on its static data, program, layout, cache and instance. -/
def staticOkTOf (C : QCfg) (T : TData) (F : TFrz) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) : Bool :=
  staticOkTS C F (qprogBF C T ⟨nK C, 0⟩).2 Q lay c N

/-- **The facts the typed guard gives**, in their consumers' forms. -/
structure StaticFactsT (C : QCfg) (T : TData) (F : TFrz) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) : Prop where
  /-- `typed_sound`'s `hwf`. -/
  wf : Q.wf = true
  /-- `typed_sound`'s `hlay`, `PhiQC_eq`'s `hlay`. -/
  hlay : lay.Ok Q
  /-- `PhiQC_eq`'s `hc`. -/
  cache : c.okB Q lay = true
  /-- V_S's region check (B1-V's closed forms). -/
  regs : N.okB C.p.nuMain C.p.nuRec = true
  /-- V_S's regions are the layout's (`TNat.layOk`, `layOkN_eq`; `src?_inst`). -/
  hlayOk : layOkN N lay = true
  /-- The record is the mini-bus's. -/
  mini : TypedV.fitsMiniB C.p N.mbT = true
  /-- The layout places the read tables' cells consecutively (`MbFit`). -/
  mbFit : MbFit C fun n => (layout0 C.p).t + lay.wordK n
  /-- The frozen read words are the layout's. -/
  mbW : ∀ e ∈ F.mbW, e.2 = (layout0 C.p).t + lay.wordK e.1
  /-- **QLT's cells are the layout's constants** (`typed_sound`'s `Inputs` on QLT, L-D's `NodeSound`). -/
  cst : lay.cst = qltCst C
  /-- `typed_sound`'s `hinj` (`g`-injectivity below the cell bound). -/
  inj : GInj (max (Q.cells .K) (Q.cells .E))

theorem staticFactsTC {C : QCfg} {T : TData} {F : TFrz} {δ : List Seg} {Q : Program} {lay : Typed.Lay}
    {c : PhiCache} {N : TypedV.TNat} {ck : Bool} (hQ : Q = QB C T) (hδ : δ = (qprogBF C T ⟨nK C, 0⟩).2)
    (hck : ck = K.checkTerms Q lay c.terms.toArray) (h : staticOkTC C F δ Q lay c N ck = true) :
    StaticFactsT C T F Q lay c N := by
  unfold staticOkTC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hl⟩, hc⟩, hr⟩, hk⟩, hm⟩, hf⟩, hW⟩, hcs⟩, hi⟩ := h
  refine ⟨?_, hl, ?_, hr, hk, hm, mbFit_of C lay ((mbFitBF_eq C Q lay hl).symm.trans hf), ?_,
    (beq_iff_eq.mp hcs).trans (qltCstF_eq C), ?_⟩
  · rw [hQ, QB_eqF]
    exact toProgram_wf _ _ _ (by rw [← Lvm.Fin.segsOkF_eq, ← hδ]; exact hw)
  · rw [PhiCache.okB_keys, ← PhiCache.keysBF_eq, ← hck, hc.1, hc.2]
    rfl
  · intro e he
    simp only [List.all_eq_true, beq_iff_eq] at hW
    exact hW e he
  · have hm : max (Q.cells .K) (Q.cells .E) < 2 ^ 64 - 1 := of_decide_eq_true hi
    intro a b ha hb hab
    exact FK.FKx_pow_inj (by omega) (by omega) hab

theorem staticFactsTS {C : QCfg} {T : TData} {F : TFrz} {δ : List Seg} {Q : Program} {lay : Typed.Lay}
    {c : PhiCache} {N : TypedV.TNat} (hQ : Q = QB C T) (hδ : δ = (qprogBF C T ⟨nK C, 0⟩).2)
    (h : staticOkTS C F δ Q lay c N = true) : StaticFactsT C T F Q lay c N :=
  staticFactsTC hQ hδ (K.checkTermsF_eq Q lay _) h

theorem staticFactsTOf {C : QCfg} {T : TData} {F : TFrz} {Q : Program} {lay : Typed.Lay} {c : PhiCache}
    {N : TypedV.TNat} (hQ : Q = QB C T) (h : staticOkTOf C T F Q lay c N = true) :
    StaticFactsT C T F Q lay c N :=
  staticFactsTS hQ rfl h

/-! ## The cache of a term array -/

/-- The cache of a term array (`cacheW`'s form, compiled by the fast `K.compileTF`, which is `K.compileT`:
`K.compileTF_eq`; CTF). -/
def cacheOfTerms (ts : Array CTerm) : PhiCache := ⟨ts.toList, K.compileTF ts⟩

theorem cacheOfTerms_terms (ts : Array CTerm) : (cacheOfTerms ts).terms.toArray = ts := Array.toArray_toList

end Lvm.QTyped
