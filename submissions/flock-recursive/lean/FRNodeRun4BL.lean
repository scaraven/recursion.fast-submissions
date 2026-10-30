-- G6: this module also holds the former modules `FRNodeRun4AskT`, `FRNodeRows4AskBS` (one section each, in import order).
import FRNodeRows4AskTS
import FRNodeRows4AskIS
import FRNodeRows4AskB
import FRXOut

section G6_FRNodeRun4AskT

-- New for `flock-recursive` (IMP-RESULT §5 item 2; SRA-RESULT §1.1; track ASK-T): `Gap4.imp` with the
-- ask templates discharged — what remains per active slot is `SlotRunA` alone.

/-!
# `Gap4.imp` from the replay and `SlotRunA` (the asks discharged)

IMPC's `gap4Imp_of_impc` (SRA's `gap4Imp_of_rsv` with the import classes) reduces `Gap4.imp` (per
active slot, `SlotImp`) to the replay (`RepOk`, its fold), the fold of the ask templates, and per active
slot and selectable index `ATOk` of the ask template `Aq` and `SlotRunA`. With `Aq := askAq` (ASK-T's
generator, folded into `nodeIRows4` by `FRNodeRows4.askTG` with `input`, the reserve and `impcTG`):

* **`atOk_askT`**: `ATOk` of `askAq` at every active slot (`atAsk_T`; it covers no non-ask op, so its
  `ATImp` is empty), its inputs from the statement's rows (IMP's `inpCells_of_rows`);
* **`gap4Imp_of_askT`**: `Gap4.imp` from `RepOk`, the replay's fold, `StmtN4R` and `SlotRunA` at every
  active slot and selectable index. The ask obligation and the ask templates' fold are gone
  (`askFold_askT`: `withImpc askAq` has `askTG`'s fields by `rfl`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-- The ask generator covers no non-ask op: its `ATImp` holds vacuously. -/
theorem atImp_askT (impl : OpImpl) (X : Ext) (π : ℕ) (κ : Kind) (inp : Input) (w : Asg) :
    ATImp impl X (askTGT X π).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov
  exact absurd hcov (by simp [askTGT, TG.toAT])

/-- **The ask template is sound at every active slot** of a node meeting `StmtN4` (every selectable
index): `ATOk` of `askAq` on the slot's input and trace. -/
theorem atOk_askT (impl : OpImpl) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {v : ℕ} (hv : N4c.Active4 (rd4 X.pf4) κ w v)
    {ι : Kind} (hι : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι) :
    ATOk impl (Xof (protoOf κ v)) (askAq (protoOf κ v)) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) (slotAsg κ v w)
      ((rd4 X.pf4).slotTr κ v w) :=
  ⟨atAsk_T _ impl hS hv (slotIn_π (rd4 X.pf4) κ vk c₁ w v)
      (inpCells_of_rows (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr) (fun e tr => X.pfHdr_reassemble4 e tr)
        hS v hv ι hι),
    atImp_askT impl _ _ ι _ _⟩

/-! ## Controls -/

section Ctl
open Tpl

/-- A toy selector form and a compile state whose register 0 is a digest on cells 5, 6 (or an `F` on 5). -/
def ctlPT : Params := ⟨Lin.cell 0, fun κ => Lin.cell (1 + selIx κ)⟩
def ctlCS (s : Slot) : CS := { CS.init 10 with slots := #[s] }

/-- (+) **A uniform digest operand costs one row per half** (its cells against arena₁'s); (−) a slot that
is not a digest's gives the failing row; (+) an activity that depends on the kind gives one gated row per
kind and half. -/
theorem dopRows_ctl :
    dopRows ctlPT (ctlCS (some (.d, [Lin.cell 5, Lin.cell 6]))) 0 0 7 (fun _ => true) =
      [eqCR ctlPT (Lin.cell 5) (arC 0 7), eqCR ctlPT (Lin.cell 6) (arC 0 8)] ∧
    dopRows ctlPT (ctlCS (some (.f, [Lin.cell 5]))) 0 0 7 (fun _ => true) = [failRT ctlPT] ∧
    (dopRows ctlPT (ctlCS (some (.d, [Lin.cell 5, Lin.cell 6]))) 0 0 7 (fun κ => κ == .L32)).length = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- (−) **The byte operand's check**: without a previous `piField` it fails. -/
theorem preOk_ctl (cs : CS) (m k : ℕ) : preOk cs none m k = false ∧ preOk cs (some (.input 0)) m k = false :=
  ⟨rfl, rfl⟩

/-- (−) **`dop_ok` is load-bearing**: an inactive operand's rows pin arena₁'s elements to zero; at an
assignment where they are not, a row fails. -/
theorem dop_ctl : ¬ ∀ x ∈ dopRows ctlPT (ctlCS (some (.d, [Lin.cell 5, Lin.cell 6]))) 0 0 7 (fun _ => false),
    x.Holds (fun c => if c = 0 ∨ c = 1 then 1 else if c = arC 0 7 then 1 else 0) := by
  intro h
  have := (dop_ok (ι := .L32) ⟨by simp [ctlPT], fun κ => by cases κ <;> simp [ctlPT, selIx, arC, arA1]⟩ h).2 rfl
  simp [arC] at this

end Ctl

end N4s
end FR

end G6_FRNodeRun4AskT

section G6_FRNodeRows4AskBS

-- New for `flock-recursive` (IMPC2 §6–§7; track IMPC2): the bit generator's composition with the
-- node's ask template (`AT.addD`), `ATImp` of its bit classes, and `Gap4.imp` with it folded.

/-!
# `bitTGB` beside the node's ask template

`FRNodeRows4AskB.bitTGB` covers every `selectHalf` (its rows only after a `bitOf`) and every
`tensorW`; neither is an import as compiled, so its `ATImp` is vacuous (**`atImp_bitB`**): at such an op
compiled as an import the generator's rows are a failing row. Its rows bind cells that the run proof
uses (`bitOf`'s import, `bits n`'s auxiliary cells); they are not `ATImp`'s business.

* **`AT.addD`** (`TG.addD` as an ask template): each side asked for rows only at its own covered ops
  and the asks. `atAsk_addD`, `atImp_addD`, `atOk_addD`.
* **`tplExt4_imp_tc`**: at a `selectHalf` or a `tensorW`, whether the compile's extension imports does
  not depend on the template bodies (only the layout), so `bitTGB` may read it off the template-free
  context `XofA π` (`FRNodeRows4AskB.bitTGB`'s process-start fix).
* **`gap4Imp_of_bitsB`**: ASK-T's `gap4Imp_of_askT` with `bitTGB` beside the template (`withBitsB`), the
  fold a hypothesis; what remains per slot is `SlotRunA` over the larger template.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4

/-! ## Two ask templates, each asked at its own ops -/

/-- **`TG.addD` as an ask template.** -/
def _root_.FR.Circ.AT.addD (A B : AT) : AT :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k =>
    if B.cov op then
      B.rows P cs pre op k ++ (if A.cov op || op.item?.isSome then A.rows P cs pre op k else [])
    else A.rows P cs pre op k ++ (if op.item?.isSome then B.rows P cs pre op k else [])⟩

theorem toAT_addD (A B : TG) : (A.addD B).toAT = A.toAT.addD B.toAT := rfl

section AddD
variable {impl : OpImpl} {X : Ext} {A B : AT} {κ : Kind} {inp : Input} {w : Asg} {tr : Trace}
  {P : Params} {cs : CS} {pre : Option Op} {op : Op} {k : ℕ} {regs : Array Val}

theorem askCtx_addD_left (h : AskCtx impl (A.addD B) κ inp w P cs pre op k regs)
    (hc : (A.cov op || op.item?.isSome) = true) : AskCtx impl A κ inp w P cs pre op k regs := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r ?_⟩
  simp only [AT.addD]
  split
  · simp only [List.mem_append, hc, if_true]; exact Or.inr hr
  · exact List.mem_append_left _ hr

theorem askCtx_addD_right (h : AskCtx impl (A.addD B) κ inp w P cs pre op k regs)
    (hc : (B.cov op || op.item?.isSome) = true) : AskCtx impl B κ inp w P cs pre op k regs := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r ?_⟩
  simp only [AT.addD]
  split
  · exact List.mem_append_left _ hr
  · next hB =>
    have hi : op.item?.isSome = true := by simpa [hB] using hc
    simp only [List.mem_append, hi, if_true]; exact Or.inr hr

/-- **The asks are sound if the first part's are** (both parts are asked at an ask). -/
theorem atAsk_addD (h : ATAsk impl X A κ inp w tr) : ATAsk impl X (A.addD B) κ inp w tr :=
  fun P cs pre op k regs q e hc hev =>
    h P cs pre op k regs q e (askCtx_addD_left hc (by simp [ask_item hev])) hev

/-- **The covered imports are sound if each part's are.** -/
theorem atImp_addD (hA : ATImp impl X A κ inp w) (hB : ATImp impl X B κ inp w) :
    ATImp impl X (A.addD B) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  rcases (by simpa [AT.addD] using hcov : A.cov op = true ∨ B.cov op = true) with h | h
  · exact hA P cs pre op k regs vs ok h (askCtx_addD_left hc (by simp [h])) hev himp
  · exact hB P cs pre op k regs vs ok h (askCtx_addD_right hc (by simp [h])) hev himp

theorem atOk_addD (hA : ATOk impl X A κ inp w tr) (hB : ATImp impl X B κ inp w) :
    ATOk impl X (A.addD B) κ inp w tr :=
  ⟨atAsk_addD hA.1, atImp_addD hA.2 hB⟩

end AddD

/-! ## `bitTGB`'s classes are not imports -/

/-- `opOut`'s `selectHalf` is never an import. -/
theorem opOut_selectHalf_imp (P : Params) (cs : CS) (b x y : ℕ) : (opOut P cs (.selectHalf b x y)).imp = false := by
  simp only [opOut]
  split <;> (try split) <;> rfl

/-- At a `tensorW`, the extension's import flag does not depend on the template bodies. -/
theorem tplExt4_tw_imp (F : TFilt) (R : ShR) (tp tp' : Tpl.TKey → Tpl.Tpl) (cb : Tpl.TKey → ℕ → ℕ) (P : Params) (cs : CS)
    (j r : ℕ) :
    (tplExt4 F R ⟨tp, cb⟩ P cs (.tensorW j r)).map Out.imp =
      (tplExt4 F R ⟨tp', cb⟩ P cs (.tensorW j r)).map Out.imp := by
  have h1 : (tplExt4S F R ⟨tp, cb⟩ P cs (.tensorW j r)).map Out.imp =
      (tplExt4S F R ⟨tp', cb⟩ P cs (.tensorW j r)).map Out.imp := by
    simp only [tplExt4S, tplExtF, tplExt]
    rcases cs.slot r with _ | ⟨_ | _ | _ | _ | _ | n, lr⟩ <;> try rfl
    by_cases hn : n ≤ logNMax <;> simp [hn, Option.filter, tplOut]
    try (split <;> rfl)
  have h2 : (tplExtKM F ⟨tp, cb⟩ P cs (.tensorW j r)).map Out.imp =
      (tplExtKM F ⟨tp', cb⟩ P cs (.tensorW j r)).map Out.imp := by
    simp only [tplExtKM]
    rcases Circ.akS (cs.slotK r .L32) with _ | a <;> rcases Circ.akS (cs.slotK r .P30) with _ | b <;>
      rcases Circ.akS (cs.slotK r .N30) with _ | c <;> try rfl
    simp only
    split <;> rfl
  simp only [tplExt4, Ext.orElse]
  cases h : tplExt4S F R ⟨tp, cb⟩ P cs (.tensorW j r) <;>
    cases h' : tplExt4S F R ⟨tp', cb⟩ P cs (.tensorW j r) <;> rw [h, h'] at h1 <;>
    simp only [Option.map] at h1 <;> try (cases h1)
  · simp only [Option.orElse]; split
    · simp only [Ext.orElse, extGetK]
      cases h3 : tplExtKM F ⟨tp, cb⟩ P cs (.tensorW j r) <;>
        cases h4 : tplExtKM F ⟨tp', cb⟩ P cs (.tensorW j r) <;> rw [h3, h4] at h2 <;>
        simp_all [Option.orElse]
    · rfl
  · simp_all [Option.orElse]

/-- **At a `selectHalf` or a `tensorW`, the extension's import flag does not depend on the template
bodies** (the template-free context `trailMS` keys the memo with gives the compile's). -/
theorem tplExt4_imp_tc (F : TFilt) (R : ShR) (tc tc' : Tpl.TCtx) (hcb : tc.cb = tc'.cb) (P : Params) (cs : CS)
    (op : Op) (hop : bitCovB op = true) :
    (tplExt4 F R tc P cs op).map Out.imp = (tplExt4 F R tc' P cs op).map Out.imp := by
  cases op <;> simp only [bitCovB, reduceCtorEq] at hop
  · obtain ⟨tp, cb⟩ := tc; obtain ⟨tp', cb'⟩ := tc'; cases hcb
    exact tplExt4_tw_imp F R tp tp' cb P cs _ _
  · simp only [tplExt4, tplExt4S, Ext.orElse, tplExtKM, tplExtF, tplExt, extGetK, Option.orElse,
      Option.filter, Option.map]

/-- **`ATImp` of the bits' generator** (`bitTGB`, read off an extension `Xa` agreeing with the compile's
on the import flag of its ops): vacuous, since at a covered op the compile made an import its rows are
a failing row. -/
theorem atImp_bitB {impl : OpImpl} {X Xa : Ext} {π : ℕ} {T : BTab} {κ : Kind} {inp : Input} {w : Asg}
    (hX : ∀ P cs op, bitCovB op = true → (Xa P cs op).map Out.imp = (X P cs op).map Out.imp) :
    ATImp impl X (bitTGB Xa π T).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  have hr := hc.2.2.2
  have hcv : bitCovB op = true := hcov
  have hx := hX P cs op hcv
  cases op <;> simp only [bitCovB, reduceCtorEq] at hcv
  · rename_i j r
    have h1 : (stepOut Xa P cs (.tensorW j r)).imp = true := by
      simp only [stepOut] at himp ⊢
      cases hXo : X P cs (.tensorW j r) <;> cases hXa : Xa P cs (.tensorW j r) <;>
        simp_all [Option.getD]
    exact absurd (hr _ (by simp [TG.toAT, bitTGB, bitRowsB, h1])) (failRT_false hc.1)
  · rename_i b x y
    have h1 : ((Xa P cs (.selectHalf b x y)).map Out.imp).getD false = true := by
      rw [hx]; simp only [stepOut] at himp
      cases hXo : X P cs (.selectHalf b x y) with
      | none => rw [hXo] at himp; simp [opOut_selectHalf_imp] at himp
      | some o => rw [hXo] at himp; simpa using himp
    exact absurd (hr _ (by simp [TG.toAT, bitTGB, bitRowsB, h1])) (failRT_false hc.1)

/-! ## The node's template with the bits folded -/

/-- Prototype `π`'s compile extension with a template-free context (`bitTGB`'s). -/
def XofA (π : ℕ) : Ext := XofC π ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩

/-- Prototype `π`'s bit tables. -/
def bitTabP (π : ℕ) : BTab := bitTab (protoProg π).ops (if π = 0 then nodeGrp else segGrp)

theorem xofA_imp (π : ℕ) (P : Params) (cs : CS) (op : Op) (hop : bitCovB op = true) :
    (XofA π P cs op).map Out.imp = (Xof π P cs op).map Out.imp := by
  have hd : ∀ w col, op ≠ .dotKF w col := by rintro w col rfl; cases hop
  simp only [XofA, Xof, XofC]
  rw [tplExt4A_ne hd, tplExt4A_ne hd]
  exact tplExt4_imp_tc _ _ ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩ (protoLay π).ctx rfl P cs op hop

/-- **The node's template with the bits' generator** (the `askTG` edit's first step). -/
def withBitsB (Aq : ℕ → AT) (π : ℕ) : AT := (withImpc Aq π).addD (bitTGB (XofA π) π (bitTabP π)).toAT

/-- **`Gap4.imp` with the bits' generator folded**: ASK-T's `gap4Imp_of_askT` over `withBitsB askAq`.
`hfoldA` is the fold of the template it is stated over (IMPC2b's `FRNodeRun4BT` folds the statement
reads too, `askFold_bitsS`). -/
theorem gap4Imp_of_bitsB {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withBitsB askAq) κ v arR2, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunA (rt (protoOf κ v)) (withBitsB askAq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) :=
  gap4Imp_of_runS hT₀ hT hok (fun e tr => X.pfHdr_reassemble4 e tr)
    (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr) hfoldR hfoldA hS.1 fun v hv ι hι =>
    ⟨atOk_addD (atOk_add (atOk_add (atOk_add (atOk_askT _ hS.1 hv hι)
        (atImp_inp (inpCells_of_rows (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr)
          (fun e tr => X.pfHdr_reassemble4 e tr) hS.1 v hv ι hι)))
        (atImp_rsv_slot hS.2.1 hS.2.2 v ι _)) (atImp_impc (pfCells_of_rows hS.1 hv)))
      (atImp_bitB (xofA_imp _)), h v hv ι hι⟩

/-! ## Controls -/

namespace BitCtl

/-- A toy selector form (`one` cell 0, selectors cells 1–3). -/
def P0 : Params := ⟨Lin.cell 0, fun κ => Lin.cell (1 + selIx κ)⟩

/-- (+) `selRows`: kinds agreeing give one copy row, two classes one product row, three sources one
gated row per kind; (−) a kind without a source gives the failing row. -/
theorem selRows_ctl :
    (selRows P0 0 [] fun _ => some (some 3)).length = 1 ∧
    (selRows P0 0 [] fun ι => some (if ι = .P30 then none else some 3)).length = 1 ∧
    (selRows P0 0 [] fun ι => some (some (selIx ι))).length = 3 ∧
    selRows P0 0 [] (fun ι => if ι = .N30 then none else some none) = [failRT P0] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- A generator that refuses whatever it is asked (`impcTG`'s `pfRows` at a read that is not an
element), and one covering `piElem` with no rows. -/
def refuse : TG := ⟨fun _ => false, fun P _ _ _ _ => [failRT P]⟩
def covE : TG := ⟨fun op => match op with | .piElem .. => true | _ => false, fun _ _ _ _ _ => []⟩

/-- (+) **`addD` does not ask `A` at `B`'s ops**: at a `piElem` only `covE` covers, no row; at an ask
both are asked. (−) `add` asks both, so the refusal is a row. -/
theorem addD_ctl :
    (refuse.addD covE).rows P0 (CS.init 0) none (.piElem 0 0) 0 = [] ∧
    (refuse.addD covE).rows P0 (CS.init 0) none (.askSqueeze 0) 0 = [failRT P0] ∧
    (refuse.add covE).rows P0 (CS.init 0) none (.piElem 0 0) 0 = [failRT P0] := ⟨rfl, rfl, rfl⟩

end BitCtl

end N4s
end FR

end G6_FRNodeRows4AskBS

section G6_FRNodeRun4BL

-- New for `flock-recursive` (IMPC2 §7 step 3; track IMPC2b): the bit order of `F.ofBytes`, `natLE` and
-- `idxOfF`, the bit sources' values (`SrcV`, `StmtBits`, `PosBits`, `SrcOk`) and the register provenance
-- `riAcc` on the answer-driven run (`execA_ri`).

/-!
# Bit sources on the run

`FRNodeRows4AskB`'s bit rows tie an import or auxiliary cell to a *source* (`bitSrc`): a cell of the
bit area, or the constant zero. This module says what the sources hold and proves it on the run:

* **the bit order**: bit `j` of `F.ofBytes v` is bit `j % 8` of byte `j / 8` (`F.bit_ofBytes`); the
  same for `natLE` (`testBit_natLE`), so the halves `dlo`/`dhi` of a digest carry its bits `0 … 255`
  (`bit_dlo`, `bit_dhi`); bit `h` of `idxOfF b a i` is bit `i·b + h` of `natLE a` below `b`, else zero
  (`testBit_idxOfF`);
* **`SrcV`**: a source holds a bit (the cell is `Circ.bitF b`; the zero source only a false bit);
  **`StmtBits`** (the statement's cells hold its message bits, its tail is zero, byte 0 is the tag) and
  **`PosBits`** (an answer's cells hold its bits under the selected kind's map) are the two facts the
  decomposition rows give (`FRNodeRun4BS`);
* **`execA_ri`**: on the answer-driven run, every register's `riAcc` entry describes its value (an
  answer, an `idx` of an earlier register, a shift, a digest or byte read, a byte constant);
* **`srcOk_of`**: with `StmtBits` and `PosBits`, every bit source of a register holds the register's bit
  (`SrcOk`), on the run's final registers;
* **`selRows_ev`**: `selRows`' rows make the import cell the selected kind's source.
-/

namespace FR
open Circ RecursionFast Rev4

/-! ## Bit order -/

theorem testBit_ofLE' : ∀ (l : List UInt8) (m : ℕ), (ofLE l).testBit m = (l.getD (m / 8) 0).toNat.testBit (m % 8)
  | [], m => by simp [ofLE]
  | d :: l, m => by
    rw [ofLE_cons, show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.add_comm, Nat.testBit_two_pow_mul_add _ d.toNat_lt]
    by_cases hm : m < 8
    · simp [hm, Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
    · rw [if_neg hm, testBit_ofLE' l (m - 8), show m / 8 = (m - 8) / 8 + 1 by omega, List.getD_cons_succ,
        show (m - 8) % 8 = m % 8 by omega]

/-- **`natLE`'s bit order**: bit `m` is bit `m % 8` of byte `m / 8`. -/
theorem testBit_natLE (a : Digest) {m : ℕ} (hm : m < 256) :
    (natLE a).testBit m = (a[m / 8]'(by omega)).toNat.testBit (m % 8) := by
  rw [Read.natLE_eq_ofLE, testBit_ofLE', List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList]

theorem natLE_lt (a : Digest) : natLE a < 2 ^ 256 := by
  rw [Read.natLE_eq_ofLE]
  have := ofLE_lt a.toList
  simpa using this

theorem testBit_natLE_ge (a : Digest) {m : ℕ} (hm : 256 ≤ m) : (natLE a).testBit m = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (natLE_lt a) (Nat.pow_le_pow_right (by norm_num) hm))

theorem B64.toBytes_get (a : B64) {k : ℕ} (hk : k < 8) : (a.toBytes[k]).toNat = a.val.toNat / 2 ^ (8 * k) % 256 := by
  interval_cases k <;> simp [B64.toBytes, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem B64.testBit_val (a : B64) {j : ℕ} (hj : j < 64) :
    a.val.toNat.testBit j = (a.toBytes[j / 8]'(by omega)).toNat.testBit (j % 8) := by
  rw [B64.toBytes_get a (by omega), show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, decide_eq_true (Nat.mod_lt _ (by norm_num)), Bool.true_and]
  congr 1; omega

theorem F.bit_toBytes (x : F) {j : ℕ} (hj : j < 128) :
    x.bit j = (x.toBytes[j / 8]'(by omega)).toNat.testBit (j % 8) := by
  unfold F.bit F.toBytes
  by_cases h : j < 64
  · rw [if_pos h, B64.testBit_val _ h, Vector.getElem_append_left (by omega)]
  · rw [if_neg h, B64.testBit_val _ (by omega), Vector.getElem_append_right (by omega) (by omega)]
    have e : ∀ a b (ha : a < 8) (hb : b < 8), a = b → x.c₁.toBytes[a] = x.c₁.toBytes[b] := by
      rintro _ _ _ _ rfl; rfl
    rw [e _ _ _ (by omega) (show (j - 64) / 8 = j / 8 - 8 by omega), show (j - 64) % 8 = j % 8 by omega]

/-- **`F.ofBytes`' bit order**: bit `j` is bit `j % 8` of byte `j / 8`. -/
theorem F.bit_ofBytes (v : Vector UInt8 16) {j : ℕ} (hj : j < 128) :
    (F.ofBytes v).bit j = (v[j / 8]'(by omega)).toNat.testBit (j % 8) := by
  rw [F.bit_toBytes _ hj, F.toBytes_ofBytes]

theorem bit_dlo (x : Digest) {j : ℕ} (hj : j < 128) : (dlo x).bit j = (natLE x).testBit j := by
  rw [dlo, F.bit_ofBytes _ hj, testBit_natLE _ (by omega), Vector.getElem_ofFn]

theorem bit_dhi (x : Digest) {j : ℕ} (hj : j < 128) : (dhi x).bit j = (natLE x).testBit (128 + j) := by
  rw [dhi, F.bit_ofBytes _ hj, testBit_natLE _ (by omega), Vector.getElem_ofFn]
  have e : ∀ a b (ha : a < 32) (hb : b < 32), a = b → x[a] = x[b] := by rintro _ _ _ _ rfl; rfl
  rw [e _ _ (by omega) (by omega) (show 16 + j / 8 = (128 + j) / 8 by omega), show j % 8 = (128 + j) % 8 by omega]

/-- **`idxOfF`'s bits**: bit `h` is bit `i·b + h` of `natLE a` below `b`, zero above. -/
theorem testBit_idxOfF (b : ℕ) (a : Digest) (i h : ℕ) :
    (idxOfF b a i).testBit h = (decide (h < b) && (natLE a).testBit (i * b + h)) := by
  rw [idxOfF_eq, idxOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm h]

theorem B64.eq_of_testBit {a b : B64} (h : ∀ j < 64, a.val.toNat.testBit j = b.val.toNat.testBit j) : a = b := by
  obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
  congr 1
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 64
  · exact h j hj
  · have hp : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.toNat_lt hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le b.toNat_lt hp)]

/-- **An `F` element is its bits.** -/
theorem F.eq_of_bit {x y : F} (h : ∀ j < 128, x.bit j = y.bit j) : x = y := by
  obtain ⟨x₀, x₁⟩ := x; obtain ⟨y₀, y₁⟩ := y
  have h0 := fun j (hj : j < 64) => by simpa [F.bit, hj] using h j (by omega)
  have h1 := fun j (hj : j < 64) => by simpa [F.bit, show ¬ j + 64 < 64 by omega] using h (j + 64) (by omega)
  rw [B64.eq_of_testBit h0, B64.eq_of_testBit h1]

namespace N4s

/-! ## Sources and their values -/

/-- A source's value: its bit cell, or zero. -/
def srcVal (w : Asg) (π : ℕ) : Option ℕ → F
  | some c => w (bitC π c)
  | none => 0

/-- **A source holds bit `b`**: the cell is `Circ.bitF b`; the zero source holds only a false bit. -/
def SrcV (w : Asg) (π : ℕ) : Option ℕ → Bool → Prop
  | some c, b => w (bitC π c) = Circ.bitF b
  | none, b => b = false

theorem srcVal_of_srcV {w : Asg} {π : ℕ} {x : Option ℕ} {b : Bool} (h : SrcV w π x b) : srcVal w π x = Circ.bitF b := by
  cases x
  · simp only [SrcV] at h; subst h; rfl
  · exact h

/-- Bit `b` of the statement message (bit `b % 8` of its byte `b / 8`, in the proof `q`). -/
def stBit (T : BTab) (q : ByteArray) (b : ℕ) : Bool :=
  match T.st with
  | some s => (byteAt q (s.so + b / 8)).toNat.testBit (b % 8)
  | none => false

/-- **The statement's bits**: its tag byte, and every bit `stCell` places (a cell, or the zero tail). -/
def StmtBits (T : BTab) (w : Asg) (π : ℕ) (q : ByteArray) : Prop :=
  (∀ s, T.st = some s → byteAt q s.so = s.t) ∧ ∀ b x, T.stCell b = some x → SrcV w π x (stBit T q b)

/-- **The answers' bits** at kind `ι`: a cell `ansCell ι k j` holds bit `j` of entry `k`'s answer. -/
def PosBits (T : BTab) (w : Asg) (π : ℕ) (ι : Kind) (tr : Trace) : Prop :=
  ∀ k j x e, T.ansCell ι k j = some x → tr[k]? = some e → w (bitC π x) = Circ.bitF ((natLE e.2).testBit j)

/-- **Every bit source of a register holds the register's bit** (on the registers `regs`). -/
def SrcOk (T : BTab) (w : Asg) (π : ℕ) (ι : Kind) (regs : Array Val) : Prop :=
  ∀ r h x, T.bitSrc r h ι = some x → SrcV w π x ((rd regs r).toN.testBit h)

/-! ## Register provenance on the run -/

/-- **What an `RI` entry says of a register's value** `v` (`regs` the run's final registers). -/
def RIV (ι : Kind) (inp : Input) (tr : Trace) (regs : Array Val) : RI → Val → Prop
  | .none, _ => True
  | .ans k, v => ∃ e, tr[k]? = some e ∧ v = .d e.2
  | .idx a b i, v => v = .n (idxOfF (b ι) (rd regs (a ι)).toD (i ι))
  | .shr n s, v => v = .n ((rd regs n).toN >>> s ι)
  | .dig o, v => v = .d (digestAt inp.π o)
  | .pf o len, v => v = .b (inp.π.extract o (o + len))
  | .cb bs, v => v = .b bs

theorem riOf_len {impl : OpImpl} {ι : Kind} {inp : Input} {regs : Array Val} {op : Op} {vs : List Val}
    {ok : Bool} (hv : evalOp impl ι inp regs op = .vals vs ok) (k n : ℕ) : (riOf k n op).length = vs.length := by
  rw [evalOp_len hv]
  have hi := vals_item' hv
  unfold riOf
  rw [if_neg (by simp [hi])]
  cases op <;> simp only [List.length_replicate] <;> (try split) <;> (try split) <;> rfl

theorem rd_prefix {a more : Array Val} {i : ℕ} (h : i < a.size) : rd (a ++ more) i = rd a i := by
  simp [rd, Array.getElem?_append_left h]

theorem riV_none {ι : Kind} {inp : Input} {tr : Trace} {regs : Array Val} {l : List RI} (hl : ∀ x ∈ l, x = .none)
    (j : ℕ) (v : Val) : RIV ι inp tr regs (l.getD j .none) v := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => trivial
  | some x => rw [hl x (List.mem_of_getElem? h)]; trivial

theorem riOf_ok {impl : OpImpl} {ι : Kind} {inp : Input} {tr : Trace} {regs more : Array Val} {op : Op}
    {vs : List Val} {ok : Bool} (hv : evalOp impl ι inp regs op = .vals vs ok) (k : ℕ) {j : ℕ}
    (hj : j < vs.length) :
    RIV ι inp tr (regs ++ vs.toArray ++ more) ((riOf k regs.size op).getD j .none) (vs[j]'hj) := by
  have hi := vals_item' hv
  have hrd : ∀ i < regs.size, rd (regs ++ vs.toArray ++ more) i = rd regs i := fun i h => by
    rw [Array.append_assoc, rd_prefix h]
  cases op
  case idx a b i =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [riOf, Op.item?, Option.isSome_none, Bool.false_eq_true, if_false]
    split_ifs with hg
    · simp only [List.getD_cons_zero, RIV, List.getElem_cons_zero]
      rw [hrd _ (by cases ι <;> simp_all)]
    · exact riV_none (by simp) _ _
  case shrN m s =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [riOf, Op.item?, Option.isSome_none, Bool.false_eq_true, if_false]
    split_ifs with hg
    · simp only [List.getD_cons_zero, RIV, List.getElem_cons_zero]
      rw [hrd _ hg]
    · exact riV_none (by simp) _ _
  case piDigest f o =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp [riOf, Op.item?, RIV]
  case piField f o len =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp [riOf, Op.item?, RIV]
  case const c =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [riOf, Op.item?, Option.isSome_none, Bool.false_eq_true, if_false, List.getElem_cons_zero]
    split
    · rename_i x y z hx hy hz
      split_ifs with he
      · obtain ⟨rfl, rfl⟩ := he
        simp only [List.getD_cons_zero, RIV]
        cases ι <;> assumption
      · exact riV_none (by simp) _ _
    · exact riV_none (by simp) _ _
  all_goals (rw [riOf, if_neg (by simp [hi])] <;> first | exact riV_none (by simp) _ _ | simp)

/-- **Register provenance along the answer-driven run** (`riAcc`, from ask `k` of `tr`): every entry
describes its register's value on the run's final registers. -/
theorem execA_ri {impl : OpImpl} {ι : Kind} {inp : Input} {tr : Trace} {s' : St} {tr' : Trace} :
    ∀ (ops : List Op) (k : ℕ) (acc : Array RI) (s : St),
    execA impl ι inp ops s (tr.drop k) = some (s', tr') → acc.size = s.regs.size →
    (∀ r, RIV ι inp tr s'.regs (acc.getD r .none) (rd s'.regs r)) →
    ∀ r, RIV ι inp tr s'.regs ((riAcc k ops acc).getD r .none) (rd s'.regs r)
  | [], k, acc, s, he, _, h => by simpa [riAcc] using h
  | op :: ops, k, acc, s, he, hsz, h => by
    simp only [riAcc]
    simp only [execA] at he
    split at he
    · next vs ok hv =>
      have hi : op.item?.isSome = false := vals_item' hv
      rw [if_neg (by simp [hi])]
      obtain ⟨more, hm⟩ := execA_prefix ops _ _ he
      refine execA_ri ops k _ _ he (by simp [hsz, riOf_len hv]) fun r => ?_
      by_cases hr : r < acc.size
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hr, ← Array.getD_eq_getD_getElem?]
        exact h r
      · by_cases hr2 : r < acc.size + (riOf k acc.size op).length
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by omega)]
          have hj : r - acc.size < vs.length := by rw [← riOf_len hv k acc.size]; omega
          have hrd : rd s'.regs r = vs[r - acc.size] := by
            rw [hm, rd]; simp only at hm ⊢
            rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_right (by omega)]
            rw [List.getElem?_toArray, ← hsz, List.getElem?_eq_getElem hj]; rfl
          rw [hrd]
          have := riOf_ok (tr := tr) (more := more) hv k hj
          rw [← hsz] at this
          simpa [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?] using
            (show RIV ι inp tr s'.regs ((riOf k acc.size op).getD (r - acc.size) .none) vs[r - acc.size] by
              rw [hm]; simpa [hsz] using this)
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
          trivial
    · next q hq =>
      have hi := ask_item hq
      rw [if_pos hi]
      rcases htr : tr.drop k with _ | ⟨⟨q', a⟩, tr0⟩
      · rw [htr] at he; cases he
      rw [htr] at he
      have hk : tr[k]? = some (q', a) := by
        have := congrArg List.head? htr
        rwa [List.head?_drop, List.head?_cons] at this
      have htr0 : tr0 = tr.drop (k + 1) := by
        rw [← List.drop_drop, htr]; rfl
      rw [htr0] at he
      obtain ⟨more, hm⟩ := execA_prefix ops _ _ he
      have hro : riOf k acc.size op = [.ans k] := by simp [riOf, hi]
      rw [hro]
      refine execA_ri ops (k + 1) _ _ he (by simp [hsz]) fun r => ?_
      by_cases hr : r < acc.size
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hr, ← Array.getD_eq_getD_getElem?]
        exact h r
      · by_cases hr2 : r = acc.size
        · subst hr2
          rw [show (acc ++ [RI.ans k].toArray).getD acc.size RI.none = RI.ans k by
            simp [Array.getD_eq_getD_getElem?]]
          refine ⟨(q', a), hk, ?_⟩
          rw [hm, rd]
          show ((s.regs.push (Val.d a)) ++ more)[acc.size]?.getD default = _
          rw [Array.getElem?_append_left (by simp; omega), hsz, Array.getElem?_push_eq]; rfl
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
          trivial

/-! ## The sources hold the registers' bits -/

theorem srcV_stBit {T : BTab} {w : Asg} {π : ℕ} {q : ByteArray} (hS : StmtBits T w π q) {s : StSpec}
    (hs : T.st = some s) {o j : ℕ} (hso : s.so ≤ o) (hj : j < 256) {x : Option ℕ}
    (hx : T.stCell (8 * (o - s.so) + j) = some x) :
    SrcV w π x ((natLE (digestAt q o)).testBit j) := by
  have h := hS.2 _ _ hx
  simp only [stBit, hs] at h
  rw [testBit_natLE _ hj, digestAt_eq]
  simp only [bytesAt, Vector.getElem_ofFn]
  rwa [show s.so + (8 * (o - s.so) + j) / 8 = o + j / 8 by omega, show (8 * (o - s.so) + j) % 8 = j % 8 by omega] at h

theorem idxSrc_ok {T : BTab} {w : Asg} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace} {regs : Array Val}
    (hri : ∀ r, RIV ι inp tr regs (T.rt.getD r .none) (rd regs r)) (hS : StmtBits T w π inp.π)
    (hP : PosBits T w π ι tr) {a b i : KC ℕ} {h : ℕ} {x : Option ℕ} (hx : T.idxSrc a b i h ι = some x) :
    SrcV w π x ((idxOfF (b ι) (rd regs (a ι)).toD (i ι)).testBit h) := by
  unfold BTab.idxSrc at hx
  rw [testBit_idxOfF]
  split_ifs at hx with h24 hh
  · have hra := hri (a ι)
    split at hx
    · rename_i k hk
      rw [hk] at hra
      obtain ⟨e, he, hv⟩ := hra
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [hv, Val.toD, decide_eq_true hh, Bool.true_and]
      exact hP k _ c e hc he
    · rename_i o ho
      rw [ho] at hra
      split at hx
      · rename_i s hs
        split_ifs at hx with hg
        rw [hra, Val.toD, decide_eq_true hh, Bool.true_and]
        refine srcV_stBit hS hs hg.1 hg.2 ?_
        rwa [Nat.add_assoc] at hx
      · cases hx
    · cases hx
  · cases hx
    simp [SrcV, hh]

/-- **The sources hold the bits** (`SrcOk`) on registers whose provenance `riAcc` describes, given the
statement's and the answers' bits. -/
theorem srcOk_of {T : BTab} {w : Asg} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace} {regs : Array Val}
    (hri : ∀ r, RIV ι inp tr regs (T.rt.getD r .none) (rd regs r)) (hS : StmtBits T w π inp.π)
    (hP : PosBits T w π ι tr) : SrcOk T w π ι regs := by
  intro r h x hx
  unfold BTab.bitSrc at hx
  have hr := hri r
  split at hx
  · rename_i a b i hrr
    rw [hrr] at hr
    rw [show rd regs r = _ from hr, Val.toN]
    exact idxSrc_ok hri hS hP hx
  · rename_i n s hrr
    rw [hrr] at hr
    split at hx
    · rename_i a b i hn
      have hrn := hri n
      rw [hn] at hrn
      rw [show rd regs r = _ from hr, Val.toN, Nat.testBit_shiftRight, show rd regs n = _ from hrn, Val.toN,
        Nat.add_comm (s ι)]
      exact idxSrc_ok hri hS hP hx
    · cases hx
  · cases hx

/-! ## `selRows` -/

theorem ev_subN (w : Asg) (a b : Lin) : (subN a b).ev w = a.ev w - b.ev w := by
  simp only [subN, Lin.ev_append, sub_eq_add_neg]
  congr 1
  induction b with
  | nil => simp
  | cons t b ih => simp only [List.map_cons, Lin.ev_cons, ih, neg_add]; ring

theorem srcLin_ev (w : Asg) (π : ℕ) (x : Option ℕ) : (srcLin π x).ev w = srcVal w π x := by
  cases x <;> simp [srcLin, srcVal]

theorem gateS_ev {w : Asg} {P : Params} {ι : Kind} (hP : SelOk w P ι) (act : KC Bool) :
    (gateS P act).ev w = Circ.bitF (act ι) := by
  have hs := hP.2
  simp only [gateS, kinds, List.flatMap_cons, List.flatMap_nil, List.append_nil, Lin.ev_append]
  cases ι <;> cases h1 : act .L32 <;> cases h2 : act .P30 <;> cases h3 : act .N30 <;>
    simp [hs, h1, h2, h3, Circ.bitF]

/-- **`selRows`' rows make `imp` the selected kind's source.** -/
theorem selRows_ev {P : Params} {w : Asg} {ι : Kind} (hP : SelOk w P ι) {π : ℕ} {imp : Lin}
    {src : KC (Option (Option ℕ))} (h : ∀ r ∈ selRows P π imp src, r.Holds w) :
    ∃ x, src ι = some x ∧ imp.ev w = srcVal w π x := by
  unfold selRows at h
  split at h
  · rename_i a b c ha hb hc
    have hone := hP.1
    have hsrc : ∀ κ, src κ = some (match κ with | .L32 => a | .P30 => b | .N30 => c) := fun κ => by
      cases κ <;> assumption
    refine ⟨_, hsrc ι, ?_⟩
    split at h
    · rename_i h1
      have := h _ List.mem_cons_self
      simp only [Row.Holds, hone, one_mul, ev_subN, Lin.ev_nil, srcLin_ev] at this
      rw [sub_eq_zero.1 this]
      obtain ⟨rfl, rfl⟩ := h1
      cases ι <;> rfl
    · rename_i h1
      split at h
      · rename_i h2
        have := h _ List.mem_cons_self
        simp only [Row.Holds, gateS_ev hP, ev_subN, srcLin_ev] at this
        have key : ∀ (g : Bool) (A O : F), Circ.bitF g * (A - O) = imp.ev w - O → imp.ev w = if g then A else O := by
          intro g A O e; cases g
          · simp only [Circ.bitF, Bool.false_eq_true, if_false, zero_mul] at e ⊢; exact (sub_eq_zero.1 e.symm)
          · simp only [Circ.bitF, if_true, one_mul] at e ⊢; exact (sub_left_inj.1 e).symm
        have e := key _ _ _ this
        cases ι <;> simp only at e ⊢ <;> rw [e] <;> by_cases hba : b = a <;> by_cases hca : c = a <;> simp_all
      · have := h _ (List.mem_map.2 ⟨ι, by cases ι <;> simp [kinds], rfl⟩)
        simp only [Row.Holds, hP.2, if_true, one_mul, ev_subN, Lin.ev_nil, srcLin_ev] at this
        rw [sub_eq_zero.1 this]
        cases ι <;> rfl
  · exact absurd (h _ List.mem_cons_self) (failRT_not hP.1)

end N4s
end FR

end G6_FRNodeRun4BL
