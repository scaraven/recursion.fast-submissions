-- New for `flock-recursive` (IMPC2 §6–§7; track IMPC2): the bit generator's composition with the
-- node's ask template (`AT.addD`), `ATImp` of its bit classes, and `Gap4.imp` with it folded.
import FRNodeRun4AskT
import FRNodeRows4AskB

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
