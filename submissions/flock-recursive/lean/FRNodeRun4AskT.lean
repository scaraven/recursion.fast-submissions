-- New for `flock-recursive` (IMP-RESULT §5 item 2; SRA-RESULT §1.1; track ASK-T): `Gap4.imp` with the
-- ask templates discharged — what remains per active slot is `SlotRunA` alone.
import FRNodeRows4AskTS
import FRNodeRows4AskIS

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

/-- **Today's fold** (ASK-T's asks, `input`, the reserve, IMPC's import classes):
`askIRows4 (withImpc askAq) κ v arR2 ⊆ nodeIRows4 κ`. -/
theorem askFold_askT {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withImpc askAq) κ v arR2, p ∈ nodeIRows4 κ :=
  askFold (fun π _ => ⟨rfl, rfl⟩) hone hE

/-- **`Gap4.imp` with the asks discharged** (and IMPC's import classes, `input`, the reserve): from the
replay (`RepOk`, its fold), `StmtN4R` and, at every active slot and selectable index, `SlotRunA` (the
auxiliary cells, the residual imports, the foreign flags on the answer-driven run), every active slot's
`SlotImp`. -/
theorem gap4Imp_of_askT {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunA (rt (protoOf κ v)) (withImpc askAq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) := by
  have hone := one_of_pubCells hS.1.2.2.2.2
  exact gap4Imp_of_impc hT₀ hT hok (fun e tr => X.pfHdr_reassemble4 e tr)
    (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr) hfoldR (askFold_askT hone hS.1.2.2.2.1) hS
    fun v hv ι hι => ⟨atOk_askT _ hS.1 hv hι, h v hv ι hι⟩

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
