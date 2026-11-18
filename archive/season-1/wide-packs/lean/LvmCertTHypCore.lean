-- Moved out of `LvmCertF20Inst` (lvm2 U-TAPE, UT-L, 2026-11-16; text unchanged): the instance facts every typed stage
-- shares (`THypCore`) and their derivation from the guard's static facts, so that S2GU's certificate need not import
-- S2GF's.
import LvmCertM20
import LvmE2QNodeG

/-!
# The typed instance's shared facts

* **`THypCore Ti`**: the fields `THypX` and `THypT` share; **`thypCore_ofS`** from the guard's static facts,
  **`thypCore_of`** from `NodeGC`.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.E2Q
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **The fields `THypX` and `THypT` share** (the instance's shape, the mini-bus's tables, their bus). -/
structure THypCore (Ti : TInst) : Prop where
  ok : Ti.Ok
  maps : Ti.MapsFit lay26
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ
  sc : AllSc Ti.mbT
  layOk : LayOk lay26 Ti.mbT
  keys : KeysOk Ti.mbT
  width : ∀ t ∈ Ti.mbT, 0 < t.w
  fix : FixOk Ti.mbT
  widths : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = miniDepth
  B0 : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).B = 0

/-- **`THypCore` of a stage's typed instance** `N.instL pl Q tl` from the guard's facts (`thyp20`'s proof at
`mbTOf C F`), at a stage with `P20`'s `ν`, mini-bus depth and evaluations. -/
theorem thypCore_ofS {C : Lvm.QAsm.QCfg} {F : TFrz} {Q : Lvm.Loop.Program} {tl : Lay} {N : TypedV.TNat}
    (st : StaticFactsTX C F Q tl N) (hmb0 : N.mbT = mbTOf C F) (pl : Pub → List FK) (hone : Lvm.T.oneOkB tl = true)
    (hC : C.p.nuMain = 23 ∧ C.p.nuRec = 19 ∧ C.p.busDepth = 12 ∧ C.p.tableEvals = 633) :
    THypCore (N.instL pl Q tl) := by
  have hmb : (N.instL pl Q tl).mbT = mbTOf C F := hmb0
  have hm : TypedV.fitsMiniB C.p (mbTOf C F) = true := hmb ▸ st.mini
  unfold TypedV.fitsMiniB at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hf⟩, hg⟩, hh⟩, -⟩ := hm
  have ht : Lvm.M3.tabsOkB (mbTOf C F) = true := tabsOkB_mbT _ _ _ _
  have hsc : AllSc (mbTOf C F) := Lvm.M3.allSc_of_B ht
  have hsum : Lvm.M3.sumcheckTabs (mbTOf C F) = mbTOf C F := sc_all _ hsc
  have hτ : ∀ t ∈ (N.instL pl Q tl).mbT, t.τ ≤ lay26.μ := hmb ▸ hτ_of_hi (com_mbT _ _ _ _ fun _ ↦ rfl) hh
  have hμ : ∀ (h : ∀ t ∈ (N.instL pl Q tl).mbT, t.τ ≤ lay26.μ), (inst lay26 (N.instL pl Q tl).mbT h).μBus =
      miniDepth := fun h ↦ by
    have e : (inst lay26 (N.instL pl Q tl).mbT h).μBus = C.p.busDepth := by
      rw [LeanVM.Protocol.M3Instance.μBus, Lvm.VEq.pushLeaves_inst, hmb, hb, Lvm.VEq.log2Ceil_eq_clog,
        Lvm.M3.pushLeavesR, hsum]
    rw [e, hC.2.2.1]
  exact
    { ok := ⟨st.hlay, src_one_of N Q tl hone⟩
      maps := mapsFit_inst N Q tl st.hlayOk (by
        have h := st.regs
        rwa [hC.1, hC.2.1] at h)
      hτ := hτ
      sc := hmb ▸ hsc
      layOk := hmb ▸ layOk_of_fit ⟨hC.1, hC.2.1⟩ hg
      keys := hmb ▸ Lvm.M3.keys_of_B ht
      width := hmb ▸ Lvm.M3.width_pos_of_B ht
      fix := hmb ▸ fixOk_mbT _ _ _ _
      widths := by
        rw [hmb]
        rw [hsum] at hf
        rw [← hf, hC.2.2.2]
        norm_num
      μBus := hμ
      B0 := fun h ↦ Nat.le_zero.mp ((B_inst_le lay26 (N.instL pl Q tl).mbT h).trans
        (by rw [hmb]; exact (cons_mbT _ _ _ _).le)) }

set_option maxRecDepth 100000 in
/-- **`THypCore` of a stage's typed instance** from the guard's `NodeGC` (`thypCore_ofS` on its static facts). -/
theorem thypCore_of {C : Lvm.QAsm.QCfg} {B nPub : ℕ} {F : TFrz} {Q : Lvm.Loop.Program} {tl : Lay} {N : TypedV.TNat}
    (S : NodeGC C B nPub F Q tl N) (pl : Pub → List FK) (hone : Lvm.T.oneOkB tl = true)
    (hC : C.p.nuMain = 23 ∧ C.p.nuRec = 19 ∧ C.p.busDepth = 12 ∧ C.p.tableEvals = 633) :
    THypCore (N.instL pl Q tl) :=
  thypCore_ofS S.st S.mb pl hone hC

end Lvm.CT
