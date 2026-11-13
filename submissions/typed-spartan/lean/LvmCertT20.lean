-- New for lvm2 (roll 8 = B1, wave L, L-W): the typed certificate at `P20`. The certificate of `subG staticOkB20
-- (VST P20 NT20)` (`LvmSubmissionST.submissionB20`) in roll 7's shape (guard, open obligations, `kcertSJ`):
-- the guard's facts (`sf20`), `THyp` of the typed instance `Ti20 = NT20.inst QB20 layT20`, `kcertSJ`
-- through `midSpecR_T₂`/`midShape_T₂` (`LvmTypedSpec`), `NodeSound` on `GoodT` (L-D), the refinement of
-- `VST P20 NT20` to `typedProg` (L-C), the extractor (`extJ`, `ext_eq_gen`, unchanged).
import LvmCertT
import LvmCertTHyp
import LvmTypedVEqTop
import LvmNodeSoundT20B

/-!
# The typed certificate at `P20`

* **`Ti20`**, **`SF20`** (`LvmCertTInst`): the typed instance and the guard's facts at `P20`.
* **`thyp20 S`**: `THyp Ti20` from the guard's facts `S` (the layout's word `1`, the region maps' fit, `acc_in`'s
  43 coordinates, the mini-bus's table facts, the error terms).
* **`openT20 S`**: the open obligations `OpenS VSB20 (EX (accV VSB20))`: `mid := midT₂ Ti20`, `Good := Good₂
  (GoodT Ti20 H)`, `hmid := midSpecR_T₂ H`, `hsh := midShape_T₂ H`, `child := childS`, `hnode := nodeSoundT₂ H ∘
  nodeT20 S H` (L-D), `refines := refinesT20 S H` (L-C), `ext_eq := ext_eqV … (midFollowsT20 S H)` (L-C).
* **`certificateT20`**: the certificate of `submissionB20` (`certificateR_guardV`; with the guard off `V_S`
  rejects every `S` proof).

`THyp`'s glue is proved (`LvmCertTHyp`); `refinesT20`, `midFollowsT20` are L-C's `LvmTypedVEqTop.refinesT20L`,
`midFollowsT20L`; `nodeT20` is L-D's `LvmNodeSoundT20B.nodeT20B` (with L-H's typed HAR `harithT20`).
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open Lvm.VEq (pubX)
open scoped NNReal ENNReal

/-! ## `THyp` at `P20` -/

/-- The layout's word `1` lies in the `1` region (`TInst.Ok`'s second half), from the guard's `oneOkB`. -/
theorem one20 (h : Lvm.T.oneOkB layT20 = true) : Ti20.src? layT20.one = some .one :=
  src_one_of NT20 QB20 layT20 h

/-- **The region maps land in the commitments** at `lay26` (`NT20.okB`, `NT20`'s regions are the layout's). -/
theorem maps20 (S : SF20) : Ti20.MapsFit lay26 :=
  mapsFit_inst NT20 QB20 layT20 S.hlayOk (by
    have h := S.regs
    rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, p20_facts.1, p20_facts.2.1] at h)

/-- `acc_in` has `phiVars = 43` coordinates on every statement (`accVars = 43`). -/
theorem acc20 : ∀ x, (pubX x).accIn.pt.length = phiVars := accLen

/-- **The mini-bus's table facts at `P20`** (`THyp`'s `hτ` … `μBus`, as roll 7's `MidHyp` on the bus tables). -/
structure MbHyp20 : Prop where
  hτ : ∀ t ∈ mbT20, t.τ ≤ lay26.μ
  sc : AllSc mbT20
  layOk : LayOk lay26 mbT20
  keys : KeysOk mbT20
  width : ∀ t ∈ mbT20, 0 < t.w
  fix : FixOk mbT20
  widths : (mbT20.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ mbT20, t.τ ≤ lay26.μ), (inst lay26 mbT20 h).μBus = miniDepth

/-- **The mini-bus's table facts hold at `P20`**: the shape of `mbT` (`tabsOkB`, `FixOk`, a `C_main` column per
table) and the guard's `fitsMiniB` (heights, `LayOk`, depth `13`, `936` evaluations). -/
theorem mbHyp20 (S : SF20) : MbHyp20 := by
  have hm : TypedV.fitsMiniB P20 mbT20 = true := S.mini
  unfold TypedV.fitsMiniB at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hf⟩, hg⟩, hh⟩, -⟩ := hm
  have ht : Lvm.M3.tabsOkB mbT20 = true := tabsOkB_mbT _ _ _ _
  have hsc : AllSc mbT20 := Lvm.M3.allSc_of_B ht
  have hsum : Lvm.M3.sumcheckTabs mbT20 = mbT20 := sc_all _ hsc
  refine ⟨hτ_of_hi (com_mbT _ _ _ _ fun _ ↦ rfl) hh, hsc, layOk_of_fit ⟨p20_facts.1, p20_facts.2.1⟩ hg,
    Lvm.M3.keys_of_B ht, Lvm.M3.width_pos_of_B ht, fixOk_mbT _ _ _ _, ?_, fun h ↦ ?_⟩
  · rw [hsum] at hf
    rw [← hf, p20_facts.2.2.2]
    norm_num
  · have e : (inst lay26 mbT20 h).μBus = P20.busDepth := by
      rw [LeanVM.Protocol.M3Instance.μBus, Lvm.VEq.pushLeaves_inst, hb, Lvm.VEq.log2Ceil_eq_clog,
        Lvm.M3.pushLeavesR, hsum]
    rw [e, p20_facts.2.2.1]

/-- **The typed phases' error terms at `P20`** (`L₀ = 37,696`, against `εS`, follower `LkSJ`): the mini-bus has
depth `13` and no constraints (`B = 0`). -/
theorem errs20 (S : SF20) (h : ∀ t ∈ mbT20, t.τ ≤ lay26.μ) : TErrs 37696 (inst lay26 mbT20 h) εS LkSJ :=
  errs_at _ ((mbHyp20 S).μBus h)
    (Nat.le_zero.mp ((B_inst_le lay26 mbT20 h).trans (cons_mbT _ _ _ _).le))

/-- **`THyp` of the typed instance at `P20`** from the guard's facts. -/
theorem thyp20 (S : SF20) : THyp Ti20 where
  ok := ⟨S.hlay, one20 S.one⟩
  maps := maps20 S
  acc := acc20
  hτ := (mbHyp20 S).hτ
  sc := (mbHyp20 S).sc
  layOk := (mbHyp20 S).layOk
  keys := (mbHyp20 S).keys
  width := (mbHyp20 S).width
  fix := (mbHyp20 S).fix
  widths := (mbHyp20 S).widths
  μBus := (mbHyp20 S).μBus
  errs := errs20 S

/-! ## The other WPs' obligations (`nodeT20`: L-D's; the refinement: L-C's) -/

/-- **O10, typed: `NodeSound` on `GoodT`** (the arithmetisation's soundness of the B program: `typed_sound` with
`Inputs` on the virtual regions, QLT's constants `S.cst`, `hwf`/`hlay`/`hinj` from `S`, the mini-bus's `ReaddOk`;
then roll 7's Q_link, Q_sig and Q_arith on any memory with `Holds`). Owner **L-D**. -/
theorem nodeT20 (S : SF20) (H : THyp Ti20) (vk : RecursionFast.Digest) :
    NodeSound VSB20 vk (GoodT Ti20 H) Lvm.NS.childS :=
  Lvm.NS.nodeT20B S H vk S.chk

/-- **O5b, typed: `VST P20 NT20` refines the compiled verifier of the typed middle phases** (L-C's `refines_VST`:
`decideFT` read for read against `midT₂ Ti20`, `PhiQC_eq` through `S.cache`, then roll 7's tail). -/
theorem refinesT20 (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWith (midT₂ Ti20))).V c π).runLog L = some true :=
  Lvm.VEq.refinesT20L S H

/-- **The typed middle phases follow the schedule** (L-C's `midFollows_T`, against the typed `phases P20`). -/
theorem midFollowsT20 (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  Lvm.VEq.midFollowsT20L S H

/-! ## The open obligations and the certificate -/

/-- **The open obligations of the typed submission** from the guard's facts. -/
noncomputable def openT20 (S : SF20) : OpenS VSB20 (Lvm.X.EX (accV VSB20)) :=
  have H := thyp20 S
  { mid := midT₂ Ti20
    Good := Shape.Good₂ (GoodT Ti20 H)
    Lm := εS
    hmid := midSpecR_T₂ H
    hLm := le_rfl
    hsh := midShape_T₂ H
    child := Lvm.NS.childS
    hnode := fun vk ↦ nodeSoundT₂ H (nodeT20 S H vk)
    refines := refinesT20 S H
    ext_eq := fun vk L c π _ _ hμ hv ↦
      ext_eqV (midSpecR_T₂ H) le_rfl (midShape_T₂ H) (fun vk ↦ nodeSoundT₂ H (nodeT20 S H vk)) (fun _ ↦ rfl)
        (midFollowsT20 S H) vk L c π hμ hv }

/-- **The certificate of the typed submission** against the declared claim. -/
theorem certificateT20 :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionB20 :=
  certificateR_guardV VSB20 (hq_VST20 NT20) fun h ↦ openT20 (sf20 h)

end Lvm.CT
