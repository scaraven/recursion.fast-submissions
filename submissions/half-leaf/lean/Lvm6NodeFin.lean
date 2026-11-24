-- New for lvm6 (WP NODE5a). `htail_split`/`dec_of_node` (N4-tail) for any CC input record `I` whose stream lanes
-- are `inpD`'s (the deployed `inpReal` keeps them), with the per-tuple facts asked only at the commitment's claim.
import Lvm6NodeTailHS
import Lvm6NodeFinMA

/-!
# V1's decision from the node's CC part at any inputs (WP NODE5a)

N4-tail's `htail_split`/`dec_of_node` are stated at `Dep.inpD` (LAY3's representative claim data), and their
per-tuple hypotheses `hval`, `hcl` quantify over every `c0`. The deployed circuit runs `ccGI` on `inpReal o lay
…` (NODE3 B1, MBT's `mbPre`), and claim 0 is the commitment's output only. Here:
* **`LanesOf I`**: `I`'s ring and level lanes are `inpD`'s; **`lanesOf_inpReal`** (by unfolding `inpReal`, a
  record update of `inpD`).
* **`ClaimsAt I M rp sl st`**: `ClaimsOk` with `I`'s claim gadgets and `Pre := (· = M)`: `gad` (`ClaimAt` per
  claim) and `ma` (the batch's `MA 24`).
* **`htail_fin`**, **`dec_fin`**: `htail_split`, `dec_of_node` at `I`; `hval`, `hcl` under
  `afterV (commit6 P17) (segC ws) = some (.ret c0)` (weaker hypotheses: the statements are stronger).
-/

set_option autoImplicit false

namespace Lvm6.Node.Fin

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node Lvm6.Node.Split
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V LeanVM.Parameters

/-- **CC's stream lanes are `inpD`'s** (the ring phase's lane, every level's lane). -/
structure LanesOf (I : Dep.Inp) : Prop where
  ring : I.aRing = Dep.inpD.aRing
  lev : ∀ j, I.aL j = Dep.inpD.aL j

/-- **The deployed inputs keep `inpD`'s lanes** (`inpReal` is a record update of `inpD`). -/
theorem lanesOf_inpReal (o : NodeOutE) (lay : Lvm.Typed.Lay) (z one : C2) (tv : List C2)
    (mo : List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) × List C2) :
    LanesOf (Dep.inpReal o lay z one tv mo) :=
  ⟨by simp only [Dep.inpReal], fun _ ↦ by simp only [Dep.Inp.aL, Dep.inpReal]⟩

/-- **CC's claim gadgets at `I` compute the placed claims at `M`**, and the batch at `M`'s `λ₀` is affine in its 24
variables (`ccG_tail`'s last hypotheses, `Pre := (· = M)`). -/
structure ClaimsAt (I : Dep.Inp) (M : Mem) (rp : QC.RingPhC) (sl : List SliceClaim) (st : List StackClaim6) :
    Prop where
  gad : List.Forall₂ (fun G cl ↦ QC.ClaimAt (· = M) cl G) (Dep.claimGs I rp) (csOf M rp sl st)
  ma : Whir.MA 24 (fun y ↦ (Ring.batch (ev2 M rp.lam) (csOf M rp sl st)).1 (y.drop 6 ++ y.take 6))

section P18t

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Mem}
  (hM : ∀ j < ws.length, M.k j = Lvm.QLink.laneK ws j) (hpow : PowLanes6 P6 ws)

local notation "πW" => reassemble6 P6 (decode6 P6 ws)

include hw hM hpow in
/-- **`dec_of_split`'s `htail`** from the CC part at inputs `I` with `inpD`'s lanes: `htail_split` with `I`'s
cells, and the per-tuple facts at the commitment's claim `c0` only. -/
theorem htail_fin {I : Dep.Inp} (hI : LanesOf I) {c : Ctx} {pc : Ptr}
    (hcc : Dep.OkAt c M (Dep.ccGI I Dep.ccbC Dep.gateC) pc) (hg : Dep.gateC.val M = 1)
    {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop} {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop}
    (hsh : ∀ ot os, Pt ot → Ps os → ot.en.pt.length = 18 + 6 ∧ os.2.2.2.pt.length = 13 + 6)
    (hty : ∀ oy, Py oy → (Lvm6.Ty.claimsOnStack oy).length ≤ 7)
    (hval : ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) → ∀ ot os lk oy, Pt ot → Ps os → Pl lk →
      Py oy →
      [List.ofFn (K.toS 18 (hdrOf6 πW).h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
          [I.svT.map (ev2 M), I.svS.map (ev2 M)] ∧
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy)).map (·.2) =
          I.vs.map (ev2 M))
    (hcl : ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) → ∀ ot os lk oy, Pt ot → Ps os → Pl lk →
      Py oy → ∀ rp : QC.RingPhC,
      ClaimsAt I M rp [(K.toS 18 (hdrOf6 πW).h ot).slices, (SP.spS os lk).slices]
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy))) :
    ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) →
      ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      let t := K.toS 18 (hdrOf6 πW).h ot; let s := SP.spS os lk; let ty := Lvm6.Ty.claimsOnStack oy
      [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ P17.J₀ ∧
      ∃ cl, afterV (ringPhase6 P17 [t.slices, s.slices] (stackedOf c0 t s ty)) (segR ws) = some (.ret cl) ∧
        afterV (Whir.whirP cl) (segO ws) = some (.ret true) := by
  intro c0 hc0 ot os lk oy hot hos hlk hoy
  obtain ⟨rp, l0, l1, l2, l3, s1, s2, s3, s4, hR, h0, n0, h1, n1, h2, n2, h3, n3, g1, g2, g3, g4, hF⟩ :=
    ccG_tail I Dep.ccbC Dep.gateC hg pc hcc.1 hcc.2
  obtain ⟨pR, nR, eR⟩ := ring_slots hw hM hpow
  obtain ⟨pW, eW⟩ := open_slots hw hM hpow
  have hring : I.aRing = aRing := hI.ring.trans inpD_lanes.ring
  rw [← hring] at pR eR
  rw [layO_eq, ← hI.lev 0, ← hI.lev 1, ← hI.lev 2, ← hI.lev 3, ← hI.lev 4] at pW eW
  refine htail_of_cc hR pR nR eR pW eW (rowsF_segO ws) hsh hty
    (fun ot os lk oy a b c d ↦ hval c0 hc0 ot os lk oy a b c d) (fun ot os lk oy a b c d cl hrep ↦ ?_) ot os lk oy
    hot hos hlk hoy
  have hC := hcl c0 hc0 ot os lk oy a b c d rp
  exact whir_of_ring hrep (· = M) rfl l0.1 l1.1 l2.1 l3.1 l0.2.1 l1.2.1 l2.2.1 l3.2.1 l0.2.2 l1.2.2 l2.2.2 l3.2.2
    n0 n1 n2 n3 _ _ _ _ _ h0 h1 h2 h3 s1 s2 s3 s4 g1 g2 g3 g4
    (hF _ (· = M) (ev2 M rp.lam) hC.gad (fun _ h ↦ h ▸ rfl) hC.ma)

include hw hM hpow in
/-- **V1's decision from the node at inputs `I`** (V1c's phases): `dec_of_split` with `htail_fin`. -/
theorem dec_fin {I : Dep.Inp} (hI : LanesOf I) {tyOf : Hdr → Lvm6.Ty.TyInst6} {vk : Digest} {L : Lvm.M3.Lay}
    (hL : L = Lvm6.Ty.L6)
    {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop} {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop}
    (hT : Runs M (layItems (treeItems 18) aTree) (K.treeProg 18) Pt)
    (hS : Runs M (layItems (spItems 13) aSp) (K.spCaller6 13) Ps)
    (hK : Runs M (layItems (linkItems 13) aLink) (ksLinkProgE2 13 10 (rowsBK2 3816 7567 8032)) Pl)
    (hY : Runs M (layItems (Lvm6.QD.tyItems ++ Lvm6.QD.mbItems) aTy)
      (Lvm6.Ty.typedProgE (tyOf (hdrOf6 πW)).Ti L (tyOf (hdrOf6 πW)).pw (tyOf (hdrOf6 πW)).acc) Py)
    {c : Ctx} {pc : Ptr} (hcc : Dep.OkAt c M (Dep.ccGI I Dep.ccbC Dep.gateC) pc)
    (hg : Dep.gateC.val M = 1)
    (hsh : ∀ ot os, Pt ot → Ps os → ot.en.pt.length = 18 + 6 ∧ os.2.2.2.pt.length = 13 + 6)
    (hty : ∀ oy, Py oy → (Lvm6.Ty.claimsOnStack oy).length ≤ 7)
    (hval : ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) → ∀ ot os lk oy, Pt ot → Ps os → Pl lk →
      Py oy →
      [List.ofFn (K.toS 18 (hdrOf6 πW).h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
          [I.svT.map (ev2 M), I.svS.map (ev2 M)] ∧
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy)).map (·.2) =
          I.vs.map (ev2 M))
    (hcl : ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) → ∀ ot os lk oy, Pt ot → Ps os → Pl lk →
      Py oy → ∀ rp : QC.RingPhC,
      ClaimsAt I M rp [(K.toS 18 (hdrOf6 πW).h ot).slices, (SP.spS os lk).slices]
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy))) :
    F6 (phases6 (fun sh x ↦ Lvm6.Ty.typedPhase6 sh (tyOf x)) ringPhase6 (fun _ cl ↦ Whir.whirP cl)) P17 vk πW
      (accOf P17 πW (decode6 P6 ws)) = true :=
  dec_of_split hw hM hpow hL hT hS hK hY (htail_fin hw hM hpow hI hcc hg hsh hty hval hcl)

end P18t

end Lvm6.Node.Fin
