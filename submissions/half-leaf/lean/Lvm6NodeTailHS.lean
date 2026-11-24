-- New for lvm6 (WP N4-tail phase 3). `dec_of_split`'s `htail` from the node's CC part: N4-split's opening slots
-- (`open_slots`, at `layO`) are CC's level layouts (`MidP.lay_of`, `FinP.lay_of`; lanes `aO_eq`), so
-- `htail_of_cc`'s slot hypotheses are discharged; what is left is named (`ClaimsOk`, the outputs' values).
import Lvm6NodeTailO
import Lvm6NodeTailHL
import Lvm6NodeSplitOpen
import Lvm6NodeSlots

/-!
# `htail` from the node's CC part (WP N4-tail, phase 3)

* **`MidP.lay_of`**, **`FinP.lay_of`**: a level's opening slots (`MidP.lay`, `FinP.lay`, N4-split) are CC's
  `layRounds ++ layTail` / `layFin` at any parameters the record's fields equal (`MidIs`, `FinIs`); the `P17`
  instances `midIs0…3`, `finIs` (field by field, `decide`) are PF-4's per-level table.
* **`aO_eq`**: N4-split's opening lanes are `inpD`'s (`∀ j ≤ jF, aO j = inpD.aL j`).
* **`layO_eq`**: `layO` is the concatenation of `ccG_tail`'s level layouts at `inpD`.
* **`htail_split`**: `dec_of_split`'s `htail` (V1c's phases) from the CC part's rows (`OkAt` of `ccG`, gate on),
  the simulation hypotheses (`hw`, `hM`, `hpow`), and, per output tuple, `ClaimsOk` (CC's claim gadgets compute
  the placed claims, `λ₀`'s cell, `MA 24`), the slice points' lengths, `|ty| ≤ 7` and the input cells' values.
-/

set_option autoImplicit false

namespace Lvm6.Node.Split

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V LeanVM.Parameters

/-! ## Levels: N4-split's records against CC's layouts -/

/-- A mid level's record has these layout parameters. -/
structure MidIs (q : MidP) (g ℓ ko kq t gO gQ ht wd : ℕ) : Prop where
  g : q.g = g
  ℓ : q.ℓ = ℓ
  ko : q.ko = ko
  kq : q.kq = kq
  t : q.t = t
  gO : q.gO = gO
  gQ : q.gQ = gQ
  ht : q.ht = ht
  wd : q.wd = wd

theorem MidP.lay_of (q : MidP) {g ℓ ko kq t gO gQ ht wd : ℕ} (h : MidIs q g ℓ ko kq t gO gQ ht wd) (a : ℕ) :
    q.lay a = QC.layRounds g ℓ a ++ QC.layTail ℓ ko kq t q.lev q.wdI ht wd q.lvN gO gQ (a + 27 * ℓ) := by
  simp only [MidP.lay, h.g, h.ℓ, h.ko, h.kq, h.t, h.gO, h.gQ, h.ht, h.wd]

/-- The final level's record has these layout parameters. -/
structure FinIs (q : FinP) (nf kq t κ g gq gT ℓ : ℕ) : Prop where
  nf : q.nf = nf
  kq : q.kq = kq
  t : q.t = t
  κ : q.κ = κ
  g : q.g = g
  gq : q.gq = gq
  gT : q.gT = gT
  ℓ : q.ℓ = ℓ

theorem FinP.lay_of (q : FinP) {nf kq t κ g gq gT ℓ : ℕ} (h : FinIs q nf kq t κ g gq gT ℓ) (a : ℕ) :
    q.lay a = QC.layFin nf kq t κ q.lev q.wdI g gq gT ℓ a := by
  simp only [FinP.lay, h.nf, h.kq, h.t, h.κ, h.g, h.gq, h.gT, h.ℓ]

/-! ## The `P17` table (PF-4): `midP j` against W1's `mid_j`, `finPD` against `finD` -/

theorem midIs0 : MidIs (midP 0) Whir.mid0.g 6 Whir.mid0.L.ko Whir.mid0.L.kq Whir.mid0.L.t Whir.mid0.gO
    Whir.mid0.gQ Whir.mid0.ht Whir.mid0.wd :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem midIs1 : MidIs (midP 1) Whir.mid1.g 4 Whir.mid1.L.ko Whir.mid1.L.kq Whir.mid1.L.t Whir.mid1.gO
    Whir.mid1.gQ Whir.mid1.ht Whir.mid1.wd :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem midIs2 : MidIs (midP 2) Whir.mid2.g 4 Whir.mid2.L.ko Whir.mid2.L.kq Whir.mid2.L.t Whir.mid2.gO
    Whir.mid2.gQ Whir.mid2.ht Whir.mid2.wd :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem midIs3 : MidIs (midP 3) Whir.mid3.g 4 Whir.mid3.L.ko Whir.mid3.L.kq Whir.mid3.L.t Whir.mid3.gO
    Whir.mid3.gQ Whir.mid3.ht Whir.mid3.wd :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem finIs : FinIs finPD (2 ^ 2 + 4) 2 18 2 Whir.finD.g Whir.finD.gq 2 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **N4-split's opening lanes are CC's** (`inpD.aL`). -/
theorem aO_eq : ∀ j ≤ jF, aO j = Dep.inpD.aL j :=
  fun j hj ↦ ccLanesB_spec.2 j (Nat.lt_succ_of_le hj)

/-- **`layO` is the CC part's level layouts at `inpD`** (`ccG_tail`'s). -/
theorem layO_eq : layO =
    (QC.layRounds 10 6 (Dep.inpD.aL 0) ++ QC.layTail 6 17 18 110 (P17.lvl 0) (QC.wdOf 0) Whir.mid0.ht
        Whir.mid0.wd (P17.lvl 1).lv Whir.mid0.gO Whir.mid0.gQ (Dep.inpD.aL 0 + 27 * 6)) ++
    ((QC.layRounds 10 4 (Dep.inpD.aL 1) ++ QC.layTail 4 13 7 45 (P17.lvl 1) (QC.wdOf 1) Whir.mid1.ht
        Whir.mid1.wd (P17.lvl 2).lv Whir.mid1.gO Whir.mid1.gQ (Dep.inpD.aL 1 + 27 * 4)) ++
    ((QC.layRounds 10 4 (Dep.inpD.aL 2) ++ QC.layTail 4 9 3 28 (P17.lvl 2) (QC.wdOf 2) Whir.mid2.ht
        Whir.mid2.wd (P17.lvl 3).lv Whir.mid2.gO Whir.mid2.gQ (Dep.inpD.aL 2 + 27 * 4)) ++
    ((QC.layRounds 10 4 (Dep.inpD.aL 3) ++ QC.layTail 4 5 2 21 (P17.lvl 3) (QC.wdOf 3) Whir.mid3.ht
        Whir.mid3.wd (P17.lvl 4).lv Whir.mid3.gO Whir.mid3.gQ (Dep.inpD.aL 3 + 27 * 4)) ++
    QC.layFin (2 ^ 2 + 4) 2 18 2 (P17.lvl 4) 32 10 18 2 4 (Dep.inpD.aL 4)))) := by
  rw [layO, MidP.lay_of _ midIs0, MidP.lay_of _ midIs1, MidP.lay_of _ midIs2, MidP.lay_of _ midIs3,
    FinP.lay_of _ finIs, aO_eq 0 (by decide), aO_eq 1 (by decide), aO_eq 2 (by decide), aO_eq 3 (by decide),
    aO_eq jF le_rfl]
  rfl

/-! ## `htail` -/

/-- The placed claims of §6.5 at the ring cells' maps (`claimOf6`'s list). -/
def csOf (M : Mem) (rp : QC.RingPhC) (sl : List SliceClaim) (st : List StackClaim6) : List StackClaim6 :=
  placeRing (ringOf (sl.getD 0 ⟨[], 0⟩) (rp.ft.map (ev2 M)) (rp.gt.map (ev2 M)))
    (ringOf (sl.getD 1 ⟨[], 0⟩) (rp.fs.map (ev2 M)) (rp.gs.map (ev2 M))) st

/-- **CC's level-0 claim gadgets compute the placed claims** (on memories with some `Pre` holding at `M`), the `λ₀`
cell is `λ₀` there, and the batch is affine in its 24 variables (W1's `whirSpecD` hypothesis): NODE3 phase 2's
real lanes, CLG's `ClaimAt`, ASM's `claimOf6_mle`. -/
def ClaimsOk (M : Mem) (rp : QC.RingPhC) (sl : List SliceClaim) (st : List StackClaim6) : Prop :=
  ∃ Pre : Mem → Prop, Pre M ∧
    List.Forall₂ (fun G cl ↦ QC.ClaimAt Pre cl G) (Dep.claimGs Dep.inpD rp) (csOf M rp sl st) ∧
    (∀ M', Pre M' → ev2 M' rp.lam = ev2 M rp.lam) ∧
    Whir.MA 24 (fun y ↦ (Ring.batch (ev2 M rp.lam) (csOf M rp sl st)).1 (y.drop 6 ++ y.take 6))

section P18t

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Mem}
  (hM : ∀ j < ws.length, M.k j = Lvm.QLink.laneK ws j) (hpow : PowLanes6 P6 ws)

local notation "πW" => reassemble6 P6 (decode6 P6 ws)

include hw hM hpow in
/-- **`dec_of_split`'s `htail`** (V1c's phases `ringPhase6`, `whirP`) from the node's CC part: its rows hold
(`OkAt` of `ccG` at its pointer, gate on); per output tuple, `ClaimsOk` for every ring-cell record, the slice
points' lengths, at most 7 typed claims and the input cells (`inpD.svT`, `svS`, `vs`) holding the values. -/
theorem htail_split {c : Ctx} {pc : Ptr} (hcc : Dep.OkAt c M (Dep.ccGI Dep.inpD Dep.ccbC Dep.gateC) pc)
    (hg : Dep.gateC.val M = 1)
    {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop} {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop}
    (hsh : ∀ ot os, Pt ot → Ps os → ot.en.pt.length = 18 + 6 ∧ os.2.2.2.pt.length = 13 + 6)
    (hty : ∀ oy, Py oy → (Lvm6.Ty.claimsOnStack oy).length ≤ 7)
    (hval : ∀ c0 ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      [List.ofFn (K.toS 18 (hdrOf6 πW).h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
          [Dep.inpD.svT.map (ev2 M), Dep.inpD.svS.map (ev2 M)] ∧
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy)).map (·.2) =
          Dep.inpD.vs.map (ev2 M))
    (hcl : ∀ c0 ot os lk oy, Pt ot → Ps os → Pl lk → Py oy → ∀ rp : QC.RingPhC,
      ClaimsOk M rp [(K.toS 18 (hdrOf6 πW).h ot).slices, (SP.spS os lk).slices]
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy))) :
    ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) →
      ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      let t := K.toS 18 (hdrOf6 πW).h ot; let s := SP.spS os lk; let ty := Lvm6.Ty.claimsOnStack oy
      [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ P17.J₀ ∧
      ∃ cl, afterV (ringPhase6 P17 [t.slices, s.slices] (stackedOf c0 t s ty)) (segR ws) = some (.ret cl) ∧
        afterV (Whir.whirP cl) (segO ws) = some (.ret true) := by
  intro c0 _ ot os lk oy hot hos hlk hoy
  obtain ⟨rp, l0, l1, l2, l3, s1, s2, s3, s4, hR, h0, n0, h1, n1, h2, n2, h3, n3, g1, g2, g3, g4, hF⟩ :=
    ccG_tail Dep.inpD Dep.ccbC Dep.gateC hg pc hcc.1 hcc.2
  obtain ⟨pR, nR, eR⟩ := ring_slots hw hM hpow
  obtain ⟨pW, eW⟩ := open_slots hw hM hpow
  have hring : Dep.inpD.aRing = aRing := inpD_lanes.ring
  rw [← hring] at pR eR
  rw [layO_eq] at pW eW
  refine htail_of_cc hR pR nR eR pW eW (rowsF_segO ws) hsh hty
    (fun ot os lk oy a b c d ↦ hval c0 ot os lk oy a b c d) (fun ot os lk oy a b c d cl hrep ↦ ?_) ot os lk oy
    hot hos hlk hoy
  obtain ⟨Pre, hPre, hGs, hlc, hma⟩ := hcl c0 ot os lk oy a b c d rp
  exact whir_of_ring hrep Pre hPre l0.1 l1.1 l2.1 l3.1 l0.2.1 l1.2.1 l2.2.1 l3.2.1 l0.2.2 l1.2.2 l2.2.2 l3.2.2
    n0 n1 n2 n3 _ _ _ _ _ h0 h1 h2 h3 s1 s2 s3 s4 g1 g2 g3 g4
    (hF _ Pre (ev2 M rp.lam) hGs hlc hma)

include hw hM hpow in
/-- **V1's decision from the node** (V1c's phases): `dec_of_split` with `htail_split`. Left: the phase runs
(`node6E_har`: tree, sponge caller, link, typed at `hdrOf6 πW`), the CC part's rows, and per output tuple the
shapes, `|ty| ≤ 7`, the input cells' values and `ClaimsOk`. -/
theorem dec_of_node {tyOf : Hdr → Lvm6.Ty.TyInst6} {vk : Digest} {L : Lvm.M3.Lay} (hL : L = Lvm6.Ty.L6)
    {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop} {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop}
    (hT : Runs M (layItems (treeItems 18) aTree) (K.treeProg 18) Pt)
    (hS : Runs M (layItems (spItems 13) aSp) (K.spCaller6 13) Ps)
    (hK : Runs M (layItems (linkItems 13) aLink) (ksLinkProgE2 13 10 (rowsBK2 3816 7567 8032)) Pl)
    (hY : Runs M (layItems (Lvm6.QD.tyItems ++ Lvm6.QD.mbItems) aTy)
      (Lvm6.Ty.typedProgE (tyOf (hdrOf6 πW)).Ti L (tyOf (hdrOf6 πW)).pw (tyOf (hdrOf6 πW)).acc) Py)
    {c : Ctx} {pc : Ptr} (hcc : Dep.OkAt c M (Dep.ccGI Dep.inpD Dep.ccbC Dep.gateC) pc)
    (hg : Dep.gateC.val M = 1)
    (hsh : ∀ ot os, Pt ot → Ps os → ot.en.pt.length = 18 + 6 ∧ os.2.2.2.pt.length = 13 + 6)
    (hty : ∀ oy, Py oy → (Lvm6.Ty.claimsOnStack oy).length ≤ 7)
    (hval : ∀ c0 ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      [List.ofFn (K.toS 18 (hdrOf6 πW).h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
          [Dep.inpD.svT.map (ev2 M), Dep.inpD.svS.map (ev2 M)] ∧
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy)).map (·.2) =
          Dep.inpD.vs.map (ev2 M))
    (hcl : ∀ c0 ot os lk oy, Pt ot → Ps os → Pl lk → Py oy → ∀ rp : QC.RingPhC,
      ClaimsOk M rp [(K.toS 18 (hdrOf6 πW).h ot).slices, (SP.spS os lk).slices]
        (stackedOf c0 (K.toS 18 (hdrOf6 πW).h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy))) :
    F6 (phases6 (fun sh x ↦ Lvm6.Ty.typedPhase6 sh (tyOf x)) ringPhase6 (fun _ cl ↦ Whir.whirP cl)) P17 vk πW
      (accOf P17 πW (decode6 P6 ws)) = true :=
  dec_of_split hw hM hpow hL hT hS hK hY (htail_split hw hM hpow hcc hg hsh hty hval hcl)

end P18t

end Lvm6.Node.Split
