-- New for lvm2 σ_LEAF (SLF-L draft for SLF-V, 2026-11-16; owner V): DAY-0 STATEMENTS of `V_S` at S2GS (SLF-STMT 6).
-- Every `sorry` is tagged `-- SLF-STMT <n>`. The decision is the scratch smoke tool `vchecks`'s (SLF-L, accepted
-- parse, drive, tape and opening on SLF-P's S2GS files).
import LvmE2LDec
import LvmE2TVEq
import LvmE2QNodeU
import LvmS2GSPlan
import LvmE2SRef

/-!
# `V_S` at S2GS (day-0 statements; owner V)

* **`decideProgSG`**, **`decideFSG`** (texts in `LvmE2SRef`, moved verbatim for the proof): `decideProgLG` /
  `decideFLG` with the public values `pubOfWS` (no `σ_leaf` lanes, `acc_in` at header byte 152) and the tape's sponge
  intervals `contIvS a` (three intervals).
* `decideFSX N := decideFSG P20S P20 aSP N`, **`VSSX N`**: `parseOkS P20S` (no native leaf `SigOk`), then
  `drive P20S` with `decideFSX N`.
* Statements: `hq_VSSX` (O1), **`refinesS20`** (SLF-STMT 6, V).
-/

set_option autoImplicit false

namespace Lvm.E2S

open RecursionFast Lvm DM Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V Lvm.E2T Lvm.E2U Lvm.E2L
open Lvm.Typed (Lay)
open LeanVM.Protocol.Compile

/-- **V_S's decision at S2GS** (`P20S`, the typed phases' record `P20`, the own key leaf at `aSP`). -/
def decideFSX (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  decideFSG P20S P20 aSP N vk c sig

/-- **`V_S` at S2GS** for the native typed record `N`. -/
def VSSX (N : TNatT) : SProg := fun vk c π =>
  if parseOkS P20S vk c π then drive P20S π (decideFSX N vk c) else .ret false

/-- **SLF-STMT 6c** (owner L): **O1 for S2GS's `V_S`** (`hq_VSLX`'s proof with `qcItems_P20S`). -/
theorem hq_VSSX (N : TNatT) (H : ByteArray → RecursionFast.Digest) (vk c : RecursionFast.Digest)
    (π : RecursionFast.Proof) : ((VSSX N vk c π).queries H).length ≤ qVlvm := by
  show ((if parseOkS P20S vk c π then drive P20S π (decideFSX N vk c) else .ret false : OProg Bool).queries H).length ≤
    qVlvm
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π P20S _ 0
      (fun s ↦ by simp [OProg.queries]) (schedule P20S) 0 _ (by simp)) 1) 1).trans ?_
    have := qcItems_P20S
    show _ ≤ 16384
    omega
  · simp [OProg.queries]

/-- **SLF-STMT 6** (owner V): **`V_S` at S2GS refines the compiled specification** (`refinesL20`'s twin: `parseOkS`,
`okSL`'s scheme `schemeSWS`, the middle phases `midGS`). -/
theorem refinesS20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay)
    (hσ : Lvm.TypedV.SigInSL (layout0 P20S).s N.toN) (hlin : Lvm.M3.mbLinB N.mbT = true) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSSX N vk c π).runLog L = some true →
      ((schemeSWS fmtS20 vk (PSWithM (midP (midMk 4 relocU20 (midGS (N.inst Q lay)))))).V c π).runLog L =
        some true :=
  -- `decideFSX N vk c` and `decideFSG … vk c` (functions of `sig`) are compared through `funext` (SLF-K: the kernel's
  -- defeq of the two unapplied functions costs 6.5 M heartbeats)
  Lvm.VEq.refinesS20_of N Q lay H hσ hlin (VSSX N) fun vk c _ ↦ by
    rw [VSSX, show decideFSX N vk c = decideFSG P20S P20 aSP N vk c from funext fun _ ↦ rfl]

end Lvm.E2S
