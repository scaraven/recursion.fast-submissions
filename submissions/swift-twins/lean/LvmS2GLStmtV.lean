-- New for lvm2 MB-LIN (MBL-L draft for MBL-V, 2026-11-16; owner V): DAY-0 STATEMENTS of `V_S` at S2GL (MBL-STMT 6).
-- Every `sorry` is tagged `-- MBL-STMT <n>`; `decideFLX` is V_S's S2GL decision (`LvmE2LDec`).
import LvmS2GLMid
import LvmS2GLSched
import LvmS2GUMid
import LvmE2VDecG
import LvmE2VPhiT
import LvmE2QTypedReg
import LvmE2QHarPos
import LvmE2QTypedT
import LvmE2QPlan
import LvmFinPos
import LvmQTypedHarB
import LvmQTypedHarChk
import LvmCertTInst
import LvmE2TVEq
import LvmE2UDec
import LvmE2QInstU
import LvmE2QNodeU
import LvmE2QFrontU
import LvmE2VPhiTEqC
import LvmE2URef
import LvmE2LDec
import LvmE2LRef

/-!
# `V_S` at S2GL (day-0 statements; owner V)

* `decideFLX N` (V: `LvmE2LDec.decideFLG P20L P20 3843`), **`VSLX N`**: `parseOk P20L`, then `drive P20L` with
  `decideFLX N`.
* Statements: `hq_VSLX` (L), **`mbClaimsN_rel`** (MBL-STMT 6a, V: V_S's three claims are the specification's,
  claim for claim, at mapped arguments; V's fast run weights then prove equal to `sumClaim`'s weight inside V's own
  refinement), **`refinesL20`** (MBL-STMT 6b, V).
-/

set_option autoImplicit false

namespace Lvm.E2L

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V Lvm.E2T Lvm.E2U
open Lvm.Typed (Lay)
open LeanVM.Protocol.Compile

/-- **V_S's decision at S2GL** (MBL-V, `LvmE2LDec.decideFLG` at `P20L`: the typed phases' mini-bus record `P20`, as
S2GU; the bus phase without the table phase; the three claims `mbClaimsN` in the opening after the typed claims; the
tape's sponge intervals at S2GL's `3,843` sponge blocks, `sizes_P20L`). -/
def decideFLX (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  decideFLG P20L P20 3843 N vk c sig

/-- **`V_S` at S2GL** for the native typed record `N`. -/
def VSLX (N : TNatT) : SProg := fun vk c π =>
  if parseOk P20L vk c π then drive P20L π (decideFLX N vk c) else .ret false

/-- **MBL-STMT 6c** (owner L): **O1 for S2GL's `V_S`** (`hq_VSUX`'s proof with `qcItems_P20L`). -/
theorem hq_VSLX (N : TNatT) (H : ByteArray → RecursionFast.Digest) (vk c : RecursionFast.Digest)
    (π : RecursionFast.Proof) : ((VSLX N vk c π).queries H).length ≤ qVlvm := by
  show ((if parseOk P20L vk c π then drive P20L π (decideFLX N vk c) else .ret false : OProg Bool).queries H).length ≤
    qVlvm
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π P20L _ 0
      (fun s ↦ by simp [OProg.queries]) (schedule P20L) 0 _ (by simp)) 1) 1).trans ?_
    have := qcItems_P20L
    show _ ≤ 16384
    omega
  · simp [OProg.queries]

/-- **MBL-STMT 6a** (owner V): **V_S's three claims are the specification's** (`mbClaimsN` on the native bus
decomposition against `mbClaimsL` on the mapped bus reading; `BCRel` claim for claim, so V's weights equal the
spec's). -/
theorem mbClaimsN_rel (tabs : List Lvm.M3.Tab) (i : Lvm.BusIn) :
    List.Forall₂ Lvm.VEq.BCRel (Lvm.M3.mbClaimsN 23 tabs i)
      (Lvm.M3.mbClaimsL 23 tabs ⟨i.alphas.map FE.toExt3, FE.toExt3 i.beta, i.point.map FE.toExt3,
        i.values.map FE.toExt3⟩) := by
  unfold Lvm.M3.mbClaimsN Lvm.M3.mbClaimsL
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun s _ => ?_
  exact Lvm.VEq.Lk.sumClaim_rel 23 _ _ (MbRel.parts_rel tabs i s) (MbRel.value_rel tabs i s)

/-- **MBL-STMT 6b** (owner V): **S2GL's `V_S` refines the specification's scheme** at `fmtL20`, the middle phases
`midMk 4 relocU20 (midGL _)` (`refinesU20`'s twin; RE-FREEZE R4: `hlin`, no `C_rec` mini-bus column, so the three
claims' small-shape tails are `0`). -/
theorem refinesL20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay)
    (hσ : Lvm.TypedV.SigInSL (layout0 P20L).s N.toN) (hlin : Lvm.M3.mbLinB N.mbT = true) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSLX N vk c π).runLog L = some true →
      ((schemeSW fmtL20 vk (PSWithM (midP (midMk 4 relocU20 (midGL (N.inst Q lay)))))).V c π).runLog L =
        some true :=
  -- SLF-K: `decideFLX N vk c` and `decideFLG … vk c` (functions of `sig`) are compared through `funext` (the kernel's
  -- defeq of the two unapplied functions cost 6.5 M heartbeats)
  Lvm.VEq.refinesL20_of N Q lay H hσ hlin (VSLX N) fun vk c _ ↦ by
    rw [VSLX, show decideFLX N vk c = decideFLG P20L P20 3843 N vk c from funext fun _ ↦ rfl]

end Lvm.E2L
