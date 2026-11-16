-- New for lvm2 S2GT (GT-L, 2026-11-15): DAY-0 STATEMENTS of the verifier side at S2GT: `V_S` at S2GT (`VSGX`), its
-- refinement `refinesG20`, the fast `Φ_Q` at `E2` (`PhiQGC_eq`), O1. Every `sorry` is a day-0 statement tagged
-- `-- S2GT-STMT <n>`; `opaque`s are PLACEHOLDERS tagged `-- S2GT-PH <name> (owner)`, to be replaced by the owner's
-- definition of the same name and type. GT-L3: STMT 7 `refinesG20` moved to `LvmS2GTRef` (statement unchanged).
import LvmS2GTSched
import LvmE2TSpec
import LvmE2TV
import LvmE2TVEq
import LvmE2TWiring
import LvmWiringX
import LvmMPSig
import LvmE2VRefines
import LvmE2VDecG
import LvmE2VPhiT
import LvmE2VPhiTEqC

/-!
# V_S at S2GT (day-0 statements)

* `decideFGX N` (PLACEHOLDER, GT-V): V_S's decision at S2GT on the stream: the public values `pubOfW fe16At 16 accVT`
  (S2GT's 16-B `acc_in`), the cap, the pin, the typed phases `dTypedT P20 N` at `E2` (E2F-T-H1), the `E2` front, the
  openings (`decideProgF`'s body with the reader generalised), then `Φ_Q` at `E2` on the folded accumulator through
  `N.phiT` (S2GT: the fast evaluator `PhiQGC cacheG20`).
* **`VSGX N`**: `parseOk P20T`, then `drive P20T` with `decideFGX N` (no `withF`: it would reset the stage to `1`).
* `PhiQGC c` (PLACEHOLDER, GT-V): the fast evaluator at an `E2` point over the coordinate-split term cache (the six
  pieces `PhiPieceFT s j` through `PhiQCT`).
* Statements: **`PhiQGC_eq`** (V), `hq_VSGX` (L); **`refinesG20`** is in `LvmS2GTRef`.
-/

set_option autoImplicit false

namespace Lvm.E2T

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V
open Lvm.Typed (Lay PhiQFT phiVarsT)
open LeanVM.Protocol.Compile

/-- **`V_S` at S2GT** for the native typed record `N`. -/
def VSGX (N : TNatT) : SProg := fun vk c π =>
  if parseOk P20T vk c π then drive P20T π (decideFGX N vk c) else .ret false

/-- **S2GT-STMT 6** (owner V): **the fast `Φ_Q` at `E2` is `Φ_Q`** on a checked layout and a checked cache, at every
point of `phiVarsT = 45` coordinates (`PhiQCT_eq` with the six pieces; `TRefHypT.phiT` at S2GT). -/
theorem PhiQGC_eq (Q : Lvm.Loop.Program) (lay : Lay) (hlay : lay.Ok Q)
    (hc : (Lvm.Typed.cacheWX Q lay).okB Q lay = true) (hlin : Lvm.Typed.KT.linOkX (Lvm.Typed.cacheWX Q lay) = true)
    (pt : List FE2) (hpt : pt.length = phiVarsT) :
    PhiQGC (Lvm.Typed.cacheWX Q lay) pt = PhiQFT Q lay pt :=
  Lvm.Typed.KT.PhiQGC_eqW Q lay hlay hc hlin pt hpt

-- S2GT-STMT 7 (`refinesG20`) is in `LvmS2GTRef` (moved with its text unchanged, lead approved).

/-- **S2GT-STMT 8** (owner L): **O1 for S2GT's `V_S`**, any record (`hq_VSFX`'s proof with `qcItems_P20T`). -/
theorem hq_VSGX (N : TNatT) (H : ByteArray → RecursionFast.Digest) (vk c : RecursionFast.Digest)
    (π : RecursionFast.Proof) : ((VSGX N vk c π).queries H).length ≤ qVlvm := by
  show ((if parseOk P20T vk c π then drive P20T π (decideFGX N vk c) else .ret false : OProg Bool).queries H).length ≤
    qVlvm
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π P20T _ 0
      (fun s ↦ by simp [OProg.queries]) (schedule P20T) 0 _ (by simp)) 1) 1).trans ?_
    have := qcItems_P20T
    show _ ≤ 16384
    omega
  · simp [OProg.queries]

end Lvm.E2T
