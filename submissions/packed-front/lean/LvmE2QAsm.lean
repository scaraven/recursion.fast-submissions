-- New for lvm2 E2-FT (E2F-QH3): the node program at stage S2GF (`QF20`): Q_link and Q_sig on the S2GF plan
-- (`P20F`, route A), the `E2` front, the typed phases with the coordinate split, the claims, `C_main`'s opening.
import LvmE2QTypedX
import LvmE2QPlan
import LvmTypedLayQ
import LvmE2QPinOpen
import LvmVFastQ

/-!
# The S2GF node program

* **`cfgF20`**: `cfg20` at `P20F` (stage S2GF: `schedule P20F` is the S2GF schedule, so Q_link's plan, the QLT
  table, the position classes and `ansLane` follow it).
* **`typedPosF p`**: the typed phases' start (the first `τ` sample's position: its answer at `typedPosF p + 40`).
* **`FrontF`**: what the `E2` front hands on: its claims in `V_S`'s order (the tape's, `KS`'s, `KS`'s outputs, the
  `KS` link's; every `E2` claim split re then im in place) and `n' − 1`'s bits (the small shape).
* **`frontStub C`**: the front before QH1/QH2's gadgets land: the borrow chain only, no claims (the blob is then a
  format test, not the S2GF circuit).
* **`qarithF C T pin front`**: the typed phases (`typedGX`), their claims, then the front's, all after the root pin's
  claim, `C_main`'s opening (QH2's `openGF`: the pin first, never relocated; the typed claims as `E3` forms, the front's as
  QH2's `E2` forms).
* **`qprogF C T front pin`**, **`QF C T front pin`**: Q_link, Q_sig, the front, `qarithF`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped

/-- **`P20`'s node program at S2GF** (`cfg20`'s record at `P20F`). -/
def cfgF20 : QCfg := { cfg20 with p := P20F }

/-- The typed phases' start: the first `τ` sample's position (`pos = ent + msg`; its answer at `+ 40`). -/
def typedPosF (p : Params) : Nat := 8 * phaseLane p .bus 0 - 40

/-- What the `E2` front hands on. -/
structure FrontF where
  /-- The front's claims in `V_S`'s order (`frontClaimsD`: tape, `KS`, `KS` outputs, `KS` link; `E2` claims split re
  then im in place), as QH2's opening forms. -/
  cs : List Lvm.Q2.FClaim
  /-- `m = n' − 1`'s `logN` bits (the borrow chain on Q_sig's bits of `n'`). -/
  mb : List Cell

/-- The root OOD pin's claim (the stub of QH2's `LvmE2QPin`): `ν` `E3` samples after `C_main`'s cap and one `E3`
read, a point claim on the physical stack, first in the list. -/
def pinStub (p : Params) : BM CClaim := do
  let zs ← ldEs (phaseLane p .commit 1) 9 p.nuMain
  let a ← Lvm.QAcc.ldE (phaseLane p .commit (1 + p.nuMain))
  pure ⟨.main, .point ⟨p.nuMain, 0⟩ zs, a⟩

/-- **The front stub**: the borrow chain only. -/
def frontStub (C : QCfg) : BM FrontF := do
  let one ← const .E 1 (kc 0)
  let mb ← borrow ((sigIn C).bn + 2) one.n C.p.logN
  pure ⟨[], mb⟩

/-- **`C_main`'s opening configuration at `p`** (`cfgMain` with its start lane from the stream plan: the opening starts
at position `8 U`, `U` five lanes before the `openMain` phase's first answer; roll 11's `openU` assumes the
`KS` link's four pending `E` scalars, 96 B, while S2GF's are four `E2` scalars, 64 B). -/
def cfgMainF (p : Params) (pb pw : Nat → Nat) : Lvm.Har.SCfg :=
  { Lvm.Har.cfgMain p pb pw with U := phaseLane p .openMain 0 - 5 }

/-- **Q_arith at S2GF**: the typed phases at `typedPosF`, their claims after the pin's, then the front's, `C_main`'s
opening. -/
def qarithF (C : QCfg) (T : TData) (pin : CClaim) (o : FrontF) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let ok ← const .K 1 (kc 0)
  let t ← typedGX T (pbB C) (typedPosF p) p.accV z one
  let tc ← typedClaimsC z one T p.nuMain (layout0 p).s t
  -- the shape cell as a `K` cell: `(1 + b₁₈)(1 + b₁₉)` on the `K` bits of `n' − 1`
  let a ← addK (o.mb.getD 18 default) 1
  let b ← addK (o.mb.getD 19 default) 1
  let sK ← mulAdd .K a b zk
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨ok, zk⟩⟩
  Lvm.Q2.openGF (cfgMainF p (posBase C) (pwBase C)) (p.logN == 20 && p.nuMain == CMain.nu20) F pin
    ((tc.1 ++ tc.2).map .e3 ++ o.cs) o.mb sK g

/-- **The S2GF node program's segments** on the static data `T`, with the front `fr` and the pin `pn`. -/
def qprogF (C : QCfg) (T : TData) (fr : QCfg → BM FrontF) (pn : Params → BM CClaim) : BM Unit := do
  qlink C.p (lay C)
  let _ ← qsig (sigIn C)
  let pin ← pn C.p
  let o ← fr C
  qarithF C T pin o

/-- **The S2GF node program** on the static data `T`. -/
def QF (C : QCfg) (T : TData) (fr : QCfg → BM FrontF) (pn : Params → BM CClaim) : Program :=
  VF.toProgramF (nK C) 0 (qprogF C T fr pn)

theorem QF_eq (C : QCfg) (T : TData) (fr : QCfg → BM FrontF) (pn : Params → BM CClaim) :
    QF C T fr pn = toProgram (nK C) 0 (qprogF C T fr pn) := by
  rw [QF, VF.toProgramF_eq]

/-- The S2GF program with the front stub and the pin stub (the format test). -/
def QFS (C : QCfg) (T : TData) : Program := QF C T frontStub pinStub

end Lvm.E2Q
