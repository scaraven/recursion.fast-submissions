-- New for lvm2 S2GT (GT-C): the node program at stage S2GT (`QG`): Q_link and Q_sig on the S2GT plan (`P20T`), the
-- root pin and the `E2` front as at S2GF, the typed phases at `E2` (`typedGT`), their claims as `E2` halves,
-- `C_main`'s opening (`openGF`, unchanged).
import LvmE2QAsm
import LvmE2QAsmFront
import LvmE2QAsmSpec
import LvmE2QTypedT

/-!
# The S2GT node program

* **`pubLanesTC p`**: the child's `PUB` lanes at S2GT (`615 + 2·(accV + 1)`: `acc_in`'s `E2` scalars, two lanes each).
* **`qarithG C T pin front`**: the typed phases at `E2` (`typedGT`), their claims (`typedClaimsGT`: `E2` halves, then
  the mini-bus's `E3` table claims), then the front's, after the pin; `C_main`'s opening (`openGF`).
* **`qaG C T`**: the pin, the front, `qarithG` (what follows Q_link and Q_sig: `qprogP`'s `qa`).
* **`typedChalsT p`**: the typed phases' ground challenges `(answer lane, g)` (S2GT amendment 2: each `E2` challenge
  its own nonce): `τ` 20 × `g 1`, `ω` `g 2`, the zerocheck's 20 rounds `g 2`, `γ` `g 4`, the wiring's 21 rounds and
  the relayout's 19 rounds `g 2`, `κ` 4 × `g 1`, `t` `g 6`; **`powFrontT p`**: the front's and these.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped

/-- The child's `PUB` lanes at S2GT: the 615 fixed header lanes, `acc_in`'s `accV + 1` `E2` scalars of two lanes. -/
def pubLanesTC (p : Params) : Nat := 615 + 2 * (p.accV + 1)

/-- **Q_arith at S2GT**: the typed phases at `E2`, their claims after the pin's, then the front's, `C_main`'s
opening. -/
def qarithG (C : QCfg) (T : TData) (pin : CClaim) (o : FrontF) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let ok ← const .K 1 (kc 0)
  let t ← typedGT T p (pbB C) (pubLanesTC p) z one zk ok
  let tc ← typedClaimsGT z ⟨zk, zk⟩ ⟨ok, zk⟩ T (layout0 p).s t
  -- the shape cell as a `K` cell: `(1 + b₁₈)(1 + b₁₉)` on the `K` bits of `n' − 1`
  let a ← addK (o.mb.getD 18 default) 1
  let b ← addK (o.mb.getD 19 default) 1
  let sK ← mulAdd .K a b zk
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨ok, zk⟩, true⟩
  Lvm.Q2.openGF (cfgMainF p (posBase C) (pwBase C)) (p.logN == 20 && p.nuMain == CMain.nu20) F pin (tc ++ o.cs)
    o.mb sK g

/-- **What follows Q_link and Q_sig at S2GT**: the root pin, the `E2` front, `qarithG`. -/
def qaG (C : QCfg) (T : TData) : BM Unit := do
  let pin ← pinF C.p
  let o ← frontF C
  qarithG C T pin o

/-- **The S2GT node program** on the static data `T` (`qprogP`'s form: Q_link, Q_sig, `qaG`). -/
def QG (C : QCfg) (T : TData) : Program := VF.toProgramF (nK C) 0 (do qlink C.p (lay C); let _ ← qsig (sigIn C); qaG C T)

/-- **The typed phases' ground challenges at S2GT** `(answer lane, g)`. -/
def typedChalsT (p : Params) : List (Nat × Nat) :=
  let L := busL p
  (List.range tX).map (fun i => (L (iTau i), 1)) ++ [(L iOm, 2)] ++
    (List.range tX).map (fun k => (L (iZR k + 2), 2)) ++ [(L iGam, 4)] ++
    (List.range tY).map (fun k => (L (iWR k + 2), 2)) ++ (List.range tR).map (fun k => (L (iRR k + 2), 2)) ++
    (List.range 4).map (fun j => (L (iKap j), 1)) ++ [(L iT, 6)]

/-- **The ground challenges of the S2GT node program**: the front's (`powFront`) and the typed phases'. -/
def powFrontT (p : Params) : List (Nat × Nat) := powFront p ++ typedChalsT p

end Lvm.E2Q
