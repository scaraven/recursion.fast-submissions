-- New for lvm2 S2GT (GT-C): the S2GT node program's instance on its frozen data (`LvmE2QAsmDataG20`, the genb
-- fixpoint of blob GT) and the S2GT typed guard (the analogue of `LvmE2QInst` at S2GF).
import LvmE2QAsmDataG20
import LvmE2QAsmT
import LvmE2QTypedGuard
import LvmTypedVInst
import LvmS2GTSched

/-!
# The S2GT instance (blob GT)

* `cfgG20` (`cfg20` at `P20T`), `mbTG20`, `tdataG20`: the mini-bus's tables and the circuit's static data at the
  frozen placements `frzG20`.
* `qaG20`, `segsG20`, **`QG20`**: what follows Q_link and Q_sig, the program's segments and the program.
* `powG20` (`powFrontT P20T`), **`layG20`** (`mkLayD` with `specQF` on `dintsG20`), **`cacheG20`** (the fast
  coordinate-split cache), `NTG20N` (roll 11's `TNat` record of the regions and tables; `Φ_Q` unused by the guard).
* **`staticOkTG20`**: the S2GT typed guard (`staticOkTXc` at the S2GT instance).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.QTyped Lvm.QLink
open Lvm.M3 (Tab pushLeavesR)

/-- **S2GT's configuration**: `cfg20` at `P20T`. -/
def cfgG20 : QCfg := { cfg20 with p := P20T }

/-- The mini-bus's tables at S2GT. -/
def mbTG20 : List Tab := mbTOf cfgG20 frzG20

/-- The circuit's static data at S2GT. -/
def tdataG20 : TData :=
  let ts := mbTG20
  ⟨frzG20.com, frzG20.ks, frzG20.sig, frzG20.sflat, frzG20.pub, frzG20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfgG20, log2Ceil (pushLeavesR ts)⟩

/-- **Q_arith at S2GT** (what follows Q_link and Q_sig): the pin, the front, the typed phases at `E2`, the claims, the
opening. -/
def qaG20 : BM Unit := qaG cfgG20 tdataG20

/-- The S2GT program's segments (one run of the builder). -/
def segsG20 : List Seg :=
  ((do qlink cfgG20.p (lay cfgG20); let _ ← Lvm.QSig.qsig (sigIn cfgG20); qaG20 : BM Unit) ⟨nK cfgG20, 0⟩).2

/-- **The S2GT node program.** -/
def QG20 : Program :=
  let bs := VF.groupF segsG20
  ⟨nK cfgG20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem QG20_eq : QG20 = toProgram (nK cfgG20) 0
    (do qlink cfgG20.p (lay cfgG20); let _ ← Lvm.QSig.qsig (sigIn cfgG20); qaG20 : BM Unit) := by
  unfold QG20; rw [VF.groupF_eq]; rfl

/-- The ground challenges' lanes at S2GT (the front's and the typed phases'). -/
def powG20 : List (Nat × Nat) := powFrontT P20T

/-- **The typed layout at S2GT** on the frozen dense intervals. -/
def layG20 : Typed.Lay := (mkLayD QG20 (specQF cfgG20 QG20 powG20) dintsG20).1

/-- **`Φ_Q`'s coordinate-split cache at S2GT** (evaluated at `E2` points by V_S's `PhiQGC`). -/
def cacheG20 : PhiCacheX := cacheWXF QG20 layG20

/-- Roll 11's record of S2GT's regions and tables (the guard reads no `Φ_Q`). -/
def NTG20N : TypedV.TNat := ⟨nregsOf layG20 frzG20, fun _ => 0, mbTG20⟩

/-- **The S2GT typed guard** (`staticOkTXc` on `cacheG20`). -/
def staticOkTG20 : Bool := staticOkTXc cfgG20 frzG20 segsG20 QG20 layG20 NTG20N cacheG20

end Lvm.E2Q
