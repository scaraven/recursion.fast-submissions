-- New for lvm2 U-TAPE (UT-C): the S2GU node program's instance on its frozen data (`LvmE2QAsmDataU20`, the genb
-- fixpoint of blob U) and the S2GU typed guard (the analogue of `LvmE2QInst` at S2GF).
import LvmE2QAsmDataU20
import LvmE2QAsmU
import LvmE2QTypedGuard
import LvmTypedVInst
import LvmS2GUSched

/-!
# The S2GU instance (blob U)

* `cfgU20` (`cfg20` at `P20U`), `mbTU20`, `tdataU20`: the mini-bus's tables and the circuit's static data at the
  frozen placements `frzU20`.
* `qaU20`, `segsU20`, **`QU20`**: what follows Q_link and Q_sig, the program's segments and the program.
* `powU20` (`powU P20U`), **`layU20`** (`mkLayD` with `specQF` on `dintsU20`), **`cacheU20`** (the fast
  coordinate-split cache), `NTU20N` (roll 11's `TNat` record of the regions and tables; `Φ_Q` unused by the guard).
* **`staticOkTU20`**: the S2GU typed guard (`staticOkTXc` at the S2GU instance).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.QTyped Lvm.QLink
open Lvm.M3 (Tab pushLeavesR)

/-- **S2GU's configuration**: `cfg20` at `P20U`. -/
def cfgU20 : QCfg := { cfg20 with p := P20U }

/-- The mini-bus's tables at S2GU. -/
def mbTU20 : List Tab := mbTOf cfgU20 frzU20

/-- The circuit's static data at S2GU. -/
def tdataU20 : TData :=
  let ts := mbTU20
  ⟨frzU20.com, frzU20.ks, frzU20.sig, frzU20.sflat, frzU20.pub, frzU20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfgU20, log2Ceil (pushLeavesR ts)⟩

/-- **Q_arith at S2GU** (what follows Q_link and Q_sig): the pin, the front, the typed phases at `E2`, the claims, the
opening. -/
def qaU20 : BM Unit := qaU cfgU20 tdataU20

/-- The S2GU program's segments (one run of the builder). -/
def segsU20 : List Seg :=
  ((do qlink cfgU20.p (lay cfgU20); let _ ← Lvm.QSig.qsig (sigIn cfgU20); qaU20 : BM Unit) ⟨nK cfgU20, 0⟩).2

/-- **The S2GU node program.** -/
def QU20 : Program :=
  let bs := VF.groupF segsU20
  ⟨nK cfgU20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem QU20_eq : QU20 = toProgram (nK cfgU20) 0
    (do qlink cfgU20.p (lay cfgU20); let _ ← Lvm.QSig.qsig (sigIn cfgU20); qaU20 : BM Unit) := by
  unfold QU20; rw [VF.groupF_eq]; rfl

/-- The ground challenges' lanes at S2GU (the front's and the typed phases'). -/
def powU20 : List (Nat × Nat) := powU P20U

/-- **The typed layout at S2GU** on the frozen dense intervals. -/
def layU20 : Typed.Lay := (mkLayD QU20 (specQU cfgU20 QU20 powU20) dintsU20).1

/-- **`Φ_Q`'s coordinate-split cache at S2GU** (evaluated at `E2` points by V_S's `PhiQGC`). -/
def cacheU20 : PhiCacheX := cacheWXF QU20 layU20

/-- Roll 11's record of S2GU's regions and tables (the guard reads no `Φ_Q`). -/
def NTU20N : TypedV.TNat := ⟨nregsOf layU20 frzU20, fun _ => 0, mbTU20⟩

/-- **The S2GU typed guard** (`staticOkTXc` on `cacheU20`). -/
def staticOkTU20 : Bool := staticOkTXc cfgU20 frzU20 segsU20 QU20 layU20 NTU20N cacheU20

end Lvm.E2Q
