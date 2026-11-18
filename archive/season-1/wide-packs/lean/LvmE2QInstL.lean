-- New for lvm2 MB-LIN (MBL-C): the S2GL node program's instance on its frozen data (`LvmE2QAsmDataL20`, the genb
-- fixpoint of blob L) and the S2GL typed guard (`LvmE2QInstU`'s twin).
import LvmE2QAsmDataL20
import LvmE2QTypedL
import LvmE2QTypedGuard
import LvmTypedVInst
import LvmS2GLSched

/-!
# The S2GL instance (blob L)

* `cfgL20` (`cfg20` at `P20L`), `mbTL20`, `tdataL20`: the mini-bus's tables and the circuit's static data at the
  frozen placements `frzL20`.
* `qaL20`, `segsL20`, **`QL20`**: what follows Q_link and Q_sig, the program's segments and the program.
* `powL20` (`powU P20L`), **`layL20`** (`mkLayD` with `specQU` on `dintsL20`), **`cacheL20`** (the fast
  coordinate-split cache), `NTL20N` (the record of the regions and tables; `Φ_Q` unused by the guard).
* **`staticOkTL20`**: the S2GL typed guard (`staticOkTXc` at the S2GL instance).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.QTyped Lvm.QLink
open Lvm.M3 (Tab pushLeavesR)

/-- **S2GL's configuration**: `cfg20` at `P20L`. -/
def cfgL20 : QCfg := { cfg20 with p := P20L }

/-- The mini-bus's tables at S2GL. -/
def mbTL20 : List Tab := mbTOf cfgL20 frzL20

/-- The circuit's static data at S2GL. -/
def tdataL20 : TData :=
  let ts := mbTL20
  ⟨frzL20.com, frzL20.ks, frzL20.sig, frzL20.sflat, frzL20.pub, frzL20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfgL20, log2Ceil (pushLeavesR ts)⟩

/-- **Q_arith at S2GL** (what follows Q_link and Q_sig): the pin, the front, the typed phases with the mini-bus's three
claims, the opening. -/
def qaL20 : BM Unit := qaL cfgL20 tdataL20

/-- The S2GL program's segments (one run of the builder). -/
def segsL20 : List Seg :=
  ((do qlink cfgL20.p (lay cfgL20); let _ ← Lvm.QSig.qsig (sigIn cfgL20); qaL20 : BM Unit) ⟨nK cfgL20, 0⟩).2

/-- **The S2GL node program.** -/
def QL20 : Program :=
  let bs := VF.groupF segsL20
  ⟨nK cfgL20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem QL20_eq : QL20 = toProgram (nK cfgL20) 0
    (do qlink cfgL20.p (lay cfgL20); let _ ← Lvm.QSig.qsig (sigIn cfgL20); qaL20 : BM Unit) := by
  unfold QL20; rw [VF.groupF_eq]; rfl

/-- The ground challenges' lanes at S2GL (the front's and the typed phases'). -/
def powL20 : List (Nat × Nat) := powU P20L

/-- **The typed layout at S2GL** on the frozen dense intervals. -/
def layL20 : Typed.Lay := (mkLayD QL20 (specQU cfgL20 QL20 powL20) dintsL20).1

/-- **`Φ_Q`'s coordinate-split cache at S2GL** (evaluated at `E2` points by V_S's `PhiQGC`). -/
def cacheL20 : PhiCacheX := cacheWXF QL20 layL20

/-- The record of S2GL's regions and tables (the guard reads no `Φ_Q`). -/
def NTL20N : TypedV.TNat := ⟨nregsOf layL20 frzL20, fun _ => 0, mbTL20⟩

/-- **The S2GL typed guard** (`staticOkTXc` on `cacheL20`). -/
def staticOkTL20 : Bool := staticOkTXc cfgL20 frzL20 segsL20 QL20 layL20 NTL20N cacheL20

end Lvm.E2Q
