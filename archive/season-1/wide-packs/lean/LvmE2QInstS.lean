-- New for lvm2 σ_LEAF (SLF-C): the S2GS node program's instance on its frozen data (`LvmE2QAsmDataS20`, the genb
-- fixpoint of blob S) and the S2GS typed guard (`LvmE2QInstL`'s twin).
import LvmE2QAsmDataS20
import LvmE2QAsmS
import LvmE2QTypedGuard
import LvmTypedVInst
import LvmS2GSSched

/-!
# The S2GS instance (blob S)

* `cfgS20` (`cfg20` at `P20S`), `mbTS20`, `tdataS20`: the mini-bus's tables and the circuit's static data at the
  frozen placements `frzS20`.
* `qaS20`, `segsS20`, **`QS20`**: what follows Q_link and Q_sig, the program's segments and the program.
* `powS20` (`powU P20S`), **`layS20`** (`mkLayD` with `specQU` on `dintsS20`), **`cacheS20`** (the fast
  coordinate-split cache), `NTS20N` (the record of the regions and tables; `Φ_Q` unused by the guard).
* **`staticOkTS20`**: the S2GS typed guard (`staticOkTXc` at the S2GS instance).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.QTyped Lvm.QLink
open Lvm.M3 (Tab pushLeavesR)

/-- **S2GS's configuration**: `cfg20` at `P20S`. -/
def cfgS20 : QCfg := { cfg20 with p := P20S }

/-- The mini-bus's tables at S2GS. -/
def mbTS20 : List Tab := mbTOf cfgS20 frzS20

/-- The circuit's static data at S2GS. -/
def tdataS20 : TData :=
  let ts := mbTS20
  ⟨frzS20.com, frzS20.ks, frzS20.sig, frzS20.sflat, frzS20.pub, frzS20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfgS20, log2Ceil (pushLeavesR ts)⟩

/-- **Q_arith at S2GS** (what follows Q_link and Q_sig): the pin, the front, the typed phases with the mini-bus's three
claims, the opening. -/
def qaS20 : BM Unit := qaS cfgS20 tdataS20

/-- The S2GS program's segments (one run of the builder). -/
def segsS20 : List Seg :=
  ((do qlink cfgS20.p (lay cfgS20); let _ ← Lvm.QSig.qsigSC (sigIn cfgS20) (sigInLC cfgS20); qaS20 : BM Unit) ⟨nK cfgS20, 0⟩).2

/-- **The S2GS node program.** -/
def QS20 : Program :=
  let bs := VF.groupF segsS20
  ⟨nK cfgS20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem QS20_eq : QS20 = toProgram (nK cfgS20) 0
    (do qlink cfgS20.p (lay cfgS20); let _ ← Lvm.QSig.qsigSC (sigIn cfgS20) (sigInLC cfgS20); qaS20 : BM Unit) := by
  unfold QS20; rw [VF.groupF_eq]; rfl

/-- The ground challenges' lanes at S2GS (the front's and the typed phases'). -/
def powS20 : List (Nat × Nat) := powU P20S

/-- **The typed layout at S2GS** on the frozen dense intervals. -/
def layS20 : Typed.Lay := (mkLayD QS20 (specQU cfgS20 QS20 powS20) dintsS20).1

/-- **`Φ_Q`'s coordinate-split cache at S2GS** (evaluated at `E2` points by V_S's `PhiQGC`). -/
def cacheS20 : PhiCacheX := cacheWXF QS20 layS20

/-- The record of S2GS's regions and tables (the guard reads no `Φ_Q`). -/
def NTS20N : TypedV.TNat := ⟨nregsOf layS20 frzS20, fun _ => 0, mbTS20⟩

/-- **The S2GS typed guard** (`staticOkTXc` on `cacheS20`). -/
def staticOkTS20 : Bool := staticOkTXc cfgS20 frzS20 segsS20 QS20 layS20 NTS20N cacheS20

end Lvm.E2Q
