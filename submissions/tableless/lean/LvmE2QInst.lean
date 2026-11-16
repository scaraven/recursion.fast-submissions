-- New for lvm2 E2-FT (E2F-QH3): the S2GF node program's instance on its frozen data (`LvmE2QAsmDataF20`, the genb
-- fixpoint), V_S's typed record at S2GF and the S2GF static guard (the analogue of `LvmQTypedInst`/`LvmCertTInst`).
import LvmE2QAsmDataF20
import LvmE2QAsmSpec
import LvmE2QTypedGuard
import LvmE2QTypedSpec
import LvmTypedVInst

-- (GOLF2: 3 declarations that `certified` does not use moved verbatim to `LvmE2QInstOff`, outside its import closure.)

/-!
# The S2GF instance

* `mbTF20`, `tdataF20`: the mini-bus's tables and the circuit's static data at the frozen placements `frzF20`.
* `segsF20`, **`QF20`**: the S2GF node program's segments (one run of the builder) and the program.
* **`layF20`**: the typed layout on the frozen dense intervals `dintsF20` (`mkLayD` with `specQF`).
* **`cacheF20`** `= cacheWXF QF20 layF20` (the fast cache; `cacheF20_eq`: it is `cacheWX QF20 layF20` on the checked
  layout); **`NTF20`**: roll 11's `TNat` with `phi := PhiQCX cacheF20` (44 variables).
* **`TiF20`**: the typed instance (`NTF20.inst QF20 layF20`).
* **`staticOkTF20`**: the S2GF guard (`staticOkTXc` on `cacheF20`, which is `staticOkTX`: `staticOkTF20_eq`; it decides
  `QF20.twinsOk` and `cacheF20.okBF` with roll 11's facts);
  `staticFactsTF20`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.QTyped
open Lvm.M3 (Tab pushLeavesR)

/-- The mini-bus's tables at S2GF. -/
def mbTF20 : List Tab := mbTOf cfgF20 frzF20

/-- The circuit's static data at S2GF. -/
def tdataF20 : TData :=
  let ts := mbTF20
  ⟨frzF20.com, frzF20.ks, frzF20.sig, frzF20.sflat, frzF20.pub, frzF20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfgF20, log2Ceil (pushLeavesR ts)⟩

/-- The S2GF program's segments (one run of the builder). -/
def segsF20 : List Seg := (qprogF cfgF20 tdataF20 frontF pinF ⟨nK cfgF20, 0⟩).2

/-- **The S2GF node program.** -/
def QF20 : Program :=
  let bs := VF.groupF segsF20
  ⟨nK cfgF20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

/-- The ground challenges' lanes at S2GF (the phase gadgets' lists, `powFront`). -/
def powF20 : List (Nat × Nat) := powFront P20F

/-- **The typed layout at S2GF** on the frozen dense intervals. -/
def layF20 : Typed.Lay := (mkLayD QF20 (specQF cfgF20 QF20 powF20) dintsF20).1

/-- **`Φ_Q`'s coordinate-split cache at S2GF.** -/
def cacheF20 : PhiCacheX := cacheWXF QF20 layF20

/-- **V_S's typed record at S2GF** (roll 11's `TNat`, `phi := PhiQCX cacheF20`, 44 variables). -/
def NTF20 : TypedV.TNat := ⟨nregsOf layF20 frzF20, PhiQCX cacheF20, mbTF20⟩

/-- **The typed instance at S2GF.** -/
noncomputable def TiF20 : TInst := NTF20.inst QF20 layF20

/-- **The S2GF static guard.** -/
def staticOkTF20 : Bool := staticOkTXc cfgF20 frzF20 segsF20 QF20 layF20 NTF20 cacheF20

theorem QF20_eq : QF20 = toProgram (nK cfgF20) 0 (qprogF cfgF20 tdataF20 frontF pinF) := by
  unfold QF20; rw [VF.groupF_eq]; rfl

end Lvm.E2Q
