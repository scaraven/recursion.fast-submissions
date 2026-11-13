-- New for lvm2 (roll 8 = B1, B1-Q): the B program. Q_arith without the bus, the table sumcheck, `qacc` and the
-- table claims (and without `withPad`: no record-dependent table groups remain), calling the typed verifier
-- `typedG`. The shipped bus program `QT` (`LvmQAsmProg`) is unchanged and stays the oracle until INT switches.
import LvmQAsmProg
import LvmQTypedMB

/-!
# The B program (`QB`)

* **`qarithB C T o`**: after phases 4–7 (`phases47`, unchanged), the typed phases' verifier (`typedG` at
  `typedPos`), the `KS` ring switch and link (unchanged), the claims in `assembleT₂`'s order (the typed phases'
  first, then the tape's, `KS`'s, `KS`'s outputs, the `KS` link's), the opening (`openG`: M′, `C_main`'s alone).
* **`QB C T = toProgram (nK C) 0 (qlink; qsig; phases47 >>= qarithB)`**: `Q_link`, `Q_sig` as today.
* **`tdataP C`**: a placeholder record of the typed phases' static data (the region list's shape the layout
  solver will fill: one committed region, one `KS` alias region, `σ′`, `S_flat`, `PUB`, the word `1`; the
  mini-bus's arrays `mbArrs`). INT's refreeze replaces it by the solver's record (the same fixed-point pattern as
  `QData`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig

/-- **Q_arith of the B program** on the static data `T`. -/
def qarithB (C : QCfg) (T : TData) (o : P47Out) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let t ← typedG T (pbB C) (typedPos p) z one
  let tc ← typedClaimsC z one T p.nuMain (layout0 p).s t
  let rgK ← ringGkr (p.ksLog - 4) (Lvm.Har.aLane p 6) z.n
  let clK ← ksLinkG p (Lvm.Har.aLane p 7) z.n one.n
  let cs := tc.1 ++ tc.2 ++ (tapeClaimsC p z.n one.n o ++ kClaimsC ksB o.kko rgK) ++
    ksOutC p o.rk o.vk z.n one.n ++ clK
  openG (cfgMain p (posBase C) (pwBase C))
    (p.logN == 20 && p.nuMain == CMain.nu20) cs o.mb z one g

/-- The B program's segments. -/
def qprogB (C : QCfg) (T : TData) : BM Unit := do
  qlink C.p (lay C)
  let _ ← qsig (sigIn C)
  phases47 C >>= qarithB C T

/-- **The B program** on the static data `T`. -/
def QB (C : QCfg) (T : TData) : Program := toProgram (nK C) 0 (qprogB C T)

/-- **A placeholder of the typed phases' static data** (shape only; INT's refreeze gives the solver's). -/
def tdataP (C : QCfg) : TData where
  com := [⟨0, 20, 0⟩]
  ks := [⟨3 * 2 ^ 19 + 2 ^ 14, 14, 0⟩]
  sig := [⟨3 * 2 ^ 19, 10, 17 * 2 ^ 14⟩]
  sflat := 2 ^ 20
  pub := 3 * 2 ^ 19 + 2 ^ 10
  one := 3 * 2 ^ 19 + 2 ^ 11
  qlt := none
  mbS := (mbT C (fun _ => 0) (fun _ => (false, 0)) (fun _ => 0)).map Tab.shape
  mbR := ((mbT C (fun _ => 0) (fun _ => (false, 0)) (fun _ => 0)).map (·.τ)).foldl max 0
  mbFix := mbFixOf C

/-- The B program on the placeholder record. -/
def QBP (C : QCfg) : Program := QB C (tdataP C)

end Lvm.QTyped
