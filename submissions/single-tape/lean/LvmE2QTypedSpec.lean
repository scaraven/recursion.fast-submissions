-- New for lvm2 E2-FT (E2F-QH3; E2F-V2: on S2GF's public values `pubXF`): the typed backend's hypotheses and the
-- typed half of the good relation at stage S2GF (`THypX`, `GbTX`), the successors of `LvmTypedSpec`'s `THyp`, `GbT`
-- on `TGoodX`/`AccOkTX`/`TErrsX`.
import LvmTypedSpecXD
import LvmE2VPub

/-!
# `THypX`, `GbTX`

* **`THypX Ti`**: `THyp`'s fields with `acc_in` at `phiVarsX = 44` coordinates and the error conditions `TErrsX`
  (`τ` and `ω` one group, `κ`'s three samples, A23 at 44 variables) — what `typedSpecX` takes at `lay26`.
* **`GbTX Ti H x p`**: the typed half of a good pair at S2GF (`TGoodX` with the boundary claims) and the incoming
  accumulator at `Φ_Q` in 44 variables (`AccOkTX`), on S2GF's public values `pubXF x` (`acc_in` of 44
  coordinates; E2F-V2).
* The good pair at S2GF is `LvmE2VMidSpec.GoodTF Ti H = GbTX ∧ GkF` (`GkF`: S2GF's `KS` continuation rows; `GkS`
  checks S2GM's and is false for an honest S2GF witness), stated there (it imports this module).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm.M3 (Tab inst stackOf comCell NoCG KeysOk AllSc LayOk FixOk lay26)
open Lvm.ASM (OpenClaims Pair BndS LkSJ εS)
open Lvm.VEq (pubXF)
open scoped ENNReal NNReal

/-- **The typed backend's hypotheses at S2GF** (`THyp`'s, `acc_in` at 44 coordinates, `TErrsX`). -/
structure THypX (Ti : TInst) : Prop where
  ok : Ti.Ok
  maps : Ti.MapsFit lay26
  /-- `acc_in` has `phiVarsX = 44` coordinates (s2gf amendment 1; S2GF's public values `pubXF` read 44,
  `length_pubXF`). -/
  acc : ∀ x, (pubXF x).accIn.pt.length = phiVarsX
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ
  sc : AllSc Ti.mbT
  layOk : LayOk lay26 Ti.mbT
  keys : KeysOk Ti.mbT
  width : ∀ t ∈ Ti.mbT, 0 < t.w
  fix : FixOk Ti.mbT
  /-- The mini-bus's columns are few. -/
  widths : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = miniDepth
  errs : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), TErrsX 37696 (inst lay26 Ti.mbT h) εS LkSJ

/-- **The bus half of a good pair at S2GF** (`GbT`'s shape on `TGoodX`, `AccOkTX`). -/
def GbTX (Ti : TInst) (H : THypX Ti) (x : List UInt8) (p : Pair) : Prop :=
  (TGoodX Ti lay26 H.hτ (pubXF x) p ∧ BndS x p.1) ∧ AccOkTX Ti (pubXF x)

end Lvm.Typed
