-- New for lvm6 (WP MBT, item 3). The deployed typed instance's base `tiOf6 P : TyBase6`: the program `progQ6 layQ6`
-- (NODE3's `famQ6` at LAY5's `bOf` and NODE3's lanes `lanesD`), the layout `layQ6` (the exporter's two passes),
-- the mini-bus tables `mbTD layQ6`, the region targets `regTgt`, and the class table `P`. Compiled code builds
-- `progQ6`/`mbTD` by ST-5's/MBF's fast twins through `tyBaseOfQ` (`Lvm6NodeTiQ`, `Lvm6NodeBuildF`); the deployed
-- tables `mbT6` (with `tiOf6_mbT`, `mbT6_lin`) are in `Lvm6NodeTiQ` (INT7: one prefix build `progMb6`).
import Lvm6NodeMbF
import Lvm6VGuard
import Lvm6NodeLay
import Lvm6NodeMbT
import Lvm6NodeBuildF

/-!
# The deployed `TyBase6` (`tiOf6`, WP MBT)

* **`tiOfL lay`**: the deployed typed instance on a layout: `progQ6 lay`, the tables `mbTD lay` (those CC's claims
  50–52 read), the region maps `regW6 (mbPar6 lay)` (targets `regTgt lay`), `KS` by KSA's `ksWOf lay`, no `QLT` region (`qltV = 0`).
* **`tyBaseOf lay P`**: its `TyBase6`. The `S_flat`/`σ` bases are the layout's first regions of those sources
  (`tyLayOkB` checks them). `hτ`, `AllSc`, `LayOk` (by `alignW`), `KeysOk`, `FixOk`, `μBus = miniDepth` hold for
  every `lay` (`Lvm6NodeMbT` with `mbPar6_ok`); everything else about `lay` is the guard's (`staticOk6`).
* **`tiOf6 P = tyBaseOf layQ6 P`**; `P` is the exporter's class table, checked by `ptCheck`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Ti

open Lvm6.Node.Mb Lvm6.Node.Dep Lvm6.Node.LayQ

/-- The base of the first region of source `s` (`0` if none). -/
def regBase6 (lay : Lvm.Typed.Lay) (s : Lvm.Typed.YSrc) : ℕ :=
  ((lay.yregs.find? fun r => r.src == s).map (·.base)).getD 0

/-- **The deployed typed instance on a layout**: the program `progQ6 lay`, the mini-bus tables `mbTD lay` (the same
the circuit's claims 50–52 read), the region targets `regTgt lay` (`(mbPar6 lay).tgt`), no `QLT` region. -/
def tiOfL (lay : Lvm.Typed.Lay) : Ty.TInst6 :=
  ⟨progQ6 lay, lay, mbTD lay, regW6 (mbPar6 lay) lay .com, ksWOf lay, regW6 (mbPar6 lay) lay .sflat,
    regW6 (mbPar6 lay) lay .sigma, fun _ ↦ 0⟩

theorem tiOfL_mbT (lay : Lvm.Typed.Lay) :
    (tiOfL lay).mbT = mbTOf6 (mbPar6 lay) (fun k => ((capWords6 (mbPar6 lay) (progR lay) lay).getD k (0, 0)).1)
      (fun k => ((capWords6 (mbPar6 lay) (progR lay) lay).getD k (0, 0)).2) := rfl

theorem tiOfL_τ (lay : Lvm.Typed.Lay) : ∀ t ∈ (tiOfL lay).mbT, t.τ ≤ Ty.L6.μ := by
  rw [tiOfL_mbT]
  exact fun t ht => (mbTOf6_τ _ _ _ t ht).trans (by decide)

/-- **The `TyBase6` of a layout and a class table**: the construction facts for every `lay` (`MbPar.Ok` of
`mbPar6`; `LayOk` by `alignW`'s clamp). -/
def tyBaseOf (lay : Lvm.Typed.Lay) (P : Lvm6.V.PT) : Lvm6.V.TyBase6 where
  Ti := tiOfL lay
  P := P
  bs := regBase6 lay .sflat
  bg := regBase6 lay .sigma
  hτ := tiOfL_τ lay
  sc := by rw [tiOfL_mbT]; exact mbTOf6_sc _ _ _
  lay := by rw [tiOfL_mbT]; exact mbTOf6_layOk _ _ (mbPar6_ok lay) Ty.L6 rfl (by decide)
  keys := by rw [tiOfL_mbT]; exact mbTOf6_keys _ _ _
  fix := by rw [tiOfL_mbT]; exact mbTOf6_fix _ _ _
  μBus := mbTOf6_μBus _ _ _ Ty.L6 (tiOfL_τ lay)
  mapsReg := ⟨rfl, rfl, rfl⟩

/-- **The deployed typed instance's base** (class table `P`, the exporter's `.cls`, checked by `ptCheck`). -/
def tiOf6 (P : Lvm6.V.PT) : Lvm6.V.TyBase6 := tyBaseOf layQ6 P

theorem tiOf6_Q (P : Lvm6.V.PT) : (tiOf6 P).Ti.Q = progQ6 layQ6 := by
  unfold tiOf6 tyBaseOf tiOfL; rfl
theorem tiOf6_P (P : Lvm6.V.PT) : (tiOf6 P).P = P := by
  unfold tiOf6 tyBaseOf tiOfL; rfl

end Lvm6.Node.Ti
