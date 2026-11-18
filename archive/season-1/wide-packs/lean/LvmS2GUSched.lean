-- New for lvm2 U-TAPE (UT-L, 2026-11-16): stage S2GU's parameters, schedule pins, sizes, layout and format (the frozen
-- `ref/utape.py` at occupancy 46). A proof never changes its statement; a needed change goes to the lead old → new.
import LvmS2GTSched
import LvmDecideV0

-- (SLF-K: 10 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

/-!
# The S2GU schedule (Lean stage `3`)

* **`P20U`**: `P20T` at stage `3` with `C_main`'s root leaves narrowed to 46 words (368 B, 3 permutations: the
  `KS` block is gone, the occupied words end in lane 46).
* **`phasesS2GU p`** (`LvmSchedule`): `S2GT`'s commit (with the pin), `bus` and `tables`; the merged tape `tapeU`
  (`T1` in R-BP2's B1 order, the depth-24 GKR of `Shape {21, 24}`), the wire `wireU` (the wire sumcheck, `g_D`,
  `g_Y`, `g_M`, the `D`/`Y`/`M` slot reductions); `C_main`'s opening. `KS` and the `KS` link are gone.
* **The layout** (`LvmDecideV0.layoutU`, the constants `LvmLayout.sOffU20` …): `S` 5,242,880, `X` 5,250,560, `Y`
  5,767,168, `free_lo` 5,971,968.
* Statements (UTAPE-STMT 1–5): `phases_P20U`, `headerBytesP_P20U`, **`sizes_P20U`**, `rwU20_pos`, `qcItems_P20U`;
  `layout0_P20U`; `fmtU20`.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The S2GU parameters**: `P20T`'s (A23 at 45 variables, the 16-B `acc_in` header) at stage `3`, `C_main`'s root
leaves at occupancy 46 (`ref/utape.py --occ 46`). -/
def P20U : Params :=
  { P20T with name := "P20U", stage := 3, mainLevels := withRow0 P20T.mainLevels 46 }

/-- **S2GU's layout** (`layoutU` at `P20U`) is `LvmLayout`'s: `D` 0, `Y` (the `ks` field) 5,767,168, `Y` lane 14
5,881,856, `X` 5,250,560, `free_lo` 5,971,968, `T` 4,194,304, `S` 5,242,880. -/
theorem layout0_P20U : layout0 P20U =
    ⟨CMain.dOff20, CMain.yOffU20, CMain.yOffU20 + 14 * 2 ^ 13, CMain.xOffU20, CMain.freeLoU20, CMain.tOff20,
      CMain.sOffU20⟩ := by
  decide +kernel

end Lvm

namespace Lvm.CT

open Lvm Lvm.ASM

/-- **S2GU's occupied words**: 46 at `C_main`'s root (height 19, 64 lanes: the `KS` block is gone, the tables end in
lane 45), `occOfS` elsewhere. -/
def occOfU (ht w : ℕ) : ℕ := if ht = 19 ∧ w = 64 then 46 else occOfS ht w

end Lvm.CT
