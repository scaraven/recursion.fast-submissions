-- New for lvm2 (roll 8 = B1, B1-V): the specification's typed instance `TInst` from V_S's native one, so
-- that `typedProg` (`LvmTypedSpec`) and `decideProgT` (`LvmTypedV`) read the same region maps. INT builds the
-- P20 instance as `N.inst Q lay` with `N.layOk lay` and `N.okB` decided.
import LvmTypedSpec
import LvmTypedV

/-!
# `TInst` from `TNat`

* **`TNat.off y`**: word `y`'s target, `dst + (y − base)` in the first region that holds `y` (`TInst.src?`'s
  region when `layOk`), `0` outside every region.
* **`TNat.inst N Q lay`**: `comW`, `ksW` are `off`; `sigmaW` is `off` modulo `2^19` (M′ `S2GM`, R11-IS: `σ′`'s
  region targets `C_main`'s stream block `S`, `2^19`-aligned, and the specification reads it from the block as its
  `C_rec` column, `recOf20`; B1: `off`, a `C_rec` word); `sflatW` is the stream position's `C_rec` word
  (`sflatWord`: column `p mod 17`, row `p div 17`); `PUB`'s words are header lanes; `QLT` is no region (its
  constants are in `Φ_Q`), so `qltV` is `0`.
* **`TNat.layOk N lay`**: the native regions are the layout's `yregs` (same order, so `find?` agrees).
-/

set_option autoImplicit false

namespace Lvm.TypedV

open Lvm.Typed

/-- The region holding word `y`. -/
def TNat.regAt (N : TNat) (y : ℕ) : Option NReg :=
  N.regs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)

/-- Word `y`'s target in its region. -/
def TNat.off (N : TNat) (y : ℕ) : ℕ :=
  match N.regAt y with
  | some r => r.dst + (y - r.base)
  | none => 0

/-- **The specification's instance of a native one** (the program and the layout are B1-K's). -/
def TNat.inst (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) : TInst where
  Q := Q
  lay := lay
  mbT := N.mbT
  comW := N.off
  ksW := N.off
  sflatW y := sflatWord (N.off y)
  sigmaW y := N.off y % 2 ^ 19
  pubV pub y := pub.hdrLanes.getD (N.off y) 0
  qltV _ := 0

/-- **The native regions are the layout's.** -/
def TNat.layOk (N : TNat) (lay : Lay) : Bool :=
  lay.yregs == N.regs.map fun r ↦ ⟨r.base, r.log, r.src⟩

/-- With `layOk`, a word's source in the specification is its native region's. -/
theorem src?_inst (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (h : N.layOk lay = true) (y : ℕ) :
    (N.inst Q lay).src? y = (N.regAt y).map (·.src) := by
  have hy : lay.yregs = N.regs.map fun r ↦ (⟨r.base, r.log, r.src⟩ : YReg) := by
    simpa [TNat.layOk] using h
  simp only [TInst.src?, TNat.inst, TNat.regAt, hy, List.find?_map, Option.map_map]
  rfl

/-- The relayout's rounds are the specification's. -/
theorem relayRoundsN_eq : relayRoundsN = relayRounds := rfl

/-- `Φ_Q`'s variables are the specification's. -/
theorem phiVarsN_eq : phiVarsN = phiVars := rfl

end Lvm.TypedV
