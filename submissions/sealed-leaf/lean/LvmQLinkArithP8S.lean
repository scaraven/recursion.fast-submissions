-- lvm2 GOLF (a pure move out of `LvmQLinkArithP8`): `SLok` of `KS`'s block E at `P8` and `P8`'s `KS` link soundness.
-- Only `LvmFinDec` (outside `Solution`'s import closure) uses them, so they leave the certificate's build.
import LvmQLinkArithP8
import LvmE2QNodeFOff
import LvmQTypedHarZOff

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- **`SLok` of `KS`'s block E at `P8`** (KS14: `ksLog = recRowsLog = 14`, the selector `ρ'_10 … ρ'_13`,
`2262` sponge blocks, the split 15,360). -/
theorem okE_P8 (Q : Nat) (gate : Cell) (sh : LoopOut) : SLok (ksBlockE P8 Q sh gate) = true := by
  rw [ksBlockE, if_pos (by decide),
    show ksSelC P8 sh = [sh.cell 2 10, sh.cell 2 11, sh.cell 2 12, sh.cell 2 13] from rfl, spongeBlocks_P8,
    ksSplit_P8, show P8.ksLog = 14 from rfl]
  rw [← SLok_shape]
  simp only [ksGlueE14, List.map_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  rw [loadsAt_shape, loadsAt_shape (q := ksQV 14 Q), preRecIns_shape, preRecIns_shape (n := 13 * 14 + 6),
    preRecIns_shape (n := 25 * 14 + 6), mulChainIns_shape (n := 38 * 14 + 8),
    mulChainIns_shape (n := 39 * 14 + 8)]
  simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI,
    shape_linI, shape_addI, shape_loc, rho'C, preP, shape_ins_mk, shape_getD_mapCellSrc, sumSrc,
    reduceCtorEq, if_false, List.length_cons, List.length_nil]
  decide +kernel

/-- **`P8`'s `KS` link circuit is sound.** -/
theorem ksLink_sound_P8 {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T P Q : Nat} (rk : List FE) (pub : Pub)
    (gate : Cell) (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T) (hT : ksQV 14 Q + 3 * 4 + 3 ≤ T)
    (hg : gate.val M = 1) (h : SegsHold c M ptr (ksLinkGadget P8 4 Q gate ptr).2)
    (hA : SegsAssert M ptr (ksLinkGadget P8 4 Q gate ptr).2) :
    (ksLink0 P8 (ksLinkView P8 (M3.ofParts P8 bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 = true :=
  ksLink_sound P8 4 rk pub gate (by decide) (by decide) (by decide) hPQ (by rw [spongeBlocks_P8]; decide)
    (by rw [spongeBlocks_P8]; decide) (by rw [ksSplit_P8]; decide)
    (fun sh => okE_P8 Q gate sh) hS hT hg h hA

end Lvm.Q1
