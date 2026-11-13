-- New for lvm (WP-16a2, FIN-DEC): the static facts of HAR's `harith_core` decided on the frozen `P20` record:
-- `KS`'s glue template at `P20` (`okE_P20`, adapted from QA1's `okE_P8`, LvmQLinkArithP8), the numeric fields of
-- `HarStatic` (`HarNum`, generic), `powStatic20`, `hbs20`. Lvm2 roll 8 (L-D): the position facts (`PosLanes`,
-- `posLanesB20`/`R20`/`M20`) moved to the bus-free `LvmFinPos`.
import LvmQAsmHarMain
import LvmQAsmHarLink20
import LvmFinBVPos
import LvmFinPos
import LvmXOutSeg
import LvmNodeSoundTr

/-!
# The decided static facts at `P20`

* **`okE_P20`**: `SLok` of `KS`'s glue block E at `P20` (`ksGlueE14` at KS13: `ksLog = 13`, the selector
  `ρ'_9 … ρ'_12`, the WOTS leaf from the split 7,680, `spongeBlocks P20 - 1 = 6204`; lvm2 CR-K) (as `okE_P8`:
  the check reads only the template's shape), decided through the one-pass check `SLokF` (`SLok_of_F`).
* **`HarNum C T P4 … P8`**: the fields of `HarStatic` that are numbers of `C.p` (positions of
  phases 4–7, lane bounds, sizes); **`harStatic_of`** builds `HarStatic` from it, the layer checks,
  the glue checks, the shape facts and the WHIR layouts (generic in the configuration). (Roll 8, wave L:
  the bus program's `harNum20` is deleted: `HarNum` needs `10 ≤ tableRounds`, false on the typed schedule, and the
  typed certificate does not read the bus program's HAR.)
* **`powStatic20`**, **`hbs20`** (`bsB cfg20 + 256 ≤ nK cfg20`, from `LvmFinPos.posLanesB20`). FIN-BV's
  `PosLanes`, `posLanesR_of_K`, `posLanesR20`, `posLanesM20` and the decision `posLanesB20` are in `LvmFinPos`
  (lvm2 roll 8, L-D).

Kernel (dev VM): `okE_P20` 1.2 s (16 s with `SLok`'s quadratic lookups).
-/

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.Har Lvm.Replay Lvm.QLink
open Lvm.QAsm (QCfg QData cfg20 data20 nK bsB pwB clog2 nAns pbB)
open Lvm.X (Blk blocks lensB lanesOf lanes_eq lensB_opn)

/-! ## `KS`'s glue block at `P20` (`SLokF`, `SLok_of_F`: `LvmQAsmHarLink20`) -/

/-- **`SLok` of `KS`'s block E at `P20`** (KS13: `ksLog = 13`, `6205` sponge blocks, the split 7,680). -/
theorem okE_P20 (Q : ℕ) (gate : Cell) (sh : LoopOut) : SLok (ksBlockE P20 Q sh gate) = true := by
  rw [ksBlockE, if_pos (by decide), ksSelC_P20, sizes_P20.2.2.2.2.2.2.2.2, ksSplit_P20,
    show P20.ksLog = 13 from rfl]
  rw [← SLok_shape]
  simp only [ksGlueE14, List.map_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  rw [loadsAt_shape, loadsAt_shape (q := ksQV 13 Q), preRecIns_shape, preRecIns_shape (n := 13 * 13 + 6),
    preRecIns_shape (n := 25 * 13 + 6), mulChainIns_shape (n := 38 * 13 + 8),
    mulChainIns_shape (n := 39 * 13 + 8)]
  simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI,
    shape_linI, shape_addI, shape_loc, rho'C, preP, shape_ins_mk, shape_getD_mapCellSrc, sumSrc,
    reduceCtorEq, if_false, List.length_cons, List.length_nil]
  apply SLok_of_F
  decide +kernel

/-! ## `HarStatic`'s numbers -/

/-- **The fields of `HarStatic` that are numbers of `C.p`** (phases 4–7's positions `P47Pos`, the lane
bounds, sizes, the table phase's position, the start of phases 8–9). -/
def HarNum (C : QCfg) (T P4 P5 P6 P7 P8 : ℕ) : Prop :=
  (P4 + 40 = 8 * aLane C.p 0 ∧ P4 + 72 * C.p.logN + 40 = 8 * aLane C.p 1 ∧
    8 * aLane C.p 2 - 40 = P4 + 72 * C.p.logN + 600 ∧
    Lvm.Q1.tapeEnd (C.p.logN - 5) (aLane C.p 2) = aLane C.p 3 ∧ 8 * aLane C.p 3 - 40 = P5 ∧
    8 * Lvm.Q1.wireEnd (C.p.logN - 5) (aLane C.p 3) - 40 = P6 ∧ P6 + 40 = 8 * aLane C.p 4 ∧
    kV C.p.ksLog P6 + 40 = 8 * aLane C.p 5 ∧ kG C.p.ksLog P6 = 8 * aLane C.p 6 - 40 ∧
    8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40 + 72 * ringStages = P7 ∧ P7 + 40 = 8 * aLane C.p 7 ∧
    ksP2 C.p P7 + 96 = P8) ∧
  5 ≤ C.p.logN ∧ 4 ≤ C.p.ksLog ∧ 5 ≤ aLane C.p 2 ∧ 5 ≤ aLane C.p 3 ∧
  5 ≤ aLane C.p 6 ∧
  Lvm.Q1.wireEnd (C.p.logN - 5) (aLane C.p 3) + 2 ≤ T ∧ gkrEnd (C.p.ksLog - 4) (aLane C.p 6) + 48 ≤ T ∧
  aLane C.p 0 + 9 * C.p.logN + 2 < T ∧ aLane C.p 1 + 3 * 25 + 2 < T ∧
  aLane C.p 4 + 9 * C.p.ksLog + 2 < T ∧ aLane C.p 5 + 3 * 25 + 2 < T ∧
  C.p.logN ≤ 2 ^ clog2 C.p.logN ∧ C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog ∧
  ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T ∧
  aLane C.p 7 + 9 * (C.p.ksLog + laneBits) + 15 * C.p.ksLog + 12 ≤ T ∧
  1 ≤ spongeBlocks C.p ∧ spongeBlocks C.p ≤ 2 ^ C.p.ksLog ∧ ksSplit C.p + 431 ≤ 2 ^ C.p.ksLog ∧
  C.p.leafdecReads = 1 ∧ busPos C.p % 8 = 0 ∧ busEnd C.p (busPos C.p) + 40 ≤ 8 * T ∧
  tabPos C.p % 8 = 0 ∧ 10 ≤ C.p.tableRounds ∧ C.p.tableRounds ≤ accVars ∧ 1 ≤ C.p.accLog ∧
  11 + pubLanes ≤ T ∧ 29 ≤ T ∧ C.p.logN ≤ 64 ∧ P8 = 8 * openU C.p ∧
  (C.p.recLevels.length ≤ (opens C.p).length ∧ C.p.recLevels.length + C.p.mainLevels.length ≤ (opens C.p).length)

/-- **`HarStatic` from its numbers**, the layer checks, the glue check, the table shapes' facts and the
WHIR layouts (any configuration, record, stream lanes and positions; phase 3b's `accZ0` written out). -/
theorem harStatic_of {C : QCfg} {D : QData} {T P4 P5 P6 P7 P8 : ℕ} (hN : HarNum C T P4 P5 P6 P7 P8)
    (hlay : layOk (C.p.logN - 5) = true) (hlayk : layOk (C.p.ksLog - 4) = true)
    (okE : ∀ sh : LoopOut, SLok (ksBlockE C.p (aLane C.p 7) sh (kc (pbB C))) = true)
    (htT : tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) + 40 ≤ 8 * T)
    (hpubT : C.p.pubTab < (shapesOf C D).length)
    (hpubτ : ((shapesOf C D).map (·.τ)).getD C.p.pubTab 0 = 10)
    (hRmax : ∃ s ∈ shapesOf C D, C.p.tableRounds ≤ s.τ)
    (hnf : (fixIdx (shapesOf C D) C.p.pubTab).length ≤ 2 ^ C.p.accLog)
    (hzL : tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) / 8 + 9 * C.p.accLog + 3 * (accVars + 1) + 9 +
      5 + 2 < T)
    (hP4 : 8 * (tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) / 8 + 9 * C.p.accLog + 3 * (accVars + 1) +
      9) + 24 = P4)
    (hlr : LayOk (cfgRec C.p (posBase C) (pwBase C)) T = true)
    (hlm : LayOk (cfgMain C.p (posBase C) (pwBase C)) T = true) :
    HarStatic C D T P4 P5 P6 P7 P8 := by
  obtain ⟨⟨e0, e1, e2, e5, w5, w6, ks0, ks1, ks2, ks7, l7, l8⟩, hn, hk, hq, hqw, hqk, hTw, hTgk, hTr, hTv,
    hTrk, hTvk, hD, hDk, hTlk, hTlk', hB, hB2, hK, hld, hbP, hbT, htP, h10, hRacc, hdk1, hH, hT29, hlog,
    hP8, hop⟩ := hN
  exact ⟨⟨e0, e1, e2, e5, w5, w6, ks0, ks1, ks2, ks7, l7, l8⟩, hn, hk, hlay, hlayk, hq, hqw, hqk, hTw, hTgk,
    hTr, hTv, hTrk, hTvk, hD, hDk, hTlk, hTlk', hB, hB2, hK, okE, hld, hbP, hbT, htP, htT,
    hpubT, hpubτ, h10, hRmax, hRacc, hdk1, hnf, hzL, hH, hP4, hT29, hlog, hlr, hlm, hP8, hop⟩

-- FIN-BV's `PosLanes` at `P20` (`posLanes_of` … `posLanesB20`, `posLanesR20`, `posLanesM20`): `LvmFinPos`.

set_option maxRecDepth 200000 in
/-- **The PoW class's static facts** (`pw20`): every opening's first positions entry is at index `≥ 2`
inside the plan (its PoW entry is the one before), the PoW fields are input cells, `g < 64`. -/
theorem powStatic20 : (∀ k < (opens P20).length, 2 ≤ ((opens P20).getD k default).pe ∧
      ((opens P20).getD k default).pe < (plan P20).length) ∧
    pwB cfg20 + (opens P20).length ≤ nK cfg20 ∧ 1 ≤ 64 - P20.grind := by
  rw [Lvm.PlanChk.length_P20]
  decide +kernel

/-- **FIN-BV's `hbs`** (`sBits20`): the `s'` byte shifts' output cells are input cells. -/
theorem hbs20 : bsB cfg20 + 256 ≤ nK cfg20 := posLanesB20.2.2

end Lvm.Fin
