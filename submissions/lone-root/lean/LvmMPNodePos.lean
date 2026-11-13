-- New for lvm2 roll 11 (M′ `S2GM`, R11-N): FIN-BV's `PosLanes` for the child's one opening (`C_main`'s, openings
-- `0 … 2` from `openU P20 + 15`), as B1's `posLanesM20` (L-D's, in `LvmFinPos`; removed at M′) was for its second.
import LvmFinPos
import LvmQAsmArith2WhirP

/-!
# The child's position lanes at `S2GM`

* **`posLanesKS20`** (`decide +kernel` on `posLanesKB`, the extractor's blocks): level `i` of `C_main`'s opening is
  Q_link's opening `i`; its first positions entry starts block `1268`, `1304`, `1322` [exact, evaluated].
* **`posLanesS20`**: `PosLanes P20 g ood mainLevels (openU P20 + 15) 0` (`posLanes_of`, `posLanesR_of_K`).
-/

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Har Lvm.QLink

set_option maxRecDepth 200000 in
/-- The child's opening's position lanes through the extractor's blocks (one decision). -/
theorem posLanesKS20 : PosLanesK P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) 0 [1268, 1304, 1322] := by
  have h : posLanesKB P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) 0 [1268, 1304, 1322] = true := by
    decide +kernel
  exact posLanesK_of_B h

/-- **FIN-BV's `PosLanes` for the child's `C_main` opening** at `S2GM` (`BVT.posm`'s `hPL`). -/
theorem posLanesS20 : PosLanes P20 P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) 0 :=
  posLanes_of Lvm.QAsm.hS20.1 (posLanesR_of_K posLanesKS20)

end Lvm.Fin
