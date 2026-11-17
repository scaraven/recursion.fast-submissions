-- New for lvm2 E2-FT (E2F-C): the per-stage facts S2GF's node soundness asks (the analogues of roll 11's `hQ20`,
-- `ksSplit_P20`, `sizes_P20`'s sponge blocks, `contRows P20`), decided once at `P20F` / `cfgF20`.
import LvmE2QPlanF
import LvmE2QAsm
import LvmQAsmFactsL
import LvmNodeSoundKS
import LvmE2VMid

-- (GOLF2: 1 declarations that `certified` does not use moved verbatim to `LvmE2QHarFrontOff`, outside its import closure.)

/-!
# S2GF's per-stage facts

* **`hQF20`**: Q_link's static checks on the S2GF node program's layout (`QOk P20F (lay cfgF20)`, as `hQ20`).
* `P20F_withF`: `P20F` at its own stage record is `P20F`.
* `ksSplit_P20F`, `spongeBlocks_P20F`: `KS`'s split row and the trace's sponge blocks at S2GF; **`contRowsF_eq`**:
  E2F-V's `contRowsF` is `contRows P20F`, so the generic `KS` lemmas (`GoodKP`, `sigKSin_of_goodKP`,
  `traceDigest_of_goodKP`) apply to S2GF's good pair.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay

set_option maxRecDepth 200000 in
/-- **Q_link's static checks at S2GF** (`qOkB` decided as `qOkF`, as `hQ20`). -/
theorem hQF20 : QOk P20F (lay cfgF20) :=
  qOk_of streamOk_P20F rfl (by rw [← qOkF_eq]; unfold P20F; rw [P20_eq]; decide +kernel)

/-- `KS`'s split row at S2GF (as `P20`'s). -/
theorem ksSplit_P20F : ksSplit P20F = 7680 := by decide

/-- The trace's sponge blocks at S2GF: `4,512 = nBlk (hashedLen P20F)`. -/
theorem spongeBlocks_P20F : spongeBlocks P20F = 4512 ∧ hashedLen P20F = 613496 :=
  ⟨checks_P20F.1.2.2.2.2.1, checks_P20F.1.2.2.1⟩

theorem spongeBlocks_nBlk_P20F : spongeBlocks P20F = Lvm.KSponge.nBlk (hashedLen P20F) := by
  rw [spongeBlocks_P20F.1, spongeBlocks_P20F.2]; rfl

/-- **E2F-V's `contRowsF` is `contRows P20F`.** -/
theorem contRowsF_eq : E2V.contRowsF = contRows P20F := by
  unfold E2V.contRowsF contRows
  rw [show spongeBlocksF P20F accVF = spongeBlocks P20F from rfl, show ksSplit P20F = ksSplit P20 from rfl]

end Lvm.E2Q
