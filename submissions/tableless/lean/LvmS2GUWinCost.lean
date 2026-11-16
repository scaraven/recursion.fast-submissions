-- New for lvm2 U-TAPE (UT-L, 2026-11-16; lead decision D-WIN (B), re-freeze of UTAPE-STMT 15b): the cost of S2GU's
-- level-0 decoder (`dec0U`: the shape test, then the window `32 … 39` or `40 … 47`; both `c0Model 19 19 17 8`) and the
-- fuel bound, unchanged from M′'s (`2^44.52`).
import LvmXSComputes

/-!
# The S2GU decoder's cost (D-WIN (B))

**`decMPU_le`**, **`decMPU_fuel`** (UTAPE-STMT 15b): with S2GU's level-0 decoder (`dec0U`, the stage-`3` branch of
`dec0S`; `cost_dec0S`: at most `25,267,547,498,264 + 16`, `2^44.52`), levels 1–2 and the memory, the decoders stay
`≤ 2^45` and fit the declared fuel `decBudget t` (`fuel_base = 2^46`) with any further `R ≤ 2^45` steps.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- **The S2GU decoders with the grown memory are below `2^45`** (in fact `2^44.53`). -/
theorem decMPU_le (st : XStage) (d1 w1 a1 f1 o1 d2 w2 a2 f2 o2 t : ℕ) :
    2 ^ 26 + cost (decMP2IR d2 w2 a2 f2 o2) t + cost (decMP1IR d1 w1 a1 f1 o1) t + cost (dec0S st) t ≤ 2 ^ 45 := by
  have h0 := cost_dec0S st t
  rw [cost_decMP2IR, cost_decMP1IR]; omega

/-- **UTAPE-STMT 15b** (owner L): **the fuel bound at S2GU**: the three decoders, a memory of `2^26` words and any
`R ≤ 2^45` further steps fit the declared `decBudget t` (`fuel_base = 2^46` unchanged). -/
theorem decMPU_fuel (st : XStage) (d1 w1 a1 f1 o1 d2 w2 a2 f2 o2 R t : ℕ) (hR : R ≤ 2 ^ 45) :
    2 ^ 26 + cost (decMP2IR d2 w2 a2 f2 o2) t + cost (decMP1IR d1 w1 a1 f1 o1) t + cost (dec0S st) t + R ≤
      decBudget t := by
  have h0 := cost_dec0S st t
  rw [cost_decMP2IR, cost_decMP1IR, decBudget, fuelBase, fuelPerWord]
  have h2 : 0 ≤ (2 ^ 13 - 16) * t := Nat.zero_le _
  (clear * - hR h0 h2; omega)

end Lvm.XS
