-- New for lvm2 (CR-K, KS14): where `KS` takes its messages from, and the one definition of the `C_main`
-- words the node program reads `KS`'s output and `X` lanes from.
import LvmSchedule
import LvmLayout

/-!
# KS14: the split of `KS`'s message rows

`KS` has `2^ksLog` rows. Rows `j < ksSplit p` take their message lanes from the stream columns
`M_l[j]`; rows `j ≥ ksSplit p` take them from `X_l[j − ksSplit p]`, 17 columns of `2^ksXLog p` words. (M′,
`S2GM`: both are `C_main`'s stream block `S`, column `l` at `S + l·2^recRowsLog`; `X_l` is its rows from the
split.) The rows from the split are a subcube: their top `ksLog − ksXLog` bits are all one,
so V_S's selector is the product of those coordinates of `ρ'`.

* KS14 (`ksLog ≤ recRowsLog`, `P20`): `X` has `2^(ksLog − 4)` rows, the split is `2^14 − 2^10 = 15,360`,
  the selector `x₁₃x₁₂x₁₁x₁₀`.
* v1's layout (`ksLog = recRowsLog + 1`, `P8`): `X` has `2^recRowsLog` rows, the split is `2^recRowsLog`,
  the selector `x_r` (one variable).

**`ksYW20 l i`**, **`ksXW20 l i`**: the `C_main` word of `KS`'s output lane `l < 14` (slot `50 + l`) and
of `X_l`, row `i`, at `P20`. Every input bundle of the node program over these columns starts at one
of them (`ys`: `ksYW20 l (ksSplit P20)`, `md`: `ksYW20 l (spongeBlocks P20 − 1)`, `xs`: `ksXW20 l 0`).
-/

set_option autoImplicit false

namespace Lvm

/-- `X`'s rows (log): `ksLog − 4` under KS14 (`ksLog ≤ recRowsLog`), else `recRowsLog`. -/
def ksXLog (p : Params) : Nat := if p.ksLog ≤ p.recRowsLog then p.ksLog - 4 else p.recRowsLog

/-- **The first `KS` row whose message comes from `X`**: `2^ksLog − 2^ksXLog`. -/
def ksSplit (p : Params) : Nat := 2 ^ p.ksLog - 2 ^ ksXLog p

theorem ksXLog_P20 : ksXLog P20 = 9 := by decide

theorem ksSplit_P20 : ksSplit P20 = 7680 := by decide

theorem ksXLog_P8 : ksXLog P8 = 10 := by decide

theorem ksSplit_P8 : ksSplit P8 = 15360 := by decide

namespace CMain

/-- **`KS`'s output lane `l < 14`, row `i`, at `P20`**: `KS` slot `50 + l` of the `KS` block. -/
def ksYW20 (l i : Nat) : Nat := ksOff20 + 2 ^ P20.ksLog * (50 + l) + i

/-- **`X_l`'s row `i` at `P20`** (`KS` row `ksSplit P20 + i`'s message lane `l`; M′, `S2GM`: row
`ksSplit P20 + i` of the stream block's column `l`, so the column stride is `2^recRowsLog`). -/
def ksXW20 (l i : Nat) : Nat := xOff20 + l * 2 ^ P20.recRowsLog + i

/-- **The stream block's column `c`, row `i`, at `P20`** (M′: `C_rec`'s old word `c·2^14 + i`). -/
def sW20 (c i : Nat) : Nat := sOff20 + c * 2 ^ P20.recRowsLog + i

theorem ksYW20_eq (l i : Nat) : ksYW20 l i = 5242880 + 8192 * (50 + l) + i := rfl

theorem ksXW20_eq (l i : Nat) : ksXW20 l i = 5774848 + l * 16384 + i := rfl

theorem sW20_eq (c i : Nat) : sW20 c i = 5767168 + c * 16384 + i := rfl

end CMain

end Lvm
