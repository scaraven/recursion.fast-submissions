-- New for lvm6 (PORT17 L2: split from `Lvm6NodeBits`, WP NODE3 F2). A `BITS` class row as the layout's two aux
-- blocks (`boolBlk6`, `outBlk6`), without `Lvm6NodeBits`' imports (the node theorem's modules), so the exporter's
-- layout solve (`Lvm6NodeLaySolve`) builds before N1.
import LvmQTypedBits

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits

/-- **Row `x` of class `S`'s rows** (one iteration; bit `z`'s word `w + z`): `S`'s chunk rows at the single row `x`
(`LvmQTypedBits`): 64 booleanity rows, then the word row (when `rd`) and the output rows. -/
def rowRows6 (S : BSpec) (w x : ℕ) : List ARow :=
  BSpec.chunkRows ⟨S.τ, 1, S.outs, S.rd, fun _ ↦ S.wc x, fun j _ ↦ S.oc j x, S.pl, 0, by intros; omega⟩ w 0 0

/-- Row `x` as one block (the one-block form, kept for reference). -/
def rowBlk6 (S : BSpec) (w x : ℕ) : ABlk := ⟨0, rowRows6 S w x⟩

/-- **The booleanity block of row `x`** (its 64 booleanity rows: exactly `2^6` slots, no padding). -/
def boolBlk6 (S : BSpec) (w x : ℕ) : ABlk := ⟨0, (rowRows6 S w x).take 64⟩

/-- **The word/output block of row `x`** (the word row and the output rows, on the booleanity block's bit words). -/
def outBlk6 (S : BSpec) (w x : ℕ) : ABlk := ⟨0, (rowRows6 S w x).drop 64⟩

end Lvm6.Node.Dep
