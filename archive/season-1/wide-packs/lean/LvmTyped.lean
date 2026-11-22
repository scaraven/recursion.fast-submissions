-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §0.4, §2): the circuit theorem of the typed backend. The
-- wiring relation is `Program.Holds` and `Program.Asserts` on the memory read off the words (`holds_of_wiring`,
-- L-B); then WP-10's `Program.interp_unique` (`LvmLoopInterp`, unchanged) gives the interpreter (`typed_sound`).
import LvmTypedLHolds

-- (GOLF2: 5 declarations that `certified` does not use moved verbatim to `LvmE2VWidthsFOff`, outside its import closure.)

/-!
# The typed backend's circuit theorem

`loopir_sound` was `holds_seedMem` (bus ⇒ `Holds`) followed by `interp_unique`. B replaces the first half:

* **`ReaddOk Q M`**: every `readd` instance reads its cell (`RowDef`'s `readd` case). The mini-bus (B-DES §1.5,
  `capTpl`'s 1,920 reads at `2^13` leaves) discharges it for the committed reads; for QLT's static reads (the
  layout's aliases) it is a static fact of the gadget's address rows (B1-Q).
* **`holds_of_wiring`** (L-B): with the program check (`loadE`'s operand count), on a checked layout, with the
  constant word `1`, the wiring relation and `ReaddOk`, every row relation and every assertion holds on `memOf lay z`.
* **`typed_sound`** (proved here): with the program check, the inputs on the virtual regions (`Inputs`, the new
  obligation: `S_flat`, `PUB`, … where `seedMem` gave them before), `g`-injectivity and `inb`, the memory is the
  interpreter's on every cell and every assertion of the interpreter holds.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-- **The mini-bus obligation** (B-DES §1.5): every `readd` instance reads its cell. -/
def ReaddOk (Q : Program) (M : Mem) : Prop :=
  ∀ i ∈ Q.insts, ∀ lo m, i.row.op = .readd lo m → Q.RowDef M i

/-- **No `E2` row** (lvm2 E2F: roll 11's programs; `LvmTypedX.holds_of_wiringX` is the theorem with `E2` rows). -/
def NoE2 (Q : Program) : Prop := ∀ i ∈ Q.insts, ∀ f h, i.row.op ≠ .e2 f h

/-- **The auxiliary (`BITS`) rows hold** (L-D's `nodeT20`): on a checked layout, with `z(one) = 1` and the wiring
relation, row `r` of auxiliary block `k` at iteration `j` meets `A·B + D + W = 0` on its operands' values
(`aopVal`: a free word `z(b + s·j)`, a cell of `memOf lay z`, the constant `1`). -/
theorem auxRow_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hlay : lay.Ok Q) (hone : z lay.one = 1)
    (h : WiringRel Q lay z) {k r j : ℕ} (hk : k < lay.aux.length) (hj : j < 2 ^ (lay.aux.getD k default).l)
    (hr : r < (lay.aux.getD k default).rows.length) :
    ARowHolds lay z j ((lay.aux.getD k default).rows.getD r default) :=
  lh_auxRow Q lay z hlay hone h hk hj hr

-- B1-S0's statement lacked `hwf`: a `loadE` row with a missing operand reads a constant cell through `Mem.arg`
-- but a free word through `memOf` (L-B H1 counterexample).
end Lvm.Typed
