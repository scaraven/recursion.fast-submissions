-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §0.4, §2): the circuit theorem of the typed backend. The
-- wiring relation is `Program.Holds` and `Program.Asserts` on the memory read off the words (`holds_of_wiring`,
-- L-B); then WP-10's `Program.interp_unique` (`LvmLoopInterp`, unchanged) gives the interpreter (`typed_sound`).
import LvmTypedLHolds

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

/-- **Every non-`readd` instance's relation holds** without the mini-bus (L-D's `nodeT20`: QLT's static reads need
the address rows' relations first): with the program check, on a checked layout, with `z(one) = 1` and the wiring
relation. -/
theorem rowDef_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) {i : Inst} (hi : i ∈ Q.insts)
    (hop : ∀ lo m, i.row.op ≠ .readd lo m) : Q.RowDef (memOf lay z) i :=
  (lh_row Q lay z hwf hlay hone h hi fun lo m h' ↦ absurd h' (hop lo m)).1

/-- **Every instance's gated assertion holds** (no `ReaddOk` needed). -/
theorem rowAssert_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) {i : Inst} (hi : i ∈ Q.insts) :
    Program.RowAssert (memOf lay z) i := by
  by_cases hrd : ∃ lo m, i.row.op = .readd lo m
  · obtain ⟨lo, m, hop⟩ := hrd
    simp only [Program.RowAssert, hop]
  · exact (lh_row Q lay z hwf hlay hone h hi fun lo m h' ↦ absurd ⟨lo, m, h'⟩ hrd).2

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
/-- **The wiring relation is the program's relations** (B-DES §2): with the program check (for the operand
counts: a `loadE` row has its three operands), on a checked layout, with `z(one) = 1`, the relation at every slot
and the mini-bus obligation, every row relation and every gated assertion holds on the memory read off `z`.
Owner **L-B**. -/
theorem holds_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) (hrd : ReaddOk Q (memOf lay z)) :
    Q.Holds (memOf lay z) ∧ Q.Asserts (memOf lay z) := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ rowAssert_of_wiring Q lay z hwf hlay hone h hi⟩
  by_cases hr : ∃ lo m, i.row.op = .readd lo m
  · obtain ⟨lo, m, hop⟩ := hr
    exact hrd i hi lo m hop
  · exact rowDef_of_wiring Q lay z hwf hlay hone h hi fun lo m h' ↦ hr ⟨lo, m, h'⟩

/-- **The typed backend's circuit theorem** (B-DES §2): `holds_of_wiring`, then `Program.interp_unique`
(`LvmLoopInterp`, unchanged). The memory read off the words is the interpreter's on every cell, and the
interpreter's assertions hold. -/
theorem typed_sound (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (inK : Array FK)
    (inE : Array FE) (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (hlay : lay.Ok Q) (hone : z lay.one = 1)
    (h : WiringRel Q lay z) (hrd : ReaddOk Q (memOf lay z)) (hin : Q.Inputs (memOf lay z) inK inE)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) (hinb : (Q.interp inK inE).inb = true) :
    (memOf lay z).Agrees (Q.interpMem inK inE) (Q.cells .K) (Q.cells .E) ∧
      (Q.interp inK inE).ok = true := by
  obtain ⟨hH, hA⟩ := holds_of_wiring Q lay z hwf hlay hone h hrd
  obtain ⟨hag, hiff⟩ := Q.interp_unique hwf inK inE hsz _ hin hH hinj hinb
  exact ⟨hag, hiff.mpr hA⟩

end Lvm.Typed
