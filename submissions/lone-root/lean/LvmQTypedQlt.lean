-- New for lvm2 (roll 8 = B1, B1-Q; B1-S0 "unclear" 2, B-DES §1.5): the static half of `ReaddOk`. QLT's 18,432 `readd`s
-- read stream cells at public addresses; the typed layout aliases each result to its target's word, so the read
-- holds by the alias and the address rows (kept as constraint rows), not by the mini-bus. Reuses `qltPadded`,
-- `qltTpl` (`LvmQLink*`, untouched) and `Program.RowDef` (`LvmLoopInterp`).
import LvmTyped
import LvmQLink

/-!
# QLT's reads are static

* **`StaticAt Q M i e`**: the `readd` instance `i` reads cell `e` of its memory in `M`: `e` is a cell, the address
  operand holds `g^e`, the result is cell `e`. **`rowDef_of_static`**: then its `RowDef` holds.
* **`readdOk_of_split`**: `ReaddOk Q M` from a split of the `readd` instances into the mini-bus's (their `RowDef`
  from the bus) and the static ones (a target each).
* **`qltTargets p lay`**: the target of each of the QLT loop's nine reads per entry: `e₁ + l` (`l ≤ 4`, the rows
  reading `α = g^{e₁}` and `g^l·α`) and `e₂ + l` (`l ≤ 3`), in template order (`qltTpl` rows 7–15). The layout
  solver aliases the result cell of row `7 + r` at iteration `k` to the word of stream cell
  `(qltTargets p lay)[9 k + r]`.
* **`qltTargets_gpow`**: the address the address rows compute is `g^{target}` (`g^l·g^{e} = g^{e + l}`), so
  `StaticAt` holds once the QLT cells hold their public values (`zOf`'s `qlt` region or constants) and the address
  rows hold (their `RowDef`, from the wiring relation: `lin` rows are constraint rows).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.QLink

/-- **A static read**: instance `i` reads cell `e` of its memory. -/
def StaticAt (Q : Program) (M : Mem) (i : Inst) (e : Nat) : Prop :=
  e < Q.cells i.row.ty ∧ (M.arg i 0).c₀ = FK.x ^ e ∧ M.res i = M.rd i.row.ty e

/-- **A static read's relation holds.** -/
theorem rowDef_of_static {Q : Program} {M : Mem} {i : Inst} {lo m e : Nat} (hop : i.row.op = .readd lo m)
    (h : StaticAt Q M i e) : Q.RowDef M i := by
  unfold Program.RowDef
  rw [hop]
  exact ⟨e, h.1, h.2.1.symm, h.2.2⟩

/-- **`ReaddOk` from a split**: every `readd` instance is the mini-bus's (`cap`, with its relation) or static. -/
theorem readdOk_of_split {Q : Program} {M : Mem} (cap : Inst → Prop)
    (hcap : ∀ i ∈ Q.insts, cap i → Q.RowDef M i)
    (hst : ∀ i ∈ Q.insts, ∀ lo m, i.row.op = .readd lo m → ¬ cap i → ∃ e, StaticAt Q M i e) :
    Lvm.Typed.ReaddOk Q M := by
  intro i hi lo m hop
  by_cases hc : cap i
  · exact hcap i hi hc
  · obtain ⟨e, he⟩ := hst i hi lo m hop hc
    exact rowDef_of_static hop he

/-- The targets of one QLT entry `(e₁, e₂, v)`'s nine reads, in template order. -/
def qltEntryTargets (x : Nat × Nat × Nat) : List Nat :=
  (List.range 5).map (x.1 + ·) ++ (List.range 4).map (x.2.1 + ·)

/-- **The QLT loop's static targets** (nine per entry of `qltPadded`). -/
def qltTargets (p : Params) (lay : Layout) : List Nat := (qltPadded p lay).flatMap qltEntryTargets

theorem qltEntryTargets_length (x : Nat × Nat × Nat) : (qltEntryTargets x).length = 9 := by
  simp [qltEntryTargets]

/-- **The address rows compute the targets' `g`-powers**: row `l` of `qltTpl` (`l < 4`) is `g^{l+1}·α`, and
`g^{l+1}·g^e = g^{e + l + 1}` (the `lin` row's relation `α + (g^{l+1} + 1)·α + 0`). -/
theorem qltTargets_gpow (e l : Nat) :
    Build.gpow e + (Build.gpow (l + 1) + 1) * Build.gpow e + 0 = Build.gpow (e + (l + 1)) :=
  Build.gpow_scale (l + 1) e

end Lvm.QTyped
