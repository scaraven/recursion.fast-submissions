-- New for `flock-recursive` (BLUEPRINT §4.3 "The mux", §7, stage S-E2; B-2, B-7).
-- RET-3: the declarations revision 4 reads moved to `FRVIRFinalsCoreSG`.
import FRVIRCompileSound
import FRVIRFinalsCoreSG

/-!
# The muxed node program: `compileMux`, `compile_mux_sound`

BLUEPRINT §4.3. Each slot of the node replays `gen Mux`: one op list for the three kinds, its
kind-dependent data selector-linear in three L bits `(s_L, s_P, s_N)`:

* a kind constant `κ(kind)` is the linear form `Σ_κ s_κ κ_κ` (no row);
* an assertion active for a subset of kinds is gated by `a = Σ_{κ active} s_κ`: one product row
  `a · (x − y) = 0` per component; a `keep` whose activity depends on the kind is a select
  `old + a·(new − old)` (one product per component);
* the selector is **one-hot by three product rows** `s_L s_P = s_L s_N = s_P s_N = 0` and the
  linear row `Σ s_κ = 1` (`oneHot_of_rows`; the sum alone admits `(1, 1, 1)` in characteristic 2,
  `three_hot_sum`, `three_hot_fails`).

`compileMux` is `FRVIRCompile.compile` with the selector forms the three cells (`muxP`).
**`compile_mux_sound`**: if the selector cells are one-hot at `κ` and the kind byte of `hdr` is
`κ`'s, the mux program's rows give `semIR (gen Mux) = some true`: the gated rows of the active kind
are the rows of `gen κ`, the others vacuous — `compile_sound` at `SelOk … κ`, nothing more.
-/

namespace FR
namespace Circ
open RecursionFast

/-- **`compile_mux_sound`** (BLUEPRINT §4.3): with the selector cells one-hot at `κ`, `hdr`'s kind
byte `κ`'s, and the run of the op list at `κ` using the trace up, the mux program's rows, imports
and foreign flags give acceptance of the **mux** program, and every tracked register's cells hold
its value. -/
theorem compile_mux_sound {impl : OpImpl} {inp : Input} {ops : List Op} {tr : Trace} {s : St}
    {w : Asg} {one : ℕ} {cells : Kind → ℕ} {κ : Kind} (base : ℕ)
    (hsel : SelOk w (muxP one cells) κ) (hbyte : inp.π.data[0]? = some κ.byte)
    (he : exec impl κ inp ops St.init tr = some (s, []))
    (hr : ∀ r ∈ (compileMux one cells base ops).rows, r.Holds w)
    (hi : ∀ i ∈ (compileMux one cells base ops).imp,
      RepS w ((compileMux one cells base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileMux one cells base ops).fors,
      flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    semIR impl ⟨.mux, ops⟩ inp tr = some true ∧
      ∀ i, RepS w ((compileMux one cells base ops).slot i) (rd s.regs i) := by
  have h := compile_sound base hsel he hr hi hf
  have hk : VProg.kindOn ⟨.mux, ops⟩ inp = κ := by
    simp [VProg.kindOn, hbyte, Kind.ofByte?_byte]
  refine ⟨?_, h.2⟩
  simp only [semIR, hk, he, h.1]

/-- The mux program is the fixed-kind program on a proof of kind `κ` (`kindOn`). -/
theorem semIR_mux_eq {impl : OpImpl} {inp : Input} {ops : List Op} {tr : Trace} {κ : Kind}
    (hbyte : inp.π.data[0]? = some κ.byte) :
    semIR impl ⟨.mux, ops⟩ inp tr = semIR impl ⟨.fixed κ, ops⟩ inp tr := by
  simp [semIR, VProg.kindOn, hbyte, Kind.ofByte?_byte]

/-! ## Controls -/

/-- Three-hot selector values `(1, 1, 1)`. -/
def threeHot : Asg := fun i => if i ≤ 3 then 1 else 0

/-- Selector cells `1, 2, 3`, `one` at `0`. -/
def cells3 : Kind → ℕ
  | .L32 => 1 | .P30 => 2 | .N30 => 3

/-- **Negative control (BP-C-R3-M1)**: the three-hot selector satisfies the linear row alone (in
characteristic 2, `1 + 1 + 1 = 1`) … -/
theorem three_hot_sum : threeHot 0 * (threeHot 1 + threeHot 2 + threeHot 3) = threeHot 0 := by
  decide

/-- … but fails the one-hot rows, so it fixes no kind. -/
theorem three_hot_fails : ¬ OneHotRows threeHot 0 cells3 := by
  intro h; exact absurd h.1 (by decide)

/-- Positive control: the selector one-hot at `'N'`. -/
def hotN : Asg := fun i => if i = 0 ∨ i = 3 then 1 else 0

theorem hotN_rows : OneHotRows hotN 0 cells3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem hotN_selOk : SelOk hotN (muxP 0 cells3) .N30 :=
  ⟨by decide, fun κ => by cases κ <;> decide⟩

/-- A program whose gated assertion depends on the kind: `x := [κ = 'N'] ? 0 : 1`, assert
`x = 0` for every kind. -/
def kindProg : List Op :=
  [.const fun κ => .f (if κ = .N30 then 0 else 1), .const fun _ => .f 0, .assertEq 0 1 allK]

/-- **Positive control**: under the selector one-hot at `'N'`, the mux rows of `kindProg` hold. -/
theorem kindProg_rows_N : ∀ r ∈ (compileMux 0 cells3 10 kindProg).rows, r.Holds hotN := by
  decide

/-- **Negative control (a wrong child kind)**: under the selector one-hot at `'L'` the same rows
fail — the selector, not the prover, picks the kind's constants. -/
def hotL : Asg := fun i => if i = 0 ∨ i = 1 then 1 else 0

theorem kindProg_rows_L : ¬ ∀ r ∈ (compileMux 0 cells3 10 kindProg).rows, r.Holds hotL := by
  decide

/-! ## Controls of S-E5's compiler changes

* the **materialised select** (`muxOut`, F-9): the output cell must hold the selected value;
* an assertion **off for every kind** emits no row, the same assertion on for a kind is a live row;
* the **tensor `eqTable`**'s product rows (`prodRows`, on a 2 × 2 instance; the tables are
  `eqRows`, whose rows S-E2's controls exercise): honest products hold, a wrong one fails. -/

/-- `selectHalf` of `0` and `1` by the bit `1` (its output on the fresh cell `10`). -/
def selProg : List Op :=
  [.const fun _ => .f 0, .const fun _ => .f 1, .const fun _ => .bit true, .selectHalf 2 0 1]

/-- The selector one-hot at `'N'`, the output cell holding the selected `1`. -/
def selOk : Asg := fun i => if i = 0 ∨ i = 3 ∨ i = 10 then 1 else 0

/-- The output cell holding the other operand, `0`. -/
def selBad : Asg := fun i => if i = 0 ∨ i = 3 then 1 else 0

/-- **Positive control**: the honest select satisfies the materialised row. -/
theorem sel_rows_honest : ∀ r ∈ (compileMux 0 cells3 10 selProg).rows, r.Holds selOk := by
  decide

/-- **Negative control**: the unselected value fails it. -/
theorem sel_rows_reject : ¬ ∀ r ∈ (compileMux 0 cells3 10 selProg).rows, r.Holds selBad := by
  decide

/-- An assertion off for every kind: no row. -/
theorem off_rows_none :
    (compileMux 0 cells3 10 [.const fun _ => .f 1, .assertZero 0 fun _ => false]).rows = [] := by
  decide

/-- The same assertion on for every kind is a live row: it fails on the nonzero value. -/
theorem on_rows_reject :
    ¬ ∀ r ∈ (compileMux 0 cells3 10 [.const fun _ => .f 1, .assertZero 0 allK]).rows,
      r.Holds hotN := by
  decide

/-- The tensor's product rows for `lo = (w₁, w₂)`, `hi = (w₃, w₄)` on the cells `10 … 13`. -/
def prodCtl : List Row := prodRows (CS.init 10) [Lin.cell 1, Lin.cell 2] [Lin.cell 3, Lin.cell 4] 0

/-- `lo = (1, 0)`, `hi = (1, 1)` and their honest products `(1, 0, 1, 0)`. -/
def prodOk : Asg := fun i => if i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 10 ∨ i = 12 then 1 else 0

/-- The product `lo_0 · hi_1` (cell `12`) set to `0`. -/
def prodBad : Asg := fun i => if i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 10 then 1 else 0

/-- **Positive control**: the honest products satisfy the tensor's product rows. -/
theorem prod_rows_honest : ∀ r ∈ prodCtl, r.Holds prodOk := by decide

/-- **Negative control**: a wrong product fails them. -/
theorem prod_rows_reject : ¬ ∀ r ∈ prodCtl, r.Holds prodBad := by decide

end Circ
end FR
