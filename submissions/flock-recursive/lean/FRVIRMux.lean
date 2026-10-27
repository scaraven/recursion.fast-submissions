-- New for `flock-recursive` (BLUEPRINT §4.3 "The mux", §7, stage S-E2; B-2, B-7).
import FRVIRCompile

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

/-- The mux's selector forms: M's `one` cell and the three selector cells. -/
def muxP (one : ℕ) (cells : Kind → ℕ) : Params := ⟨Lin.cell one, fun κ => Lin.cell (cells κ)⟩

/-- **`compileMux`**: `compile` in gated mode. -/
def compileMux (one : ℕ) (cells : Kind → ℕ) (base : ℕ) (ops : List Op) : CS :=
  compile (muxP one cells) base ops

/-- The one-hot rows of the selector cells (A.8 `assertOneHot`: 3 products, 1 linear). -/
def OneHotRows (w : Asg) (one : ℕ) (cells : Kind → ℕ) : Prop :=
  w (cells .L32) * w (cells .P30) = 0 ∧ w (cells .L32) * w (cells .N30) = 0 ∧
  w (cells .P30) * w (cells .N30) = 0 ∧
  w one * (w (cells .L32) + w (cells .P30) + w (cells .N30)) = w one

/-- A cell is a bit (Lr's Booleanity). -/
def IsBitCell (w : Asg) (i : ℕ) : Prop := w i = 0 ∨ w i = 1

/-- **The one-hot rows fix the kind**: Boolean selector cells satisfying them are one-hot. -/
theorem oneHot_of_rows {w : Asg} {one : ℕ} {cells : Kind → ℕ} (hone : w one = 1)
    (hb : ∀ κ, IsBitCell w (cells κ)) (h : OneHotRows w one cells) :
    ∃ κ, SelOk w (muxP one cells) κ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hone, one_mul] at h4
  have bL := hb .L32; have bP := hb .P30; have bN := hb .N30
  simp only [muxP, SelOk, Lin.ev_cell, hone, true_and]
  rcases bL with eL | eL <;> rcases bP with eP | eP <;> rcases bN with eN | eN <;>
    simp only [eL, eP, eN, add_zero, zero_add, mul_one, one_mul, mul_zero, zero_mul] at h1 h2 h3 h4
  all_goals first
    | exact absurd h4 zero_ne_one
    | exact absurd h1 one_ne_zero | exact absurd h2 one_ne_zero | exact absurd h3 one_ne_zero
    | skip
  · exact ⟨.N30, fun κ => by cases κ <;> simp [eL, eP, eN]⟩
  · exact ⟨.P30, fun κ => by cases κ <;> simp [eL, eP, eN]⟩
  · exact ⟨.L32, fun κ => by cases κ <;> simp [eL, eP, eN]⟩

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

end Circ
end FR
