-- New for `flock-recursive` (BLUEPRINT §5.6, A.11, stage S-E3; track L-circ).
import FRVIRTplCore

/-!
# Controls of the template DSL (non-vacuity of `Gate.rows`, `Tpl.eqns_of_rows`)

* positive: a product gate's row and an inverse gate's three rows hold for the honest locals
  (`a·b`; `x⁻¹` and `x·x⁻¹`, for every `x`, `0` included), so `Eqns` is satisfiable and
  `inst_eqns`' hypothesis is not vacuous;
* negative: a wrong product or a wrong inverse of a nonzero value fails the rows.
-/

namespace FR
namespace Tpl

variable {e : Env}

/-- (+) The honest product satisfies its row. -/
theorem mul_rows_honest (a b : LinT) (k : ℕ) (h : e.loc k = a.ev e * b.ev e) :
    ∀ r ∈ (Gate.mul a b).rows k, r.Holds e := by
  intro r hr
  simp only [Gate.rows, List.mem_singleton] at hr; subst hr
  simp [RowT.Holds, h]

/-- (−) A wrong product fails its row. -/
theorem mul_rows_reject (h1 : e.one = 1) (a b : LinT) (k : ℕ) (h : e.loc k ≠ a.ev e * b.ev e) :
    ¬ ∀ r ∈ (Gate.mul a b).rows k, r.Holds e := fun hr => h (Gate.eqn_of_rows h1 k _ hr)

/-- (+) The honest inverse locals `x⁻¹`, `x·x⁻¹` satisfy the three rows, `x = 0` included. -/
theorem inv_rows_honest (h1 : e.one = 1) (a : LinT) (k : ℕ) (hi : e.loc k = (a.ev e)⁻¹)
    (hs : e.loc (k + 1) = a.ev e * (a.ev e)⁻¹) : ∀ r ∈ (Gate.inv a).rows k, r.Holds e := by
  intro r hr
  simp only [Gate.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  by_cases hx : a.ev e = 0
  · rcases hr with rfl | rfl | rfl <;> simp [RowT.Holds, hi, hs, hx, h1]
  · rcases hr with rfl | rfl | rfl <;> simp [RowT.Holds, hi, hs, hx, h1, mul_inv_cancel₀ hx]

/-- (−) A wrong inverse of a nonzero value fails the rows. -/
theorem inv_rows_reject (h1 : e.one = 1) (a : LinT) (k : ℕ) (h : e.loc k ≠ (a.ev e)⁻¹) :
    ¬ ∀ r ∈ (Gate.inv a).rows k, r.Holds e := fun hr => h (Gate.eqn_of_rows h1 k _ hr)

end Tpl
end FR
