-- New for lvm6 (WP MA): the sponge phase's claims are multiaffine (W1 F-3), WP SPH's `spongePhase6`.
import Lvm6MultiaffBase
import Lvm6SpProg

/-!
# The sponge phase's claims are multiaffine

**`spongePhase6_ma`** is the unfolded body of WP ASM's `Stmt.spongeMA` at `SP.spongePhase6`: every
claim `spS` returns (`c_out`, the 25 tied lanes, `Y`, `in`, the stream `M`, `X`) is an `eqPt` claim
or a finite sum of scalar multiples of `eqPt` claims (`isMA_finsetSum`). The statement quantifies
over the members of the list, so it does not depend on the claims' order.
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.EndToEnd.Front Lvm.E2V Finset
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-- The three parts of `IsMA (μ + 1) f`. -/
theorem IsMA.parts {μ : ℕ} {f : List E2 → E2} (h : IsMA (μ + 1) f) :
    (∀ t p, p.length = μ → f (t :: p) = (1 + t) * f (0 :: p) + t * f (1 :: p)) ∧
      IsMA μ (fun p ↦ f (0 :: p)) ∧ IsMA μ (fun p ↦ f (1 :: p)) := h

/-- A finite sum of multiaffine functions. -/
theorem isMA_finsetSum {ι : Type} (s : Finset ι) : ∀ {μ : ℕ} (F : ι → List E2 → E2),
    (∀ i ∈ s, IsMA μ (F i)) → IsMA μ (fun p ↦ ∑ i ∈ s, F i p)
  | 0, _, _ => trivial
  | μ + 1, F, h => by
    refine ⟨fun t p hp ↦ ?_, isMA_finsetSum s (fun i p ↦ F i (0 :: p)) fun i hi ↦
      (h i hi).parts.2.1, isMA_finsetSum s (fun i p ↦ F i (1 :: p)) fun i hi ↦ (h i hi).parts.2.2⟩
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi ↦ (h i hi).parts.1 t p hp

/-- **The sponge phase's claims are multiaffine** (`Stmt.spongeMA SP.spongePhase6`). -/
theorem spongePhase6_ma :
    ∀ sh x, RetAll (fun o : TreeOut ↦ ∀ c ∈ o.claims, c.Multiaffine sh.M) (SP.spongePhase6 sh x) := by
  intro sh x
  unfold SP.spongePhase6
  split_ifs
  · unfold SP.spongeBody
    refine RetAll.bind (RetAll.of_forall (fun o ↦ ?_) _)
    refine RetAll.bind (RetAll.of_forall (fun lk ↦ ?_) _)
    show ∀ c ∈ (SP.spS o lk).claims, c.Multiaffine sh.M
    intro c hc
    simp only [SP.spS, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | ⟨l, -, rfl⟩ | rfl | rfl | rfl | rfl
    · exact eqClaim_multiaffine _ _ _
    · exact eqClaim_multiaffine _ _ _
    all_goals
      refine IsMA.multiaffine ?_
      dsimp only [SP.cY, SP.cIn, SP.cM, SP.cX]
      exact isMA_finsetSum _ _ fun _ _ ↦ (isMA_eqPt _ _).smul _
  · trivial

end Lvm6
