-- New for lvm6 (WP MA): the claims every phase of `prog6` returns are multiaffine (W1 F-3):
-- claim 0 (`commit6`), the tree batch (`K.treeProgS6`), the typed phase (`Ty.typedPhase6`).
import Lvm6MultiaffBase
import Lvm6AsmProg
import Lvm6TyStmt

/-!
# Every claim a phase returns is multiaffine

Each statement is the unfolded body of WP ASM's `Stmt.commitMA`, `Stmt.treeMA`, `Stmt.typedMA`
(`Lvm6AsmSpec` on `lvm6/ASM-ma`; `PhaseSpecs.maCommit/maTree/maTyped`), so `commit6_ma`,
`treeProgS6_ma`, `typedPhase6_ma_at inst` close them as they are:

* **`commit6_ma`**: claim 0 of §6.1 is `(eq(z₀, ·), y₀)`.
* **`treeProgS6_ma`**: the tree batch's claims are `(eq(c.1, ·), c.2)` for its 13 columns
  (`K.toS`), whatever the program read.
* **`typedPhase6_ma`**: the typed phase's seven claims: the `C_rec` claims (relayout point, `σ′`)
  under `recClaim`'s slot selector, the `C_main` claims (register sums of `eqAtF`, the mini-bus's
  three sums of `eq_above · eq` block weights).
* The sponge phase (`Stmt.spongeMA`) waits for WP SPH's `spongePhase6`: its claims are
  `eqClaims_multiaffine` when they are `(eq(a, ·), v)` as the tree's.
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.EndToEnd.Front Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Claim 0 and the tree batch -/

theorem commit6_ma (sh : Shape) :
    RetAll (fun c : StackClaim6 ↦ c.Multiaffine sh.M) (commit6 sh) := by
  unfold commit6
  refine RetAll.bind (RetAll.of_forall (fun _ ↦ ?_) _)
  refine RetAll.bind (RetAll.of_forall (fun _ ↦ ?_) _)
  refine RetAll.bind (RetAll.of_forall (fun z ↦ ?_) _)
  refine RetAll.bind (RetAll.of_forall (fun y ↦ ?_) _)
  exact eqClaim_multiaffine sh.M z y

theorem treeProgS6_ma (sh : Shape) (x : Hdr) :
    RetAll (fun t : TreeOut ↦ ∀ c ∈ t.claims, c.Multiaffine sh.M) (K.treeProgS6 sh x) := by
  unfold K.treeProgS6
  split_ifs
  · refine RetAll.bind (RetAll.of_forall (fun out ↦ ?_) _)
    exact eqClaims_multiaffine sh.M (K.treeColsS (sh.logN + 1) x.h out)
  all_goals trivial

/-! ## The typed phase -/

section Typed

open Lvm6.Mb Lvm6.Ty

theorem isMA_sumClaimG (nu : ℕ) (parts : List (E2 × LeanVM.Protocol.Verifier.Placement × List E2))
    (value : E2) (ν : ℕ) : IsMA ν (sumClaimG nu parts value).weight :=
  (isMA_listSum (fun p x ↦ p.1 * eqAboveG p.2.1 x * eqEvalF p.2.2 (x.take p.2.1.variableCount))
    parts fun p _ ↦ ((isMA_above p.2.1 (isMA_eqEvalF p.2.2) ν).smul p.1).congr fun x _ ↦ by
      ring).congr fun x _ ↦ by simp only [sumClaimG, sumF_eq_sum]

/-- The mini-bus's three claims on `C_main`. -/
theorem miniBusLProg6_ma (L : Lvm.M3.Lay) (tabs : List Lvm.M3.Tab) (μ : ℕ) :
    RetAll (fun cl : List ClaimE ↦ ∀ c ∈ cl, ∀ ν, IsMA ν c.1) (miniBusLProg6 L tabs μ) := by
  unfold miniBusLProg6
  refine RetAll.bind (RetAll.of_forall (fun b ↦ ?_) _)
  show ∀ c ∈ (mbClaimsG L.nuMain tabs b).map (·.onStack), ∀ ν, IsMA ν c.1
  intro c hc ν
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hc'
  exact isMA_above _ (isMA_sumClaimG _ _ _) ν

theorem isMA_regClaimE (Ti : TInst6) (s : Lvm.Typed.YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) (ν : ℕ) :
    IsMA ν (regClaimE Ti s w r v).1 := by
  refine (isMA_listSum (fun reg X ↦ if (reg.src == s) = true then ((List.range (2 ^ reg.log)).map
    fun i ↦ eqAtF r (reg.base + i) * eqAtF X (w (reg.base + i))).sum else 0) Ti.lay.yregs
      fun reg _ ↦ ?_).congr fun X _ ↦ by simp only [regClaimE, regSumT, regSumW]
  by_cases hS : (reg.src == s) = true
  · exact (isMA_listSum (fun i X ↦ eqAtF r (reg.base + i) * eqAtF X (w (reg.base + i)))
      (List.range (2 ^ reg.log)) fun i _ ↦ (isMA_eqAtF ν _).smul _).congr fun X _ ↦ by simp [hS]
  · exact (isMA_const 0 ν).congr fun X _ ↦ by simp [hS]

/-- The typed claims at `E2`, on both windows, at every length. -/
def TypedMA (out : OpenClaimsE) : Prop :=
  (∀ c ∈ out.1, ∀ ν, IsMA ν c.1) ∧ ∀ c ∈ out.2, ∀ ν, IsMA ν c.1

theorem typedProgE_ma (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (acc : List E2 × E2) :
    RetAll TypedMA (typedProgE Ti L pw acc) := by
  unfold typedProgE
  refine RetAll.bind (RetAll.of_forall (fun z ↦ ?_) _)
  refine RetAll.bind (RetAll.of_forall (fun w ↦ ?_) _)
  refine RetAll.bind (RetAll.of_forall (fun r ↦ ?_) _)
  refine RetAll.bind (RetAll.of_forall (fun _ ↦ ?_) _)
  refine RetAll.bind (RetAll.mono (fun cl hcl ↦ ?_) (miniBusLProg6_ma L Ti.mbT miniDepth))
  show TypedMA (typedClaimsE Ti w.1 w.2.2 r.1 r.2 cl)
  refine ⟨fun c hc ν ↦ ?_, fun c hc ν ↦ ?_⟩
  · simp only [typedClaimsE, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact isMA_above _ (isMA_eqEvalF _) ν
    · exact isMA_regClaimE _ _ _ _ _ ν
  · simp only [typedClaimsE, List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · exact isMA_regClaimE _ _ _ _ _ ν
    · exact isMA_regClaimE _ _ _ _ _ ν
    · exact hcl c hc ν

/-- **The typed phase's claims are multiaffine** (`recClaim` places the `C_rec` ones). -/
theorem typedPhase6_ma (sh : Shape) (i : TyInst6) :
    RetAll (fun out : List StackClaim6 ↦ ∀ c ∈ out, c.Multiaffine sh.M) (typedPhase6 sh i) := by
  unfold typedPhase6
  split
  · refine RetAll.bind (RetAll.mono (fun out hout ↦ ?_) (typedProgE_ma i.Ti L6 i.pw i.acc))
    show ∀ c ∈ claimsOnStack out, c.Multiaffine sh.M
    intro c hc
    simp only [claimsOnStack, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨c', hc', rfl⟩ | hc
    · exact (isMA_above ⟨19, recOff⟩ (hout.1 c' hc') sh.M).multiaffine
    · exact (hout.2 c hc sh.M).multiaffine
  · trivial

/-- `typedPhase6_ma` at an instance map `inst` (the form of WP ASM's `Stmt.typedMA`). -/
theorem typedPhase6_ma_at (inst : Hdr → TyInst6) :
    ∀ sh x, RetAll (fun ty : List StackClaim6 ↦ ∀ c ∈ ty, c.Multiaffine sh.M)
      (typedPhase6 sh (inst x)) :=
  fun sh x ↦ typedPhase6_ma sh (inst x)

end Typed

end Lvm6
