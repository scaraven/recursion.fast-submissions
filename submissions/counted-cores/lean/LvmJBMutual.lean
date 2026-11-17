-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBMutual.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBMain

-- (GOLF2: 5 declarations that `certified` does not use moved verbatim to `LvmNodeSoundTOff`, outside its import closure.)

/-!
# Haböck's mutual correlated agreement

Ordinary correlated agreement says the pair `(u₀, u₁)` agrees with a pair of codewords
`(v₀, v₁)` on many coordinates.  Haböck's strengthening says more: for almost every
parameter `z`, the agreement set of the *line point* `u₀ + z u₁` is not merely larger
than the correlated agreement set — it is **equal** to it.  In other words a random `z`
reveals no accidental agreements.

The inclusion `Λ ⊆ Λ_z` is immediate.  The content is the reverse, and it is the same
one-affine-root observation that drives the §4 endgame: a coordinate outside `Λ` can
produce an accidental agreement for at most one value of `z` (`eq_of_mem_pairDisagree`).
So the sets `Λ_z \ Λ` are pairwise disjoint subsets of the correlated disagreement set
`E`, and at most `|E|` parameters can fail.

Combining with §4 (`card_pairDisagree_le`, which bounds `|E|` by `e`) gives the sharp
form: **mutual correlated agreement fails for at most `e` parameters** — no separate
argument, and no loss beyond the distance bound already assumed.
-/

namespace JBAgreement

open Finset Polynomial

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The correlated agreement set `Λ`: coordinates where *both* words match. -/
def corrAgree (u₀ u₁ v₀ v₁ : ι → F) : Finset ι :=
  univ.filter fun x => u₀ x = v₀ x ∧ u₁ x = v₁ x

/-- The agreement set `Λ_z` of the line point `u₀ + z u₁` with `v₀ + z v₁`. -/
def lineAgree (u₀ u₁ v₀ v₁ : ι → F) (z : F) : Finset ι :=
  univ.filter fun x => u₀ x + z * u₁ x = v₀ x + z * v₁ x

omit [Field F] [DecidableEq ι] in
@[simp] lemma mem_corrAgree {u₀ u₁ v₀ v₁ : ι → F} {x : ι} :
    x ∈ corrAgree u₀ u₁ v₀ v₁ ↔ (u₀ x = v₀ x ∧ u₁ x = v₁ x) := by simp [corrAgree]

omit [DecidableEq ι] in
@[simp] lemma mem_lineAgree {u₀ u₁ v₀ v₁ : ι → F} {z : F} {x : ι} :
    x ∈ lineAgree u₀ u₁ v₀ v₁ z ↔ u₀ x + z * u₁ x = v₀ x + z * v₁ x := by
  simp [lineAgree]

end JBAgreement
