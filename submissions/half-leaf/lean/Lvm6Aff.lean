-- New for lvm6 (WP M1). The affine MCA (CWYZ26) in the form the affine opening (WP W1) consumes.
-- Paper: Chiesa–Weissenberg–Yogev–Zheng, "Affine Combiners for Reed–Solomon Proximity Gaps", cited as
-- CWYZ26. The proofs are the vendored leanVM `AffineCombiner*` files (`Lvm6Aff*`, Apache-2.0, see
-- `LICENSE-leanVM`, `LICENSE-ArkLib`, `LICENSE-CompPoly`); this module only removes the characteristic
-- argument (`p := ringChar F`) and names the three statements for lvm6.
import Lvm6AffFoldRel
import Lvm6AffDeployed

/-!
# The affine MCA for lvm6 (BLUEPRINT T3)

Fix a finite field `F`, an evaluation domain `dom : ι ↪ F` of `n = |ι|` points, the two halves
`f g : ρ → ι → F` of an interleaved word (lanes `ρ`), a degree `d`, an agreement `A` with
`(A − 1)² > n d`, and interpolation parameters `(m, D, B)` with `Admissible n d A m D B`. Write
`L = jl n (A − 1) d` (the Johnson list bound at `A − 1`) and `q = |F|`.

* `card_excSet_le_nAff`: **affine MCA** (CWYZ26 Thm 1.1/4.10, Annex B `thm:mca-affine`). At most
  `nAff q n d A m D B = q² · ε_aff` pairs `(α, β)` are exceptional for the combiner `f + (α + β x) g`.
* `card_foldBad_le_nAff`: **one affine fold round** (Annex B `lem:fold-list`). If every pair of
  `lst(f, g; A − 1, d)` violates the running claim `Λ₀ F + Λ₁ G = c`, then at most
  `nAff + 2 L q` challenges `(α, β)` let a tuple of `lst(g + (α + β x) f; A, d)` satisfy the folded
  claim. Over `q²` challenges this is the escape `ε_aff + 2L/q` of BLUEPRINT §4's fold group
  (numerator `q · ε_aff + 2L` over `q`).
* `card_foldBadR_le_nAff`: the same, **relativised** to a predicate `Bp` on pairs, the form the
  agreement-set extractor's descent invariant uses (leanVM `Whir/Sound/FoldRoundCwyz`, which calls
  it at `p = 2`): only pairs satisfying `Bp` must violate the claim, and only fold tuples all of
  whose near pairs satisfy `Bp` are counted. With `Bp = True` it is `card_foldBad_le_nAff`.

No hypothesis on the characteristic: a finite field has prime characteristic `ringChar F`.
-/

namespace Lvm6.Aff

open Finset Polynomial LeanVM.Protocol.Whir.AffineCombiner

variable {F : Type*} [Field F] [Fintype F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-- **Affine MCA, counting form** (CWYZ26 Thm 4.10; Annex B `thm:mca-affine`): at admissible
`(m, D, B)`, at most `nAff |F| n d A m D B = |F|² ε_aff` exceptional pairs `(α, β)`. -/
theorem card_excSet_le_nAff (dom : ι ↪ F) {d A m D B : ℕ}
    (hadm : Admissible (Fintype.card ι) d A m D B) (f g : ρ → ι → F) :
    ((excSet dom f g d A).card : ℚ) ≤ nAff (Fintype.card F) (Fintype.card ι) d A m D B := by
  have := ringChar.charP F
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  exact card_excSet_le_nAff' (ringChar F) dom hadm f g

/-- **One affine fold round** (Annex B `lem:fold-list`, counting form; BLUEPRINT T3): at most
`nAff + 2 jl n (A − 1) d |F|` escapes `(α, β)`. -/
theorem card_foldBad_le_nAff [DecidableEq F] (dom : ι ↪ F) (f g : ρ → ι → F) {d A m D B : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (hadm : Admissible (Fintype.card ι) d A m D B)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F)
    (hviol : ∀ q ∈ pairList dom f g (A - 1) d, Λ₀ q.1 + Λ₁ q.2 ≠ c) (u₀ v c₀ c₁ : F) :
    ((foldBad dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁).card : ℚ) ≤
      nAff (Fintype.card F) (Fintype.card ι) d A m D B +
        2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by
  have := ringChar.charP F
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  exact card_foldBad_le_nAff' (ringChar F) dom f g hgap hadm Λ₀ Λ₁ c hviol u₀ v c₀ c₁

/-- **One affine fold round, relativised** (the form W1's descent invariant consumes): if every
pair of `lst(f, g; A − 1, d)` satisfying `Bp` violates the claim, at most
`nAff + 2 jl n (A − 1) d |F|` challenges `(α, β)` let a fold tuple all of whose near pairs satisfy
`Bp` satisfy the folded claim. -/
theorem card_foldBadR_le_nAff [DecidableEq F] (dom : ι ↪ F) (f g : ρ → ι → F) {d A m D B : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (hadm : Admissible (Fintype.card ι) d A m D B)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F) (Bp : (ρ → F[X]) × (ρ → F[X]) → Prop)
    (hviol : ∀ q ∈ pairList dom f g (A - 1) d, Bp q → Λ₀ q.1 + Λ₁ q.2 ≠ c) (u₀ v c₀ c₁ : F) :
    ((foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp).card : ℚ) ≤
      nAff (Fintype.card F) (Fintype.card ι) d A m D B +
        2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by
  have := ringChar.charP F
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  exact card_foldBadR_le_nAff' dom f g (ringChar F) hgap hadm Λ₀ Λ₁ c Bp hviol u₀ v c₀ c₁

end Lvm6.Aff
