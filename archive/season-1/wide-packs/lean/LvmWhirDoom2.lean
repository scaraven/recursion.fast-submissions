-- New for lvm2 (X-REC2, stage S4; BLUEPRINT2 §3.2, §5): the extractor's facts for a `C_rec` with two WHIR levels.
-- Built on WP-7's `LvmWhirDoom` (`ud_extract`'s argument, `foldAll_mem_iList`, `foldAll_encRows`).
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the extractor's doom facts at two levels)

  The doom of the level-1 commitment of a two-level unique-decoding opening, and the extraction
  facts: under no commitment doom, no level-1 doom and no final doom, the root's unique good
  candidate `q` folds to the level-1 word's unique list member, whose fold is the residual.
-/

import LvmWhirDoom
import LvmWhirParams
import LvmWhirParams24

-- (GOLF2: 9 declarations that `certified` does not use moved verbatim to `LvmXDec1UdOff`, outside its import closure.)

/-!
# Two levels: the level-1 doom and the extractor's facts

Setting (BLUEPRINT2 §3.2, S4): a root committed as a level-0 word `W₀` (`2^(μ−6+R)` leaves of
`2^6` `K` words; lvm's `C_rec`: `μ = 19`, `R = 2`), level-0 fold challenges `α₀ ∈ E^6`, then a
level-1 word `W₁` whose `2^ℓ₁` lanes (`E` scalars, a leaf of `3·2^ℓ₁` `K` words) are rows `Q'` of
the level-1 code `P₁` (`κ₁ = μ − 6 − ℓ₁`; lvm: `ℓ₁ = 4`, `κ₁ = 9`, `R₁ = 3`), level-1 fold
challenges `α₁ ∈ E^ℓ₁` and the final residual `f₂` (`2^κ₁` `E` scalars). WHIR glues a level-1
row family `V` to the folded root word through `joinMsg` (lane bits low): the level-0 message
of `V` is `joinMsg hκ (decode P₁ V)`.

* `MidDoomUd`: **the level-1 commitment's doom**: no member `V` of the level-1 list has a
  level-0 encoding close to the folded root word `C = foldAll α₀ (laneRows W₀)` (agreement on
  fewer than `A` columns). Created at the commitment of `W₁` (a prover move); from it the level-0
  query group catches the level-1 word except with probability `eQueryUd` (the certificate's
  `LvmCertSMid2`'s spec, the generalised `escRet_queryFrag_le_ud`).
* `FinalDoomL`: **the final residual's doom at level 1**: `Enc₁(f₂)` is not in the list of the
  level-1 rows folded by `α₁` (the part of `FinViol` that the extractor needs).
* **`ud_extract2`**: `¬ CommitDoomUd ∧ ¬ MidDoomUd ∧ ¬ FinalDoomL` ⇒ the root's unique candidate
  `q` is good; the level-1 list has a unique member `V`; `joinMsg (decode V) = foldMsg α₀ q` (the
  level-1 message is the level-0 fold of `q`); `f₂ = Σ_u eq(α₁, u) · decode V u`; both words agree
  with their codewords on at least the thresholds, and off each level's luck event the agreement
  set of the folded word with the encoding of the next message is the joint agreement set. So the
  extractor decodes level 1 first (`V`'s message on the agreement set of `foldAll α₁ Q'` with
  `Enc₁(f₂)`), then level 0 as v1 with `f₁ := joinMsg (decode V)`.
* `not_finalDoomUd_foldMsg`: the level-0 fold of a candidate is never final-doomed: v1's level-0
  decoder facts (`ud_extract`, `LvmXDecUd.decodeRec_of_ud`) apply with `f := foldMsg α₀ q`.
* `ud_extract_rec20`, `ud_extract_rec18`: the instances at lvm's `C_rec` (P20: `κ = 13, 9`,
  `R = 2, 3`; S2's P8, μ = 18: `κ = 12, 8`), with non-vacuity at P20 (`ud_extract_rec20_nonvacuous`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-! ## The level-1 rows -/

/-- **The level-1 rows** of a word whose leaves hold `2^ℓ` `E` scalars as `K` triples (WHIR's
`laneO 1`, `extRow`): row `u` at column `v` is lane `⟨u⟩` of leaf `v`. -/
def rows1 (ℓ n : ℕ) (W : Word) : (Fin ℓ → Bool) → Fin n → E :=
  fun u v ↦ (lanesOf 1 (W v)).getD (bitsToNat u) 0

/-! ## The doom predicates -/

/-- **The level-1 commitment's doom**: every member `V` of the level-1 list of `Q'` has a level-0
encoding (`Enc₀(joinMsg (decode V))`) that agrees with the folded root word `C` on fewer than `A`
columns. -/
def MidDoomUd {κ₀ R₀ ℓ₁ : ℕ} (A : ℕ) (P₁ : LevelCode) (hκ : κ₀ = ℓ₁ + P₁.κ)
    (C : Fin (2 ^ (κ₀ + R₀)) → E) (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) : Prop :=
  ∀ V ∈ iList P₁.code P₁.thr Q',
    (univ.filter fun x ↦ enc κ₀ R₀ (joinMsg hκ (decode P₁ V)) x = C x).card < A

/-- **The final residual's doom at level 1**: `Enc₁(f₂)` is not in the list of the level-1 rows
folded by `α₁`. -/
def FinalDoomL {ℓ₁ : ℕ} (P₁ : LevelCode) (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (α₁ : Fin ℓ₁ → E)
    (f₂ : (Fin P₁.κ → Bool) → E) : Prop :=
  (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) ∉ iList P₁.code P₁.thr (foldAll α₁ Q')

/-! ## The facts -/

/-! ## lvm's `C_rec` -/

end
end LeanVM.Protocol.Whir.Sound
