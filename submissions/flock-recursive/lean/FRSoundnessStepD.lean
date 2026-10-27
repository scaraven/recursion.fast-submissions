-- New for `flock-recursive` (BLUEPRINT §5.2, A.10; stage S-G1d).
import FRSoundnessTruths

/-!
# The multi-squeeze coordinate rows (A.10's `hround` for Z1, S1, Lr1, RS1, E1, P3)

A multi-squeeze phase of `r` answers draws `2r` F coordinates (`coordAt`: F coordinates `0, 1`
of each answer, `chFEquiv`). **`coords_round_le`**: if the phase's escape puts the coordinate
tuple in a set `B ⊆ (F × F)^r`, its conditional count from the entry is at most
`|B| / 2^(256 r)`, the probability of `B` under uniform coordinates. This is the F-coordinate
analogue of `card_pos_in`/`p2_round_le`: `(Fin r → Digest) ≃ (Fin r → F × F)` by `chFEquiv`, so
the count of answer tuples is `|B|` exactly (`card_coords_in`). The Schwartz–Zippel counts
(`zerocheck_bad_le`, `pair_bad_le`, `seq_bad_le`, `rs1_joint`) bound `|B|`.
-/

namespace FR.Snd
open RecursionFast Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- The coordinate tuple of `r` answers. -/
noncomputable def coordsOf {r : ℕ} (v : Fin r → Digest) : Fin r → F × F := fun s => chFEquiv (v s)

/-- **`card_coords_in`**: the answer tuples whose coordinates lie in `B` number exactly `|B|`. -/
theorem card_coords_in {r : ℕ} (B : Finset (Fin r → F × F)) :
    (univ.filter fun v : Fin r → Digest => coordsOf v ∈ B).card = B.card :=
  Finset.card_equiv (Equiv.piCongrRight fun _ => chFEquiv) fun v => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl

open Classical in
/-- **The coordinate row** (`hround`): if the escape puts the phase's coordinate tuple
(`fAt` at the `r` answers after the entry `s0`) in `B`, the phase's conditional count from its
entry is at most `|B| / 2^(256 r)`. -/
theorem coords_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (B : Finset (Fin r → F × F))
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      (fun s : Fin r => (fAt (ext es₀ as) (s0 + 1 + s) 0, fAt (ext es₀ as) (s0 + 1 + s) 1)) ∈ B) :
    condCount D L es₀ r [] ≤ (B.card : ℝ≥0) / 2 ^ (256 * r) := by
  unfold condCount extCount
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  have hle := Finset.card_le_card (s := univ.filter fun v : Fin r → Digest =>
      EscAtG D L (ext es₀ (List.ofFn v)))
    (t := univ.filter fun v : Fin r → Digest => coordsOf v ∈ B) fun v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have := hesc _ (by simp) hv
    have hv' : ∀ s : Fin r, ∀ c, fAt (ext es₀ (List.ofFn v)) (s0 + 1 + s) c = chF (v s) c := by
      intro s c
      rw [fAt, show s0 + 1 + (s : ℕ) = es₀.length + s by omega,
        ansAt_ext _ (by simp), List.getElem_ofFn]
    simp only [hv'] at this
    exact this
  rw [card_coords_in B] at hle
  gcongr

/-- The count in probability form: `|B| / |F × F|^r`. -/
theorem coords_prob (r : ℕ) (B : Finset (Fin r → F × F)) :
    (B.card : ℝ≥0) / 2 ^ (256 * r) = (B.card : ℝ≥0) / (Fintype.card (F × F) : ℝ≥0) ^ r := by
  rw [Fintype.card_prod, F.card_F, pow_mul]; push_cast; ring_nf

/-- Control: the full set has count `1` (every tuple; `card_coords_in` is not an upper bound
only). -/
theorem card_coords_univ (r : ℕ) :
    (univ.filter fun v : Fin r → Digest => coordsOf v ∈ (univ : Finset (Fin r → F × F))).card =
      2 ^ (256 * r) := by
  rw [card_coords_in, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, F.card_F,
    Fintype.card_fin, ← pow_add, ← pow_mul]

/-- Control: the empty set is never hit. -/
theorem card_coords_empty (r : ℕ) :
    (univ.filter fun v : Fin r → Digest => coordsOf v ∈ (∅ : Finset (Fin r → F × F))).card = 0 := by
  rw [card_coords_in, Finset.card_empty]

end FR.Snd
