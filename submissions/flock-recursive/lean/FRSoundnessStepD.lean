-- New for `flock-recursive` (BLUEPRINT §5.2, A.10; stage S-G1d).
-- RET-1: position-free declarations moved to `FRSoundnessCoreSteps`.
import FRSoundnessTruths
import FRSoundnessCoreSteps

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

end FR.Snd
