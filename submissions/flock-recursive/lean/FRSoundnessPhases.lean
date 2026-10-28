-- New for `flock-recursive` (BLUEPRINT A.10 L1, L3, Lr3, E3, B′; stage S-G1h, item 3 begun).
-- RET-1: position-free declarations moved to `FRSoundnessCoreHide`.
import FRSoundnessWalk
import FRSoundnessCoreHide

/-!
# Per-phase obligations, part 1: the single-squeeze batching rows (A.10)

Five phases start with one squeeze that batches claims already on the chain by powers of a fresh
F challenge: L1 (`α`, 2 claims), L3 (`β`, 8 `v_kind`), Lr3 (`κ_L`, 3), E3 (`κ_E`, 3), B′ (`κ′`,
`J_f` terms). Their doom after the squeeze is "the batched claim is false"; before it, "some
claim is false". **`batch_single`**: at such a squeeze at most `k·2^128` answers escape
(`batch_pow_bad_le`, `single_F_le`); **`batch_N_le`**: every such count (`k ≤ 239`) fits
`PhaseObl`'s single-squeeze budget `N ≤ 2^256·deltaR`. This discharges `PhaseObl.hsingle` at these
five positions once the phases' claims and truths are fixed (the rest of item 3, S-G1h RESULT).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

end FR.Snd
