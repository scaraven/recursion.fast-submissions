-- New for `flock-recursive` (`flock-128`, design D128 §2.1, §4.1, §8 item 7; stage I3): the degree-2
-- F round readers with `c₂` derived from the claim.
import FRSoundnessCoreSteps
import FRVIR4Pow

/-!
# The degree-2 F rounds' readers with `c₂ := claim + c₁` (L2, S2, E4)

D128 §2.1: a degree-2 F round sends `c₀ ‖ c₁ ‖ nonce` and the verifier derives `c₂ := claim + c₁`
(`FRVIR4.roundOpsF4`), as a degree-3 round derives `c₃` (`FRSoundnessCoreSteps.g3At`, `clR`).
3.x's readers (`g2At`, `clR2`, `Chk2`) read `c₂` from the message's third slot, which is now the
nonce; they stay for the K rounds (P1, Pf), whose messages are unchanged.

* **`g2dAt b es l c`**: round `l`'s coefficients `(c₀, c₁, c + c₁)` from claim `c`;
  **`clR2d`**: the running claims from the initial claim `c0` (for L2, S2, E4 the verifier's target,
  computed in the skeleton, `FRVIR4.initOps4`: `c0L`, `c0S`, `c4E4` are already those targets).
* **`chk2d`**: the round check `g(0) + g(1) = claim` holds for every message (characteristic two),
  so 3.x's `Chk2`-based rejection predicates (`RejL2`, `RejS2`, E4's) become vacuous for these
  phases; their dooms keep the round's bad-challenge event over `g2dAt` (the next claim is
  `peval (g2dAt …) r`, `ir_reader_agree` with `FRVIR4Pow.round2d_claim`).
* **`clR2d_congr`**: the claims read only the entries before round `l`.
* Controls: `chk2_nonce_ctl` (3.x's reader fails on a nonce in the third slot, the derived one holds).

The front lemmas that read these phases (`FRSoundness4R4FrE.rounds2_log`, `roundsF2_view4`, …) are
re-proved over `clR2d` in stage I5 (`docs/v4/flock-128/stages/I3-RESULT.md` §5).
-/

namespace FR.Snd
open RecursionFast

section Rounds2d

variable (b : ℕ)

/-- **Round `l`'s coefficients from claim `c`** (D128): `c₀`, `c₁` from the message at `b + 2l`,
`c₂ = c + c₁` (the third slot is the nonce). -/
def g2dAt (es : Log) (l : ℕ) (c : F) : Array F :=
  #[readF (msgAt es (b + 2 * l)) 0, readF (msgAt es (b + 2 * l)) 16, c + readF (msgAt es (b + 2 * l)) 16]

variable (c0 : Log → Log → F)

/-- **The running claims**: `c0`, then `g_l(r_l)` with `g_l = g2dAt … (claim l)`. -/
def clR2d (L es : Log) : ℕ → F
  | 0 => c0 L es
  | l + 1 => peval (g2dAt b es l (clR2d L es l)) (rch b es l)

/-- **The round check holds by construction**: `g(0) + g(1) = c` for `g = (c₀, c₁, c + c₁)`
(characteristic two: `g(0) + g(1) = c₁ + c₂`). -/
theorem chk2d (es : Log) (l : ℕ) (c : F) :
    peval (g2dAt b es l c) 0 + peval (g2dAt b es l c) 1 = c := by
  rw [g2dAt, peval_three, peval_three]
  generalize readF (msgAt es (b + 2 * l)) 0 = x
  generalize readF (msgAt es (b + 2 * l)) 16 = y
  have hx : x + x = 0 := CharTwo.add_self_eq_zero x
  have hy : y + y = 0 := CharTwo.add_self_eq_zero y
  linear_combination hx + hy

variable {b c0}

/-- The claims read only the entries before round `l`. -/
theorem clR2d_congr {L es es' : Log} (hc : c0 L es = c0 L es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) → clR2d b c0 L es l = clR2d b c0 L es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR2d]
    rw [clR2d_congr hc (h.mono (by omega))]
    simp only [g2dAt, rch, fAt, ansAt, msgAt, h (b + 2 * l) (by omega), h (b + 2 * l + 1) (by omega)]

end Rounds2d

/-- **The IR's next claim is the reader's** (`FRVIR4Pow.round2d_claim`): Horner's
`c₀ + r(c₁ + r(c + c₁))` is `peval (c₀, c₁, c + c₁) r`. -/
theorem ir_reader_agree (c₀ c₁ c r : F) :
    c₀ + r * (c₁ + r * (c + c₁)) = peval #[c₀, c₁, c + c₁] r := by
  rw [peval_three]; ring

/-- (−) **3.x's reader on a nonce**: with `c₀ = c₁ = 0` and the nonce `1` in the third slot, 3.x's
check `g(0) + g(1) = claim` fails at claim `0`; (+) the derived reader's `g = (0, 0, 0 + 0)` passes. -/
theorem chk2_nonce_ctl :
    peval (#[0, 0, 1] : Array F) 0 + peval #[0, 0, 1] 1 ≠ 0 ∧
      peval (#[0, 0, 0 + 0] : Array F) 0 + peval #[0, 0, 0 + 0] 1 = 0 := by
  rw [peval_three, peval_three, peval_three, peval_three]
  refine ⟨?_, by ring⟩
  simp

end FR.Snd
