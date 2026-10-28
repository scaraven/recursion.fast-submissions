-- New for `flock-recursive` (stage R4): controls for the program layer on `gen4`.
import FRSoundness4R4View
import FRSoundness4R4Stmt

/-!
# Controls for R4's definitions

| Definition | Positive | Negative |
|---|---|---|
| `refPhase4` | `refPhase4_sqz0` (an empty squeeze run passes, consuming nothing) | `refPhase4_seed_nil` (a seed with no entry fails), `refPhase4_abs_wrong` (an absorb answered for another query fails) |
| `fsMsgs4` | `fsMsgs4_len`, `fsMsgs4_items`, `fsMsgs4_ctl` (message 1 is `stmt` at 48, 128 bytes) | `fsMsgs4_ctl` (message 3 is a squeeze, not a message) |
| `relocFin` | `relocFin_ops`, `finOps4_eq` | `relocF_moves` (relocation to `seq4` changes `E`'s offset: `reloc_seq4_moves`) |
| `SkRun4` | `skRun4_of_accept` | `not_skRun4_nil` (an empty trace has no 482 entries) |
| `exec_ext` | the lemma | `exec_ask_nil` (an ask on an empty trace fails) |
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP)

theorem refPhase4_sqz0 (n i : ℕ) (c : GCtx) (r : Array Val) (tr : Trace) :
    refPhase4 impl κ inp S p n ("P2", .squeezes 0 (.pos i)) c r tr = some ([], true, tr) := rfl

theorem refPhase4_seed_nil (n : ℕ) (c : GCtx) (r : Array Val) :
    refPhase4 impl κ inp S p n ("seed", .seed) c r [] = none := rfl

theorem refPhase4_abs_wrong (n f len : ℕ) (c : GCtx) (r : Array Val) (q : ByteArray) (a : Digest)
    (tr : Trace) (hq : q ≠ absorbQ (rd r c.st).toD (FR.msgAt inp 0 (fieldOffOf S f + phaseOffOf S n f) len)) :
    refPhase4 impl κ inp S p n ("x", .absorb f len) c r ((q, a) :: tr) = none := by
  simp [refPhase4, ans1, hq]

theorem fsMsgs4_ctl : (fsMsgs4 seq4).getD 1 none = some (48, 128) ∧ (fsMsgs4 seq4).getD 3 none = none := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

theorem relocF_moves : fieldOffOf seq4 fE ≠ fieldOff fE := reloc_seq4_moves

theorem not_skRun4_nil {y : List Val × List Bool × Trace} : ¬ SkRun4 impl p inp [] y := fun h => by
  have := h.len; simp [fsOf] at this

theorem exec_ask_nil (st : ℕ) (s : St) : exec impl κ inp [.askSqueeze st] s [] = none := rfl

end FR.Snd.R4
