import LvmQLinkArith
import LvmDecide

-- (GOLF2: 14 declarations that `certified` does not use moved verbatim to `LvmQTypedHarZOff`, outside its import closure.)

/-!
# QA1 links: what `F` reads in the link phases (phases 5 and 7 of `decideProg`)

`chLinkPhase`, `ksLinkPhase` are the two link phases of `decideProg` (`LvmDecide`, lines "5] CH link",
"7] KS link"), verbatim, as `DM` programs. **`chLinkPhase_run`**, **`ksLinkPhase_run`**: on any reader
state `s`, at position `P = s.ent + s.msg`, the phase reads the view `feAt Σ` at fixed offsets from `P`
(`chLinkView`, `ksLinkView`: every sample, sumcheck and scalar of the phase), adds exactly the link's
check to `ok`, and moves the position by a constant (`chLinkLen`, `ksLinkLen`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM

section
/- `feAt` sealed here: `congr 1` below otherwise tries to close the tail goal by unfolding `feAt` into byte reads
(a failing defeq of 20 s); the proof term is the same. -/
attribute [local irreducible] feAt

theorem samples_val (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    (samples n sig s).1 = (List.range n).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
  | 0, s => rfl
  | n + 1, s => by
    have e : (samples (n + 1) sig s).1 = feAt sig (s.ent + 40 + s.msg) ::
        (samples n sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).1 := rfl
    rw [e, samples_val sig n, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.comp_def]
    rw [show s.ent + 40 + s.msg = s.ent + s.msg + 40 + 72 * 0 by omega]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [show s.ent + 72 + s.msg + 0 + 40 + 72 * i = s.ent + s.msg + 40 + 72 * (i + 1) by omega]

end

/-- One step of `samples`, evaluated (the kernel unfolds the left side once; `samples_st` rewrites
with it instead of comparing two `samples` terms by `rfl`). -/
theorem samples_succ_run (sig : ByteArray) (n : Nat) (s : RS) : samples (n + 1) sig s =
    (feAt sig (s.ent + 40 + s.msg) :: (samples n sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).1,
      (samples n sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).2) := rfl

theorem samples_st (sig : ByteArray) : ∀ (n : Nat) (s : RS), 1 ≤ n →
    (samples n sig s).2 = ⟨s.ent + s.msg + 72 * n, 0, s.ok⟩
  | 0, _, h => by omega
  | 1, s, _ => by
    show (⟨s.ent + 72 + s.msg, 0, s.ok⟩ : RS) = _
    rw [show s.ent + 72 + s.msg = s.ent + s.msg + 72 * 1 by omega]
  | n + 2, s, _ => by
    have e : (samples (n + 2) sig s).2 = (samples (n + 1) sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).2 := by
      rw [samples_succ_run]
    rw [e, samples_st sig (n + 1) _ (by omega)]
    simp only []
    rw [show s.ent + 72 + s.msg + 0 + 72 * (n + 1) = s.ent + s.msg + 72 * (n + 2) by omega]

/-- `n` challenges from position `P`: the answers at `P + 40 + 72i`. -/
theorem samples_run (sig : ByteArray) (n : Nat) (s : RS) (hn : 1 ≤ n) :
    samples n sig s = ((List.range n).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i),
      ⟨s.ent + s.msg + 72 * n, 0, s.ok⟩) := by
  rw [← samples_val, ← samples_st sig n s hn]
  rfl

/-! ## Phase 5: the `CH` link -/

/-- The positions of phase 5 from its start `P`: the shift sumcheck, the `in` slices, the second
sumcheck, the `Y` slices, the constant lanes, the end. -/
def chP1 (p : Params) (P : Nat) : Nat := P + 72 * (p.logN + 3 + 6)
def chP2 (p : Params) (P : Nat) : Nat := chP1 p P + p.logN * roundLen 3
def chP3 (p : Params) (P : Nat) : Nat := chP2 p P + 24 * kBits + 72 * ringStages
/-- `n` challenges at `P + 40 + 72i` of the view. -/
def samplesAt (v : Nat → FE) (P n : Nat) : List FE := (List.range n).map fun i => v (P + 40 + 72 * i)

/-! ## Phase 7: the `KS` link -/

/-- The positions of phase 7: the shift sumcheck, the four scalars. -/
def ksP1 (p : Params) (P : Nat) : Nat := P + 72 * (p.ksLog + laneBits)
def ksP2 (p : Params) (P : Nat) : Nat := ksP1 p P + p.ksLog * roundLen 3

end Lvm.Q1
