-- New for lvm2 E2F (slice S1, E2F-QH2): the proof-of-work rows of the front's ground answers: one auxiliary block
-- (`powRangeRows`, `LvmE2QGad`) per answer, its operand lane 2 of the answer (a stream `K` cell); the lemma from the
-- rows to V's `powOKR g c` on the answer `V` reads there (E2F-LEAD's review action 2).
import LvmE2QGad

/-!
# The PoW blocks (`powBlk`, `powBlks`)

An `E2` ground challenge (V's `sampleG g`) is lanes 0–1 of the `E` answer `c = feAt Σ (8 q)` at answer lane `q`;
V requires `powOKR g c`. The circuit adds, per answer, the auxiliary block `powBlk g bw q`: `powRangeRows g` on the
free bit words `bw … bw + 63 − g` and the operand `v = ` the stream cell `q + 2` (lane 2).

* **`powBlks bw as`**: the blocks of the answers `as = [(q, g)]`, bit words consecutive from `bw`
  (`powWords as` of them).
* **`powBlk_ok`**: if the block's rows hold and the stream cell `q + 2` is lane 2 of `c`, then `powOKR g c`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Typed

/-- **The PoW block of one answer** at lane `q` (`g` bits), its bits the free words `bw + i`. -/
def powBlk (g bw q : Nat) : ABlk :=
  ⟨0, powRangeRows g (fun i => .word (bw + i) 0) (.cell ⟨.K, q + 2, []⟩)⟩

/-- The bit words of the answers. -/
def powWords (as : List (Nat × Nat)) : Nat := (as.map fun a => 64 - a.2).sum

/-- **The PoW blocks of the answers** `(q, g)`, bit words consecutive from `bw`. -/
def powBlks : Nat → List (Nat × Nat) → List ABlk
  | _, [] => []
  | bw, (q, g) :: as => powBlk g bw q :: powBlks (bw + (64 - g)) as

/-- **The PoW block gives V's check**: if its rows hold (at iteration 0) and the `K` cell `q + 2` of the memory read
off the words is lane 2 of the answer `c`, then `powOKR g c`. -/
theorem powBlk_ok (lay : Lay) (z : ℕ → FK) {g bw q : ℕ} (hg : g ≤ 64) {c : FE}
    (hc : (memOf lay z).k (q + 2) = c.c₂) (h : ∀ r ∈ (powBlk g bw q).rows, ARowHolds lay z 0 r) :
    DM.powOKR g c = true := by
  have hv : FE.ofK (aopVal lay z 0 (.cell ⟨.K, q + 2, []⟩)).c₀ = aopVal lay z 0 (.cell ⟨.K, q + 2, []⟩) := rfl
  have := powRange_sem lay z 0 g hg (fun i => .word (bw + i) 0) (.cell ⟨.K, q + 2, []⟩)
    (fun i => ⟨bw + i, 0, rfl⟩) hv h
  apply powOK_of_range hg
  rw [← hc]
  exact this

end Lvm.Q2
