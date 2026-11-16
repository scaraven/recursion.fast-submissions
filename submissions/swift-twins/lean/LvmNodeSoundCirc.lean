-- WP-14c (NodeSound, O10). New for lvm: the node program's parts from the M3 instance: WP-10's
-- `loopir_sound` (hypotheses from WP-9/9b's `AuxHyps`) makes the interpreter's memory hold every
-- segment of `Q = Q_link ++ Q_sig ++ Q_arith` (QL's assembly order) with every assertion; then
-- QL's `qlink_sound`, WP-12's `qsig_sound_in` with WP-12b's `sigBitsOk`.
import LvmNodeSoundLeft
import LvmSigBits

-- (GOLF2: 5 declarations that `certified` does not use moved verbatim to `LvmNodeSoundCircOff`, outside its import closure.)

/-!
# The circuit's parts on the committed pair

`qprog lay I qa = do qlink P20 lay; let _ ← qsig I; qa` (QL's order), `Q = toProgram nK nE (qprog …)`,
`M = Q.interpMem (inKOf q) (inEOf q)` on the stack `q` of a candidate pair. Pointers: Q_link at
`p0 = ⟨nK, nE⟩`, Q_sig at `p1`, Q_arith at `p2`.

* **`segs_of_aux`**: `AuxHyps` (`loopir_sound`'s hypotheses: static checks, `M3Holds`, `inb`) ⇒
  every segment of `Q` holds in `M` and every assertion holds.
* **`link_of_aux`**: with Q_link's inputs where its layout says (`QIn`) and its static checks
  (`StreamOk`, `QOk`), the stream meets `LaneLink`, is a trace of the schedule (`LinkOk` of
  `decode`) and its padding is pinned.
* **`sig_of_aux`**: with the `KS` cells (`SigKSin`) and the six `BITS` tables in `aux` with their
  cells below the cell count, Q_sig's `SigOk` and `ChildOk`.
* **`arith_of_aux`**: Q_arith's segments hold and assert at `p2` (what `Q_arith_eq` consumes).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits

/-- **The node program** (QL's assembly order) at the schedule of `p`: Q_link, Q_sig, Q_arith (lvm2 E2-FT: any `p`;
S2GF's `P20F`). -/
def qprogP {α : Type} (p : Params) (lay : Layout) (I : SigIn) (qa : BM α) : BM α := do
  qlink p lay
  let _ ← qsig I
  qa

/-- The node program at `P20` (`qprogP P20`). -/
abbrev qprog {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) : BM α := qprogP P20 lay I qa

theorem ctxOf_cells (Q : Program) : (ctxOf Q).cells = Q.cells := rfl

section Parts

variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)

/-- The node program as a LoopIR program. -/
abbrev Qn : Program := toProgram nK nE (qprog lay I qa)

/-- Q_link's pointer. -/
def p0 : Ptr := ⟨nK, nE⟩

/-- Q_sig's pointer. -/
def p1P (p : Params) : Ptr := (p0 nK nE).adv (qlink p lay (p0 nK nE)).2

/-- Q_sig's pointer at `P20`. -/
abbrev p1 : Ptr := p1P lay nK nE P20

/-- Q_arith's pointer. -/
def p2P (p : Params) : Ptr := (p1P lay nK nE p).adv (qsig I (p1P lay nK nE p)).2

/-- Q_arith's pointer at `P20`. -/
abbrev p2 : Ptr := p2P lay I nK nE P20

variable (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ L.μ)

variable {lay I qa nK nE pl groups arrs aux L hτ}

end Parts

end Lvm.NS
