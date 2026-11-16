-- New for lvm2 E2-FT (E2F-QH3): the S2GF layout specification: roll 11's (`specQ`) with the front's auxiliary
-- blocks (the two row switches' bit blocks, the 1,085 ground challenges' PoW range blocks).
import LvmE2QAsmFront
import LvmE2QPow
import LvmE2QAsmRow
import LvmTypedLayQ
import LvmE2QWPhase

-- (GOLF2: 2 declarations that `certified` does not use moved verbatim to `LvmE2QInstOff`, outside its import closure.)

/-!
# The S2GF layout specification (`specQF`)

* **`powChalsF20`**: the ground challenges of `schedule P20F`, `(item, g)` (generated from the frozen
  `s2gf-items.tsv` by `E2F/QH3/tools/gen_pow.py`: a sample after an `e2 nonce` read, `g` from its group numerator:
  62 at `g = 1`, 987 at `g = 2`, 36 at `g = 6`).
* **`powLanes p`**: their answer lanes (`itemLanes`) with `g`.
* **`specQF C Q`**: `specQ C Q` with three more auxiliary word regions: the wire's and `KS`'s row-switch bits
  (`rowAuxL`: `8,192` words each, looped blocks onto the free cells `tBw`, `tBk` and the slice lanes), the PoW bits
  (`powBlksL`, blob v4: the booleanity rows looped over the bit region's power-of-two runs (`boolRuns`), one
  recomposition row per answer; v2's looped runs per answer (`LvmE2QAsmPow`) cost the evaluator more, their strides not
  being powers of two).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.QAsm Lvm.Typed

/-- The typed phases' ground challenges at S2GF: none (the typed phases are at `E3`, no grinding). -/
def typedChalsX : List (Nat × Nat) := []

/-- **The ground challenges of the S2GF node program** `(answer lane, g)`, as the phase gadgets' lists at
`frontF`'s lanes (C 22:35: each phase's `PowOkV` list is a sub-list by `List.mem_append`): the tape's `r`
(`chalsG`), the tape GKR (`tapeChals2`), the wire (`wireChals`), `KS`'s instance (`chalsG`), the `KS` GKR
(`gkrChals2`), the `KS` link (`ksLinkChals`), the typed phases (`typedChalsX`, none). Natively equal, as a
multiset of `(lane, g)`, to the frozen transcript's census (`powLanes P20F powChalsF20`: 1,085; `(c,g)` (1,1) 62,
(2,2) 87, (3,2) 900, (46,6) 36) [checked natively, scratch E2F/QH3]. -/
def powFront (p : Params) : List (Nat × Nat) :=
  let A := (itemLanes p).toArray
  let pl (ph : Phase) (j : Nat) : Nat := A.getD (phaseItem0 p ph + j) 0
  Lvm.Q2.chalsG (pl .tape 2) Lvm.E2V.gC1 p.logN ++ Lvm.Q1.tapeChals2 (p.logN - 5) (pl .tape (2 * p.logN + 3)) ++
    Lvm.Q2.wireChals p.logN (pl .wire 0) ++ Lvm.Q2.chalsG (pl .ks 1) Lvm.E2V.gC1 p.ksLog ++
    Lvm.Q1.gkrChals2 (p.ksLog - 4) (pl .ks (2 * p.ksLog + 2)) ++ Lvm.Q2.ksLinkChals p.ksLog (pl .ksLink 1) ++
    typedChalsX

/-- The first slice lane of the wire's row switch (QH2's `wireLanes`). -/
def wireSlices (p : Params) : Nat := (Lvm.Q2.wireLanes p.logN (phaseLane p .wire 0)).slices

/-- The first slice lane of `KS`'s row switch (QH1: slice `k` at `gkrQO2 + 226 + 2k`). -/
def ksSlices (p : Params) : Nat := Lvm.Q1.gkrQO2 (p.ksLog - 4) (phaseLane p .ks (2 * p.ksLog + 2)) + 226

/-- The looped booleanity blocks over the words `[bw, bw + n)`, bits `a < k` of `n` from the top: per set bit `a`, one
block of `2^a` iterations of `rowBoolL` at the word `bw + (n − n mod 2^(a+1))` (the larger runs first, so each run's
base is `2^a`-aligned when `bw` is). -/
def boolRuns (bw n : Nat) : Nat → List ABlk
  | 0 => []
  | a + 1 => (if n.testBit a then [⟨a, [Lvm.Q2.rowBoolL (bw + (n - n % 2 ^ (a + 1)))]⟩] else []) ++ boolRuns bw n a

/-- An answer's PoW recomposition row (`powRangeRows`' last row): `v + Σ_i 2^i·b(bw + i) = 0`, `v` the stream cell
`q + 2` (lane 2). -/
def powRecRow (g bw q : Nat) : ARow :=
  ⟨((List.range (64 - g)).map fun i => (2, .word (bw + i) 0, FE.ofK ⟨UInt64.ofNat (2 ^ i)⟩)) ++
    [(3, .cell ⟨.K, q + 2, []⟩, 1)]⟩

/-- The answers' recomposition rows, bit words consecutive from `bw` (as `powBlks`). -/
def powRecRows : Nat → List (Nat × Nat) → List ARow
  | _, [] => []
  | bw, (q, g) :: as => powRecRow g bw q :: powRecRows (bw + (64 - g)) as

/-- **The PoW blocks, blob v4** (lever L3a): the booleanity rows of every bit word looped over the bit region's
power-of-two runs (`boolRuns`), the recomposition rows one per answer in one block. The words and the rows' content
are `powBlks`'s; only the booleanity rows are looped. -/
def powBlksL (bw : Nat) (pw : List (Nat × Nat)) : List ABlk :=
  boolRuns bw (Lvm.Q2.powWords pw) ((Lvm.Q2.powWords pw).log2 + 1) ++ [⟨0, powRecRows bw pw⟩]

/-- **The S2GF layout specification.** -/
def specQF (C : QCfg) (Q : Program) (pw : List (Nat × Nat)) : LSpec :=
  let S := specQ C Q
  let n := S.auxWords.length
  { S with
    auxWords := S.auxWords ++ [Lvm.Q2.rowAuxWords, Lvm.Q2.rowAuxWords, Lvm.Q2.powWords pw]
    auxOf := fun bw => S.auxOf bw ++ (Lvm.Q2.rowAuxL (bw n) (tBw C) (wireSlices C.p) ++
      Lvm.Q2.rowAuxL (bw (n + 1)) (tBk C) (ksSlices C.p)) ++ powBlksL (bw (n + 2)) pw }

end Lvm.E2Q
