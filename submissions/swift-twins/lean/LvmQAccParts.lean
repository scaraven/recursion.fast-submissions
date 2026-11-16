-- New for lvm (AC-Q): the two sums of Q_acc (BLUEPRINT §12.5 steps 1 and 4). Reuses QA2's
-- `eqTab`/`eqTab_spec`/`eqW_append` (`LvmQWhirBatch`) and the building blocks of `LvmQAccBase`.
import LvmQWhirBatch
import LvmQSumcheckCore
import LvmQSigHdr

-- (GOLF2: 25 declarations that `certified` does not use moved verbatim to `LvmQAccSoundOff`, outside its import closure.)

-- ===== merged from `LvmQAccBase` (GOLF module merge: `LvmQAccBase.lean` is now a stub importing `LvmQAccParts`) =====
section
-- New for lvm (AC-Q). Searched for reusable straight-line chains: QA2's `dotG`/`pows`/`eqTab`
-- (`LvmQWhirBatch`, loops over affine cells, reused for the `eq` tables), Q_sig's `Ok`/`seqAll`
-- helpers (`LvmQSigHdr`, reused), FR's `FRVIR*` (R1CS, no LoopIR). The glue chains below (a dot
-- product over arbitrary cells, Horner, the line point, gated `E` equalities) had no counterpart.

/-!
# Q_acc's building blocks (BLUEPRINT §12.5)

Straight-line gadgets over `E` cells, each with a pointer-generic spec (QL's frame form):

* `ldE q`: the `E` scalar of stream lanes `q, q+1, q+2` (`ldE_feAt`: `F`'s `feAt Σ (8q)` on
  streamed cells); `ldEs qs`: one per entry.
* `macChain l acc`: `acc + Σ a·b` over the cell pairs `l` (one `muladd` row each).
* `horner cs t z`: `polyEval cs t` (`F`'s Horner, constant first; `z` holds `0`).
* `linePt a b t`: `a + t·(a + b)` (the accumulator's line, characteristic 2).
* `assertEqE a b g`: `g·(a + b) = 0` (`a = b` when the gate `g` is `1`).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

variable {c : Ctx} {M : Mem}

/-! ## Stream scalars -/

/-- The `E` scalar at stream lanes `q, q + 1, q + 2`. -/
def ldE (q : Nat) : BM Cell := loadE (kc q) (kc (q + 1)) (kc (q + 2))

/-- The scalars at the lanes `qs`, in order. -/
def ldEs (qs : List Nat) : BM (List Cell) := seqAll (qs.map ldE)

/-- The scalars at the lanes `qs` at consecutive `E` cells; their first cell. -/
def ldEsB (qs : List Nat) : BM Nat := do
  let p ← getPtr
  let _ ← ldEs qs
  pure p.e

/-! ## A dot product with `K` cells -/

/-! ## Constants -/

/-- The `E` constants `0` and `1` (`x + x + k'`, from any `K` cell `x`), at `p.e`, `p.e + 1`. -/
def consts (x : Nat) : BM (Cell × Cell) := do
  let z ← const .E 0 (kc x)
  let o ← const .E 1 (kc x)
  pure (z, o)

/-! ## Dot products over cell pairs -/

/-- `acc + Σ a·b` over the pairs, one `E` `muladd` row per pair. -/
def macChain : List (Cell × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | ab :: l, acc => do
    let acc' ← mulAdd .E ab.1 ab.2 acc
    macChain l acc'

/-! ## Horner and the line -/

/-- `polyEval cs t` (constant first): `z` (a cell holding `0`) for no coefficient, else
`horner rest · t + c₀`. -/
def horner : List Cell → Cell → Cell → BM Cell
  | [], _, z => pure z
  | c₀ :: cs, t, z => do
    let r ← horner cs t z
    mulAdd .E r t c₀

/-- `a + t·(a + b)`: the point of the line through `a` (at `0`) and `b` (at `1`) at `t`. -/
def linePt (a b t : Cell) : BM Cell := do
  let s ← add a b
  mulAdd .E t s a

/-- The line point of every coordinate pair, in order. -/
def linePts (ab : List (Cell × Cell)) (t : Cell) : BM (List Cell) :=
  seqAll (ab.map fun x => linePt x.1 x.2 t)

/-! ## Gated equalities -/

/-- Assert `g·(a + b) = 0`. -/
def assertEqE (a b g : Cell) : BM Unit := assertEq a b g

theorem assertEqE_spec {a b g : Cell} {p : Ptr} (h : Ok c M (assertEqE a b g) p) (hg : g.val M = 1) :
    a.val M = b.val M := by
  obtain ⟨h1, h2⟩ := h
  simp only [assertEqE, assertEq, bind_apply] at h1 h2
  rw [segsHold_append] at h1
  rw [segsAssert_append] at h2
  have hs := lin_spec h1.1
  have ha := assert0_spec h2.2
  simp only [add] at hs ha
  rw [hg, one_mul] at ha
  have : (lin (jn a.ty b.ty) 1 0 a b p).1.val M = 0 := ha
  rw [hs, ofK_one, ofK_zero, one_mul, add_zero] at this
  exact (CharTwo.add_eq_zero (R := FE)).mp this

/-- Assert `a_i = b_i` for every pair. -/
def assertEqs (ab : List (Cell × Cell)) (g : Cell) : BM (List Unit) :=
  seqAll (ab.map fun x => assertEqE x.1 x.2 g)

end Lvm.QAcc
end
-- ===== end of `LvmQAccBase` =====

/-!
# Q_acc's sums

* **`qyown kb la dk z one fx`** (step 1): `y' = Σ_{k<|fx|} eq(κ', k) · v'_k`, `κ'` the `dk` `E` cells
  from `kb`, `v'_k` the cell `fx[k]` (the child's evaluations of `fixCols`, the table gadget's cells). The
  `eq` table is built as two halves (`la` low coordinates, `dk − la` high ones, `eqW_append`) and
  multiplied per column: `2^la + 2^(dk−la)` table entries instead of `2^dk`.
* **`qpub al z one τp hd vkc nL`** (step 4): `Σ_{i<nL} eq(r', i) · L_i` (`r'` the `τp` cells `al i`), the extension of the
  child's `PUB` lanes `L` at the table point's first `τp` coordinates: `L_i` is stream lane `hd + i`
  except the key lanes `1 … 4`, which are the current proof's `PUB` cells `vkc …` (the child's `pubOf`
  takes `vk` from `V`'s argument, not from its header).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

variable {c : Ctx} {M : Mem}

/-! ## Lists of gadgets with pointer-generic values -/

/-! ## `Σ_k eq(pt, k)·x_k` by blocks -/

/-- **`Σ_{k<|xs|} eq(pt, k) · x_k`**, `pt` the `dk` `E` cells `al i`: two half `eq` tables (`la` low
coordinates, `dk − la` high ones), per block `h` of `2^la` entries the chain `Σ_l eqL[l]·x_{h·2^la+l}`,
then `Σ_h eqH[h]·acc_h` (entries past `|xs|` are `z`). -/
def eqDot (al : Nat → Cell) (la dk : Nat) (z one : Cell) (xs : List Cell) : BM Cell := do
  let eL ← eqTab al z one false la
  let eH ← eqTab (fun i => al (la + i)) z one false (dk - la)
  let accs ← forN ((xs.length + 2 ^ la - 1) / 2 ^ la) fun h =>
    macChain ((List.range (2 ^ la)).map fun l => (ec (eL + l), xs.getD (h * 2 ^ la + l) z)) z
  macChain ((List.range ((xs.length + 2 ^ la - 1) / 2 ^ la)).map fun h =>
    (ec (eH + h), accs.getD h default)) z

/-! ## Step 1: `y' = Σ_k eq(κ', k)·v'_k` -/

/-- `y'`: `eqDot` over `κ'` (the `dk` cells from `kb`) and the child's `fixCols` evaluations. -/
def qyown (kb la dk : Nat) (z one : Cell) (fx : List Cell) : BM Cell :=
  eqDot (fun i => ec (kb + i)) la dk z one fx

/-! ## Step 4: the child's `PUB` evaluation -/

/-- Its cell. -/
def pubLaneC (hd vkc i : Nat) : Cell := if 1 ≤ i ∧ i < 5 then kc (vkc + (i - 1)) else kc (hd + i)

/-- `Σ_{i<nL} eq(r', i) · L_i` (`r'` the `τp` cells `al i`; `eqDot` split `τp/2`). -/
def qpub (al : Nat → Cell) (z one : Cell) (τp hd vkc nL : Nat) : BM Cell :=
  eqDot al (τp / 2) τp z one ((List.range nL).map (pubLaneC hd vkc))

end Lvm.QAcc
