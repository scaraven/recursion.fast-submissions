-- New for `flock-recursive` (BLUEPRINT revision 4.3, (A)(ii), A.6, A.8 `linkW`; stage S-H4, pass 8,
-- item 1: the signature the node decoder outputs). 3.x analogue: `FRNodeRead.readSig` (L cells).
import FRXOut4
import FRNodeRows4WotsB

/-!
# The signature read off H's message slots (`sigH`)

L is not decoded (`out_cells_rows`), so the decoder reads a signed child's signature from the H
blocks of its WOTS run (revision 4.3, (A)(ii)), whose message slots are rows 4–7 of `f⁽⁰⁾`:

* **the index** is the key leaf's `j` field: message bytes `1 … 8` of WOTS block `399`, little
  endian (the `j` family);
* **`ots_i`** is chain `i`'s first step block's `x` field: message bytes `11 … 42` of WOTS block
  `3i` (the `x` family);
* **path sibling `t`** is the level's `l` field (message bytes `1 … 32` of block `466 + 2t`) when
  bit `t` of the index is `1`, else its `r` field: bytes `33 … 63` of block `466 + 2t` and byte `0`
  of block `467 + 2t` (the `r0`, `r31` families).

`FRXSig4H.sig_of_H` proves it L's signature (`readSig4`) on every witness of the node statement.
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

/-- **Message byte `p` (`p < 64`) of H block `b`**: byte `p mod 16` of element `4 + ⌊p/16⌋`. -/
def hMB (w : Circ.Asg) (b p : ℕ) : UInt8 := W4.fb (w (W4.hc b (4 + p / 16))) (p % 16)

/-- The 32 message bytes of H block `b` from byte `o`. -/
def hMD (w : Circ.Asg) (b o : ℕ) : Digest := Vector.ofFn fun i : Fin 32 => hMB w b (o + i)

/-- **The index** (the key leaf's `j` field, little endian). -/
def idxH (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) : ℕ :=
  ofLE ((List.range 8).map fun k => hMB w (W4.wb κ σ 399) (1 + k))

/-- **Path level `t`'s `r` field**: bytes `33 … 63` of `hashB1`'s block, byte `0` of `hashB2`'s. -/
def rFH (κ : NodeKind) (σ t : ℕ) (w : Circ.Asg) : Digest :=
  Vector.ofFn fun i : Fin 32 =>
    if i.val < 31 then hMB w (W4.wb κ σ (466 + 2 * t)) (33 + i) else hMB w (W4.wb κ σ (467 + 2 * t)) 0

/-- **Path sibling `t`**: the `l` field if bit `t` of the index is `1`, else the `r` field. -/
def sibFH (κ : NodeKind) (σ t : ℕ) (w : Circ.Asg) : Digest :=
  if idxH κ σ w / 2 ^ t % 2 = 1 then hMD w (W4.wb κ σ (466 + 2 * t)) 1 else rFH κ σ t w

/-- **Signed child `σ`'s signature read off H** (revision 4.3, (A)(ii)). -/
def sigH (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) : Sig where
  idx := idxH κ σ w
  ots := (List.range wotsLen).map fun i => hMD w (W4.wb κ σ (3 * i)) 11
  path := (List.range sigHeight).map fun t => sibFH κ σ t w

/-- `hMB` is the block's message byte (`msgByte_hc`). -/
theorem hMB_eq (w : Circ.Asg) (b : ℕ) {p : ℕ} (hp : p < 64) :
    hMB w b p = (Block.msgBytes (N4c.bitsB4 w b)).getD p 0 := (W4.msgByte_hc w b hp).symm

/-- **Every cell `sigH` reads is decoded** (a message slot of an H block: rows 4–7). -/
theorem hMB_dec0 (b p : ℕ) (hp : p < 64) : Dec0 (W4.hc b (4 + p / 16)) := by
  unfold Dec0 W4.hc; omega

/-! ## Controls -/

/-- A witness whose key-leaf message element 4 (child `0`) is `256` (byte 1 is `1`), zero
elsewhere. -/
def wIdx1 (κ : NodeKind) : Circ.Asg := fun e => if e = W4.hc (W4.wb κ 0 399) 4 then ⟨⟨256⟩, ⟨0⟩⟩ else 0

/-- (+/−) **`sigH` reads H, not L**: on `wIdx1` the index read off H is `1` while L's index cell
is `0` (so `sig_of_H` needs the rows: the two readers differ off the statement); on the zero
witness the index is `0`. -/
theorem sigH_ctl : (sigH .N2 0 (wIdx1 .N2)).idx = 1 ∧ (N4s.readSig4 .N2 0 (wIdx1 .N2)).idx = 0 ∧
    (sigH .N2 0 (fun _ => 0)).idx = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end FR.X
