-- new for lvm (WP-12b): `Q_sig`'s `BITS` rows (WP-12's `SigBits`) as six `BITS` tables of the lvm
-- M3 instance, and `SigBitsOk`: the `SigBits` hypothesis of `qsig_sound` from the bus (WP-9b).
-- Searched for reuse: none of FR/leanerVM/leanVM has a bus-read bit table (see `LvmBitsTab`).
import LvmBitsTab
import LvmQSigDefs

-- (GOLF2: 6 declarations that `certified` does not use moved verbatim to `LvmQAsmHar47Off`, outside its import closure.)

/-!
# `SigBitsOk`: `Q_sig`'s `BITS` outputs from the tables

**The tables** (`sigSpecs I o bpl`, one `BSpec` per output class; `bpl k` places class `k`'s
committed columns):

| k | class | rows (`2^τ`) | word cell of row `x` | outputs, cells |
|---|---|---|---|---|
| 0 | `idx` | 1 (1) | `σ'.idx` = `I.sg` | `shl 8`, `bit 0..15`, `shr 16` at `I.bi + j` |
| 1 | `md` | 4 (4) | `I.md + x` | `bit 0..63` at `I.bd + 64x + j` |
| 2 | `cs` | 1 (1) | none (free word) | `bit 0..9` at `I.bc + j` |
| 3 | step inputs | 1,596 (2^11) | `xin I o i s l`, `x = 4(3i+s)+l` | `shl 24`, `shr 40` at `I.bx + 2x + j` |
| 4 | byte shifts | 672 (2^10) | chain ends 532, path halves 128, `h'`, `c_L'`, `leafStmt` 4 each | `shl 8`, `shr 56` at `I.be`/`I.bp`/`I.bh`/`I.bcl`/`I.bls` `+ 2x' + j` |
| 5 | `n'` | 1 (1) | `I.hd + 13` | `shl 8`, `shr 56`, `bit 0..I.ln`, `shr (I.ln+1)`, `shl (64-I.ln)` at `I.bn + j` |

2,275 real rows, 3,079 table rows; Q_link's position fields (A20, `BOut.fld`) are further `BSpec`s
of QL's.

**`SigBitsOk`** (the hypothesis `NodeSound` hands to `qsig_sound`): `SigBits I o` holds for the
interpreter's `K` memory on the inputs read off the stack. **`sigBitsOk`** proves it from WP-9b's
`AuxHyps` (`loopir_sound`'s hypotheses), the six tables being auxiliary tables of the instance
(`SigTabsIn`), and their cells lying below `Q.cells .K` (`SigCellsLt`).
-/

set_option autoImplicit false

namespace Lvm.SigBits

open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.Loop Lvm.QSig

/-! ## The six classes -/

section Specs

variable (I : SigIn) (o : SigOut) (pl : Nat → Bool × Nat)

/-- `σ'.idx`: its low byte shift, its 16 bits, its high part. -/
def sIdx : BSpec :=
  ⟨0, 1, .shl 8 :: ((List.range 16).map .bit ++ [.shr 16]), true, fun _ => I.sg,
    fun j _ => I.bi + j, pl, 18, by intros; omega⟩

/-- The message digest's 256 bits. -/
def sMd : BSpec :=
  ⟨2, 4, (List.range 64).map .bit, true, fun x => I.md + x, fun j x => I.bd + 64 * x + j, pl, 64,
    by intros; omega⟩

/-- The checksum's ten bits, of a free word. -/
def sCs : BSpec :=
  ⟨0, 1, (List.range 10).map .bit, false, fun _ => 0, fun j _ => I.bc + j, pl, 10, by intros; omega⟩

/-- The chain step inputs (11-byte prefix): `shl 24`, `shr 40`. -/
def s24 : BSpec :=
  ⟨11, 1596, [.shl 24, .shr 40], true, fun x => xin I o (x / 12) (x / 4 % 3) (x % 4),
    fun j x => I.bx + 2 * x + j, pl, 2, by intros; omega⟩

/-- The one-byte shifts: chain ends, path halves, `h'`, `c_L'`, `leafStmt` lanes. -/
def s8 : BSpec :=
  ⟨10, 672, [.shl 8, .shr 56], true,
    fun x => if x < 532 then endc o (x / 4) (x % 4)
      else if x < 660 then (o.pa.cell (4 + 4 * ((x - 532) / 4 % 2) + (x - 532) % 4) ((x - 532) / 8)).n
      else if x < 664 then I.hd + 14 + (x - 660)
      else if x < 668 then I.hd + 5 + (x - 664) else I.yls + (x - 668),
    fun j x => if x < 532 then I.be + 2 * x + j
      else if x < 660 then I.bp + 2 * (x - 532) + j
      else if x < 664 then I.bh + 2 * (x - 660) + j
      else if x < 668 then I.bcl + 2 * (x - 664) + j else I.bls + 2 * (x - 668) + j, pl, 2,
    by intros; split_ifs <;> omega⟩

/-- `n'`: its byte shifts, its low `I.ln + 1` bits, its range parts. -/
def sN : BSpec :=
  ⟨0, 1, .shl 8 :: .shr 56 :: ((List.range (I.ln + 1)).map .bit ++ [.shr (I.ln + 1), .shl (64 - I.ln)]),
    true, fun _ => I.hd + 13, fun j _ => I.bn + j, pl, I.ln + 5, by intros; omega⟩

/-- **`Q_sig`'s `BITS` tables**, class `k` placed by `bpl k`. -/
def sigSpecs (bpl : Nat → Nat → Bool × Nat) : List BSpec :=
  [sIdx I (bpl 0), sMd I (bpl 1), sCs I (bpl 2), s24 I o (bpl 3), s8 I o (bpl 4), sN I (bpl 5)]

end Specs

/-! ## `SigBitsOk` -/

section Ok

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

theorem getD_idx {z : Nat} (hz : z < 16) :
    (BOut.shl 8 :: ((List.range 16).map BOut.bit ++ [BOut.shr 16])).getD (1 + z) (.bit 0) = .bit z := by
  rw [show 1 + z = z + 1 by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega : z < ((List.range 16).map BOut.bit).length), hz]

theorem getD_n {ln z : Nat} (hz : z ≤ ln) :
    (BOut.shl 8 :: BOut.shr 56 :: ((List.range (ln + 1)).map BOut.bit ++
      [BOut.shr (ln + 1), BOut.shl (64 - ln)])).getD (2 + z) (.bit 0) = .bit z := by
  rw [show 2 + z = z + 1 + 1 by omega]
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega : z < ((List.range (ln + 1)).map BOut.bit).length),
    show z < ln + 1 by omega]

theorem getD_n_top {ln : Nat} :
    (BOut.shl 8 :: BOut.shr 56 :: ((List.range (ln + 1)).map BOut.bit ++
      [BOut.shr (ln + 1), BOut.shl (64 - ln)])).getD (ln + 3) (.bit 0) = .shr (ln + 1) := by
  rw [show ln + 3 = (ln + 1) + 1 + 1 by omega]
  simp [List.getD_eq_getElem?_getD]

theorem getD_n_low {ln : Nat} :
    (BOut.shl 8 :: BOut.shr 56 :: ((List.range (ln + 1)).map BOut.bit ++
      [BOut.shr (ln + 1), BOut.shl (64 - ln)])).getD (ln + 4) (.bit 0) = .shl (64 - ln) := by
  rw [show ln + 4 = ((ln + 1) + 1) + 1 + 1 by omega]
  simp [List.getD_eq_getElem?_getD]

theorem getD_bit {n z : Nat} (hz : z < n) : ((List.range n).map BOut.bit).getD z (.bit 0) = .bit z := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hz]; rfl

end Ok

-- (lvm2 GOLF: the non-vacuity checks `honest_sig` and `honest_check` moved to `LvmSigBitsH`, outside `Solution`'s
-- import closure: nothing uses them, and `honest_check`'s decision cost ≈ 7 s of the certificate's build.)

end Lvm.SigBits
