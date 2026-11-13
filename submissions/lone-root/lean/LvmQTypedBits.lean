-- New for lvm2 (roll 8 = B1, B1-Q; B-DES §1.1, B1-P1P2 §5.3): `BITS` as typed rows. A `BITS` class (WP-12's
-- `BSpec`, the bus's auxiliary table) becomes auxiliary constraint blocks of the typed layout (`Lay.aux`,
-- `LvmTypedLayout.ABlk`): the 64 bit words are free committed words, the word and the outputs are program cells.
-- Reuses `BSpec` (`LvmBitsTab`), `bspecs` (`LvmQAsmTabs`), `BOut.coef`, `wt` (`LvmBits`).
import LvmQAsmTabs
import LvmTypedLayout

/-!
# `BITS` as typed rows

A class `S` with `n` real rows becomes, per **chunk** `[x₀, x₀ + 2^l)` of its real rows on which every cell function
(`wc`, `oc j`) is affine, one auxiliary block of `2^l` iterations (`BSpec.chunks`: the binary pieces of `[0, n)`,
halved until affine; no padding row, so no extrapolated cell is constrained). Its rows, at iteration `j` (row
`x = x₀ + j`), bit `z`'s word being `bw + 64 x + z`:

* **booleanity** `β_z·β_z + β_z = 0` (`A`, `B`, `D` on the bit word), `z < 64`;
* **the word** (when `rd`): `w + Σ_z x^z·β_z = 0` (`D` on the cell `wc x` and the bit words);
* **output `j`**: `oc_j + Σ_z coef_j(z)·β_z = 0` (`D`).

These are WP-12's `Row.Constraints` and `Row.out` (`LvmBits.row_sound` gives the outputs from them); the bus's
reads, counts and address columns are gone. Rows: `64 + [rd] + |outs|` per class row [exact].

* **`BSpec.ablks S bw`**: the blocks of class `S`, its bits from word `bw`.
* **`bitsAux C bw`**: the node program's classes (`bspecs`: Q_sig's six, the lane classes, `s'`, the PoW fields),
  class `k`'s bits from `bw k` (the layout solver's).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits Lvm.QAsm

/-- `f` is affine on `[x₀, x₀ + 2^l)`: its value at `x₀` and its step. -/
def affOn (f : Nat → Nat) (x₀ l : Nat) : Option (Nat × Nat) :=
  let b := f x₀
  let s := f (x₀ + 1) - b
  if l = 0 then some (b, 0)
  else if b ≤ f (x₀ + 1) ∧ (List.range (2 ^ l)).all (fun j => f (x₀ + j) == b + s * j) then some (b, s) else none

/-- The cell functions of a class: the word's (when `rd`), then the outputs'. -/
def _root_.Lvm.BitsTab.BSpec.cellFns (S : BSpec) : List (Nat → Nat) :=
  (if S.rd then [S.wc] else []) ++ (List.range S.outs.length).map fun j => S.oc j

/-- The cell functions tabulated on the real rows `[0, n)` (B1-IX: once per class, so the chunk search reads arrays;
on a chunk inside `[0, n)` an entry is the function's value, `tab_getD`). -/
def _root_.Lvm.BitsTab.BSpec.cellTabs (S : BSpec) : List (Array Nat) := S.cellFns.map fun f => (Array.range S.n).map f

/-- `affOn` on a tabulated function (`isSome` of `affOn` at the function, inside the table). -/
def affOnA (a : Array Nat) (x₀ l : Nat) : Bool :=
  let b := a.getD x₀ 0
  let s := a.getD (x₀ + 1) 0 - b
  l == 0 || (decide (b ≤ a.getD (x₀ + 1) 0) && (List.range (2 ^ l)).all fun j => a.getD (x₀ + j) 0 == b + s * j)

/-- A table entry inside the real rows is the function's value. -/
theorem tab_getD (f : Nat → Nat) {n i : Nat} (hi : i < n) : ((Array.range n).map f).getD i 0 = f i := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- Every cell function is affine on the chunk (on the tables `ts`, `S.cellTabs`). -/
def _root_.Lvm.BitsTab.BSpec.affChunk (ts : List (Array Nat)) (x₀ l : Nat) : Bool := ts.all fun a => affOnA a x₀ l

/-- The largest aligned chunk at `x₀` inside `[x₀, n)` on which the cells are affine (from size `2^l` down). -/
def _root_.Lvm.BitsTab.BSpec.chunkAt (S : BSpec) (ts : List (Array Nat)) (x₀ : Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => if x₀ % 2 ^ (l + 1) = 0 ∧ x₀ + 2 ^ (l + 1) ≤ S.n ∧ BSpec.affChunk ts x₀ (l + 1) then l + 1
    else S.chunkAt ts x₀ l

/-- **The chunks** `(x₀, l)` of the real rows, in order (`fuel` bounds the count). -/
def _root_.Lvm.BitsTab.BSpec.chunksGo (S : BSpec) (ts : List (Array Nat)) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, x₀ =>
    if S.n ≤ x₀ then [] else
      let l := S.chunkAt ts x₀ (Nat.log2 (S.n - x₀))
      (x₀, l) :: S.chunksGo ts fuel (x₀ + 2 ^ l)

/-- The chunks of a class. -/
def _root_.Lvm.BitsTab.BSpec.chunks (S : BSpec) : List (Nat × Nat) := S.chunksGo S.cellTabs S.n 0

/-- The address of a cell function on a chunk (`K` memory). -/
def cellAddr (f : Nat → Nat) (x₀ l : Nat) : Addr :=
  match affOn f x₀ l with
  | some (b, s) => ⟨.K, b, [s]⟩
  | none => ⟨.K, f x₀, [0]⟩

/-- Bit `z`'s word at iteration `j` of the chunk at `x₀`: `bw + 64 (x₀ + j) + z`. -/
def bitOp (bw x₀ z : Nat) : AOp := .word (bw + 64 * x₀ + z) 64

/-- The rows of a chunk. -/
def _root_.Lvm.BitsTab.BSpec.chunkRows (S : BSpec) (bw x₀ l : Nat) : List ARow :=
  ((List.range 64).map fun z => (⟨[(0, bitOp bw x₀ z, 1), (1, bitOp bw x₀ z, 1), (2, bitOp bw x₀ z, 1)]⟩ : ARow)) ++
  (if S.rd then [⟨(2, .cell (cellAddr S.wc x₀ l), 1) ::
      (List.range 64).map fun z => (2, bitOp bw x₀ z, FE.ofK (wt z))⟩] else []) ++
  (List.range S.outs.length).map fun j =>
    ⟨(2, .cell (cellAddr (S.oc j) x₀ l), 1) ::
      ((List.range 64).filter fun z => (S.out j).coef z != 0).map fun z => (2, bitOp bw x₀ z, FE.ofK ((S.out j).coef z))⟩

/-- **The typed blocks of a `BITS` class**, its bits from word `bw` (64 words per real row). -/
def _root_.Lvm.BitsTab.BSpec.ablks (S : BSpec) (bw : Nat) : List ABlk := S.chunks.map fun c => ⟨c.2, S.chunkRows bw c.1 c.2⟩

/-- A placement record with no placements (`BITS` as typed rows reads none). -/
def noData : QData := ⟨[], [], [], 0, []⟩

/-- **The node program's `BITS` classes as typed rows**, class `k`'s bits from `bw k`. -/
def bitsAux (C : QCfg) (bw : Nat → Nat) : List ABlk :=
  (bspecs C noData).zipIdx.flatMap fun x => x.1.ablks (bw x.2)

/-- The bit words a class needs (`64 n`). -/
def bitsWords (C : QCfg) : List Nat := (bspecs C noData).map fun S => 64 * S.n

end Lvm.QTyped
