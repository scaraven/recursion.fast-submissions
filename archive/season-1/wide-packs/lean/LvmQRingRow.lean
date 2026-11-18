-- New for lvm2 E2F (slice S1, E2F-QH2): the 128-row switch of the front's bit slices (design/E2-S-switch.md §2, V's
-- `LvmDecideE2.rowSwitchD`), replacing v1's ring switch (`LvmQRingG.ringG`) at S2GF: the target gadget on `E` rows and
-- the auxiliary (`BITS`-class) rows that tie the free row words `t_j` to the 64 `E2` slices by the bit transpose.
import LvmE2QWKit
import LvmTypedLayout

/-!
# The row switch (`rowG`, `rowAux`)

V reads the 64 slices `s_i ∈ E2` (16 B each, lanes `qs + 2 i`, `re` then `im`), then seven `E3` answers `r''`
(no nonce; answers `qr + 9 k`), and sets `ρ_j = eq(r'', j)` (`eqKernel`, coordinate `k` = bit `k` of `j`) and the
target `σ = Σ_j ρ_j·t_j`, `t_j = rowWordD sv j = Σ_i bit_j(s_i)·x^i` (`bit_j(s)` = bit `j mod 64` of coordinate
`j div 64`).

LoopIR has no bit operation and no free cells, so the row words are **free `K` cells** `tB + j` (`j < 128`, placed
by the layout in the `BITS` output region, like a `BSpec`'s outputs) tied to the stream by auxiliary rows on
`8,192` free bit words `bw + 64 j + i` (bit `i` of row word `j`):

* booleanity `b·b + b = 0` per bit word;
* recomposition `t_j + Σ_i x^i·b_{j,i} = 0` (`D` on the cell `tB + j`);
* transposition `s_i^(h) + Σ_{j<64} x^j·b_{j+64h, i} = 0` (`D` on the slice lane `qs + 2 i + h`).

Holding, they give `t_j = rowWordD sv j` (bits are bits, the rows of the transpose are the slices' bits).
The template part **`rowG qs qr tB z o`**: seven `loadE` rows, the `eq` table (`E` rows), `σ` (128 `muladd` rows
on the `K` cells `t_j`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Typed

/-! ## The auxiliary rows -/

/-- `x^i` as a weight (`i < 64`: the word with bit `i`). -/
def xPowW (i : Nat) : FE := FE.ofK ⟨UInt64.ofNat (2 ^ i)⟩

/-- Bit `i` of row word `j`: the free word `bw + 64 j + i`. -/
def rowBit (bw j i : Nat) : AOp := .word (bw + 64 * j + i) 0

/-- The booleanity rows of the `8,192` bit words. -/
def rowBoolRows (bw : Nat) : List ARow :=
  (List.range 128).flatMap fun j => (List.range 64).map fun i =>
    (⟨[(0, rowBit bw j i, 1), (1, rowBit bw j i, 1), (2, rowBit bw j i, 1)]⟩ : ARow)

/-- The recomposition row of row word `j`: `t_j + Σ_i x^i·b_{j,i} = 0`. -/
def rowRecRow (bw tB j : Nat) : ARow :=
  ⟨(2, .cell ⟨.K, tB + j, []⟩, 1) :: (List.range 64).map fun i => (2, rowBit bw j i, xPowW i)⟩

/-- The transposition row of slice `i`, coordinate `h`: `s_i^(h) + Σ_{j<64} x^j·b_{j+64h, i} = 0`. -/
def rowTrRow (bw qs h i : Nat) : ARow :=
  ⟨(2, .cell ⟨.K, qs + 2 * i + h, []⟩, 1) :: (List.range 64).map fun j => (2, rowBit bw (j + 64 * h) i, xPowW j)⟩

/-- **The auxiliary block of a row switch**: booleanity of the `8,192` bit words, the 128 recompositions onto the
free cells `tB + j`, the 128 transpositions onto the slice lanes `qs + 2 i + h`. -/
def rowAux (bw tB qs : Nat) : ABlk :=
  ⟨0, rowBoolRows bw ++ (List.range 128).map (rowRecRow bw tB) ++
    (List.range 2).flatMap fun h => (List.range 64).map (rowTrRow bw qs h)⟩

/-- The bit words a row switch needs. -/
def rowAuxWords : Nat := 128 * 64

/-! ## The target -/

/-- `eqKernel` on `E` cells from `tab` (`z` an `E` zero cell, `o` an `E` one cell): per coordinate `1 + r`, then
`e·(1 + r)` and `e·r` for every `e`. -/
def eqTabE (z o : Cell) : List Cell → List Cell → BM (List Cell)
  | tab, [] => pure tab
  | tab, r :: rs => do
    let r1 ← add r o
    let lo ← mapB (fun e => mulAdd .E e r1 z) tab
    let hi ← mapB (fun e => mulAdd .E e r z) tab
    eqTabE z o (lo ++ hi) rs

/-- `acc + Σ_j a_j·b_j` on `E` rows. -/
def dotE : Cell → List (Cell × Cell) → BM Cell
  | acc, [] => pure acc
  | acc, (a, b) :: r => mulAdd .E a b acc >>= fun acc' => dotE acc' r

/-- A row switch's output. -/
structure RowOut where
  /-- `eq(r'', j)`, `j < 128` (`E` cells). -/
  eqR : List Cell
  /-- The target `σ` (`E` cell). -/
  target : Cell
  /-- The seven `r''` (`E` cells). -/
  rr : List Cell

/-- The answer lanes of the seven samples from the first one `qr`. -/
def rowLanes (qr : Nat) : List Nat := (List.range 7).map fun k => qr + 9 * k

/-- **The row switch's target**: the seven `E3` answers at `qr + 9 k`, `ρ = eq(r'', ·)`, `σ = Σ_j ρ_j·t_j` with
`t_j` the free `K` cells `tB + j` (`z`, `o`: `E` zero and one cells). -/
def rowG (qr tB z o : Nat) : BM RowOut :=
  mapB (fun q => loadE (kc q) (kc (q + 1)) (kc (q + 2))) (rowLanes qr) >>= fun rr =>
  eqTabE (ec z) (ec o) [ec o] rr >>= fun eqR =>
  dotE (ec z) ((List.range 128).map fun j => (eqR.getD j default, kc (tB + j))) >>= fun t =>
  pure ⟨eqR, t, rr⟩

end Lvm.Q2
