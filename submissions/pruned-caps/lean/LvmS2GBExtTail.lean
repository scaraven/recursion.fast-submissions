-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): the extractor's π tail at S2GB (straight-line programs from
-- static per-level data: the covered-node bitmap, the count, the uncovered layer nodes from the heap queries).
import LvmS2GBExtDyn

/-!
# The π tail in the extractor

Per opened level (static data `TLv`): `m` (cap bits), the bitmap base `bm`, for every path the memory word of its
position answer holding bit `s` and the bit offset `s % 64` (`pos`), and per heap slot `2^(m−1) + y` the memory word
of its query's word 0 (`heap`, indexed by `y = x / 2`).

* `clrIR`: the bitmap to `0`; `markIR`: per path, `x := bits [s, s + m)` of the answer, `bm[x] := 1`;
* `cntIR'`: `tN +=` the uncovered nodes; `sizeIR'`: `piStatic + 32 · tN` emitted;
* `emitIR'`: per `x` ascending with `bm[x] = 0`, the 4 words of half `x % 2` of heap slot `2^(m−1) + x / 2`.
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm.X

/-- Tail registers (free at the node output: the segments' context is `oR`, `oKF`, `oBd _`). -/
def tA : ℕ := 215
/-- Tail register. -/ def tB : ℕ := 217
/-- Tail register. -/ def tC : ℕ := 219
/-- Tail register (constants). -/ def tK : ℕ := 221
/-- The uncovered count. -/ def tN : ℕ := 225

/-- **One opened level's static data.** -/
structure TLv where
  /-- Cap bits. -/
  m : ℕ
  /-- The bitmap's base (memory). -/
  bm : ℕ
  /-- Per path: the memory word of its answer holding bit `s`, and `s % 64`. -/
  pos : List (ℕ × ℕ)
  /-- Per `y < 2^(m−1)`: the memory word of heap slot `2^(m−1) + y`'s query word 0. -/
  heap : List ℕ

/-- `M[a] := 0` for `a = b, b + 1, …, b + n − 1`. -/
def clrIR (b : ℕ) : ℕ → XIR
  | 0 => .blk []
  | n + 1 => .seq (.seq (.blk [.const tA (toWord b), .const tC 0]) (.store tA tC)) (clrIR (b + 1) n)

/-- One path: `x :=` bits `[off, off + m)` of the words at `a`, `a + 1`; `M[bm + x] := 1`. -/
def mark1IR (bm m a off : ℕ) : XIR :=
  .seq (.seq (.blk [.const tA (toWord a)]) (.load tB tA))
    (.seq (if off + m ≤ 64 then .blk [.const tK (toWord off), .op .shr tB tB tK]
      else .seq (.seq (.blk [.const tA (toWord (a + 1))]) (.load tC tA))
        (.blk [.const tK (toWord off), .op .shr tB tB tK, .const tK (toWord (64 - off)), .op .shl tC tC tK,
          .op .or tB tB tC]))
      (.seq (.blk [.const tK (toWord (2 ^ m - 1)), .op .and tB tB tK, .const tK (toWord bm), .op .add tB tB tK,
        .const tC 1]) (.store tB tC)))

/-- Every path of a level. -/
def markIR (bm m : ℕ) : List (ℕ × ℕ) → XIR
  | [] => .blk []
  | (a, off) :: ps => .seq (mark1IR bm m a off) (markIR bm m ps)

/-- `tN +=` `[M[b + x] = 0]` for `x < n`. -/
def cntIR' (b : ℕ) : ℕ → XIR
  | 0 => .blk []
  | n + 1 => .seq (.seq (.blk [.const tA (toWord b)]) (.seq (.load tB tA)
      (.blk [.const tK 0, .op .eq tB tB tK, .op .add tN tN tB]))) (cntIR' (b + 1) n)

/-- Output the words `M[a], …, M[a + n − 1]`. -/
def cpWIR (a : ℕ) : ℕ → XIR
  | 0 => .blk []
  | n + 1 => .seq (.seq (.blk [.const tA (toWord a)]) (.seq (.load tB tA) (.out tB))) (cpWIR (a + 1) n)

/-- Layer node `x` if uncovered: half `x % 2` (4 words) of the heap slot's query (word 0 at `q`). -/
def node1IR (bm x q : ℕ) : XIR :=
  .seq (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) (.ite tB (.blk []) (cpWIR (q + 4 * (x % 2)) 4))

/-- The uncovered nodes `x ∈ xs` of a level, in order. -/
def nodesIR (bm : ℕ) (heap : List ℕ) : List ℕ → XIR
  | [] => .blk []
  | x :: xs => .seq (node1IR bm x (heap.getD (x / 2) 0)) (nodesIR bm heap xs)

/-- **The bitmaps**: cleared, then marked. -/
def bmIR : List TLv → XIR
  | [] => .blk []
  | l :: ls => .seq (.seq (clrIR l.bm (2 ^ l.m)) (markIR l.bm l.m l.pos)) (bmIR ls)

/-- **The count** over the levels. -/
def cntAllIR : List TLv → XIR
  | [] => .blk []
  | l :: ls => .seq (cntIR' l.bm (2 ^ l.m)) (cntAllIR ls)

/-- **The size word**: `pz0 + 32 · (uncovered nodes)`. -/
def sizeWIR (pz0 : ℕ) (ls : List TLv) : XIR :=
  .seq (.blk [.const tN 0]) (.seq (cntAllIR ls)
    (.seq (.blk [.const tK 5, .op .shl tN tN tK, .const tK (toWord pz0), .op .add tN tN tK]) (.out tN)))

/-- **The tail**: per level the uncovered nodes in ascending `x`. -/
def tailIR : List TLv → XIR
  | [] => .blk []
  | l :: ls => .seq (nodesIR l.bm l.heap (List.range (2 ^ l.m))) (tailIR ls)

end Lvm.XB
