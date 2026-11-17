-- New for lvm (WP-13a): the extractor's static layout, read off `V_S`'s schedule (`LvmSchedule`,
-- `LvmDriver`). FR's counterpart is `FRXChainFlock`'s `fsMsgs` (adapted: lvm's FS queries are
-- `st ‖ pending` with no tag, `LvmDriver.fsQuery`).
import LvmDriver

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmXOutSegOff`, outside its import closure.)

/-!
# The extractor's layout (BLUEPRINT §2, §6.2)

Everything the extractor program needs about an `S` proof and its child's stream, computed from
the parameter record `p` (production: `pX = P20`) by the schedule, so that `V_S`, the circuit and
the extractor read one definition.

* **Fiat–Shamir messages** `fsMsgs p`: per position `p ≥ 1` of the chain the π range `(o, len)` the
  query absorbs (position 1 is the seed: `a₀ ‖ π[8, 5984)`; position `k ≥ 2` the `k − 1`-th FS
  query `st ‖ π[pend, off)`), over the whole schedule as `LvmDriver.driveItems` reads it (an
  opening's rows and siblings are skipped, never absorbed).
* `nChain p`: the chain's targets `0 … nChain − 1` (0 is `q₀`), through the fold samples of
  `C_rec`'s level 1 (lvm2 S4: `openRec` = `ρ`, intro, `α₀` ×6, level 1's cap, level 0's positions,
  `λ`, opening, intro, `α₁` ×4, `f₂`); `alphaPos p j` / `alpha1Pos p j` the positions of `α₀_j` /
  `α₁_j`; `capRec1Off p` the π offset of level 1's cap, `f2Off p` of the final `f₂` (`2^9` `E`
  scalars), `capRecOff p` of `C_rec`'s (level 0's) cap.
* **The child's stream** (`Σ = tagTrace ‖ traceBytes tr`, lanes): `blocks p`, the trace entries
  after the seed as blocks (one query, or an opening of `t` positions); lane offsets follow.
-/

namespace Lvm.X

open RecursionFast Lvm

/-- The extractor's parameter set. -/
abbrev pX : Params := P20

/-! ## The Fiat–Shamir chain -/

/-- The FS messages `(π offset, length)` of the items, from the body offset `off` with the pending
bytes starting at `pend`, exactly as `LvmDriver.driveItems` moves them: a read or a cap advances `off`
(the cap's bytes stay pending), an FS query absorbs `π[pend, off)`, a positions item is `nPosQ` queries
(the first absorbs what is pending, the rest the state alone), and an opening skips its
`t · (row + 32 · path)` bytes, which no query absorbs (`pend := off`). -/
def fsPre (p : Params) : List Item → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .read m :: r, off, pend => fsPre p r (off + eBytes * m) pend
  | .readW m w :: r, off, pend => fsPre p r (off + w * m) pend
  | .cap c ref :: r, off, pend => fsPre p r (off + nodeBytes * 2 ^ p.capSendBits ref.lv c) pend
  | .sample :: r, off, pend => (pend, off - pend) :: fsPre p r off off
  | .positions ref :: r, off, pend =>
      (pend, off - pend) :: (List.replicate ((p.level ref).nPosQ - 1) (off, 0) ++ fsPre p r off off)
  | .opening ref :: r, off, _ =>
      fsPre p r (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))
        (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))

/-- **The chain's messages**: position `k ≥ 1` absorbs `fsMsgs p` entry `k − 1` (the seed first). -/
def fsMsgs (p : Params) : List (ℕ × ℕ) :=
  (8, headerBytes - 8) :: fsPre p (schedule p) headerBytes headerBytes

/-- The FS queries before `C_rec`'s opening phase. -/
def nPre (p : Params) : ℕ :=
  (fsPre p (((phases p).take 7).flatMap (·.2)) headerBytes headerBytes).length

/-- `C_rec`'s level `j`. -/
def recL (p : Params) (j : ℕ) : Level := p.level ⟨.crec, j⟩

/-- The FS queries of a level's proof of work (`LvmSchedule.grindI`): the separator and the PoW
challenge, none without grinding. -/
def gQs (p : Params) : ℕ := if p.grind = 0 then 0 else 2

/-- The FS queries of level 0's out-of-domain point (lvm2 J2P-VQP, J2′: `κ₀` samples after level 1's cap,
JB-L §3), none without OOD. -/
def oQs (p : Params) : ℕ := if p.recOod then (recL p 0).kappa else 0

/-- **The chain's targets** `0 … nChain p − 1`: `q₀`, the seed, the FS queries before `openRec`,
`openRec`'s first sample (`ρ`), the fold samples of `C_rec`'s level 0 (`α₀`), its OOD point (J2′), its
proof of work (separator, PoW challenge; S2J), its positions queries, its `λ`, and the fold samples of
level 1 (`α₁`). -/
def nChain (p : Params) : ℕ :=
  nPre p + 4 + (recL p 0).fold + oQs p + gQs p + (recL p 0).nPosQ + (recL p 1).fold

/-- The chain position of level 0's fold challenge `α_j` (`j < 6`). -/
def alphaPos (p : Params) (j : ℕ) : ℕ := nPre p + 3 + j

/-- The chain position of level 1's fold challenge `α₁_j` (`j < 4`): after level 0's OOD point, proof
of work, positions queries and `λ`. -/
def alpha1Pos (p : Params) (j : ℕ) : ℕ :=
  nPre p + 4 + (recL p 0).fold + oQs p + gQs p + (recL p 0).nPosQ + j

/-- The π offset of `C_rec`'s level-1 cap (after level 0's last fold round's 2 scalars; v1's `f₁`
offset). -/
def capRec1Off (p : Params) : ℕ :=
  ((fsMsgs p).getD (nPre p + 2 + (recL p 0).fold) (0, 0)).1 + 2 * eBytes

/-- The π offset of `C_rec`'s final `f₂` (`2^9` `E` scalars, after level 1's last fold round's 2
scalars). -/
def f2Off (p : Params) : ℕ := ((fsMsgs p).getD (nChain p - 1) (0, 0)).1 + 2 * eBytes

/-- The π offset of `C_rec`'s cap (after `C_main`'s, BLUEPRINT §2.1 commit phase). -/
def capRecOff (p : Params) : ℕ := headerBytes + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap

/-! ## The child's stream -/

/-- A run of trace entries: one query of class `c` and length `len`, or the openings of `t`
positions (a leaf query of `row` bytes, then `path` node queries of 64 bytes each). -/
inductive Blk where
  | one (c : QClass) (len : ℕ)
  | opn (t row path : ℕ)
  deriving DecidableEq, Repr

/-- The blocks of the items, with `pend` bytes pending (`LvmSchedule.itemQueries`). -/
def itemBlks (p : Params) : List Item → ℕ → List Blk
  | [], _ => []
  | .read m :: r, pend => itemBlks p r (pend + eBytes * m)
  | .readW m w :: r, pend => itemBlks p r (pend + w * m)
  | .cap c ref :: r, pend => itemBlks p r (pend + nodeBytes * 2 ^ p.capSendBits ref.lv c)
  | .sample :: r, pend => .one .fs (32 + pend) :: itemBlks p r 0
  | .positions ref :: r, pend =>
      .one .fs (32 + pend) :: (List.replicate ((p.level ref).nPosQ - 1) (.one .fs 32) ++
        itemBlks p r 0)
  | .opening ref :: r, _ =>
      .opn (p.level ref).t (p.level ref).row (p.level ref).path ::
        (List.replicate (p.heapQ ref.lv (p.level ref).cap) (.one .q0 64) ++ itemBlks p r 0)

/-- **The trace after `q₀`**: the seed, then the schedule's blocks. -/
def blocks (p : Params) : List Blk := .one .seed (seedLenP p) :: itemBlks p (schedule p) 0

/-- A block's queries `(class, length)`. -/
def Blk.queries : Blk → List (QClass × ℕ)
  | .one c len => [(c, len)]
  | .opn t row path => (List.replicate t ((.leaf, row) :: List.replicate path (.node, 64))).flatten

/-- A block's lanes in the stream (an entry is `|q|`, `q`, the answer). -/
def Blk.lanes : Blk → ℕ
  | .one _ len => 5 + len / 8
  | .opn t row path => t * (5 + row / 8 + 13 * path)

/-- A block's bytes in the reassembled proof (BLUEPRINT §2.2: a seed contributes `header[8..]`, an FS
query its message, an opening its rows and siblings). -/
def Blk.pBytes : Blk → ℕ
  | .one .seed len => len - 32
  | .one .fs len => len - 32
  | .one _ _ => 0
  | .opn t row path => t * (row + 32 * path)

/-- A block's `traceBytes` length: `8 + |q| + 32` per entry. -/
def Blk.trBytes : Blk → ℕ
  | .one _ len => 40 + len
  | .opn t row path => t * (40 + row + 104 * path)

/-- A block's entries. -/
def Blk.count : Blk → ℕ
  | .one _ _ => 1
  | .opn t _ path => t * (1 + path)

/-- A block's query lengths are lane-aligned and at least 32 bytes (`LvmXOut`'s `blkLensOk`). -/
def blkLensOkL : Blk → Bool
  | .one _ len => len % 8 == 0 && 32 ≤ len
  | .opn _ row _ => row % 8 == 0 && 32 ≤ row

/-- **The leaf lengths at `pX`**: the rows of both commitments' levels (`leafLens_rows`), a leaf
carrying its row's occupied words (`C_main`'s root: 47 of 64, 376 B (lvm2 roll 11, M′ `S2GM`; no `C_rec`); the later
levels' 48, 384 B; lvm2 PORT-17 and CR-Z2, Z2 after #17). The reassembly copies a query of one of
these lengths whole (a leaf), and the length rule (`LvmSchedule.lengthRule`) keeps every FS query off them. -/
def leafLens : List ℕ := [376, 384]

/-- A leaf is not a node query. -/
theorem ne64_of_leaf {len : ℕ} (h : len ∈ leafLens) : len ≠ 64 := by
  simp only [leafLens, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

/-- The words a query of `len` bytes contributes to the proof (`LvmXOut`'s `pieceLen`). -/
def pieceLenL (len : ℕ) : ℕ :=
  if len = 64 then 4 else if len ∈ leafLens then len / 8 else (len - 32) / 8

/-- A block's contribution to the proof in words (`LvmXOut`'s `blkPieceLen`). -/
def blkPieceLenL : Blk → ℕ
  | .one _ len => pieceLenL len
  | .opn t row path => t * (pieceLenL row + path * pieceLenL 64)

/-! Per block, the measures of its output segments (`LvmXTop.segAll`): `segCost`, `segOuts` and
`segSize` (`LvmXSeg`) of `blkPSeg 0 b` and `blkTSeg 0 b` (`LvmXOutSeg`), each `+ 1` for its `cat`
where the measure counts it. -/

/-- `segCost (blkPSeg 0 b) + 1`. -/
def blkPCostL : Blk → ℕ
  | .one .seed len | .one .fs len => 14 + 36 * ((len - 32) / 8) + 1
  | .one _ _ => 1 + 1
  | .opn t row path => 12 + t * (14 + 36 * (row / 8) + (12 + path * (457 + 7)) + 1 + 7) + 1

/-- `segOuts (blkPSeg 0 b)`. -/
def blkPOutsL : Blk → ℕ
  | .one .seed len | .one .fs len => (len - 32) / 8
  | .one _ _ => 0
  | .opn t row path => t * (row / 8 + path * 4)

/-- `segSize (blkPSeg 0 b) + 1`. -/
def blkPSizeL : Blk → ℕ
  | .one .seed _ | .one .fs _ => 50 + 1
  | .one _ _ => 1 + 1
  | .opn _ _ _ => 50 + (399 + 19) + 1 + 19 + 1

/-- `segCost (blkTSeg 0 b) + 1`. -/
def blkTCostL : Blk → ℕ
  | .one _ len => 3 + (14 + 36 * (len / 8 + 4)) + 1 + 1
  | .opn t row path =>
    12 + t * (3 + (14 + 36 * (row / 8 + 4)) + 1 + (12 + path * (3 + (14 + 36 * 12) + 1 + 7)) + 1 + 7) + 1

/-- `segOuts (blkTSeg 0 b)`. -/
def blkTOutsL : Blk → ℕ
  | .one _ len => 1 + (len / 8 + 4)
  | .opn t row path => t * (1 + (row / 8 + 4) + path * (1 + 12))

/-- `segSize (blkTSeg 0 b) + 1`. -/
def blkTSizeL : Blk → ℕ
  | .one _ _ => 3 + 50 + 1 + 1
  | .opn _ _ _ => 3 + 50 + 1 + (3 + 50 + 1 + 19) + 1 + 19 + 1

/-! ## All the static numbers at `P20`, in one kernel evaluation

`layout_P20`, `blocks_tally`, `blocks_sizes` and the chain's facts (`LvmXChainL`: `piSize_eq`,
`msgs_cap`, `msgs_ok`; `LvmXOut`: `blocks_lens`; `LvmXTop`: the segments' measures) all evaluate the schedule, the blocks, the tally or the FS messages at `pX`;
one decision evaluates each of them once (separately they cost 1–3 s of kernel time each). -/

/-! Proof help (GOLF-DEC3): the fifteen block sums and checks of `layout_all_P20` in one walk of the blocks with
`Nat.add` accumulators (`bW`), instead of fifteen `map`/`sum` walks (about 0.6 M kernel heartbeats each). -/

/-- Fifteen sums over the blocks in one walk (proof help). -/
private def bW (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : Blk → ℕ) :
    List Blk → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ
  | [], a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 =>
    [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
  | b :: bs, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 =>
    bW f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 bs (Nat.add a1 (f1 b)) (Nat.add a2 (f2 b))
      (Nat.add a3 (f3 b)) (Nat.add a4 (f4 b)) (Nat.add a5 (f5 b)) (Nat.add a6 (f6 b)) (Nat.add a7 (f7 b))
      (Nat.add a8 (f8 b)) (Nat.add a9 (f9 b)) (Nat.add a10 (f10 b)) (Nat.add a11 (f11 b)) (Nat.add a12 (f12 b))
      (Nat.add a13 (f13 b)) (Nat.add a14 (f14 b)) (Nat.add a15 (f15 b))

private theorem bW_eq (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : Blk → ℕ) : ∀ (bs : List Blk)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℕ),
    bW f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 bs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =
      [a1 + (bs.map f1).sum, a2 + (bs.map f2).sum, a3 + (bs.map f3).sum, a4 + (bs.map f4).sum,
        a5 + (bs.map f5).sum, a6 + (bs.map f6).sum, a7 + (bs.map f7).sum, a8 + (bs.map f8).sum,
        a9 + (bs.map f9).sum, a10 + (bs.map f10).sum, a11 + (bs.map f11).sum, a12 + (bs.map f12).sum,
        a13 + (bs.map f13).sum, a14 + (bs.map f14).sum, a15 + (bs.map f15).sum]
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp only [bW, List.map_nil, List.sum_nil, Nat.add_zero]
  | b :: bs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [bW, bW_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs, List.map_cons, List.sum_cons, Nat.add_eq, Nat.add_assoc]

/-- A check as a count of failures (proof help). -/
private theorem all_of_sum (p : Blk → Bool) : ∀ (bs : List Blk), (bs.map fun b => cond (p b) 0 1).sum = 0 →
    bs.all p = true
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.map_cons, List.sum_cons] at h
    cases hb : p b <;> rw [hb] at h
    · exact absurd h (by simp)
    · rw [List.all_cons, hb, Bool.true_and]; exact all_of_sum p bs (by simpa using h)

/-- The FS messages' length and their two checks as failure counts, in one walk (proof help): every message
within `queryCap`, and the first `k` lane-aligned and inside `π` of `pi` bytes. -/
private def mW (pi : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → List ℕ
  | [], _, n, b1, b2 => [n, b1, b2]
  | m :: l, k, n, b1, b2 => mW pi l (Nat.sub k 1) (Nat.add n 1)
      (Nat.add b1 (cond (32 + m.2 ≤ queryCap) 0 1))
      (Nat.add b2 (cond (Nat.beq k 0 || (m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ pi && 32 + m.2 ≤ queryCap)) 0 1))

private theorem mW_eq (pi : ℕ) : ∀ (l : List (ℕ × ℕ)) (k n b1 b2 : ℕ), mW pi l k n b1 b2 =
    [n + l.length, b1 + (l.map fun m => cond (32 + m.2 ≤ queryCap) 0 1).sum,
      b2 + ((l.take k).map fun m => cond (m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ pi && 32 + m.2 ≤ queryCap)
        0 1).sum]
  | [], _, _, _, _ => by simp [mW]
  | m :: l, 0, n, b1, b2 => by
    rw [mW, show Nat.sub 0 1 = 0 from rfl, mW_eq pi l]
    simp only [List.take_zero, List.map_nil, List.sum_nil, List.length_cons, List.map_cons, List.sum_cons,
      Nat.beq_refl, Bool.true_or, Bool.cond_true, Nat.add_eq, Nat.add_zero, List.cons.injEq, and_true]
    omega
  | m :: l, k + 1, n, b1, b2 => by
    rw [mW, show Nat.sub (k + 1) 1 = k from Nat.add_sub_cancel k 1, mW_eq pi l]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_cons,
      Nat.add_eq, List.cons.injEq, and_true]
    have : Nat.beq (k + 1) 0 = false := rfl
    rw [this, Bool.false_or]
    omega

private theorem all_of_sumP {α : Type} (p : α → Bool) : ∀ (l : List α), (l.map fun b => cond (p b) 0 1).sum = 0 →
    l.all p = true
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.map_cons, List.sum_cons] at h
    cases hb : p b <;> rw [hb] at h
    · exact absurd h (by simp)
    · rw [List.all_cons, hb, Bool.true_and]; exact all_of_sumP p bs (by simpa using h)

/-- `getD` past a prefix (proof help, as `LvmMPXLayout`'s). -/
private theorem getD_drop_le' {α : Type} (l : List α) (n i : ℕ) (d : α) (h : n ≤ i) :
    l.getD i d = (l.drop n).getD (i - n) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' h]

set_option maxRecDepth 100000 in
/-- The layout, the blocks' tallies and sizes, `|π|`, and the FS messages' facts at `P20` (lvm2 roll 11, `S2GM`, R11-X:
restated at M′'s schedule; there is no `openRec` phase: `nPre`, `alphaPos 0` and `capRecOff` are `C_main`'s
`nPreM`, `foldPosM 0 0` and the end of its cap, while `nChain`, `alpha1Pos`, `capRec1Off`, `f2Off` are the schedule
functions' values on `C_rec`'s absent levels; M′'s positions are `LvmMPXLayout`'s). -/
theorem layout_all_P20 :
    (nPre pX = 1206 ∧ nChain pX = 1212 ∧ alphaPos pX 0 = 1209 ∧ capRec1Off pX = 190000 ∧
      capRecOff pX = 14176 ∧ (fsMsgs pX).length = 1303 ∧
      (fsMsgs pX).getD 1211 (0, 0) = (190096, 48) ∧ alpha1Pos pX 0 = 1212 ∧ f2Off pX = 190144 ∧
      (fsMsgs pX).getD 1208 (0, 0) = (189952, 48)) ∧
    (1 + ((blocks pX).map Blk.count).sum = qS pX ∧
      47 + ((blocks pX).map Blk.trBytes).sum = (tally pX).trace ∧
      ((blocks pX).map fun b => match b with | .opn t _ _ => t | _ => 0).sum = (tally pX).nLeaf ∧
      ((blocks pX).map fun b => match b with | .opn t _ p => t * p | _ => 0).sum = (tally pX).nNode) ∧
    (6 + ((blocks pX).map Blk.lanes).sum = streamLanes pX ∧
      8 + ((blocks pX).map Blk.pBytes).sum = piSize pX ∧
      (blocks pX).all (fun b => match b with
        | .one _ len => len % 8 == 0 && 32 ≤ len | .opn _ row _ => row % 8 == 0) = true) ∧
    piSize pX = 380768 ∧
    (fsMsgs pX).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    ((fsMsgs pX).take (nChain pX - 1)).all (fun m =>
      m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ piSize pX && 32 + m.2 ≤ queryCap) = true ∧
    ((blocks pX).all blkLensOkL = true ∧ 8 + 8 * ((blocks pX).map blkPieceLenL).sum = piSize pX) ∧
    ((blocks pX).map blkPCostL).sum = 2479424 ∧ ((blocks pX).map blkTCostL).sum = 2880758 ∧
    ((blocks pX).map blkPOutsL).sum = 47595 ∧ ((blocks pX).map blkTOutsL).sum = 81326 ∧
    ((blocks pX).map blkPSizeL).sum = 67920 ∧ ((blocks pX).map blkTSizeL).sum = 72109 := by
  -- the block sums from one walk (`bW`), the rest as before; one kernel evaluation (GOLF-DEC3)
  have h : nPre pX = 1206 ∧ nChain pX = 1212 ∧ alphaPos pX 0 = 1209 ∧ (recL pX 0).fold = 0 ∧
      capRecOff pX = 14176 ∧ alpha1Pos pX 0 = 1212 ∧
      ((fsMsgs pX).drop 1208).take 4 = [(189952, 48), (190000, 48), (190048, 48), (190096, 48)] ∧
      qS pX = 3860 ∧ (tally pX).trace = 650655 ∧ (tally pX).nLeaf = 250 ∧ (tally pX).nNode = 2306 ∧
      streamLanes pX = 81332 ∧ piSize pX = 380768 ∧
      mW 380768 (fsMsgs pX) 1211 0 0 0 = [1303, 0, 0] ∧
      bW Blk.count Blk.trBytes (fun b => match b with | .opn t _ _ => t | _ => 0)
        (fun b => match b with | .opn t _ p => t * p | _ => 0) Blk.lanes Blk.pBytes
        (fun b => cond (match b with
          | .one _ len => len % 8 == 0 && 32 ≤ len | .opn _ row _ => row % 8 == 0) 0 1)
        (fun b => cond (blkLensOkL b) 0 1) blkPieceLenL blkPCostL blkTCostL blkPOutsL blkTOutsL blkPSizeL
        blkTSizeL (blocks pX) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 =
        [3859, 650608, 250, 2306, 81326, 380760, 0, 0, 47595, 2479424, 2880758, 47595, 81326, 67920, 72109] := by
    decide +kernel
  obtain ⟨h1, h2, h3, h4, h5, h6, hd, hq, htr, hl, hn, hT, hpi, hm, hw⟩ := h
  rw [mW_eq] at hm
  simp only [Nat.zero_add, List.cons.injEq, and_true] at hm
  obtain ⟨hlen, hc, hok⟩ := hm
  have hg : ∀ i < 4, (fsMsgs pX).getD (1208 + i) (0, 0) = (((fsMsgs pX).drop 1208).take 4).getD i (0, 0) := by
    intro i hi
    rw [getD_drop_le' _ 1208 _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  have g0 : (fsMsgs pX).getD 1208 (0, 0) = (189952, 48) := by have := hg 0 (by omega); rw [hd] at this; exact this
  have g3 : (fsMsgs pX).getD 1211 (0, 0) = (190096, 48) := by have := hg 3 (by omega); rw [hd] at this; exact this
  have hA : nPre pX = 1206 ∧ nChain pX = 1212 ∧ alphaPos pX 0 = 1209 ∧ capRec1Off pX = 190000 ∧
      capRecOff pX = 14176 ∧ (fsMsgs pX).length = 1303 ∧
      (fsMsgs pX).getD 1211 (0, 0) = (190096, 48) ∧ alpha1Pos pX 0 = 1212 ∧ f2Off pX = 190144 ∧
      (fsMsgs pX).getD 1208 (0, 0) = (189952, 48) := by
    refine ⟨h1, h2, h3, ?_, h5, hlen, g3, h6, ?_, g0⟩
    · rw [capRec1Off, h1, h4, show 1206 + 2 + 0 = 1208 from rfl, g0]; rfl
    · rw [f2Off, h2, show 1212 - 1 = 1211 from rfl, g3]; rfl
  have e : (1211 : ℕ) = nChain pX - 1 := by rw [h2]
  rw [← hpi, e] at hok
  rw [bW_eq] at hw
  simp only [Nat.zero_add, List.cons.injEq, and_true] at hw
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := hw
  refine ⟨hA, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, all_of_sum _ _ w7⟩, hpi, all_of_sumP _ _ hc, all_of_sumP _ _ hok,
    ⟨all_of_sum _ _ w8, ?_⟩,
    w10, w11, w12, w13, w14, w15⟩
  · rw [w1, hq]
  · rw [w2, htr]
  · rw [w3, hl]
  · rw [w4, hn]
  · rw [w5, hT]
  · rw [w6, hpi]
  · rw [w9, hpi]

/-- **The layout numbers at `P20`** (re-decided at every freeze; lvm2 roll 11, `S2GM`: no `openRec`, so these `C_rec`
functions take their values on absent levels; `C_main`'s opening is `LvmMPXLayout.layoutM_P20`). -/
theorem layout_P20 : nPre pX = 1206 ∧ nChain pX = 1212 ∧ alphaPos pX 0 = 1209 ∧
    capRec1Off pX = 190000 ∧ capRecOff pX = 14176 ∧ (fsMsgs pX).length = 1303 ∧
    (fsMsgs pX).getD 1211 (0, 0) = (190096, 48) ∧ alpha1Pos pX 0 = 1212 ∧ f2Off pX = 190144 ∧
    (fsMsgs pX).getD 1208 (0, 0) = (189952, 48) :=
  layout_all_P20.1

/-- **The blocks are `V_S`'s queries** (`LvmSchedule.tally`): `qS − 1` entries after `q₀`, the
trace bytes, the leaf and node counts. -/
theorem blocks_tally : 1 + ((blocks pX).map Blk.count).sum = qS pX ∧
    47 + ((blocks pX).map Blk.trBytes).sum = (tally pX).trace ∧
    ((blocks pX).map fun b => match b with | .opn t _ _ => t | _ => 0).sum = (tally pX).nLeaf ∧
    ((blocks pX).map fun b => match b with | .opn t _ p => t * p | _ => 0).sum = (tally pX).nNode :=
  layout_all_P20.2.1

end Lvm.X
