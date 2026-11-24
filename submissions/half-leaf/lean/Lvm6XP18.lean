-- lvm6 X5 (at `P17` since PORT17 X1): the trace-entry lengths from CD's plan and their kernel-checked facts (one evaluation), for `nodeOutIR`;
-- X6a (F-X5): the lengths as 21 blocks of runs (`blocksD`) and the compressed left segment `leftSegD`.
import Lvm6XLeft
import Lvm6QFormat
import Lvm6P17Memo

/-!
# `lensD`, `leafLsD` and the facts, at `P17` (PORT17 X1; the names keep `18` until C1's rename)

`lensD = ((planOf P17).drop 1).map len` (4,105 entries), `leafLsD = [368, 256]`; `factsD` (four `decide +kernel`s
over L1's plan memo `planP17`): the classifier is the plan's, every length is `≡ 0 mod 8` and `< 2^32`,
`6 + lanesOf lensD = 64,866`, and `lensD = 856 :: blkLens blocksD` (the seed's message, then 21 blocks of runs;
`blocksD` is `Lvm6XBlk.blkTabOf`'s output, `blkTabAt_P17`). **`leftSegD = leftSegB leafLsD 856 blocksD`**:
`segOut_leftSegD` (it denotes `leftSeg leafLsD lensD`), and by a kernel evaluation of the 21 blocks only
(`factsB`): `okX`, depth 2, cost 4,267,417, outputs 93,671, size 16,223, the proof's 28,803 words.
-/

namespace Lvm6.X

open RecursionFast Lvm Lvm.X

/-! ## The lengths (`P17`) -/

/-- **The query lengths of trace entries `1 … qS − 1` at `P17`** (CD's plan; entry 0 is `q₀`). -/
@[irreducible] def lensD : List ℕ := ((Lvm6.Q.planOf Lvm6.P17).drop 1).map Lvm6.Q.PE6.len

/-- **The leaf lengths** (`P17` and `P18`): level 0's 46-word rows, levels 1–4's 32-word rows. -/
def leafLsD : List ℕ := [368, 256]

/-- **`P17`'s lengths as blocks**: `(t, rs)` is `t` repetitions of the runs `rs`, a run `(c, len)` is `c` entries of
length `len` (`Lvm6XBlk.blkTabOf`'s output on `lensD.tail`, checked in `factsD`). -/
def blocksD : List (ℕ × List (ℕ × ℕ)) :=
  [(1, [(1, 4128), (1, 40), (23, 32), (1, 88), (16, 32), (1, 168), (1, 376), (5, 32), (1, 808)]),
    (11, [(15, 72), (12, 88), (1, 792)]),
    (1, [(15, 72), (12, 88), (6, 72), (1, 88), (10, 72), (1, 1064), (12, 40), (1, 440), (5, 32), (1, 808)]),
    (11, [(10, 72), (12, 88), (1, 792)]),
    (1, [(10, 72), (12, 88), (6, 72), (1, 88), (9, 72), (1, 1064), (17, 40), (13, 72), (1, 104), (19, 40), (20, 72),
      (1, 88), (21, 72), (1, 200), (17, 72), (1, 56), (1, 40), (1, 744), (1, 40), (4, 32), (1, 72), (1, 232), (1, 32),
      (1, 40), (2, 104), (1, 232), (1, 32), (1, 40), (4, 104), (1, 232), (1, 32), (1, 40), (6, 104), (1, 232), (1, 32),
      (1, 40), (8, 104), (1, 232), (1, 32), (1, 40), (10, 104), (1, 232), (2, 32), (1, 40), (32, 32)]),
    (6, [(1, 104), (1, 32)]),
    (1, [(1, 2176), (1, 40), (17, 32), (1, 56), (19, 32)]),
    (110, [(1, 368), (13, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 1120), (1, 40), (13, 32), (1, 56), (8, 32)]),
    (45, [(1, 256), (13, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 1120), (1, 40), (9, 32), (1, 56), (4, 32)]),
    (28, [(1, 256), (13, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 1120), (1, 40), (5, 32), (1, 56), (3, 32)]),
    (21, [(1, 256), (12, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 168), (2, 32)]),
    (18, [(1, 256), (11, 64)]),
    (1, [(2, 72)])]

/-- `EK6.leaf` as a `Bool` match (the kernel evaluates it faster than the derived `DecidableEq`). -/
def isLeafB : Lvm6.Q.EK6 → Bool
  | .leaf => true
  | _ => false

theorem decide_eq_leaf (k : Lvm6.Q.EK6) : decide (k = .leaf) = isLeafB k := by cases k <;> rfl

theorem decide_mem_leafLsD (n : ℕ) : decide (n ∈ leafLsD) = (n == 368 || n == 256) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
  simp only [leafLsD, List.mem_cons, List.not_mem_nil, or_false]

/-- The `P17` facts, one kernel evaluation over `planP17`: the classifier is the plan's (an entry has a leaf length iff it is a
leaf), every length is a multiple of 8 below `2^32`, the stream's lanes, the blocks. -/
theorem factsD :
    ((Lvm6.Q.planOf Lvm6.P17).all (fun e => decide (e.len ∈ leafLsD) == decide (e.k = .leaf)) &&
      lensD.all (fun len => len % 8 == 0 && decide (len < 2 ^ 32)) &&
      lanesOf lensD == 64860 && lensD == 856 :: blkLens blocksD) = true := by
  -- the classifier as `Bool` matches: about half the kernel time of the `decide`s' instances
  have hA : (fun e : Lvm6.Q.PE6 => decide (e.len ∈ leafLsD) == decide (e.k = .leaf)) =
      fun e => (e.len == 368 || e.len == 256) == isLeafB e.k := by
    funext e; rw [decide_eq_leaf, decide_mem_leafLsD]
  rw [hA]; unfold lensD; rw [Lvm6.planOf_P17_eq]
  -- four kernel evaluations (each under the per-unit budget) instead of one
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> decide +kernel

theorem leafLsD_spec : ∀ e ∈ Lvm6.Q.planOf Lvm6.P17, (e.len ∈ leafLsD ↔ e.k = .leaf) := by
  have h := factsD
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_decide] at h
  exact h.1.1.1

theorem lensOK : ∀ len ∈ lensD, len % 8 = 0 ∧ len < 2 ^ 32 := by
  have h := factsD
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.2

theorem lanesD : 6 + lanesOf lensD = 64866 := by
  have h := factsD
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.2]

theorem lensD_blocks : lensD = 856 :: blkLens blocksD := by
  have h := factsD
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-! ## The compressed left segment -/

/-- **The left child's segment at `P17`**, compressed. -/
def leftSegD : Seg := leftSegB leafLsD 856 blocksD

/-- **`leftSegD` denotes the unrolled `leftSeg`.** -/
theorem segOut_leftSegD (W : ℕ → Word) : segOut W false 0 leftSegD = segOut W false 0 (leftSeg leafLsD lensD) := by
  rw [leftSegD, segOut_leftSegB, ← lensD_blocks]

/-- The compressed segment's static facts, one kernel evaluation over the 21 blocks. -/
theorem factsB :
    (okX leftSegD && depthSeg leftSegD == 2 && segCost leftSegD == 4267417 && segOuts leftSegD == 93671 &&
      segSize leftSegD == 16223 && segLen false (pSegB leafLsD 856 blocksD) == 28803) = true := by
  decide +kernel

theorem okX_left : okX leftSegD = true := by
  have h := factsB; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1

theorem depth_left : depthSeg leftSegD = 2 := by
  have h := factsB; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.2

theorem segCost_left : segCost leftSegD = 4267417 := by
  have h := factsB; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.2

theorem segOuts_left : segOuts leftSegD = 93671 := by
  have h := factsB; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.2

theorem segSize_left : segSize leftSegD = 16223 := by
  have h := factsB; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

/-- The left child's proof at `P17` is 28,803 words: `segLen` of the unrolled proof segment. -/
theorem pLen : segLen false (pSeg6 leafLsD lensD) = 28803 := by
  have h := factsB
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.2, ← segOut_length (fun _ => 0) false _ 0, ← segOut_length (fun _ => 0) false _ 0, lensD_blocks]
  rw [pSegB, pSeg6, segOut, segOut, segOut_blksF _ (shift_pieceSeg _ leafLsD), pSegs6_eq]

end Lvm6.X
