-- lvm6 X5: `P18`'s trace-entry lengths from CD's plan and their kernel-checked facts (one evaluation), for `nodeOutIR`;
-- X6a (F-X5): the lengths as 21 blocks of runs (`blocks18`) and the compressed left segment `leftSeg18`.
import Lvm6XLeft
import Lvm6QFormat

/-!
# `lens18`, `leafLs18` and the `P18` facts

`lens18 = ((planOf P18).drop 1).map len` (4,348 entries), `leafLs18 = [368, 256]`; `facts18` (one `decide +kernel`):
the classifier is the plan's, every length is `≡ 0 mod 8` and `< 2^32`, `6 + lanesOf lens18 = 68,019`, and
`lens18 = 856 :: blkLens blocks18` (the seed's message, then 21 blocks of runs).
**`leftSeg18 = leftSegB leafLs18 856 blocks18`** (F-X5: `rep`s over the runs and blocks instead of one unit per entry):
`segOut_leftSeg18` (it denotes `leftSeg leafLs18 lens18`), and by a kernel evaluation of the 21 blocks only
(`facts18B`): `okX`, depth 2, cost 4,484,509, outputs 97,790, size 16,223 (was 1,525,793 unrolled), the proof's
29,769 words.
-/

namespace Lvm6.X

open RecursionFast Lvm Lvm.X

/-! ## `P18`'s lengths -/

/-- **The query lengths of trace entries `1 … qS − 1` at `P18`** (CD's plan; entry 0 is `q₀`). -/
@[irreducible] def lens18 : List ℕ := ((Lvm6.Q.planOf Lvm6.P18).drop 1).map Lvm6.Q.PE6.len

/-- **The leaf lengths at `P18`**: level 0's 46-word rows, levels 1–4's 32-word rows. -/
def leafLs18 : List ℕ := [368, 256]

/-- **`P18`'s lengths as blocks**: `(t, rs)` is `t` repetitions of the runs `rs`, a run `(c, len)` is `c` entries of
length `len` (computed from `lens18` by a scratch run-length pass, checked in `facts18`). -/
def blocks18 : List (ℕ × List (ℕ × ℕ)) :=
  [(1, [(1, 4128), (1, 40), (24, 32), (1, 88), (17, 32), (1, 168), (1, 376), (5, 32), (1, 808)]),
    (11, [(16, 72), (12, 88), (1, 792)]),
    (1, [(16, 72), (12, 88), (6, 72), (1, 88), (10, 72), (1, 1064), (12, 40), (1, 440), (5, 32), (1, 808)]),
    (11, [(10, 72), (12, 88), (1, 792)]),
    (1, [(10, 72), (12, 88), (6, 72), (1, 88), (9, 72), (1, 1064), (17, 40), (13, 72), (1, 104), (19, 40), (20, 72), (1, 88), (21, 72), (1, 200), (18, 72), (1, 56), (1, 40), (1, 744), (1, 40), (4, 32), (1, 72), (1, 232), (1, 32), (1, 40), (2, 104), (1, 232), (1, 32), (1, 40), (4, 104), (1, 232), (1, 32), (1, 40), (6, 104), (1, 232), (1, 32), (1, 40), (8, 104), (1, 232), (1, 32), (1, 40), (10, 104), (1, 232), (2, 32), (1, 40), (32, 32)]),
    (6, [(1, 104), (1, 32)]),
    (1, [(1, 2176), (1, 40), (18, 32), (1, 56), (19, 32)]),
    (110, [(1, 368), (14, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 1120), (1, 40), (14, 32), (1, 56), (8, 32)]),
    (45, [(1, 256), (14, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 1120), (1, 40), (10, 32), (1, 56), (5, 32)]),
    (28, [(1, 256), (14, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 1120), (1, 40), (6, 32), (1, 56), (3, 32)]),
    (21, [(1, 256), (13, 64)]),
    (4, [(1, 104), (1, 32)]),
    (1, [(1, 232), (2, 32)]),
    (18, [(1, 256), (12, 64)]),
    (1, [(3, 72)])]

/-- `EK6.leaf` as a `Bool` match (the kernel evaluates it faster than the derived `DecidableEq`). -/
def isLeafB : Lvm6.Q.EK6 → Bool
  | .leaf => true
  | _ => false

theorem decide_eq_leaf (k : Lvm6.Q.EK6) : decide (k = .leaf) = isLeafB k := by cases k <;> rfl

theorem decide_mem_leafLs18 (n : ℕ) : decide (n ∈ leafLs18) = (n == 368 || n == 256) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
  simp only [leafLs18, List.mem_cons, List.not_mem_nil, or_false]

/-- The `P18` facts, one kernel evaluation: the classifier is the plan's (an entry has a leaf length iff it is a
leaf), every length is a multiple of 8 below `2^32`, the stream's lanes, the blocks. -/
theorem facts18 :
    ((Lvm6.Q.planOf Lvm6.P18).all (fun e => decide (e.len ∈ leafLs18) == decide (e.k = .leaf)) &&
      lens18.all (fun len => len % 8 == 0 && decide (len < 2 ^ 32)) &&
      lanesOf lens18 == 68013 && lens18 == 856 :: blkLens blocks18) = true := by
  -- the classifier as `Bool` matches: about half the kernel time of the `decide`s' instances
  have hA : (fun e : Lvm6.Q.PE6 => decide (e.len ∈ leafLs18) == decide (e.k = .leaf)) =
      fun e => (e.len == 368 || e.len == 256) == isLeafB e.k := by
    funext e; rw [decide_eq_leaf, decide_mem_leafLs18]
  rw [hA]; unfold lens18; decide +kernel

theorem leafLs18_spec : ∀ e ∈ Lvm6.Q.planOf Lvm6.P18, (e.len ∈ leafLs18 ↔ e.k = .leaf) := by
  have h := facts18
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_decide] at h
  exact h.1.1.1

theorem lensOK18 : ∀ len ∈ lens18, len % 8 = 0 ∧ len < 2 ^ 32 := by
  have h := facts18
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.2

theorem lanes18 : 6 + lanesOf lens18 = 68019 := by
  have h := facts18
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.2]

theorem lens18_blocks : lens18 = 856 :: blkLens blocks18 := by
  have h := facts18
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-! ## The compressed left segment -/

/-- **The left child's segment at `P18`**, compressed. -/
def leftSeg18 : Seg := leftSegB leafLs18 856 blocks18

/-- **`leftSeg18` denotes the unrolled `leftSeg`.** -/
theorem segOut_leftSeg18 (W : ℕ → Word) : segOut W false 0 leftSeg18 = segOut W false 0 (leftSeg leafLs18 lens18) := by
  rw [leftSeg18, segOut_leftSegB, ← lens18_blocks]

/-- The compressed segment's static facts, one kernel evaluation over the 21 blocks. -/
theorem facts18B :
    (okX leftSeg18 && depthSeg leftSeg18 == 2 && segCost leftSeg18 == 4484509 && segOuts leftSeg18 == 97790 &&
      segSize leftSeg18 == 16223 && segLen false (pSegB leafLs18 856 blocks18) == 29769) = true := by
  decide +kernel

theorem okX_left18 : okX leftSeg18 = true := by
  have h := facts18B; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1

theorem depth_left18 : depthSeg leftSeg18 = 2 := by
  have h := facts18B; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.2

theorem segCost_left18 : segCost leftSeg18 = 4484509 := by
  have h := facts18B; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.2

theorem segOuts_left18 : segOuts leftSeg18 = 97790 := by
  have h := facts18B; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.2

theorem segSize_left18 : segSize leftSeg18 = 16223 := by
  have h := facts18B; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

/-- The left child's proof at `P18` is 29,769 words: `segLen` of the unrolled proof segment. -/
theorem pLen18 : segLen false (pSeg6 leafLs18 lens18) = 29769 := by
  have h := facts18B
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.2, ← segOut_length (fun _ => 0) false _ 0, ← segOut_length (fun _ => 0) false _ 0, lens18_blocks]
  rw [pSegB, pSeg6, segOut, segOut, segOut_blksF _ (shift_pieceSeg _ leafLs18), pSegs6_eq]

end Lvm6.X
