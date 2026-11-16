-- New for lvm2 E2-FT (E2F-B): the PoW rows of the ground answers in looped auxiliary blocks. A run of answers
-- whose lanes step evenly and that share `g` becomes one block of `2^l` iterations, not `2^l` blocks of one each.
-- This cuts the `Φ_Q` cache's one-instance `K1` terms (E2F-LEAD's blob v2 decision).
import LvmE2QPow

/-!
# Looped PoW blocks (`pchunks`, `powBlksC`)

* **`PChunk`**: `2^l` answers at lanes `q0 + s·j` (`j < 2^l`), all with `g` bits. `PChunk.mem` lists them.
* **`pchunks as`**: the answer list `as` cut, in order, into runs. Each run is the longest power-of-two run
  (`chunkAt`, at most `2^10`) whose answers are exactly the list's next ones. **`pchunks_flat`**: the runs'
  answers, concatenated, are `as`.
* **`powBlkC bw c`**: `powRangeRows c.g` looped over the run. At iteration `j` the bit words are
  `bw + i + (64 − g)·j` and the operand is the stream cell `q0 + 2 + s·j`. **`powBlksC bw cs`**: the runs' blocks,
  their words consecutive from `bw` (`powWordsC cs` of them).
* **`powBlksC_mem`**: every answer of the runs is iteration `j` of one of the blocks.
* **`powBlkC_ok`**: if the block's rows hold at iteration `j` and the cell `q0 + s·j + 2` is lane 2 of `v`, then V's
  `powOKR g v` holds.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Typed

/-- A run of ground answers: `2^l` answers at lanes `q0 + s·j`, all with `g` bits. -/
structure PChunk where
  /-- The first answer's lane. -/
  q0 : ℕ
  /-- The lane step. -/
  s : ℕ
  /-- The PoW bits. -/
  g : ℕ
  /-- `log₂` of the answer count. -/
  l : ℕ
  deriving Inhabited

/-- The answers `(lane, g)` of a run. -/
def PChunk.mem (c : PChunk) : List (ℕ × ℕ) := (List.range (2 ^ c.l)).map fun j ↦ (c.q0 + c.s * j, c.g)

/-- The longest power-of-two run (at most `2^10`) starting at the answer `a`, followed by `rest`. Its step is the
next answer's lane minus `a`'s, and the check is that its answers are the list's first `2^l`. -/
def chunkAt (a : ℕ × ℕ) (rest : List (ℕ × ℕ)) : PChunk :=
  let s := (rest.headD a).1 - a.1
  let ok (l : ℕ) : Bool := (PChunk.mk a.1 s a.2 l).mem == (a :: rest).take (2 ^ l)
  ⟨a.1, s, a.2, ((List.range 11).filter ok).foldl max 0⟩

/-- **The answer list cut, in order, into runs.** -/
def pchunks : List (ℕ × ℕ) → List PChunk
  | [] => []
  | a :: rest => chunkAt a rest :: pchunks ((a :: rest).drop (2 ^ (chunkAt a rest).l))
termination_by as => as.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := Nat.one_le_two_pow (n := (chunkAt a rest).l)
  omega

theorem foldl_max_mem : ∀ (L : List ℕ) (i : ℕ), L.foldl max i = i ∨ L.foldl max i ∈ L
  | [], _ => Or.inl rfl
  | x :: xs, i => by
    rw [List.foldl_cons]
    rcases foldl_max_mem xs (max i x) with h | h
    · rw [h]
      rcases Nat.le_total i x with hx | hx
      · exact Or.inr (by rw [Nat.max_eq_right hx]; exact List.mem_cons_self)
      · exact Or.inl (Nat.max_eq_left hx)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A run's answers are the list's first `2^l`. -/
theorem chunkAt_mem (a : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
    (chunkAt a rest).mem = (a :: rest).take (2 ^ (chunkAt a rest).l) := by
  have key : ∀ (s : ℕ) (L : List ℕ), (∀ l ∈ L, (PChunk.mk a.1 s a.2 l).mem = (a :: rest).take (2 ^ l)) →
      (PChunk.mk a.1 s a.2 (L.foldl max 0)).mem = (a :: rest).take (2 ^ (L.foldl max 0)) := by
    intro s L hL
    rcases foldl_max_mem L 0 with h | h
    · rw [h]
      simp only [PChunk.mem, pow_zero, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero]
      rfl
    · exact hL _ h
  unfold chunkAt
  exact key _ _ fun l hl ↦ beq_iff_eq.mp (List.mem_filter.mp hl).2

/-- **The runs' answers are the list.** -/
theorem pchunks_flat : ∀ as : List (ℕ × ℕ), (pchunks as).flatMap PChunk.mem = as
  | [] => by rw [pchunks]; rfl
  | a :: rest => by
    rw [pchunks, List.flatMap_cons, chunkAt_mem, pchunks_flat, List.take_append_drop]
termination_by as => as.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := Nat.one_le_two_pow (n := (chunkAt a rest).l)
  omega

/-- **The looped PoW block of a run**: its bits are the free words `bw + i + (64 − g)·j`. -/
def powBlkC (bw : ℕ) (c : PChunk) : ABlk :=
  ⟨c.l, powRangeRows c.g (fun i ↦ .word (bw + i) (64 - c.g)) (.cell ⟨.K, c.q0 + 2, [c.s]⟩)⟩

/-- **The PoW blocks of the runs**, bit words consecutive from `bw`. -/
def powBlksC : ℕ → List PChunk → List ABlk
  | _, [] => []
  | bw, c :: cs => powBlkC bw c :: powBlksC (bw + 2 ^ c.l * (64 - c.g)) cs

/-- The bit words of the runs. -/
def powWordsC (cs : List PChunk) : ℕ := (cs.map fun c ↦ 2 ^ c.l * (64 - c.g)).sum

/-- **Every answer of the runs is an iteration of one of their blocks.** -/
theorem powBlksC_mem : ∀ (bw : ℕ) (cs : List PChunk) {a : ℕ × ℕ}, a ∈ cs.flatMap PChunk.mem →
    ∃ bw' c j, powBlkC bw' c ∈ powBlksC bw cs ∧ j < 2 ^ c.l ∧ a = (c.q0 + c.s * j, c.g)
  | _, [], _, h => absurd h List.not_mem_nil
  | bw, c :: cs, a, h => by
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      exact ⟨bw, c, j, List.mem_cons_self, List.mem_range.mp hj, rfl⟩
    · obtain ⟨b, c', j, hb, hj, e⟩ := powBlksC_mem (bw + 2 ^ c.l * (64 - c.g)) cs h
      exact ⟨b, c', j, List.mem_cons_of_mem _ hb, hj, e⟩

/-- **A looped PoW block gives V's check at each iteration.** If the block's rows hold at iteration `j` and the `K`
cell `q0 + s·j + 2` of the memory read off the words is lane 2 of the answer `v`, then `powOKR g v`. -/
theorem powBlkC_ok (lay : Lay) (z : ℕ → FK) {bw j : ℕ} {c : PChunk} (hg : c.g ≤ 64) {v : FE}
    (hv : (memOf lay z).k (c.q0 + c.s * j + 2) = v.c₂) (h : ∀ r ∈ (powBlkC bw c).rows, ARowHolds lay z j r) :
    DM.powOKR c.g v = true := by
  have hw : FE.ofK (aopVal lay z j (.cell ⟨.K, c.q0 + 2, [c.s]⟩)).c₀ = aopVal lay z j (.cell ⟨.K, c.q0 + 2, [c.s]⟩) :=
    rfl
  have := powRange_sem lay z j c.g hg (fun i ↦ .word (bw + i) (64 - c.g)) (.cell ⟨.K, c.q0 + 2, [c.s]⟩)
    (fun i ↦ ⟨bw + i, 64 - c.g, rfl⟩) hw h
  have he : Addr.at ⟨.K, c.q0 + 2, [c.s]⟩ [j] = c.q0 + c.s * j + 2 := by
    simp only [Addr.at, Lvm.Loop.dot]
    omega
  simp only [aopVal, he] at this
  apply powOK_of_range hg
  rw [← hv]
  exact this

end Lvm.Q2
