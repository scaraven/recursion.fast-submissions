-- lvm6 X3 (extractor): the left child's output from the `STREAM` window (FORMAT6 v2.5.2 §T: slot 33, stride 1,
-- `tB = 0`, `sB = 2^18`). New; the output segments and their compiled code are season 1's (`LvmXOutSeg`: `Seg`,
-- `segIR`, `segIR_sem`), the segments are generic in the trace's query lengths.
import Lvm6XChild
import LvmXOutSeg

/-!
# The left child's signed file

The left child is `⟨reassemble6 leafLs tr', tr', σ'⟩` with `tr' = readTrace6 lens (W (tB + ·))` and `σ' = sigOf W sB`
(`leftOf6`). Its words are one segment over the stream lanes (season 1's `Seg`), then `σ'`'s 597 words:

* **`trSeg6 lens`**: the trace: its count, `q₀`'s entry (`7`, lane 1 shifted, lanes 2–5), then each entry's length
  (static) and its query's and answer's lanes (`trSegs6`); **`logWords_readTrace6`**.
* **`pSeg6 leafLs lens`**: the proof: the seed's message (`HDR`, the seed's query after its 32-byte state), then per
  entry by its length a node's sibling (`sibc`: the half that is not the previous answer), a leaf's lanes, or a
  message's lanes after the state (`pieceSeg`); **`reassemble6_words`**.
* **`leftSeg`** (the proof's byte length, the proof, the trace), **`segOut_leftSeg`**.
* **Compressed** (X6a, F-X5: unrolled per entry, `leftSeg` at `P18` is 1,525,793 statements, over `progCap`):
  **`leftSegB leafLs len0 bs`**, the entries as blocks `(t, rs)` of runs `(c, len)`, one `rep` per run and per block
  (season 1's `Seg.rep`, as its `blkTSeg`/`blkPSeg`); **`segOut_leftSegB`**: it denotes `leftSeg` of the unrolled
  lengths (`segOut_blksF`, for units whose words shift with the base: `entSeg`, `pieceSeg`).
* **`leftOutIR sg tB sB`**: a segment `sg` from base `tB` (season 1's contiguous `apC`), then `outCpIR sB 597`;
  **`leftOutIR_sem`**: for `sg` denoting `leftSeg leafLs lens` (and `okX`, depth `≤ 9`), it appends
  `signedWords (leftOf6 lens leafLs (rd M) tB sB)`; **`cost_leftOutIR`** (exact: `4795 + segCost sg`; `okX` admits
  `rep`, `cost_segIR_okX` is exact for it).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X

/-! ## Segments with exact cost -/

/-- The segments the left child uses: no `kite` or `shw`; counts below `2^32`; a sibling after an answer. -/
def okX : Seg → Bool
  | .nil | .wd _ | .sh8 _ => true
  | .cat x y => okX x && okX y
  | .cp _ n => decide (n < 2 ^ 32)
  | .rep c _ x => decide (c < 2 ^ 32) && okX x
  | .sibc o => decide (4 ≤ o)
  | _ => false

theorem okSeg_of_okX : ∀ (s : Seg), okX s = true → okSeg s = true
  | .nil, _ => rfl
  | .cat x y, h => by
    simp only [okX, Bool.and_eq_true] at h
    simp only [okSeg, okSeg_of_okX x h.1, okSeg_of_okX y h.2, Bool.and_self]
  | .wd _, _ => rfl
  | .cp _ _, h => h
  | .rep _ _ x, h => by
    simp only [okX, Bool.and_eq_true] at h
    simp only [okSeg, h.1, okSeg_of_okX x h.2, Bool.and_self]
  | .shw _, h => by simp [okX] at h
  | .sh8 _, _ => rfl
  | .kite _ _, h => by simp [okX] at h
  | .sibc _, h => h

/-- **The exact cost** of such a segment is `segCost`. -/
theorem cost_segIR_okX (ap : AP) (t : ℕ) : ∀ (s : Seg) (d : ℕ), okX s = true → cost (segIR ap d s) t = segCost s
  | .nil, _, _ => by simp [segIR, cost, segCost, blkSteps]
  | .cat x y, d, h => by
    simp only [okX, Bool.and_eq_true] at h
    simp only [segIR, cost, segCost, cost_segIR_okX ap t x d h.1, cost_segIR_okX ap t y d h.2]
  | .wd _, _, _ => by simp [segIR, cost, segCost, blkSteps]
  | .cp _ n, _, h => by
    simp only [okX, decide_eq_true_eq] at h
    simp [segIR, cpIR, ldw, ldPs, cost, segCost, blkSteps, toNat_toWord (show n < 2 ^ 64 by omega)] <;> omega
  | .rep c _ x, d, h => by
    simp only [okX, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [segIR, cost, segCost, blkSteps, List.length_cons, List.length_nil, cost_segIR_okX ap t x (d + 1) h.2,
      toNat_toWord (show c < 2 ^ 64 by omega)]
    norm_num
    ring
  | .shw _, _, h => by simp [okX] at h
  | .sh8 _, _, _ => by simp [segIR, ldw, ldPs, cost, segCost, blkSteps]
  | .kite _ _, _, h => by simp [okX] at h
  | .sibc _, _, _ => by simp [segIR, sibcIR, cmpW, cpIR, ldw, ldPs, cost, segCost, blkSteps, toNat_toWord]

/-! ## The segments -/

/-- An entry's trace words at lane `u`: its length, its query's and answer's lanes. -/
def entSeg (u len : ℕ) : Seg := .cat (.wd (toWord len)) (.cp (u + 1) (len / 8 + 4))

/-- The trace words of the entries from lane `u`. -/
def trSegs6 : ℕ → List ℕ → Seg
  | _, [] => .nil
  | u, len :: r => .cat (entSeg u len) (trSegs6 (u + 5 + len / 8) r)

/-- **The trace's segment**: the count, `q₀`'s entry, the entries from lane 6. -/
def trSeg6 (lens : List ℕ) : Seg :=
  .cat (.wd (toWord (lens.length + 1))) (.cat (.wd (toWord 7)) (.cat (.sh8 1) (.cat (.cp 2 4) (trSegs6 6 lens))))

/-- An entry's proof words at lane `u`, by its length: a node's sibling, a leaf's lanes, a message's lanes. -/
def pieceSeg (leafLs : List ℕ) (u len : ℕ) : Seg :=
  if len = 64 then .sibc u else if len ∈ leafLs then .cp (u + 1) (len / 8) else .cp (u + 5) ((len - 32) / 8)

/-- The proof words of the entries from lane `u`. -/
def pSegs6 (leafLs : List ℕ) : ℕ → List ℕ → Seg
  | _, [] => .nil
  | u, len :: r => .cat (pieceSeg leafLs u len) (pSegs6 leafLs (u + 5 + len / 8) r)

/-- **The proof's segment**: the seed's message (lane 6's entry after its state), then the later entries. -/
def pSeg6 (leafLs : List ℕ) : List ℕ → Seg
  | [] => .nil
  | len :: r => .cat (.cp (6 + 5) ((len - 32) / 8)) (pSegs6 leafLs (6 + 5 + len / 8) r)

/-- **The left child's segment**: the proof's byte length, the proof, the trace. -/
def leftSeg (leafLs lens : List ℕ) : Seg :=
  .cat (.wd (toWord (8 * segLen false (pSeg6 leafLs lens)))) (.cat (pSeg6 leafLs lens) (trSeg6 lens))

/-! ## Their words -/

section Words

variable (W : ℕ → Word)

theorem segOut_cp0 (o n : ℕ) : segOut W false 0 (.cp o n) = wsAt W o n := by
  simp only [segOut, wsAt, Nat.zero_add]

theorem segOut_cat (x y : Seg) : segOut W false 0 (.cat x y) = segOut W false 0 x ++ segOut W false 0 y := rfl

theorem trW6 : ∀ (u : ℕ) (r : List ℕ), (∀ len ∈ r, len % 8 = 0) →
    ((walk u r).map fun x => entAt W x.1 x.2).flatMap
        (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) = segOut W false 0 (trSegs6 u r)
  | _, [], _ => rfl
  | u, len :: r, h8 => by
    simp only [walk, List.map_cons, List.flatMap_cons]
    rw [entryWords_entAt W u len (h8 len (by simp)), trW6 _ r (fun l hl => h8 l (List.mem_cons_of_mem _ hl))]
    simp only [trSegs6, entSeg, segOut, entW, wsAt, Nat.zero_add, List.cons_append, List.nil_append,
      List.append_assoc]

/-- **The trace's words.** -/
theorem logWords_readTrace6 (lens : List ℕ) (h8 : ∀ len ∈ lens, len % 8 = 0) :
    logWords (readTrace6 lens W) = segOut W false 0 (trSeg6 lens) := by
  rw [logWords, readTrace6, List.flatMap_cons, entryWords_q0, trW6 W 6 lens h8]
  simp only [trSeg6, segOut, List.length_cons, List.length_map, length_walk, wsAt, Nat.zero_add,
    List.cons_append, List.nil_append]

/-- One entry's contribution, after the previous entry's answer (lanes `u − 4 … u − 1`). -/
theorem piece6_entAt (leafLs : List ℕ) (u len : ℕ) (h8 : len % 8 = 0) :
    piece6 leafLs (digW (wsAt W (u - 4) 4)) (entAt W u len) =
      wordsBytes (segOut W false 0 (pieceSeg leafLs u len)) := by
  have hq : (entAt W u len).1.data.toList = wordsBytes (wsAt W (u + 1) (len / 8)) := rfl
  have hl : (wordsBytes (wsAt W (u + 1) (len / 8))).length = len := by
    rw [wordsBytes_length, length_wsAt]; omega
  rw [piece6, hq, hl, pieceSeg]
  by_cases h64 : len = 64
  · subst h64
    have e8 : (64 : ℕ) / 8 = 8 := rfl
    simp only [e8, ↓reduceIte]
    have t1 : (wordsBytes (wsAt W (u + 1) 8)).take 32 = wordsBytes (wsAt W (u + 1) 4) := by
      rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_take, wsAt_take _ _ _ _ (by norm_num)]
    have t2 : (wordsBytes (wsAt W (u + 1) 8)).drop 32 = wordsBytes (wsAt W (u + 5) 4) := by
      rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wsAt_drop, show u + 1 + 4 = u + 5 by omega]
    have t3 : (digW (wsAt W (u - 4) 4)).toList = wordsBytes (wsAt W (u - 4) 4) := digW_toList (length_wsAt _ _ _)
    have hsib : segOut W false 0 (.sibc u) =
        if wsAt W (u + 1) 4 = wsAt W (u - 4) 4 then wsAt W (u + 5) 4 else wsAt W (u + 1) 4 := by
      simp only [segOut, wsAt, Nat.zero_add]
      split_ifs with h1 <;> simp only [h1, ↓reduceIte]
    rw [t1, t2, t3, hsib]
    by_cases he : wsAt W (u + 1) 4 = wsAt W (u - 4) 4
    · rw [if_pos (congrArg wordsBytes he), if_pos he]
    · rw [if_neg (fun e => he (wordsBytes_inj e)), if_neg he]
  · simp only [h64, ↓reduceIte]
    by_cases hL : len ∈ leafLs
    · simp only [hL, ↓reduceIte, segOut_cp0]
    · simp only [hL, ↓reduceIte, segOut_cp0]
      rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wsAt_drop]
      congr 2 <;> omega

theorem pieces6_walk (leafLs : List ℕ) : ∀ (u : ℕ) (r : List ℕ), 4 ≤ u → (∀ len ∈ r, len % 8 = 0) →
    pieces6 leafLs (digW (wsAt W (u - 4) 4)) ((walk u r).map fun x => entAt W x.1 x.2) =
      wordsBytes (segOut W false 0 (pSegs6 leafLs u r))
  | _, [], _, _ => rfl
  | u, len :: r, hu, h8 => by
    have hn : (entAt W u len).2 = digW (wsAt W (u + 5 + len / 8 - 4) 4) := by
      rw [show u + 5 + len / 8 - 4 = u + 1 + len / 8 by omega]; rfl
    simp only [walk, List.map_cons]
    rw [pieces6, hn, pieces6_walk leafLs _ r (by omega) (fun l hl => h8 l (List.mem_cons_of_mem _ hl)),
      piece6_entAt W leafLs u len (h8 len (by simp)), pSegs6, segOut_cat, wordsBytes_append]

/-- **The proof's words**: the reassembled proof is the proof segment's words. -/
theorem reassemble6_words (leafLs lens : List ℕ) (h8 : ∀ len ∈ lens, len % 8 = 0) :
    (reassemble6 leafLs (readTrace6 lens W)).data.toList = wordsBytes (segOut W false 0 (pSeg6 leafLs lens)) := by
  cases lens with
  | nil => rfl
  | cons len0 r =>
    show (bArr ((entAt W 6 len0).1.data.toList.drop 32 ++ pieces6 leafLs (entAt W 6 len0).2
        ((walk (6 + 5 + len0 / 8) r).map fun x => entAt W x.1 x.2))).data.toList = _
    have hs : (entAt W 6 len0).1.data.toList.drop 32 = wordsBytes (wsAt W (6 + 5) ((len0 - 32) / 8)) := by
      rw [show (entAt W 6 len0).1.data.toList = wordsBytes (wsAt W (6 + 1) (len0 / 8)) from rfl,
        show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wsAt_drop]
      congr 2 <;> omega
    have hp : pieces6 leafLs (entAt W 6 len0).2 ((walk (6 + 5 + len0 / 8) r).map fun x => entAt W x.1 x.2) =
        wordsBytes (segOut W false 0 (pSegs6 leafLs (6 + 5 + len0 / 8) r)) := by
      rw [← pieces6_walk W leafLs _ r (by omega) (fun l hl => h8 l (List.mem_cons_of_mem _ hl)),
        show 6 + 5 + len0 / 8 - 4 = 6 + 1 + len0 / 8 by omega]
      rfl
    rw [bArr_data, hs, hp, pSeg6, segOut_cat, segOut_cp0, wordsBytes_append]

/-- **The left child's words** from the segment (the proof's length, the proof, the trace). -/
theorem segOut_leftSeg (leafLs lens : List ℕ) (h8 : ∀ len ∈ lens, len % 8 = 0) :
    segOut W false 0 (leftSeg leafLs lens) =
      bytesWords (reassemble6 leafLs (readTrace6 lens W)).data.toList ++ logWords (readTrace6 lens W) := by
  rw [logWords_readTrace6 W lens h8, bytesWords, reassemble6_words W leafLs lens h8, packBytes_wordsBytes,
    wordsBytes_length, segOut_length]
  simp only [leftSeg, segOut, List.cons_append, List.nil_append]

end Words

/-- The trace reads lanes below `6 + lanesOf lens` only. -/
theorem readTrace6_congr {W W' : ℕ → Word} (lens : List ℕ) (h : ∀ v < 6 + lanesOf lens, W v = W' v) :
    readTrace6 lens W = readTrace6 lens W' := by
  have hq : q0Ent W = q0Ent W' := by
    have e1 : W 1 = W' 1 := h 1 (by omega)
    have e2 : wsAt W 2 4 = wsAt W' 2 4 := List.map_congr_left fun j hj => h _ (by simp at hj; omega)
    simp only [q0Ent, e1, e2]
  rw [readTrace6, readTrace6, hq]
  congr 1
  exact List.map_congr_left fun x hx => entAt_congr fun v hv => h v (by have := walk_lt 6 lens x hx; omega)

/-! ## Compressed segments (F-X5): runs of equal lengths and repeated patterns as `rep`s

A **run** `(c, len)` is `c` entries of length `len`; a **block** `(t, rs)` is `t` repetitions of the runs `rs`.
`blksF f u bs` emits, from lane `u`, a unit `f v len` per entry at its lane `v` (`entSeg` for the trace,
`pieceSeg` for the proof), as a `rep` per run and a `rep` per block (a count of `1` emits the body once, `rep1`).
**`segOut_blksF`**: it denotes the unrolled `segsF f u (blkLens bs)`, for a unit `f` whose words shift with the base
(`Shift f`). -/

/-- The unrolled units of the entries from lane `u`. -/
def segsF (f : ℕ → ℕ → Seg) : ℕ → List ℕ → Seg
  | _, [] => .nil
  | u, len :: r => .cat (f u len) (segsF f (u + 5 + len / 8) r)

theorem trSegs6_eq : ∀ (u : ℕ) (r : List ℕ), trSegs6 u r = segsF entSeg u r
  | _, [] => rfl
  | u, len :: r => by rw [trSegs6, segsF, trSegs6_eq _ r]

theorem pSegs6_eq (leafLs : List ℕ) : ∀ (u : ℕ) (r : List ℕ), pSegs6 leafLs u r = segsF (pieceSeg leafLs) u r
  | _, [] => rfl
  | u, len :: r => by rw [pSegs6, segsF, pSegs6_eq leafLs _ r]

/-- `x` `c` times at stride `s`; once without a loop. -/
def rep1 (c s : ℕ) (x : Seg) : Seg := if c = 1 then x else .rep c s x

/-- The entries of the runs `rs`. -/
def runLens (rs : List (ℕ × ℕ)) : List ℕ := rs.flatMap fun r => List.replicate r.1 r.2

/-- The runs from lane `u`, one `rep` each. -/
def runsF (f : ℕ → ℕ → Seg) : ℕ → List (ℕ × ℕ) → Seg
  | _, [] => .nil
  | u, r :: rs => .cat (rep1 r.1 (5 + r.2 / 8) (f u r.2)) (runsF f (u + r.1 * (5 + r.2 / 8)) rs)

/-- The entries of the blocks `bs`. -/
def blkLens (bs : List (ℕ × List (ℕ × ℕ))) : List ℕ :=
  bs.flatMap fun b => (List.replicate b.1 (runLens b.2)).flatten

/-- **The blocks from lane `u`**, one `rep` each over its runs. -/
def blksF (f : ℕ → ℕ → Seg) : ℕ → List (ℕ × List (ℕ × ℕ)) → Seg
  | _, [] => .nil
  | u, b :: bs => .cat (rep1 b.1 (lanesOf (runLens b.2)) (runsF f u b.2))
      (blksF f (u + b.1 * lanesOf (runLens b.2)) bs)

theorem lanesOf_append (l₁ l₂ : List ℕ) : lanesOf (l₁ ++ l₂) = lanesOf l₁ + lanesOf l₂ := by
  simp only [lanesOf, List.map_append, List.sum_append]

theorem lanesOf_replicate (c len : ℕ) : lanesOf (List.replicate c len) = c * (5 + len / 8) := by
  simp only [lanesOf, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem lanesOf_flatten_replicate (L : List ℕ) : ∀ t, lanesOf (List.replicate t L).flatten = t * lanesOf L
  | 0 => by simp [lanesOf]
  | t + 1 => by rw [List.replicate_succ, List.flatten_cons, lanesOf_append, lanesOf_flatten_replicate L t]; ring

section Comp

variable (W : ℕ → Word)

/-- A unit whose words shift with the base. -/
def Shift (f : ℕ → ℕ → Seg) : Prop := ∀ b u len, segOut W false b (f u len) = segOut W false 0 (f (b + u) len)

theorem shift_entSeg : Shift W entSeg := fun b u len => by
  simp only [entSeg, segOut, Nat.zero_add, List.cons_append, List.nil_append, List.cons.injEq, true_and]
  exact List.map_congr_left fun j _ => by rw [Nat.add_assoc b u 1]

theorem shift_pieceSeg (leafLs : List ℕ) : Shift W (pieceSeg leafLs) := fun b u len => by
  unfold pieceSeg
  split_ifs
  · simp only [segOut, Nat.zero_add, Nat.add_assoc]
  · simp only [segOut, Nat.zero_add, Nat.add_assoc]
  · simp only [segOut, Nat.zero_add, Nat.add_assoc]

theorem segOut_rep_succ (b c s : ℕ) (x : Seg) :
    segOut W false b (.rep (c + 1) s x) = segOut W false b x ++ segOut W false (b + s) (.rep c s x) := by
  simp only [segOut]
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.mul_zero, Nat.add_zero]
  congr 1
  exact List.flatMap_congr fun j _ => by congr 1; simp only [Nat.succ_eq_add_one]; ring

theorem segOut_rep1 (b c s : ℕ) (x : Seg) : segOut W false b (rep1 c s x) = segOut W false b (.rep c s x) := by
  unfold rep1
  split_ifs with h
  · subst h; rw [segOut_rep_succ]; simp [segOut]
  · rfl

theorem segOut_segsF_append (f : ℕ → ℕ → Seg) : ∀ (u : ℕ) (l₁ l₂ : List ℕ),
    segOut W false 0 (segsF f u (l₁ ++ l₂)) =
      segOut W false 0 (segsF f u l₁) ++ segOut W false 0 (segsF f (u + lanesOf l₁) l₂)
  | u, [], l₂ => by simp [segsF, segOut, lanesOf]
  | u, len :: r, l₂ => by
    rw [List.cons_append, segsF, segsF, segOut, segOut, segOut_segsF_append f _ r l₂, List.append_assoc]
    simp only [lanesOf, List.map_cons, List.sum_cons]
    rw [show u + 5 + len / 8 + (List.map (fun len => 5 + len / 8) r).sum =
      u + (5 + len / 8 + (List.map (fun len => 5 + len / 8) r).sum) by omega]

theorem segOut_segsF_shift {f : ℕ → ℕ → Seg} (hf : Shift W f) : ∀ (b u : ℕ) (L : List ℕ),
    segOut W false b (segsF f u L) = segOut W false 0 (segsF f (b + u) L)
  | _, _, [] => rfl
  | b, u, len :: r => by
    rw [segsF, segsF, segOut, segOut, hf, segOut_segsF_shift hf b _ r,
      show b + (u + 5 + len / 8) = b + u + 5 + len / 8 by omega]

theorem segOut_rep_run {f : ℕ → ℕ → Seg} (hf : Shift W f) (u len : ℕ) : ∀ (c b : ℕ),
    segOut W false b (.rep c (5 + len / 8) (f u len)) = segOut W false 0 (segsF f (b + u) (List.replicate c len))
  | 0, _ => by simp [segOut, segsF]
  | c + 1, b => by
    rw [segOut_rep_succ, segOut_rep_run hf u len c, hf, List.replicate_succ, segsF, segOut,
      show b + (5 + len / 8) + u = b + u + 5 + len / 8 by omega]

theorem segOut_runsF {f : ℕ → ℕ → Seg} (hf : Shift W f) : ∀ (rs : List (ℕ × ℕ)) (b u : ℕ),
    segOut W false b (runsF f u rs) = segOut W false 0 (segsF f (b + u) (runLens rs))
  | [], _, _ => rfl
  | r :: rs, b, u => by
    have e : runLens (r :: rs) = List.replicate r.1 r.2 ++ runLens rs := by simp [runLens]
    rw [runsF, segOut, segOut_rep1, segOut_rep_run W hf, segOut_runsF hf rs, e, segOut_segsF_append,
      lanesOf_replicate, show b + (u + r.1 * (5 + r.2 / 8)) = b + u + r.1 * (5 + r.2 / 8) by omega]

theorem segOut_rep_blk {f : ℕ → ℕ → Seg} (hf : Shift W f) (u : ℕ) (rs : List (ℕ × ℕ)) : ∀ (t b : ℕ),
    segOut W false b (.rep t (lanesOf (runLens rs)) (runsF f u rs)) =
      segOut W false 0 (segsF f (b + u) (List.replicate t (runLens rs)).flatten)
  | 0, _ => by simp [segOut, segsF]
  | t + 1, b => by
    rw [segOut_rep_succ, segOut_rep_blk hf u rs t, segOut_runsF W hf, List.replicate_succ, List.flatten_cons,
      segOut_segsF_append, show b + lanesOf (runLens rs) + u = b + u + lanesOf (runLens rs) by omega]

/-- **The blocks denote the unrolled units.** -/
theorem segOut_blksF {f : ℕ → ℕ → Seg} (hf : Shift W f) : ∀ (bs : List (ℕ × List (ℕ × ℕ))) (u : ℕ),
    segOut W false 0 (blksF f u bs) = segOut W false 0 (segsF f u (blkLens bs))
  | [], _ => rfl
  | b :: bs, u => by
    have e : blkLens (b :: bs) = (List.replicate b.1 (runLens b.2)).flatten ++ blkLens bs := by simp [blkLens]
    rw [blksF, segOut, segOut_rep1, segOut_rep_blk W hf, segOut_blksF hf bs, e, segOut_segsF_append,
      lanesOf_flatten_replicate, Nat.zero_add]

end Comp

/-- **The compressed proof segment**: the seed's message, then the blocks' pieces. -/
def pSegB (leafLs : List ℕ) (len0 : ℕ) (bs : List (ℕ × List (ℕ × ℕ))) : Seg :=
  .cat (.cp (6 + 5) ((len0 - 32) / 8)) (blksF (pieceSeg leafLs) (6 + 5 + len0 / 8) bs)

/-- **The compressed trace segment**: the count, `q₀`'s entry, the seed's entry, the blocks' entries. -/
def trSegB (len0 : ℕ) (bs : List (ℕ × List (ℕ × ℕ))) : Seg :=
  .cat (.wd (toWord ((len0 :: blkLens bs).length + 1))) (.cat (.wd (toWord 7)) (.cat (.sh8 1) (.cat (.cp 2 4)
    (.cat (entSeg 6 len0) (blksF entSeg (6 + 5 + len0 / 8) bs)))))

/-- **The compressed left segment**: the proof's byte length, the proof, the trace. -/
def leftSegB (leafLs : List ℕ) (len0 : ℕ) (bs : List (ℕ × List (ℕ × ℕ))) : Seg :=
  .cat (.wd (toWord (8 * segLen false (pSegB leafLs len0 bs)))) (.cat (pSegB leafLs len0 bs) (trSegB len0 bs))

/-- **`segOut_leftSegB`**: the compressed segment denotes `leftSeg` of the unrolled lengths. -/
theorem segOut_leftSegB (W : ℕ → Word) (leafLs : List ℕ) (len0 : ℕ) (bs : List (ℕ × List (ℕ × ℕ))) :
    segOut W false 0 (leftSegB leafLs len0 bs) = segOut W false 0 (leftSeg leafLs (len0 :: blkLens bs)) := by
  have hp : ∀ W, segOut W false 0 (pSegB leafLs len0 bs) = segOut W false 0 (pSeg6 leafLs (len0 :: blkLens bs)) :=
    fun W => by
      rw [pSegB, pSeg6, segOut, segOut, segOut_blksF W (shift_pieceSeg W leafLs), pSegs6_eq]
  have ht : segOut W false 0 (trSegB len0 bs) = segOut W false 0 (trSeg6 (len0 :: blkLens bs)) := by
    simp only [trSegB, trSeg6, segOut_cat, trSegs6_eq, segsF, segOut_blksF W (shift_entSeg W)]
  have hl : segLen false (pSegB leafLs len0 bs) = segLen false (pSeg6 leafLs (len0 :: blkLens bs)) := by
    rw [← segOut_length (fun _ => 0) false _ 0, ← segOut_length (fun _ => 0) false _ 0, hp]
  rw [leftSegB, leftSeg, segOut_cat, segOut_cat, segOut_cat, segOut_cat, ht, hp, hl]

/-! ## The program -/

/-- The source base `oR := tB`, the segment base `0`, the kind flag `0`. -/
def leftPre (tB : ℕ) : XIR := .blk [.const oR (toWord tB), .const (oBd 0) (toWord 0), .const oKF 0]

/-- **The left child's output**: the segment `sg` over the stream from `tB` (at `P18` the compressed
`leftSegB`, which denotes `leftSeg`), then `σ'`'s 597 words from `sB`. -/
def leftOutIR (sg : Seg) (tB sB : ℕ) : XIR :=
  .seq (leftPre tB) (.seq (segIR apC 0 sg) (outCpIR sB 597))

/-- **`leftOutIR_sem`**: for a segment `sg` that denotes `leftSeg leafLs lens`, the program appends the left child's
signed file `signedWords (leftOf6 …)` and writes registers only. -/
theorem leftOutIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {sg : Seg} {lens leafLs : List ℕ} {tB sB : ℕ}
    (hX : okX sg = true) (hD : depthSeg sg ≤ 9)
    (hsg : ∀ W, segOut W false 0 sg = segOut W false 0 (leftSeg leafLs lens))
    (hl : ∀ len ∈ lens, len % 8 = 0 ∧ len < 2 ^ 32) (htr : regs ≤ tB) (htw : tB + (6 + lanesOf lens) < 2 ^ 40)
    (hsr : regs ≤ sB) (hsw : sB + 597 < 2 ^ 64) :
    (semXIR I (leftOutIR sg tB sB) s).o.toList =
      s.o.toList ++ signedWords (leftOf6 lens leafLs (rd s.M) tB sB) ∧
    (∀ x, regs ≤ x → rd (semXIR I (leftOutIR sg tB sB) s).M x = rd s.M x) ∧
    Inv (semXIR I (leftOutIR sg tB sB) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have wpre : WF (leftPre tB) := by simp +decide [leftPre, WF, Prim.dst, oR, oBd, oKF]
  have r0 : rd (semXIR I (leftPre tB) s).M oR = toWord tB ∧ rd (semXIR I (leftPre tB) s).M (oBd 0) = toWord 0 ∧
      rd (semXIR I (leftPre tB) s).M oKF = 0 ∧ (semXIR I (leftPre tB) s).o = s.o ∧
      ∀ x, regs ≤ x → rd (semXIR I (leftPre tB) s).M x = rd s.M x := by
    simp only [leftPre, semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, trivial, fun x hx => ?_⟩
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds, oR, oBd, oKF]; omega))
        only [rd_set_self, rd_set_ne]
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds, oR, oBd, oKF]; omega))
        only [rd_set_self, rd_set_ne]
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds, oR, oBd, oKF]; omega))
        only [rd_set_self, rd_set_ne]
    · simp only [regs] at hx
      simp (disch := first | decide | (simp only [oR, oBd, oKF]; omega)) only [rd_set_ne]
  obtain ⟨p0, b0, k0, o0, h0⟩ := r0
  have hc1 : Ctx s.M tB false (semXIR I (leftPre tB) s) :=
    ⟨inv_sem I wpre hM, size_sem I _ s, h0, p0, by simp [k0]⟩
  have hd : depthSeg sg + 0 ≤ 9 := hD
  have e2 := segIR_sem I apC (hA_apC htr (by omega)) sg 0 0 _ (okSeg_of_okX _ hX) hd hc1 b0
  have hc2 := ctx_segIR I apC sg 0 hd hc1
  simp only [leftOutIR, semXIR_seq]
  generalize semXIR I (segIR apC 0 sg) (semXIR I (leftPre tB) s) = s2 at e2 hc2
  obtain ⟨c1, c2, c3⟩ := outCpIR_sem I s2 hc2.inv hsr hsw
  refine ⟨?_, fun x hx => (c2 x hx).trans (hc2.heap x hx), c3⟩
  have hsig : wsAt (rd s2.M) sB 597 = wsAt (rd s.M) sB 597 := by
    simp only [wsAt]
    exact List.map_congr_left fun j _ => hc2.heap _ (by simp only [regs] at hsr ⊢; omega)
  have htr' : readTrace6 lens (src s.M apC tB) = readTrace6 lens fun u => rd s.M (tB + u) :=
    readTrace6_congr lens fun v hv => src_apC s.M (by omega)
  rw [c1, e2, o0, hsig, hsg, segOut_leftSeg _ leafLs lens fun len h => (hl len h).1, htr']
  simp only [signedWords, leftOf6, sigWords_sigOf, List.append_assoc]

/-! ## The exact cost -/

/-- **The exact cost**: the setup, the segment, `σ'`'s copy. -/
theorem cost_leftOutIR (sg : Seg) (tB sB t : ℕ) (hX : okX sg = true) :
    cost (leftOutIR sg tB sB) t = 4795 + segCost sg := by
  simp only [leftOutIR, leftPre, cost, cost_segIR_okX apC t _ 0 hX,
    cost_outCpIR sB 597 t (by norm_num), blkSteps, List.length_cons, List.length_nil]
  have h5 : (if 0 + 1 + 1 + 1 = 0 then 1 else 2 * (0 + 1 + 1 + 1) - 1) = 5 := rfl
  omega

end Lvm6.X
