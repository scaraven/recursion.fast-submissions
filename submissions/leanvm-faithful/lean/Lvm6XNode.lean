-- lvm6 X5 (BLUEPRINT v3 §2.1, §3 step 3; X2 §4 item 1): the node witness's output program at `P18`: the tag,
-- `c'` from the header, `L = leafStmt h n` (season 1's `LvmXKeccak`), X3's left child over the `STREAM` lanes,
-- X2's right child. The emitters are season 1's `LvmXTop.emitIR`/`tcpIR` (parked), on registers 232–235.
import Lvm6XP18
import LvmXKeccak

/-!
# `nodeOutIR`: the node witness at `P18`

* **`lens18`**: CD's plan of `P18` without `q₀` (`(planOf P18).drop 1`), the query lengths of trace entries
  `1 … qS − 1` (4,348 entries; `6 + lanesOf lens18 = 68,019` stream words, CD §0). **`leafLs18 = [368, 256]`**:
  the leaf lengths (`leafLs18_spec`: every leaf entry of the plan has one, no other entry does).
* The layout (`colB6`, `stride6 = 2^19`): the decoded stack, slot `m`'s word at row `r` at `colB6 + m·2^19 + r`; the
  `STREAM` window is slot 33, so CD's bases are `tB6 = colB6 + 33·2^19`, `sB6 = tB6 + 2^18`, `sLB6 = sB6 + 597`.
* **`nodeOutIR`** (tape words: `n` 7, `h` 8–11, `c'` 12–15, the header's `§2` offsets 16, 24, 56):
  `1`, `c'`, `leafStmt h n`, `leftOutIR leftSeg18 tB6 sB6`, `rightOutIR 2^18 colB6 2^19 sLB6`.
  **`nodeOutIR_sem`**: it appends `witWords (nodeWit6 lens18 leafLs18 c' (leafStmt h n) 2^18 cols (rd M) tB6 sB6
  sLB6)` and writes registers only. **`cost_nodeOutIR` = 11,844,699** (exact), `outs_nodeOutIR ≤ 1,147,573`,
  **`sizeIR_nodeOutIR` = 26,849** (X6a, F-X5 fixed: the left segment `leftSeg18` is `rep`s over runs and blocks;
  1,536,419 unrolled per entry).
* `leftOf6_congr`, `sigOf_congr`: the children read only the window's words (shifted congruence).
-/

namespace Lvm6.X

open RecursionFast Lvm Lvm.X

/-! ## The layout -/

/-- The stack's column stride `2^19`. -/ def stride6 : ℕ := 524288
/-- The leaf count `2^18`. -/ def n18 : ℕ := 262144
/-- The decoded stack's base `2^26`. -/ def colB6 : ℕ := 67108864
/-- The trace stream's base: slot 33 (CD `tB = 0`). -/ def tB6 : ℕ := 84410368
/-- `σ'`'s base (CD `sB = 2^18`). -/ def sB6 : ℕ := 84672512
/-- `σ_leaf`'s base (CD `sLB = 2^18 + 597`). -/ def sLB6 : ℕ := 84673109

theorem tB6_eq : tB6 = colB6 + 33 * stride6 := rfl
theorem sB6_eq : sB6 = tB6 + 2 ^ 18 := rfl
theorem sLB6_eq : sLB6 = sB6 + 597 := rfl

/-! ## Emitters (season 1's `emitIR`, `tcpIR`) -/

/-- The word emitted. -/ def oW6 : ℕ := 232
/-- The tape position. -/ def oP6 : ℕ := 233
/-- The loop count. -/ def oN6 : ℕ := 234
/-- The loop counter. -/ def oC6 : ℕ := 235

/-- Output the constant `w`. -/
def emit6IR (w : Word) : XIR := .seq (.blk [.const oW6 w]) (.out oW6)

theorem wf_emit6IR (w : Word) : WF (emit6IR w) := by
  simp +decide [emit6IR, WF, Prim.dst, oW6]

theorem emit6IR_sem (I : Array Word) (s : St) (hM : Inv s.M) (w : Word) :
    (semXIR I (emit6IR w) s).o.toList = s.o.toList ++ [w] ∧
    (∀ y, y ≠ oW6 → rd (semXIR I (emit6IR w) s).M y = rd s.M y) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun y hy => ?_⟩
  · simp only [emit6IR, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
    rw [rd_set_self (by simp only [oW6]; (clear * - s hs; omega))]
  · simp only [emit6IR, semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne (Ne.symm hy)

/-- One word: `out I[oP6]`, `oP6 += 1`. -/
def tcp6Body : XIR := .seq (.input oW6 oP6) (.seq (.out oW6) (.blk [.op .add oP6 oP6 cOne]))

/-- **Output tape words `a … a + n − 1`.** -/
def tcp6IR (a n : ℕ) : XIR :=
  .seq (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) (.loopK oC6 oN6 (toWord n) tcp6Body)

theorem wf_tcp6IR (a n : ℕ) : WF (tcp6IR a n) := by
  simp +decide [tcp6IR, tcp6Body, WF, Writes, Prim.dst, oW6, oP6, oN6, oC6, cTmp, regs]

theorem tcp6Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : rd s.M oP6 = toWord p)
    (hp2 : p < 2 ^ 64) :
    (semXIR I tcp6Body s).o.toList = s.o.toList ++ [I.getD p 0] ∧
    rd (semXIR I tcp6Body s).M oP6 = toWord (p + 1) ∧
    (∀ y, y ≠ oW6 → y ≠ oP6 → rd (semXIR I tcp6Body s).M y = rd s.M y) ∧
    (semXIR I tcp6Body s).M.size = s.M.size := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [tcp6Body, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
  refine ⟨?_, ?_, fun y h1 h2 => ?_, by simp⟩
  · rw [rd_set_self (by simp only [oW6]; (clear * - s p hs; omega)), hp, toNat_toWord hp2]
  · simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hp, h1]
    exact add_one_toWord p
  · rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]

/-- **The tape copy**: `n` tape words from `a` are output; only `oW6, oP6, oN6, oC6, cTmp` change. -/
theorem tcp6IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a n : ℕ} (h : a + n < 2 ^ 64) :
    (semXIR I (tcp6IR a n) s).o.toList = s.o.toList ++ (List.range n).map (fun j => I.getD (a + j) 0) ∧
    (∀ y, y ≠ oW6 → y ≠ oP6 → y ≠ oN6 → y ≠ oC6 → y ≠ cTmp → rd (semXIR I (tcp6IR a n) s).M y = rd s.M y) ∧
    Inv (semXIR I (tcp6IR a n) s).M ∧ (semXIR I (tcp6IR a n) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf := wf_tcp6IR a n
  have hM1 : Inv (semXIR I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s).M := inv_sem I hwf.1 hM
  have p1 : rd (semXIR I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s).M oP6 = toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have n1 : rd (semXIR I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s).M oN6 = toWord n := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ oP6 → y ≠ oN6 →
      rd (semXIR I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s).M y = rd s.M y :=
    fun y a b => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b) _
  have z1 := size_sem I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s
  have o1 : (semXIR I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s).o = s.o := rfl
  rw [tcp6IR, semXIR_seq]
  generalize semXIR I (.blk [.const oP6 (toWord a), .const oN6 (toWord n)]) s = s1 at hM1 p1 n1 f1 z1 o1
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ rd t.M oP6 = toWord (a + j) ∧
    (∀ y, y ≠ oW6 → y ≠ oP6 → y ≠ oN6 → y ≠ oC6 → y ≠ cTmp → rd t.M y = rd s.M y) ∧ t.M.size = s.M.size
  have h0 : Q 0 ⟨entryK oC6 oN6 (toWord n) s1.M, s1.o⟩ := by
    dsimp only [Q]
    refine ⟨inv_of_frame hM1 (size_entryK oC6 oN6 (toWord n) s1.M) fun i hi => entryK_frame _ (by simp only [oC6]; (clear * - i s a n s1 hi; omega))
        (by simp only [cTmp]; (clear * - i s a n s1 hi; omega)), ?_, fun y a b c d e => ?_, by rw [size_entryK, z1]⟩
    · rw [entryK_frame _ (by decide) (by decide), p1, Nat.add_zero]
    · rw [entryK_frame _ (Ne.symm d) (Ne.symm e), f1 y b c]
  have hf : ∀ j t, j < n → Q j t → (semXIR I tcp6Body t).o.toList = t.o.toList ++ [I.getD (a + j) 0] ∧
      Q (j + 1) (decS oC6 (semXIR I tcp6Body t)) := by
    intro j t hj ⟨q1, q2, q3, q4⟩
    obtain ⟨b1, b2, b3, b4⟩ := tcp6Body_sem I t q1 q2 (by (clear * - a j s n h s1 t hj; omega))
    refine ⟨b1, inv_of_frame (inv_sem I hwf.2.2.2.2 q1) (size_decS ..) fun i hi =>
      rd_decS (by simp only [oC6]; (clear * - i I s a n s1 j t hi; omega)) _, by rw [rd_decS (by decide), b2, Nat.add_assoc],
      fun y a b c d e => by rw [rd_decS (Ne.symm d), b3 y a b, q3 y a b c d e], by rw [size_decS, b4, q4]⟩
  obtain ⟨l1, l2⟩ := loopK_emit I (b := tcp6Body) Q (fun j => [I.getD (a + j) 0]) s1 hM1 (by decide)
    (by decide) (by decide) (by (clear * - n s a h s1; omega)) n1 h0 hf
  refine ⟨?_, l2.2.2.1, l2.1, l2.2.2.2⟩
  rw [l1, o1, flatMap_single]

/-! ## The children read only the window -/

/-- **`sigOf` reads 597 words** (shifted congruence). -/
theorem sigOf_congr {W W' : ℕ → Word} {b b' : ℕ} (h : ∀ j < 597, W (b + j) = W' (b' + j)) :
    sigOf W b = sigOf W' b' := by
  have hw : ∀ o, o + 4 ≤ 597 → wsAt W (b + o) 4 = wsAt W' (b' + o) 4 := fun o ho => by
    simp only [wsAt]
    exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [Nat.add_assoc, Nat.add_assoc, h _ (by omega)]
  have h0 : W b = W' b' := by simpa using h 0 (by norm_num)
  have hl : wotsLen = 133 := rfl
  have hp : sigHeight = 16 := rfl
  have e1 : (List.range wotsLen).map (fun e => digW (wsAt W (b + 1 + 4 * e) 4)) =
      (List.range wotsLen).map (fun e => digW (wsAt W' (b' + 1 + 4 * e) 4)) :=
    List.map_congr_left fun e he => by
      have := List.mem_range.mp he
      rw [show b + 1 + 4 * e = b + (1 + 4 * e) by ring, show b' + 1 + 4 * e = b' + (1 + 4 * e) by ring,
        hw _ (by omega)]
  have e2 : (List.range sigHeight).map (fun e => digW (wsAt W (b + 1 + 4 * wotsLen + 4 * e) 4)) =
      (List.range sigHeight).map (fun e => digW (wsAt W' (b' + 1 + 4 * wotsLen + 4 * e) 4)) :=
    List.map_congr_left fun e he => by
      have := List.mem_range.mp he
      rw [show b + 1 + 4 * wotsLen + 4 * e = b + (1 + 4 * wotsLen + 4 * e) by ring,
        show b' + 1 + 4 * wotsLen + 4 * e = b' + (1 + 4 * wotsLen + 4 * e) by ring, hw _ (by omega)]
  unfold sigOf
  rw [h0, e1, e2]

/-- **The left child reads the stream lanes and `σ'`** (shifted congruence). -/
theorem leftOf6_congr {lens leafLs : List ℕ} {W W' : ℕ → Word} {tB tB' sB sB' : ℕ}
    (ht : ∀ u < 6 + lanesOf lens, W (tB + u) = W' (tB' + u)) (hs : ∀ j < 597, W (sB + j) = W' (sB' + j)) :
    leftOf6 lens leafLs W tB sB = leftOf6 lens leafLs W' tB' sB' := by
  have e : readTrace6 lens (fun u => W (tB + u)) = readTrace6 lens (fun u => W' (tB' + u)) :=
    readTrace6_congr lens ht
  simp only [leftOf6, e, sigOf_congr hs]

/-! ## The program -/

/-- **The node witness's output at `P18`**: the tag `1`, `c'` (tape words 12–15), `leafStmt h n` (`h` at 8–11,
`n` at 7), the left child, the right child. -/
def nodeOutIRL (sg : Seg) : XIR :=
  .seq (emit6IR (toWord 1)) (.seq (tcp6IR 12 4) (.seq (leafStmtIR 8 7)
    (.seq (leftOutIR sg tB6 sB6) (rightOutIR n18 colB6 stride6 sLB6))))

/-- **`nodeOutIR`** at `P18`: the compressed left segment `leftSeg18`. -/
def nodeOutIR : XIR := nodeOutIRL leftSeg18

theorem wf_leftOutIR (sg : Seg) (tB sB : ℕ) (hD : depthSeg sg ≤ 9) : WF (leftOutIR sg tB sB) :=
  ⟨by simp +decide [leftPre, WF, Prim.dst, oR, oBd, oKF], wf_segIR apC _ 0 (by omega), wf_outCpIR sB 597⟩

theorem noLoopT_leftOutIR (sg : Seg) (tB sB : ℕ) : NoLoopT (leftOutIR sg tB sB) :=
  ⟨trivial, noLoopT_segIR apC _ 0, noLoopT_outCpIR sB 597⟩

theorem outs_leftOutIR_le (sg : Seg) (tB sB t : ℕ) : outs (leftOutIR sg tB sB) t ≤ segOuts sg + 597 := by
  have h1 := outs_segIR apC sg 0 t
  simp only [leftOutIR, leftPre, outs, outs_outCpIR sB 597 t (by norm_num)]
  omega

theorem sizeIR_leftOutIR (sg : Seg) (tB sB : ℕ) : sizeIR (leftOutIR sg tB sB) = 27 + segSize sg := by
  simp only [leftOutIR, leftPre, sizeIR, sizeIR_segIR, sizeIR_outCpIR, blkSteps, List.length_cons,
    List.length_nil]
  have h5 : (if 0 + 1 + 1 + 1 = 0 then 1 else 2 * (0 + 1 + 1 + 1) - 1) = 5 := rfl
  omega

theorem wf_nodeOutIR : WF nodeOutIR :=
  ⟨wf_emit6IR _, wf_tcp6IR _ _, wf_leafStmtIR _ _, wf_leftOutIR _ _ _ (by rw [depth_left18]; omega),
    wf_rightOutIR _ _ _ _⟩

theorem noLoopT_nodeOutIR : NoLoopT nodeOutIR :=
  ⟨by simp [emit6IR, NoLoopT], by simp [tcp6IR, tcp6Body, NoLoopT], noLoopT_leafStmtIR _ _, noLoopT_leftOutIR _ _ _,
    noLoopT_rightOutIR _ _ _ _⟩

/-- **The exact cost** at `P18`. -/
theorem cost_nodeOutIR (t : ℕ) : cost nodeOutIR t = 11844699 := by
  simp only [nodeOutIR, nodeOutIRL, cost, emit6IR, tcp6IR, tcp6Body, blkSteps, List.length_cons, List.length_nil,
    cost_leafStmtIR, cost_leftOutIR leftSeg18 tB6 sB6 t okX_left18, segCost_left18,
    cost_rightOutIR n18 colB6 stride6 sLB6 t (by simp only [n18]; norm_num), toNat_toWord (show 4 < 2 ^ 64 by norm_num)]
  simp only [n18]
  norm_num

theorem outs_nodeOutIR (t : ℕ) : outs nodeOutIR t ≤ 1147573 := by
  have h := outs_leftOutIR_le leftSeg18 tB6 sB6 t
  rw [segOuts_left18] at h
  simp only [nodeOutIR, nodeOutIRL, outs, emit6IR, tcp6IR, tcp6Body, outs_leafStmtIR,
    outs_rightOutIR n18 colB6 stride6 sLB6 t (by simp only [n18]; norm_num), toNat_toWord (show 4 < 2 ^ 64 by norm_num)]
  simp only [n18]
  omega

theorem sizeIR_nodeOutIR : sizeIR nodeOutIR = 26849 := by
  simp only [nodeOutIR, nodeOutIRL, sizeIR, emit6IR, tcp6IR, tcp6Body, blkSteps, List.length_cons, List.length_nil,
    sizeIR_leafStmtIR, sizeIR_leftOutIR, segSize_left18, rightOutIR, sizeIR_leafOutIR, sizeIR_outCpIR]
  norm_num

/-- **`nodeOutIR_sem`**: on a tape with `n` at word 7, `h` at words 8–11 and `c'` at words 12–15, the program appends
the node witness's words (the columns and the window read off the heap) and writes registers only. -/
theorem nodeOutIRL_sem {sg : Seg} {lens leafLs : List ℕ} (hX : okX sg = true) (hD : depthSeg sg ≤ 9)
    (hsg : ∀ W, segOut W false 0 sg = segOut W false 0 (leftSeg leafLs lens))
    (hlo : ∀ len ∈ lens, len % 8 = 0 ∧ len < 2 ^ 32)
    (hla : 6 + lanesOf lens ≤ 2 ^ 18) (I : Array Word) (s : St) (hM : Inv s.M) (c' h : Digest) (n : ℕ)
    (hc : (List.range 4).map (fun j => I.getD (12 + j) 0) = packBytes c'.toList)
    (hh : ∀ i < 4, I.getD (8 + i) 0 = (packBytes h.toList).getD i 0) (hn : I.getD 7 0 = toWord n)
    (hn64 : n < 2 ^ 64) :
    (semXIR I (nodeOutIRL sg) s).o.toList = s.o.toList ++ witWords (nodeWit6 lens leafLs c' (leafStmt h n) n18
      (fun m r => rd s.M (colB6 + m * stride6 + r)) (rd s.M) tB6 sB6 sLB6) ∧
    (∀ x, regs ≤ x → rd (semXIR I (nodeOutIRL sg) s).M x = rd s.M x) ∧ Inv (semXIR I (nodeOutIRL sg) s).M := by
  simp only [nodeOutIRL, semXIR_seq]
  -- the tag
  obtain ⟨e1, f1⟩ := emit6IR_sem I s hM (toWord 1)
  have i1 := inv_sem I (wf_emit6IR (toWord 1)) hM
  have g1 : ∀ x, regs ≤ x → rd (semXIR I (emit6IR (toWord 1)) s).M x = rd s.M x :=
    fun x hx => f1 x (by simp only [oW6, regs] at hx ⊢; omega)
  generalize semXIR I (emit6IR (toWord 1)) s = s1 at e1 i1 g1
  -- `c'`
  obtain ⟨e2, f2, i2, -⟩ := tcp6IR_sem I s1 i1 (a := 12) (n := 4) (by norm_num)
  have g2 : ∀ x, regs ≤ x → rd (semXIR I (tcp6IR 12 4) s1).M x = rd s1.M x :=
    fun x hx => f2 x (by simp only [oW6, regs] at hx ⊢; omega) (by simp only [oP6, regs] at hx ⊢; omega)
      (by simp only [oN6, regs] at hx ⊢; omega) (by simp only [oC6, regs] at hx ⊢; omega)
      (by simp only [cTmp, regs] at hx ⊢; omega)
  generalize semXIR I (tcp6IR 12 4) s1 = s2 at e2 i2 g2
  -- `L`
  obtain ⟨e3, g3⟩ := leafStmtIR_sem I s2 i2 h n hh hn hn64 (by norm_num) (by norm_num)
  have i3 := inv_sem I (wf_leafStmtIR 8 7) i2
  generalize semXIR I (leafStmtIR 8 7) s2 = s3 at e3 i3 g3
  -- the left child
  obtain ⟨e4, g4, i4⟩ := leftOutIR_sem I s3 i3 (lens := lens) (leafLs := leafLs) (tB := tB6) (sB := sB6) hX hD hsg hlo
    (by simp only [regs, tB6]; omega) (by simp only [tB6]; omega)
    (by simp only [regs, sB6]; omega) (by simp only [sB6]; norm_num)
  generalize semXIR I (leftOutIR sg tB6 sB6) s3 = s4 at e4 i4 g4
  -- the right child
  obtain ⟨e5, g5, i5⟩ := rightOutIR_sem I s4 i4 (n := n18) (colB := colB6) (S := stride6) (sLB := sLB6)
    (by simp only [regs, colB6]; omega) (by simp only [colB6, n18, stride6]; norm_num)
    (by simp only [regs, sLB6]; omega) (by simp only [sLB6]; norm_num)
  have G : ∀ x, regs ≤ x → rd s4.M x = rd s.M x := fun x hx =>
    (g4 x hx).trans ((g3 x hx).trans ((g2 x hx).trans (g1 x hx)))
  refine ⟨?_, fun x hx => (g5 x hx).trans (G x hx), i5⟩
  have hl : leftOf6 lens leafLs (rd s3.M) tB6 sB6 = leftOf6 lens leafLs (rd s.M) tB6 sB6 :=
    leftOf6_congr (fun u _ => (g3 (tB6 + u) (by simp only [regs, tB6]; omega)).trans
      ((g2 (tB6 + u) (by simp only [regs, tB6]; omega)).trans (g1 (tB6 + u) (by simp only [regs, tB6]; omega))))
      (fun j _ => (g3 (sB6 + j) (by simp only [regs, sB6]; omega)).trans
      ((g2 (sB6 + j) (by simp only [regs, sB6]; omega)).trans (g1 (sB6 + j) (by simp only [regs, sB6]; omega))))
  have hq : (fun m r => rd s4.M (colB6 + m * stride6 + r)) = (fun m r => rd s.M (colB6 + m * stride6 + r)) :=
    funext fun m => funext fun r => G (colB6 + m * stride6 + r) (by simp only [regs, colB6]; omega)
  have hσ : sigOf (rd s4.M) sLB6 = sigOf (rd s.M) sLB6 :=
    sigOf_congr fun j _ => G (sLB6 + j) (by simp only [regs, sLB6]; omega)
  rw [e5, e4, e3, e2, e1, hc]
  simp only [hl, hq, hσ, nodeWit6, witWords, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append]


theorem nodeOutIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (c' h : Digest) (n : ℕ)
    (hc : (List.range 4).map (fun j => I.getD (12 + j) 0) = packBytes c'.toList)
    (hh : ∀ i < 4, I.getD (8 + i) 0 = (packBytes h.toList).getD i 0) (hn : I.getD 7 0 = toWord n)
    (hn64 : n < 2 ^ 64) :
    (semXIR I nodeOutIR s).o.toList = s.o.toList ++ witWords (nodeWit6 lens18 leafLs18 c' (leafStmt h n) n18
      (fun m r => rd s.M (colB6 + m * stride6 + r)) (rd s.M) tB6 sB6 sLB6) ∧
    (∀ x, regs ≤ x → rd (semXIR I nodeOutIR s).M x = rd s.M x) ∧ Inv (semXIR I nodeOutIR s).M := by
  unfold nodeOutIR
  exact nodeOutIRL_sem okX_left18 (by rw [depth_left18]; omega) segOut_leftSeg18 lensOK18 (by rw [lanes18]; norm_num) I s
    hM c' h n hc hh hn hn64

end Lvm6.X
