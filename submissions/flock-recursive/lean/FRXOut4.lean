-- New for `flock-recursive` (BLUEPRINT revision 4.3, §6.2 step 5, A.7; stage S-H4, pass 7, item 1:
-- the node output's cell map). 3.x analogue: `FRNodeRead` (`readStmt`), `FRXOutRun` (`src_stream`).
import FRXDec4F0
import FRNodeRead4

/-!
# The node witness on the heap after the decode (`FRXOut4`, first half)

After `decF04 κ` the heap holds level 0's rows `1 … 7` of `f⁽⁰⁾` (`decF04_sem`). The committed
witness the node relation reads is `w := wF κ L es`, cell `e` being coefficient `e / 64` of row
`e mod 64` (`T4.fF` at a node kind, unfolded: the `FRX` modules do not import `FRSoundness4TailFold`).

* **`decF04_wF`**: every cell `e` of a decoded row (`Dec0 e`: `1 ≤ e mod 64 < 8`) inside `f`
  (`e < 2^(m − 7)`) sits at `wAddr κ e` as `wF κ L es e`.
* **What the output reads is decoded** (`out_cells_dec0`): H's message slots (rows 4–7), the
  activity selectors `κ.oneCell + selR σ ι` (rows 1–3) and the children's statement cells `stC`
  (an aggregate's `h_out`, rows 2–3). **Finding (pass 7):** the last two are outside rows 4–7, which
  the blueprint's (A)(ii) decoded; `decF04` now decodes rows 1–7 (`FRXDec4Map`, `C = 7`).
  (−) `sigCell_not_dec0`: L's first cell (row 0) is not decoded, so the output cannot read the
  signature from L (`readSig4`); revision 4.3 reads it from H (`sig_of_H`, S-G/S-E).
* **The segment count** `kSel` (computable: the first sub-slot whose selector sum is not `1`) is
  the reader's `kAct` (`kSel_eq`).
* **The statements** `stD κ σ w` (the cells `stC κ σ 0, 1`) are the node statement's `c₁`, `c₂` on
  every witness meeting `PubCells4` (`stD_of_pubCells`): no link is needed for them.
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

/-! ## The decoded cells and their addresses -/

/-- **Level 0's decoded cells**: rows `1 … 7` (`e mod 64`). -/
def Dec0 (e : ℕ) : Prop := 1 ≤ e % 64 ∧ e % 64 < 8

instance (e : ℕ) : Decidable (Dec0 e) := by unfold Dec0; infer_instance

/-- **The committed witness of a node proof** (`T4.fF (.node κ) L es`, `fTab` unfolded at level 0's
64 rows): cell `e` is coefficient `e / 64` of row `e mod 64` of `f⁽⁰⁾`, in F. -/
noncomputable def wF (κ : NodeKind) (L es : Log) : Circ.Asg :=
  fun e => (T4.msgOf (.node κ) L es 0 (e % 64) (e / 64)).f₀

/-- **Cell `e`'s heap address** after `decF04 κ` (row `e mod 64 − 1` of the decoded rows). -/
def wAddr (κ : NodeKind) (e : ℕ) : ℕ :=
  map4.l0.ob + 2 * 2 ^ T4.mLog (.node κ) 0 * (e % 64 - 1) + 2 * (e / 64)

/-- A node's `f` has `2^(m − 7)` cells, `2^(m − 13)` (level 0's message length) per row. -/
theorem cells_cols (κ : NodeKind) {e : ℕ} (he : e < 2 ^ (κ.m - 7)) : e / 64 < 2 ^ T4.mLog (.node κ) 0 := by
  have h : 2 ^ (κ.m - 7) = 64 * 2 ^ T4.mLog (.node κ) 0 := by cases κ <;> decide
  rw [h] at he
  exact Nat.div_lt_of_lt_mul he

/-- **The decode leaves `f`'s decoded cells at `wAddr`**, under `decF04_sem`'s hypotheses. -/
theorem decF04_wF (κ : NodeKind) (c : Digest) (π : Proof) (L : Log) (hD : Dom4 pL4 c π L)
    (hps : π.size = piSizeOf seq4) (hS : ¬ StateHit L) (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep4, fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap : ∀ i < 5, ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, T4.capDig es i e = capPi4 i π e)
    (hfin : ∀ x < 2 ^ T4.mLog (.node κ) 4, T4.finalAt es x = finPi4 π x)
    (hfar : ∀ i < 5, ¬ T4.farL (.node κ) L es i)
    (hA : ∀ i < 5, T4.consSet (.node κ) L es i =
      jointAgree (T4.wordK (.node κ) L es i) (T4.decodeL (.node κ) L es i))
    (s : St) (hM : Inv s.M) (hsz : memX4 + L.length + L.length ≤ s.M.size) :
    ∀ e, Dec0 e → e < 2 ^ (κ.m - 7) →
      rdF (semXIR (tp c π L) (decF04 κ) s).M (wAddr κ e) = wF κ L es e := by
  intro e he hlt
  have h := decF04_sem κ c π L hD hps hS st₀ hfm hcap hfin hfar hA s hM hsz (e % 64 - 1) (by
    have := he.2; omega) (e / 64) (cells_cols κ hlt)
  rw [show 1 + (e % 64 - 1) = e % 64 by have := he.1; omega] at h
  rw [wF, ← h, wAddr]
  rfl

/-! ## What the output reads lies in rows 1–7 -/

/-- H block `b`'s message slot `j < 4` (cell `128 b + 4 + j`, rows 4–7). -/
theorem msg_dec0 (b j : ℕ) (hj : j < 4) : Dec0 (b * 128 + 4 + j) := by
  unfold Dec0; omega

/-- **The cells the output reads beyond H's messages are decoded**: every slot's three activity
selectors (rows 1–3) and both children's statement halves (`seedC`'s message slots, or an
aggregate's `c_A` block's `h_out`, rows 2–3). -/
theorem out_cells_dec0 (κ : NodeKind) :
    (∀ σ ι, Dec0 (κ.oneCell + selR σ ι)) ∧ ∀ σ h, h < 2 → Dec0 (N4c.stC κ σ h) := by
  have h1 : κ.oneCell % 64 = 0 := by simp only [NodeKind.oneCell]; omega
  refine ⟨fun σ ι => ?_, fun σ h hh => ?_⟩
  · have : selIx ι < 3 := by cases ι <;> decide
    unfold Dec0 selR slotM4; omega
  · unfold Dec0 N4c.stC N4c.seedC
    split_ifs <;> omega

/-- (−) **The finding**: a selector and an aggregate's statement cell lie outside rows 4–7 (the
blueprint's (A)(ii)); (−) L's first signature cell (row 0) is not decoded at all. -/
theorem out_cells_rows (κ : NodeKind) :
    (κ.oneCell + selR 1 .L32) % 64 = 1 ∧ N4c.stC κ 1 0 % 64 = 2 ∧ ¬ Dec0 (N4s.sigCell κ 0 0) := by
  have h1 : κ.oneCell % 64 = 0 := by simp only [NodeKind.oneCell]; omega
  have h2 : N4c.isAgg κ 1 = true := by cases κ <;> decide
  refine ⟨by simp only [selR, selIx, slotM4]; omega, ?_, ?_⟩
  · simp only [N4c.stC, h2, if_true]; omega
  · simp only [Dec0, N4s.sigCell]; omega

/-! ## The segment count, computably -/

/-- **Aggregate `a`'s segment count, computably**: its first sub-slot (below `maxK`) whose
selector sum is not `1`, else `maxK` (the reader's `kAct`, `kSel_eq`). -/
def kSel (κ : NodeKind) (a : ℕ) (w : Circ.Asg) : ℕ :=
  ((List.range κ.maxK).find? fun i => decide ((selSum κ (N4c.sub κ a i)).ev w ≠ 1)).getD κ.maxK

theorem find_range_getD (P : ℕ → Bool) : ∀ n,
    ((List.range n).find? P).getD n = n ∧ (∀ i < n, P i = false) ∨
      ∃ j < n, ((List.range n).find? P).getD n = j ∧ P j = true ∧ ∀ i < j, P i = false
  | 0 => .inl ⟨rfl, fun i h => absurd h (Nat.not_lt_zero i)⟩
  | n + 1 => by
    rw [List.range_succ, List.find?_append]
    rcases find_range_getD P n with ⟨h1, h2⟩ | ⟨j, hj, h1, h2, h3⟩
    · have hn : (List.range n).find? P = none := by
        rw [List.find?_eq_none]; intro x hx; simp [h2 x (List.mem_range.1 hx)]
      rw [hn, Option.none_or]
      cases hP : P n
      · exact .inl ⟨by simp [hP], fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
          · exact h2 i h
          · exact hP⟩
      · exact .inr ⟨n, Nat.lt_succ_self n, by simp [hP], hP, h2⟩
    · have hs : (List.range n).find? P = some j := by
        cases h : (List.range n).find? P with
        | none =>
          rw [h] at h1; simp only [Option.getD_none] at h1; omega
        | some v => rw [h] at h1; simp only [Option.getD_some] at h1; rw [h1]
      rw [hs, Option.some_or]
      exact .inr ⟨j, by omega, rfl, h2, h3⟩

/-- **`kSel` is the reader's `kAct`.** -/
theorem kSel_eq (κ : NodeKind) (a : ℕ) (w : Circ.Asg) : kSel κ a w = N4s.kAct κ a w := by
  classical
  unfold N4s.kAct kSel
  rw [eq_comm, Nat.find_eq_iff]
  rcases find_range_getD (fun i => decide ((selSum κ (N4c.sub κ a i)).ev w ≠ 1)) κ.maxK with
    ⟨h1, h2⟩ | ⟨j, hj, h1, h2, h3⟩
  · rw [h1]
    refine ⟨.inl rfl, fun n hn => ?_⟩
    have := h2 n hn
    simp only [decide_eq_false_iff_not, not_not] at this
    rintro (h | h)
    · omega
    · exact h this
  · rw [h1]
    refine ⟨.inr (by simpa using h2), fun n hn => ?_⟩
    have := h3 n hn
    simp only [decide_eq_false_iff_not, not_not] at this
    rintro (h | h)
    · omega
    · exact h this

/-! ## The children's statements -/

/-- **Signed child `σ`'s statement** read from its cells `stC κ σ 0, 1` (`PubCells4`'s). -/
noncomputable def stD (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) : Digest :=
  Read.digestOf w (N4c.stC κ σ 0) (N4c.stC κ σ 1)

/-- **On `PubCells4` the cells hold `c₁`, `c₂`** (`digestOf_halves`): reading the statements from
`f` needs no link. -/
theorem stD_of_pubCells {κ : NodeKind} {w : Circ.Asg} {vk c₁ c₂ : Digest}
    (h : N4c.PubCells4 κ w vk c₁ c₂) : stD κ 0 w = c₁ ∧ stD κ 1 w = c₂ := by
  unfold N4c.PubCells4 at h
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq] at h
  exact ⟨Snd.digestOf_halves h.2.2.2.1 h.2.2.2.2.1, Snd.digestOf_halves h.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.1⟩

/-! ## The proof a slot's trace carries: `reassemble4` (A.5 at revision 4.1, field by field) -/

/-- `n` bytes of query `j` from byte `o` (zero past its end): every contribution has its field
size whatever the trace, so `reassemble4`'s layout is fixed. -/
def qB4 (a : Array (ByteArray × Digest)) (j o n : ℕ) : List UInt8 :=
  N4s.fitL n (Read.bl (qBytes a j o n))

/-- The ladder `m` the trace's seed declares (byte 71, `kindOfC`'s rule: `L32` if no kind byte). -/
def trM4 (a : Array (ByteArray × Digest)) : ℕ :=
  ((((a.getD 0 (ByteArray.empty, 0)).1).data[71]?).bind Snd.CKind.ofByte?).getD (.seg .L32) |>.m

/-- **Sibling `h` of a position** at the kind's ladder `m` (3.x's `sibling`, `posOps4`'s
`merkleOps4`): the node query's half chosen by bit `h` of the position below the kind's height,
32 zero bytes above it. -/
def sib4 (S : Seq) (m i h j : ℕ) (q : ByteArray) : List UInt8 :=
  if h < (S.lvK m i).sib then
    N4s.fitL 32 (Read.bl (if j / 2 ^ h % 2 = 0 then q.extract 40 72 else q.extract 8 40))
  else List.replicate 32 0

/-- Position `p`'s index at the kind's ladder (`per = 256 / logN` positions an answer). -/
def posOf4 (S : Seq) (m i : ℕ) (ans : List Digest) (p : ℕ) : ℕ :=
  idxOf (S.lvK m i).logN (ans.getD (p / (S.lvK m i).per) 0) (p % (S.lvK m i).per)

/-- **Phase `sh`'s bytes for field `f`** (3.x's `Read.ctb` over `Sh`, at `S`'s counts and the
kind's ladder `m`), its items from `ix`, the position answers `ans`. -/
def ctb4 (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest) :
    Sh → ℕ → List UInt8
  | .seed, f => if f = fHdr then qB4 a ix 71 48 else []
  | .absorb g len, f => if f = g then qB4 a ix 40 len else []
  | .squeezes _ _, _ => []
  | .uni g, f => if f = g then qB4 a ix 40 uniBytes else []
  | .rounds g n _ inK, f =>
    if f = g then (List.range n).flatMap fun j => qB4 a (ix + 2 * j) 40 (roundBytes inK) else []
  | .queries i, f =>
    if f = fCols then (List.range (S.lv i).t).flatMap fun p =>
      qB4 a (ix + (1 + (S.lv i).sib) * p) 8 (colBytes i)
    else if f = fSibs then (List.range (S.lv i).t).flatMap fun p =>
      (List.range (S.lv i).sib).flatMap fun h =>
        sib4 S m i h (posOf4 S m i ans p) ((a.getD (ix + (1 + (S.lv i).sib) * p + 1 + h) (ByteArray.empty, 0)).1)
    else []

/-- The position answers after phase `sh` (a `P2` phase's squeezes). -/
def ansOf4 (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest) : Sh → List Digest
  | .squeezes n (.pos _) => (List.range n).map fun j => (a.getD (ix + j) (ByteArray.empty, 0)).2
  | _ => ans

/-- **The phases' bytes for field `f`**, from item `ix` with the answers `ans`. -/
def ctbs4 (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) : ℕ → List Digest → List Sh → ℕ → List UInt8
  | _, _, [], _ => []
  | ix, ans, sh :: shs, f =>
    ctb4 S m a ix ans sh f ++ ctbs4 S m a (ix + (sh.itemsL S.lv).length) (ansOf4 a ix ans sh) shs f

/-- **`reassemble4 S tr`** (A.5 at revision 4.4.1; S-N2's `pf`): the proof the trace `tr` of `S`'s
items carries, field by field: fields `0 … 19` (A.3's rows, `D` and `A` the last two; `ctbs4` over
`phasesOf S`). -/
def reassemble4 (S : Seq) (tr : Trace) : Proof :=
  let a := tr.toArray
  let shs := (phasesOf S).map Prod.snd
  ⟨((List.range nFields4).flatMap (fun f => ctbs4 S (trM4 a) a 0 [] shs f)).toArray⟩

/-- **The slots' proof decoder** (S-N2's `pf`, the reader `rd4 pf4`): `reassemble4` at `seq4`. -/
def pf4 : Trace → Proof := reassemble4 seq4

/-- Byte 0 of an `n`-byte fitted extract from `o` is byte `o` (`0` past the end). -/
theorem fitL_extract_getD (b : ByteArray) (o n : ℕ) (hn : 0 < n) :
    (N4s.fitL n (Read.bl (b.extract o (o + n)))).getD 0 0 = byteAt b o := by
  unfold N4s.fitL Read.bl byteAt
  rw [ByteArray.data_extract, Array.toList_extract, List.extract, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hn]
  split_ifs with h
  · have hl : 0 < (List.take n (List.drop o b.data.toList)).length := by
      simp only [List.length_take, List.length_drop, Array.length_toList]
      have : b.size = b.data.size := rfl
      omega
    rw [List.getElem?_append_left hl, List.getElem?_take, if_pos hn, List.getElem?_drop, Nat.add_zero]
    simp only [Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem (by exact h)]
    rfl
  · have hl : (List.take n (List.drop o b.data.toList)) = [] := by
      simp only [List.take_eq_nil_iff, List.drop_eq_nil_iff, Array.length_toList]
      right; have : b.size = b.data.size := rfl; omega
    rw [hl, List.nil_append, List.getElem?_replicate, if_pos hn]
    rfl
/-- **`reassemble4` meets S-E13a's `PfHdr`** (`N4s.PfHdr (reassemble4 seq4)` is this statement):
byte 0 of the proof is byte 71 of the seed query (`hdr`'s first byte, the kind byte). -/
theorem pfHdr_reassemble4 (e : ByteArray × Digest) (tr : Trace) :
    byteAt (reassemble4 seq4 (e :: tr)) 0 = byteAt e.1 71 := by
  have h0 : (phasesOf seq4).map Prod.snd = .seed :: ((phasesOf seq4).tail.map Prod.snd) := by
    rw [phasesOf]; rfl
  have hl : (qB4 (e :: tr).toArray 0 71 48).length = 48 := N4s.fitL_length _ _
  rw [reassemble4, N4s.byteAt_mk]
  simp only [h0, nFields4, List.range_succ_eq_map, List.flatMap_cons, ctbs4, ctb4, fHdr, if_true,
    List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hl]; norm_num),
    ← List.getD_eq_getElem?_getD, qB4, qBytes]
  exact fitL_extract_getD _ _ _ (by norm_num)

theorem flatMap_const_length {α : Type} (l : List α) (g : α → List UInt8) (n : ℕ)
    (h : ∀ x ∈ l, (g x).length = n) : (l.flatMap g).length = l.length * n := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, h x (by simp), ih fun y hy => h y (by simp [hy]),
      List.length_cons]
    ring

theorem sib4_length (S : Seq) (m i h j : ℕ) (q : ByteArray) : (sib4 S m i h j q).length = 32 := by
  unfold sib4; split_ifs <;> simp [N4s.fitL_length]

/-- Each contribution has its field size (`Sh.bytesToL`), whatever the trace. -/
theorem ctb4_length (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest)
    (sh : Sh) (f : ℕ) : (ctb4 S m a ix ans sh f).length = sh.bytesToL S.lv f := by
  cases sh with
  | seed => simp only [ctb4, Sh.bytesToL]; split_ifs <;> simp [qB4, N4s.fitL_length]
  | absorb g len => simp only [ctb4, Sh.bytesToL]; split_ifs <;> simp [qB4, N4s.fitL_length]
  | squeezes n ch => rfl
  | uni g => simp only [ctb4, Sh.bytesToL]; split_ifs <;> simp [qB4, N4s.fitL_length]
  | rounds g n d inK =>
    simp only [ctb4, Sh.bytesToL]; split_ifs
    · rw [flatMap_const_length _ _ (roundBytes inK) fun _ _ => by simp [qB4, N4s.fitL_length],
        List.length_range]
    · rfl
  | queries i =>
    simp only [ctb4, Sh.bytesToL]; split_ifs
    · rw [flatMap_const_length _ _ (colBytes i) fun _ _ => by simp [qB4, N4s.fitL_length],
        List.length_range]
    · rw [flatMap_const_length _ _ ((S.lv i).sib * 32) fun _ _ => by
        rw [flatMap_const_length _ _ 32 fun _ _ => sib4_length .., List.length_range], List.length_range,
        Nat.mul_assoc]
    · rfl

theorem ctbs4_length (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (f : ℕ) :
    ∀ (shs : List Sh) (ix : ℕ) (ans : List Digest),
      (ctbs4 S m a ix ans shs f).length = (shs.map fun sh => sh.bytesToL S.lv f).sum
  | [], _, _ => rfl
  | sh :: shs, ix, ans => by
    rw [ctbs4, List.length_append, ctb4_length, ctbs4_length S m a f shs, List.map_cons, List.sum_cons]

/-- **`reassemble4`'s size is the format's** (`piSizeOf S`), on every trace. -/
theorem reassemble4_size (S : Seq) (tr : Trace) : (reassemble4 S tr).size = piSizeOf S := by
  simp only [reassemble4, ByteArray.size, List.size_toArray, List.length_flatMap, ctbs4_length, piSizeOf,
    fieldSizeOf, List.map_map]
  rfl

/-- Byte `j < n` of an `n`-byte fitted extract from `o` is byte `o + j` (`0` past the end). -/
theorem fitL_extract_getDj (b : ByteArray) (o n : ℕ) {j : ℕ} (hj : j < n) :
    (N4s.fitL n (Read.bl (b.extract o (o + n)))).getD j 0 = byteAt b (o + j) := by
  unfold N4s.fitL Read.bl byteAt
  rw [ByteArray.data_extract, Array.toList_extract, List.extract, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj]
  have hs : b.size = b.data.size := rfl
  split_ifs with h
  · have hl : j < (List.take n (List.drop o b.data.toList)).length := by
      simp only [List.length_take, List.length_drop, Array.length_toList]
      omega
    rw [List.getElem?_append_left hl, List.getElem?_take, if_pos hj, List.getElem?_drop]
    simp only [Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem (by exact h)]
    rfl
  · have hl : (List.take n (List.drop o b.data.toList)).length ≤ j := by
      simp only [List.length_take, List.length_drop, Array.length_toList]
      omega
    rw [List.getElem?_append_right hl, List.getElem?_replicate, if_pos (by omega)]
    rfl

/-- `seq4`'s first two phases: the seed (`hdr`) and the statement's absorb (`stmt`, 128 bytes). -/
theorem phasesOf_seq4_two : ∃ rest, (phasesOf seq4).map Prod.snd = .seed :: .absorb fStmt 128 :: rest :=
  ⟨_, rfl⟩

/-- **`reassemble4` meets B4's `PfView`** (`N4s.PfView (reassemble4 seq4)` is this statement): the
proof's bytes `0 … 47` are the seed query's bytes `71 … 118` (`hdr`, field 0) and its bytes
`48 … 175` the second query's message bytes `40 … 167` (`stmt`, field 1; field 0 has 48 bytes,
`fieldSizesOf_seq4`). -/
theorem pfView_reassemble4 (e₀ e₁ : ByteArray × Digest) (tr : Trace) :
    (∀ j < 48, byteAt (reassemble4 seq4 (e₀ :: e₁ :: tr)) j = byteAt e₀.1 (71 + j)) ∧
      ∀ j < 128, byteAt (reassemble4 seq4 (e₀ :: e₁ :: tr)) (48 + j) = byteAt e₁.1 (40 + j) := by
  obtain ⟨rest, h0⟩ := phasesOf_seq4_two
  have hr : List.range nFields4 = 0 :: 1 :: List.range' 2 18 := rfl
  have hF0 : fieldSizeOf seq4 0 = 48 := by
    have h := congrArg (·[0]?) fieldSizesOf_seq4
    simpa only [List.getElem?_map, List.getElem?_range (show 0 < nFields4 by decide), Option.map_some,
      List.getElem?_cons_zero, Option.some.injEq] using h
  have hlq : ∀ a i o n, (qB4 a i o n).length = n := fun _ _ _ _ => N4s.fitL_length _ _
  have hq : ∀ (a : Array (ByteArray × Digest)) (i o n : ℕ) {e : ByteArray × Digest},
      a.getD i (ByteArray.empty, 0) = e → ∀ j < n, (qB4 a i o n).getD j 0 = byteAt e.1 (o + j) :=
    fun a i o n e he j hj => by rw [qB4, qBytes, he]; exact fitL_extract_getDj _ _ _ hj
  have hl0 : ∀ a, (ctbs4 seq4 (trM4 a) a 0 [] ((phasesOf seq4).map Prod.snd) 0).length = 48 := fun a => by
    rw [ctbs4_length, List.map_map, ← hF0, fieldSizeOf]; rfl
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;> rw [reassemble4, N4s.byteAt_mk] <;>
    simp only [hr, List.flatMap_cons]
  · rw [List.getD_append _ _ _ _ (by rw [hl0]; exact hj), h0, ctbs4, ctb4, fHdr, if_pos rfl,
      List.getD_append _ _ _ _ (by rw [hlq]; exact hj)]
    exact hq _ 0 71 48 rfl j hj
  · rw [List.getD_append_right _ _ _ _ (by rw [hl0]; omega), hl0, Nat.add_sub_cancel_left, h0, ctbs4,
      ctbs4, ctb4, if_neg (by decide : (1 : ℕ) ≠ fHdr), List.nil_append, ctb4, fStmt, if_pos rfl,
      List.append_assoc, List.getD_append _ _ _ _ (by rw [hlq]; exact hj)]
    exact hq _ _ 40 128 rfl j hj

/-! ## The decoder's links and the witness it outputs (the target of `NodeDec4 nd`) -/

/-- **The decode law's links** (`NodeDec4.Links` of `nd`): exactly `decF04_sem`'s hypotheses on
the log `L` and the transcript `es` the verifier's run reads off it, the chain's initial state
existential. S-L4 discharges them in `Links4` (`hL_of_res`). -/
def LinksD4 (κ : NodeKind) (L es : Log) (π : Proof) (c : Digest) : Prop :=
  ¬ StateHit L ∧
    (∃ st₀, ∀ p < nRep4, fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p)) ∧
    (∀ i < 5, ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, T4.capDig es i e = capPi4 i π e) ∧
    (∀ x < 2 ^ T4.mLog (.node κ) 4, T4.finalAt es x = finPi4 π x) ∧
    (∀ i < 5, ¬ T4.farL (.node κ) L es i) ∧
    ∀ i < 5, T4.consSet (.node κ) L es i =
      jointAgree (T4.wordK (.node κ) L es i) (T4.decodeL (.node κ) L es i)

/-- **Signed child `σ` as the decoder outputs it**: the reader's proof and trace (`rd4 pf4`), the
signature from H by `sg` (revision 4.3: L is not decoded, `out_cells_rows`; `sg` is the H cell map
of S-G/S-E's `sig_of_H`). -/
noncomputable def sgnX (sg : NodeKind → ℕ → Circ.Asg → Sig) (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) :
    Signed :=
  ⟨((N4s.rd4 pf4).sgn κ σ w).π, ((N4s.rd4 pf4).sgn κ σ w).tr, sg κ σ w⟩

/-- **The node witness the decoder outputs** (`NodeDec4.readW` of `nd`): the statements from their
cells (`stD`), both signed children (`sgnX`), on `f⁽⁰⁾ = wF κ L es`. -/
noncomputable def readW4 (sg : NodeKind → ℕ → Circ.Asg → Sig) (κ : NodeKind) (L es : Log) : Wit :=
  .node (stD κ 0 (wF κ L es)) (stD κ 1 (wF κ L es)) (sgnX sg κ 0 (wF κ L es)) (sgnX sg κ 1 (wF κ L es))

/-- **Where `sg` agrees with L's signature** (`sig_of_H`), `sgnX` is the reader's signed child. -/
theorem sgnX_eq {sg : NodeKind → ℕ → Circ.Asg → Sig} {κ : NodeKind} {σ : ℕ} {w : Circ.Asg}
    (h : sg κ σ w = N4s.readSig4 κ σ w) : sgnX sg κ σ w = (N4s.rd4 pf4).sgn κ σ w := by
  have e : ((N4s.rd4 pf4).sgn κ σ w).σ = N4s.readSig4 κ σ w := by
    simp only [N4s.rd4, N4s.sgn4]; split_ifs <;> rfl
  rw [sgnX, h, ← e]

/-- **On `PubCells4` and `sig_of_H`, `readW4` is the reader's node witness** at the statement's
`c₁`, `c₂` (what `node_sound4` proves a witness of the relation). -/
theorem readW4_eq {sg : NodeKind → ℕ → Circ.Asg → Sig} {κ : NodeKind} {L es : Log} {vk c₁ c₂ : Digest}
    (hP : N4c.PubCells4 κ (wF κ L es) vk c₁ c₂)
    (hs : ∀ σ < 2, sg κ σ (wF κ L es) = N4s.readSig4 κ σ (wF κ L es)) :
    readW4 sg κ L es = .node c₁ c₂ ((N4s.rd4 pf4).sgn κ 0 (wF κ L es)) ((N4s.rd4 pf4).sgn κ 1 (wF κ L es)) := by
  obtain ⟨h1, h2⟩ := stD_of_pubCells hP
  rw [readW4, h1, h2, sgnX_eq (hs 0 (by norm_num)), sgnX_eq (hs 1 (by norm_num))]

/-! ## Controls -/

/-- (value) **`reassemble4` has the format's size** at `seq4` on rev44: `876,304` bytes, on every
trace (the empty one included). -/
theorem pf4_size (tr : Trace) : (pf4 tr).size = 876304 := by
  rw [pf4, reassemble4_size, piSizeOf_seq4]

/-- (+/−) **`pf4` reads the kind byte from the seed query**: a seed query whose byte 71 is `N4`'s
byte gives a proof starting with it; one whose byte 71 is `0` does not. -/
theorem pf4_hdr_ctl (q : ByteArray) (d : Digest) (tr : Trace) (h : q.size = 72) (hb : q[71]'(by omega) = NodeKind.N4.byte) :
    byteAt (pf4 ((q, d) :: tr)) 0 = NodeKind.N4.byte ∧ byteAt (pf4 ((ByteArray.mk (Array.replicate 72 0), d) :: tr)) 0 ≠ NodeKind.N4.byte := by
  refine ⟨?_, ?_⟩
  · rw [pf4, pfHdr_reassemble4, byteAt, dif_pos (show 71 < q.size by omega)]; exact hb
  · rw [pf4, pfHdr_reassemble4]; simp only; decide

/-- (−) **The segment count is the first unselected sub-slot**: on the all-zero witness every
selector sum is `0 ≠ 1`, so `kSel = 0`; (+) `kSel ≤ maxK` always. -/
theorem kSel_ctl (κ : NodeKind) (a : ℕ) (w : Circ.Asg) : kSel κ a (fun _ => 0) = 0 ∧ kSel κ a w ≤ κ.maxK := by
  refine ⟨?_, ?_⟩
  · have hp : 0 < κ.maxK := by cases κ <;> decide
    unfold kSel
    obtain ⟨n, hn⟩ : ∃ n, κ.maxK = n + 1 := ⟨κ.maxK - 1, by omega⟩
    rw [hn, List.range_succ_eq_map, List.find?_cons]
    simp [selSum, Circ.Lin.ev, Circ.Lin.cell]
  · rw [kSel_eq]; exact N4s.kAct_le κ a w

end FR.X
