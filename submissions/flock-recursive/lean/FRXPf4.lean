-- G6: this module also holds the former modules `FRXOut4`, `FRXSig4`, `FRXSig4W`, `FRXTr4` (one section each, in import order).
import FRXDec4F0
import FRNodeRun4
import FRNodeRows4WotsB
import FRXOut

section G6_FRXOut4

-- New for `flock-recursive` (BLUEPRINT revision 4.3, §6.2 step 5, A.7; stage S-H4, pass 7, item 1:
-- the node output's cell map). 3.x analogue: `FRNodeRead` (`readStmt`), `FRXOutRun` (`src_stream`).

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

end G6_FRXOut4

section G6_FRXSig4

-- New for `flock-recursive` (BLUEPRINT revision 4.3, (A)(ii), A.6, A.8 `linkW`; stage S-H4, pass 8,
-- item 1: the signature the node decoder outputs). 3.x analogue: `FRNodeRead.readSig` (L cells).

/-!
# The signature read off H's message slots (`sigH`)

L is not decoded (`out_cells_rows`), so the decoder reads a signed child's signature from the H
blocks of its WOTS run (revision 4.3, (A)(ii)), whose message slots are rows 4–7 of `f⁽⁰⁾`:

* **the index** is the key leaf's `j` field: message bytes `1 … 8` of WOTS block `399`, little
  endian (the `j` family);
* **`ots_i`** is chain `i`'s first step block's `x` field: message bytes `11 … 42` of WOTS block
  `3i` (the `x` family);
* **path sibling `t`** is the level's `l` field (message bytes `1 … 32` of block `466 + 2t`) when
  bit `t` of the index is `1`, else its `r` field: bytes `33 … 63` of block `466 + 2t` and byte `0`
  of block `467 + 2t` (the `r0`, `r31` families).

`FRXSig4H.sig_of_H` proves it L's signature (`readSig4`) on every witness of the node statement.
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

/-- **Message byte `p` (`p < 64`) of H block `b`**: byte `p mod 16` of element `4 + ⌊p/16⌋`. -/
def hMB (w : Circ.Asg) (b p : ℕ) : UInt8 := W4.fb (w (W4.hc b (4 + p / 16))) (p % 16)

/-- The 32 message bytes of H block `b` from byte `o`. -/
def hMD (w : Circ.Asg) (b o : ℕ) : Digest := Vector.ofFn fun i : Fin 32 => hMB w b (o + i)

/-- **The index** (the key leaf's `j` field, little endian). -/
def idxH (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) : ℕ :=
  ofLE ((List.range 8).map fun k => hMB w (W4.wb κ σ 399) (1 + k))

/-- **Path level `t`'s `r` field**: bytes `33 … 63` of `hashB1`'s block, byte `0` of `hashB2`'s. -/
def rFH (κ : NodeKind) (σ t : ℕ) (w : Circ.Asg) : Digest :=
  Vector.ofFn fun i : Fin 32 =>
    if i.val < 31 then hMB w (W4.wb κ σ (466 + 2 * t)) (33 + i) else hMB w (W4.wb κ σ (467 + 2 * t)) 0

/-- **Path sibling `t`**: the `l` field if bit `t` of the index is `1`, else the `r` field. -/
def sibFH (κ : NodeKind) (σ t : ℕ) (w : Circ.Asg) : Digest :=
  if idxH κ σ w / 2 ^ t % 2 = 1 then hMD w (W4.wb κ σ (466 + 2 * t)) 1 else rFH κ σ t w

/-- **Signed child `σ`'s signature read off H** (revision 4.3, (A)(ii)). -/
def sigH (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) : Sig where
  idx := idxH κ σ w
  ots := (List.range wotsLen).map fun i => hMD w (W4.wb κ σ (3 * i)) 11
  path := (List.range sigHeight).map fun t => sibFH κ σ t w

/-- `hMB` is the block's message byte (`msgByte_hc`). -/
theorem hMB_eq (w : Circ.Asg) (b : ℕ) {p : ℕ} (hp : p < 64) :
    hMB w b p = (Block.msgBytes (N4c.bitsB4 w b)).getD p 0 := (W4.msgByte_hc w b hp).symm

/-- **Every cell `sigH` reads is decoded** (a message slot of an H block: rows 4–7). -/
theorem hMB_dec0 (b p : ℕ) (hp : p < 64) : Dec0 (W4.hc b (4 + p / 16)) := by
  unfold Dec0 W4.hc; omega

/-! ## Controls -/

/-- A witness whose key-leaf message element 4 (child `0`) is `256` (byte 1 is `1`), zero
elsewhere. -/
def wIdx1 (κ : NodeKind) : Circ.Asg := fun e => if e = W4.hc (W4.wb κ 0 399) 4 then ⟨⟨256⟩, ⟨0⟩⟩ else 0

/-- (+/−) **`sigH` reads H, not L**: on `wIdx1` the index read off H is `1` while L's index cell
is `0` (so `sig_of_H` needs the rows: the two readers differ off the statement); on the zero
witness the index is `0`. -/
theorem sigH_ctl : (sigH .N2 0 (wIdx1 .N2)).idx = 1 ∧ (N4s.readSig4 .N2 0 (wIdx1 .N2)).idx = 0 ∧
    (sigH .N2 0 (fun _ => 0)).idx = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end FR.X

end G6_FRXSig4

section G6_FRXSig4W

-- New for `flock-recursive` (BLUEPRINT revision 4.3, §6.2 step 5, (A)(ii); stage S-H4, pass 8,
-- item 2, the signature's half: its output words over H's message words). 3.x analogue:
-- `FRNodeReadW.sigWords_readSig` (L words), `FRNodeReadS.shw_bytes` (one byte of shift).

/-!
# The signature's output words as shifted H message words

H's message slots form a **byte stream**: byte `p` is message byte `p mod 64` of block `⌊p/64⌋`
(`hMBs`). Its **words** `hMW w n` (word `n mod 8` of block `⌊n/8⌋`'s message) are heap words after
the decode: word `n mod 2` of element `4 + (n mod 8)/2`, i.e. the address shape of 3.x's stream
words (`FRXOut.addrW` with `(m₁, s₃, s₄) = (3, 3, 2)`) at level 0's row stride.

A field at byte `8n + s` straddles words `n`, `n + 1`; the machine reads it as
`shWd W s n = (W n >>> 8s) + (W (n + 1) <<< (64 − 8s))` (**`wOf_hBs`**, any shift `0 < s < 8`).

**`sigWords_sigH`**: `sigWords (sigH κ σ w)` is the index's word (shift 1 at block `399`), then
four words per chain value (shift 3 from word 1 of block `3i`), then four per sibling (shift 1 from
word 0 of block `466 + 2t` for an index bit `1`, word 4 for `0`: the `r` field runs into block
`467 + 2t`, the next one, as the stream does).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

/-! ## The H message stream -/

/-- **Byte `p` of the H message stream**: message byte `p mod 64` of block `⌊p/64⌋`. -/
def hMBs (w : Circ.Asg) (p : ℕ) : UInt8 := hMB w (p / 64) (p % 64)

/-- **Word `n` of the H message stream**: word `n mod 2` of element `4 + (n mod 8)/2` of block
`⌊n/8⌋`. -/
def hMW (w : Circ.Asg) (n : ℕ) : Word :=
  (Read.elemWords (w (W4.hc (n / 8) (4 + n % 8 / 2)))).getD (n % 2) 0

/-- **The word at byte `8n + s`** of a word stream (`0 < s < 8`), as the machine assembles it. -/
def shWd (W : ℕ → Word) (s n : ℕ) : Word := (W n >>> (8 * s)) + (W (n + 1) <<< (64 - 8 * s))

/-- The word of the bytes `f 0, …, f 7` (little endian). -/
def wOf (f : ℕ → UInt8) : Word := toWord (ofLE ((List.range 8).map f))

/-! ## Bytes of words -/

/-- Byte `k` of a word is its `k`-th base-256 digit. -/
theorem wordBytes_getD (v : Word) {k : ℕ} (hk : k < 8) :
    (wordBytes v).getD k 0 = (v.toNat / 256 ^ k % 256).toUInt8 := by
  rw [wordBytes, enc64, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn, toUInt8_mod]

/-- **An element's words' bytes are its bytes.** -/
theorem elemWords_byte (a : F) {j k : ℕ} (hj : j < 2) (hk : k < 8) :
    (wordBytes ((Read.elemWords a).getD j 0)).getD k 0 = W4.fb a (8 * j + k) := by
  have h := wordsBytes_elemWords (F.toBytes a)
  rw [F.ofBytes_toBytes] at h
  have e : (wordsBytes (Read.elemWords a)).getD (8 * j + k) 0 = W4.fb a (8 * j + k) := by
    rw [h, W4.fb, List.getD_eq_getElem _ _ (by simp; omega)]
    simp [Nat.mod_eq_of_lt (show 8 * j + k < 16 by omega)]
  rw [← e]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · simp only [Read.elemWords, List.getD_cons_zero, wordsBytes, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Nat.mul_zero, Nat.zero_add]
    rw [List.getD_append _ _ _ _ (by rw [wordBytes_length]; exact hk)]
  · simp only [Read.elemWords, List.getD_cons_succ, List.getD_cons_zero, wordsBytes, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Nat.mul_one]
    rw [List.getD_append_right _ _ _ _ (by rw [wordBytes_length]; omega), wordBytes_length,
      show 8 + k - 8 = k by omega]

/-- **Byte `k` of H message word `n`** is stream byte `8n + k`. -/
theorem hMW_byte (w : Circ.Asg) (n : ℕ) {k : ℕ} (hk : k < 8) :
    (wordBytes (hMW w n)).getD k 0 = hMBs w (8 * n + k) := by
  rw [hMW, elemWords_byte _ (Nat.mod_lt _ (by norm_num)) hk, hMBs, hMB]
  congr 3 <;> omega

/-- **A word is determined by its bytes.** -/
theorem wOf_eq {f : ℕ → UInt8} {v : Word} (h : ∀ k < 8, (wordBytes v).getD k 0 = f k) : wOf f = v := by
  have hl : (List.range 8).map f = wordBytes v := by
    refine List.ext_getElem (by simp [wordBytes_length]) fun k h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, ← h k h1, List.getD_eq_getElem _ _ h2]
  rw [wOf, hl, ofLE_wordBytes]
  exact BitVec.eq_of_toNat_eq (toNat_toWord v.isLt)

/-- The digits of `a / 2^(8s) + b · 2^(64 − 8s)` (`a < 2^64`, `b < 2^(8s)`). -/
theorem shift_digit {a b s k : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ (8 * s)) (hs : s < 8) (hk : k < 8) :
    (a / 2 ^ (8 * s) + b * 2 ^ (64 - 8 * s)) / 256 ^ k % 256 =
      if k < 8 - s then a / 256 ^ (s + k) % 256 else b / 256 ^ (k + s - 8) % 256 := by
  have p256 : ∀ n, (256 : ℕ) ^ n = 2 ^ (8 * n) := fun n => by rw [pow_mul]; norm_num
  split_ifs with h
  · -- `b`'s part is a multiple of `256^(k+1)`
    obtain ⟨c, hc⟩ : ∃ c, 2 ^ (64 - 8 * s) = 256 ^ (k + 1) * c :=
      ⟨2 ^ (64 - 8 * s - 8 * (k + 1)), by rw [p256, ← pow_add]; congr 1; omega⟩
    rw [hc, show b * (256 ^ (k + 1) * c) = 256 ^ k * (256 * (b * c)) by ring,
      Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, Nat.div_div_eq_div_mul,
      p256, p256, ← pow_add, show 8 * s + 8 * k = 8 * (s + k) by ring]
  · -- `a`'s part is below `256^k`
    have h1 : a / 2 ^ (8 * s) < 256 ^ (8 - s) := by
      rw [p256, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      exact ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ (64 - 8 * s) = 256 ^ (8 - s) := by rw [p256]; congr 1; omega
    have h3 : (256 : ℕ) ^ k = 256 ^ (8 - s) * 256 ^ (k + s - 8) := by rw [← pow_add]; congr 1; omega
    rw [h2, h3, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt h1, Nat.zero_add]

/-- **The shifted pair's bytes**: bytes `s … 7` of the first word, then bytes `0 … s − 1` of the
second (`0 < s < 8`). -/
theorem shWd_byte (W : ℕ → Word) {s : ℕ} (hs0 : 0 < s) (hs : s < 8) (n : ℕ) {k : ℕ} (hk : k < 8) :
    (wordBytes (shWd W s n)).getD k 0 = if k < 8 - s then (wordBytes (W n)).getD (s + k) 0
      else (wordBytes (W (n + 1))).getD (k + s - 8) 0 := by
  have ha := (W n).isLt
  have hb := (W (n + 1)).isLt
  have e : (shWd W s n).toNat = (W n).toNat / 2 ^ (8 * s) + (W (n + 1)).toNat % 2 ^ (8 * s) * 2 ^ (64 - 8 * s) := by
    have hm : (W (n + 1)).toNat * 2 ^ (64 - 8 * s) % 2 ^ 64 =
        (W (n + 1)).toNat % 2 ^ (8 * s) * 2 ^ (64 - 8 * s) := by
      rw [show (2 : ℕ) ^ 64 = 2 ^ (8 * s) * 2 ^ (64 - 8 * s) by rw [← pow_add]; congr 1; omega,
        Nat.mul_mod_mul_right]
    have hlt : (W n).toNat / 2 ^ (8 * s) + (W (n + 1)).toNat % 2 ^ (8 * s) * 2 ^ (64 - 8 * s) < 2 ^ 64 := by
      have h1 : (W n).toNat / 2 ^ (8 * s) < 2 ^ (64 - 8 * s) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
        exact ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : (W (n + 1)).toNat % 2 ^ (8 * s) < 2 ^ (8 * s) := Nat.mod_lt _ (by positivity)
      calc _ < 2 ^ (64 - 8 * s) + (2 ^ (8 * s) - 1) * 2 ^ (64 - 8 * s) := by
              have := Nat.mul_le_mul_right (2 ^ (64 - 8 * s)) (Nat.le_sub_one_of_lt h2); omega
        _ = 2 ^ 64 := by
              rw [Nat.sub_one_mul, ← pow_add, show 8 * s + (64 - 8 * s) = 64 by omega]
              have : 2 ^ (64 - 8 * s) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
    simp only [shWd, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [hm, Nat.mod_eq_of_lt hlt]
  rw [wordBytes_getD _ hk, e, shift_digit ha (Nat.mod_lt _ (by positivity)) hs hk]
  split_ifs with h
  · rw [wordBytes_getD _ (by omega)]
  · rw [wordBytes_getD _ (by omega)]
    have h4 : (2 : ℕ) ^ (8 * s) = 256 ^ (k + s - 8) * 256 ^ (8 - k) := by
      rw [← pow_add, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]; congr 1; omega
    rw [h4, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega : 8 - k ≠ 0))]

/-- `wOf` reads only bytes `0 … 7`. -/
theorem wOf_congr {f g : ℕ → UInt8} (h : ∀ k < 8, f k = g k) : wOf f = wOf g := by
  unfold wOf; congr 2; exact List.map_congr_left fun k hk => h k (List.mem_range.1 hk)

/-- **The machine's shifted pair is the stream's word at byte `8n + s`** (`0 < s < 8`). -/
theorem wOf_hMBs (w : Circ.Asg) {s : ℕ} (hs0 : 0 < s) (hs : s < 8) (n : ℕ) :
    wOf (fun k => hMBs w (8 * n + s + k)) = shWd (hMW w) s n := by
  refine wOf_eq fun k hk => ?_
  rw [shWd_byte _ hs0 hs n hk]
  split_ifs with h
  · rw [hMW_byte _ _ (by omega), Nat.add_assoc]
  · rw [hMW_byte _ _ (by omega)]; congr 1; omega

/-- **A 32-byte digest's words** are its four 8-byte groups. -/
theorem packBytes_ofFn32 (f : ℕ → UInt8) :
    packBytes (Vector.ofFn fun i : Fin 32 => f i).toList = (List.range 4).map fun j => wOf fun k => f (8 * j + k) := by
  rw [Vector.toList_ofFn, packBytes, List.length_ofFn]
  refine List.map_congr_left fun j hj => ?_
  have hj4 := List.mem_range.1 hj
  unfold wOf; congr 2
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- **A digest at stream byte `8m + s`** is four shifted pairs from word `m`. -/
theorem packBytes_hMBs (w : Circ.Asg) {s : ℕ} (hs0 : 0 < s) (hs : s < 8) (m : ℕ) {d : Digest}
    (h : ∀ i (hi : i < 32), d[i] = hMBs w (8 * m + s + i)) :
    packBytes d.toList = (List.range 4).map fun j => shWd (hMW w) s (m + j) := by
  have hd : d = Vector.ofFn fun i : Fin 32 => hMBs w (8 * m + s + i) :=
    Vector.ext fun i hi => by rw [Vector.getElem_ofFn, h i hi]
  rw [hd, packBytes_ofFn32 (fun i => hMBs w (8 * m + s + i))]
  refine List.map_congr_left fun j _ => ?_
  rw [← wOf_hMBs w hs0 hs]
  exact wOf_congr fun k _ => by congr 1; ring

/-- Stream byte `64b + p` (`p < 64`) is message byte `p` of block `b`. -/
theorem hMBs_blk (w : Circ.Asg) (b : ℕ) {p : ℕ} (hp : p < 64) : hMBs w (64 * b + p) = hMB w b p := by
  unfold hMBs; congr 1 <;> omega

/-! ## The signature's words -/

/-- **`sigWords (sigH κ σ w)` as shifted H message words**: the index (shift 1 from word `8·b₃₉₉`),
per chain four words (shift 3 from word `8·b_{3i} + 1`), per level four words (shift 1 from word
`8·b_{466+2t}`, `+ 4` when the index bit is `0`). -/
theorem sigWords_sigH (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) :
    sigWords (sigH κ σ w) =
      shWd (hMW w) 1 (8 * W4.wb κ σ 399) ::
        ((List.range wotsLen).flatMap fun i => (List.range 4).map fun j =>
          shWd (hMW w) 3 (8 * W4.wb κ σ (3 * i) + 1 + j)) ++
        (List.range sigHeight).flatMap fun t => (List.range 4).map fun j =>
          shWd (hMW w) 1 (8 * W4.wb κ σ (466 + 2 * t) + (if idxH κ σ w / 2 ^ t % 2 = 1 then 0 else 4) + j) := by
  have hb1 : ∀ t, W4.wb κ σ (467 + 2 * t) = W4.wb κ σ (466 + 2 * t) + 1 := fun t => by unfold W4.wb; omega
  have e1 : toWord (sigH κ σ w).idx = shWd (hMW w) 1 (8 * W4.wb κ σ 399) := by
    show wOf (fun k => hMB w (W4.wb κ σ 399) (1 + k)) = _
    rw [← wOf_hMBs w (by norm_num) (by norm_num)]
    exact wOf_congr fun k hk => by
      rw [show 8 * (8 * W4.wb κ σ 399) + 1 + k = 64 * W4.wb κ σ 399 + (1 + k) by ring, hMBs_blk _ _ (by omega)]
  have e2 : (sigH κ σ w).ots.flatMap (fun d => packBytes d.toList) =
      (List.range wotsLen).flatMap fun i => (List.range 4).map fun j =>
        shWd (hMW w) 3 (8 * W4.wb κ σ (3 * i) + 1 + j) := by
    show ((List.range wotsLen).map fun i => hMD w (W4.wb κ σ (3 * i)) 11).flatMap _ = _
    rw [List.flatMap_map]
    refine List.flatMap_congr fun i _ => ?_
    refine packBytes_hMBs w (by norm_num) (by norm_num) _ fun q hq => ?_
    rw [hMD, Vector.getElem_ofFn,
      show 8 * (8 * W4.wb κ σ (3 * i) + 1) + 3 + q = 64 * W4.wb κ σ (3 * i) + (11 + q) by ring,
      hMBs_blk _ _ (by omega)]
  have e3 : (sigH κ σ w).path.flatMap (fun d => packBytes d.toList) =
      (List.range sigHeight).flatMap fun t => (List.range 4).map fun j =>
        shWd (hMW w) 1 (8 * W4.wb κ σ (466 + 2 * t) + (if idxH κ σ w / 2 ^ t % 2 = 1 then 0 else 4) + j) := by
    show ((List.range sigHeight).map fun t => sibFH κ σ t w).flatMap _ = _
    rw [List.flatMap_map]
    refine List.flatMap_congr fun t _ => ?_
    refine packBytes_hMBs w (by norm_num) (by norm_num) _ fun q hq => ?_
    unfold sibFH
    split_ifs with hbit
    · rw [hMD, Vector.getElem_ofFn, show 8 * (8 * W4.wb κ σ (466 + 2 * t) + 0) + 1 + q =
        64 * W4.wb κ σ (466 + 2 * t) + (1 + q) by ring, hMBs_blk _ _ (by omega)]
    · rw [rFH, Vector.getElem_ofFn]
      dsimp only
      by_cases h31 : q < 31
      · rw [if_pos h31, show 8 * (8 * W4.wb κ σ (466 + 2 * t) + 4) + 1 + q =
          64 * W4.wb κ σ (466 + 2 * t) + (33 + q) by ring, hMBs_blk _ _ (by omega)]
      · have k31 : q = 31 := by omega
        rw [if_neg h31, k31, hb1, show 8 * (8 * W4.wb κ σ (466 + 2 * t) + 4) + 1 + 31 =
          64 * (W4.wb κ σ (466 + 2 * t) + 1) + 0 by ring, hMBs_blk _ _ (by norm_num)]
  rw [sigWords, e1, e2, e3]

/-! ## The H message words on the heap -/

/-- **H message word `n`'s heap address** after `decF04 κ`: word `n mod 2` of element
`4 + (n mod 8)/2` of block `⌊n/8⌋` (`wAddr`). -/
def hAddr (κ : NodeKind) (n : ℕ) : ℕ := wAddr κ (W4.hc (n / 8) (4 + n % 8 / 2)) + n % 2

/-- **The address shape** (3.x's `addrW` with `(m₁, s₃, s₄) = (3, 3, 2)` at level 0's row stride
`2^(mLog 0 + 1)`): base `ob + 3·stride`, row `(n >>> 1) & 3`, column `4·(n >>> 3)`, word `n & 1`. -/
theorem hAddr_eq (κ : NodeKind) (n : ℕ) :
    hAddr κ n = map4.l0.ob + 2 ^ (T4.mLog (.node κ) 0 + 1) * (3 + n / 2 % 4) + 4 * (n / 8) + n % 2 := by
  unfold hAddr wAddr W4.hc
  rw [pow_succ]
  have e1 : (n / 8 * 128 + (4 + n % 8 / 2)) % 64 = 4 + n / 2 % 4 := by omega
  have e2 : (n / 8 * 128 + (4 + n % 8 / 2)) / 64 = 2 * (n / 8) := by omega
  rw [e1, e2, show 4 + n / 2 % 4 - 1 = 3 + n / 2 % 4 by omega]
  ring

/-- **The heap holds H's message words** after the decode (`decF04_wF`'s conclusion `hD`), for every
block inside `f` (`hn`). -/
theorem hMW_heap {κ : NodeKind} {L es : Log} {M : Mem}
    (hD : ∀ e, Dec0 e → e < 2 ^ (κ.m - 7) → rdF M (wAddr κ e) = wF κ L es e) {n : ℕ}
    (hn : n / 8 * 128 + 8 ≤ 2 ^ (κ.m - 7)) : rd M (hAddr κ n) = hMW (wF κ L es) n := by
  have h := hD (W4.hc (n / 8) (4 + n % 8 / 2)) (by unfold Dec0 W4.hc; omega) (by unfold W4.hc; omega)
  rw [hMW, ← h]
  unfold hAddr
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> rw [h2] <;> rfl

end FR.X

end G6_FRXSig4W

section G6_FRXTr4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5; stage S-H4, pass 9, item 1:
-- the traces' output words). 3.x analogue: `FRNodeReadW.readItems_words`, `FRNodeReadS.logWords_trSeg`
-- (over one slot's stream words and 3.x's `items`); here over any word list and `itemsOf S`.

/-!
# A trace's output words over a word stream, at any item sequence

A segment's trace is `readItems B 1 (itemsOf S)` read off a byte stream `B` whose items start at
byte `1` (the seed's entry) and lie 8-byte aligned after it. When `B` is the bytes of a word list
`Ws` (`wordsBytes Ws`, eight little-endian bytes a word), its output words (`logWords`) are the
segment `trSeg4 S` over the words (`segOut`, 3.x's `Seg` language):

* **`entryW_alignedL`**, **`readItems_wordsL`**: an aligned entry's words are its length word and
  `qlen/8 + 4` stream words;
* **`entryW_seedL`**: the seed's entry (stream byte `1`, not aligned) is `seedSeg`'s words;
* **`logWords_trSeg4`**: `logWords (readItems (wordsBytes Ws) 1 (itemsOf S)) = segOut W κ 0
  (trSeg4 S)`, given `S`'s items aligned (`TrOk4 S`, decided at `seq4`: `trOk4_seq4`) and the
  stream long enough.

`tPh4`, `tSegs4` are 3.x's `tPh`, `tSegs` over revision 4.1's `Sh` with `S`'s level map.
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4

/-! ## Specification: the trace's segments at revision 4.1 -/

/-- **A phase's trace segment** at stream word `u` (a later phase; the seed is `seedSeg`), with
`S`'s level map `lv`. -/
def tPh4 (lv : ℕ → Level) (u : ℕ) : Sh → Seg
  | .seed => .nil
  | .absorb _ len => tItems u [.absorb len]
  | .squeezes n _ => .rep n 10 (tItems u [.squeeze])
  | .uni _ => tItems u [.absorb uniBytes, .squeeze]
  | .rounds _ n _ inK => .rep n (wsum [.absorb (roundBytes inK), .squeeze])
      (tItems u [.absorb (roundBytes inK), .squeeze])
  | .queries i => .rep (lv i).t (wsum (posItemsL lv i))
      (.cat (tItems u [.col i]) (.rep (lv i).sib 14 (tItems (u + (Item.col i).slen / 8) [.node i 0])))

/-- The phases' trace segments from stream word `u`. -/
def tSegs4 (lv : ℕ → Level) : ℕ → List Sh → Seg
  | _, [] => .nil
  | u, sh :: shs => .cat (tPh4 lv u sh) (tSegs4 lv (u + wsum (sh.itemsL lv)) shs)

/-- The phases of `S` after the seed. -/
def restSh4 (S : Seq) : List Sh := ((phasesOf S).map Prod.snd).tail

/-- **A trace's segment** at `S`: the count, the seed entry, the later phases from stream word 20. -/
def trSeg4 (S : Seq) : Seg :=
  .cat (.wd (toWord (itemsOf S).length)) (.cat seedSeg (tSegs4 S.lv 20 (restSh4 S)))

/-- **`S`'s items are aligned** (decided): the seed first, every later query `≡ 0 (mod 8)`, no
seed among the later phases. -/
def TrOk4 (S : Seq) : Prop :=
  (phasesOf S).head?.map Prod.snd = some .seed ∧ (∀ sh ∈ restSh4 S, sh ≠ .seed) ∧
    ∀ it ∈ (restSh4 S).flatMap (Sh.itemsL S.lv), it.qlen % 8 = 0

instance (S : Seq) : Decidable (TrOk4 S) := by unfold TrOk4; infer_instance

/-! ## Proof helpers: words of a word stream -/

/-- **An aligned entry's output words**: its length word, then `m + 4` stream words. -/
theorem entryW_alignedL (Ws : List Word) (a m : ℕ) (it : Item) (hq : it.qlen = 8 * m)
    (hb : 8 * a + 8 + 8 * m + 32 ≤ 8 * Ws.length) :
    entryW (entryAt (wordsBytes Ws) (8 * a) it) = toWord it.qlen :: (Ws.drop (a + 1)).take (m + 4) := by
  have hB : (wordsBytes Ws).length = 8 * Ws.length := by rw [wordsBytes_length]
  have e1 : ((wordsBytes Ws).drop (8 * a + 8)).take it.qlen = wordsBytes ((Ws.drop (a + 1)).take m) := by
    rw [hq, show 8 * a + 8 = 8 * (a + 1) by ring, wordsBytes_drop, wordsBytes_take]
  have e2 : (Vector.ofFn fun i : Fin 32 => (wordsBytes Ws).getD (8 * a + 8 + it.qlen + i) 0).toList =
      wordsBytes ((Ws.drop (a + 1 + m)).take 4) := by
    rw [digest_toList _ _ (by omega), hq, show 8 * a + 8 + 8 * m = 8 * (a + 1 + m) by ring, wordsBytes_drop,
      show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_take]
  have hl : ((Ws.drop (a + 1)).take m).length = m := by simp only [List.length_take, List.length_drop]; omega
  show bytesWords (List.take it.qlen (List.drop (8 * a + 8) (wordsBytes Ws))).toArray.toList ++
    packBytes (Vector.ofFn fun i : Fin 32 => (wordsBytes Ws).getD (8 * a + 8 + it.qlen + i) 0).toList = _
  rw [List.toList_toArray, e1, e2, bytesWords, packBytes_wordsBytes, packBytes_wordsBytes, wordsBytes_length,
    hl, List.cons_append, List.take_add, List.drop_drop, hq]

/-- **Aligned items' output words** (`trW`). -/
theorem readItems_wordsL (Ws : List Word) : ∀ (its : List Item) (a : ℕ), (∀ it ∈ its, it.qlen % 8 = 0) →
    8 * a + (its.map Item.slen).sum ≤ 8 * Ws.length →
    (readItems (wordsBytes Ws) (8 * a) its).flatMap entryW = trW Ws a its
  | [], _, _, _ => rfl
  | it :: its, a, hq, hb => by
    simp only [List.map_cons, List.sum_cons, Item.slen] at hb
    have h8 := hq it (by simp)
    rw [readItems, List.flatMap_cons, trW,
      entryW_alignedL Ws a (it.qlen / 8) it (by omega) (by omega),
      show 8 * a + it.slen = 8 * (a + it.slen / 8) by simp only [Item.slen]; omega,
      readItems_wordsL Ws its _ (fun x hx => hq x (by simp [hx])) (by simp only [Item.slen] at *; omega)]

/-- **The seed entry's words** (stream byte `1`) are `seedSeg`'s over the words. -/
theorem entryW_seedL (Ws : List Word) (W : ℕ → Word) (κ : Bool)
    (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u) (hL : 20 ≤ Ws.length) :
    entryW (entryAt (wordsBytes Ws) 1 .seed) = segOut W κ 0 seedSeg := by
  have hB : (wordsBytes Ws).length = 8 * Ws.length := by rw [wordsBytes_length]
  have e0 : entryW (entryAt (wordsBytes Ws) 1 .seed) = bytesWords (((wordsBytes Ws).drop 9).take 119) ++
      packBytes (Vector.ofFn fun i : Fin 32 => (wordsBytes Ws).getD (128 + i) 0).toList := by
    rw [entryW, entryAt, List.toList_toArray]; rfl
  have hl : (((wordsBytes Ws).drop 9).take 119).length = 119 := by
    simp only [List.length_take, List.length_drop, hB]; omega
  have hP : packBytes (((wordsBytes Ws).drop 9).take 119) =
      ((List.range 14).map fun j => (W (j + 1) >>> 8) + (W (j + 1 + 1) <<< 56)) ++ [W 15 >>> 8] := by
    rw [packBytes, hl, show (119 + 7) / 8 = 14 + 1 from rfl, List.range_succ, List.map_append]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun j hj => ?_
      have hj := List.mem_range.1 hj
      rw [List.drop_take, List.take_take, List.drop_drop, show min 8 (119 - 8 * j) = 8 by omega,
        show 9 + 8 * j = 8 * (j + 1) + 1 by omega, straddle Ws (j + 1) (by omega), shw_bytes,
        hget _ (by omega), hget _ (by omega)]
    · rw [List.map_singleton, List.drop_take, List.take_take, List.drop_drop,
        show min 8 (119 - 8 * 14) = 7 from rfl, show 9 + 8 * 14 = 8 * 15 + 1 from rfl,
        lastByte7 Ws 15 (by omega), sh8_bytes, hget _ (by omega)]
  have hA : packBytes (Vector.ofFn fun i : Fin 32 => (wordsBytes Ws).getD (128 + i) 0).toList =
      (List.range 4).map fun j => W (16 + j) := by
    rw [digest_toList _ _ (by omega), show (128 : ℕ) = 8 * 16 from rfl, wordsBytes_drop,
      show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_take, packBytes_wordsBytes]
    refine List.ext_getElem (by simp; omega) fun j h1 h2 => ?_
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    exact hget _ _
  rw [e0, bytesWords, hl, hP, hA]
  simp only [seedSeg, segOut, Nat.zero_add, Nat.one_mul, flatMap_single]
  simp

/-- `trW` over a word list is `trWf` over a function agreeing with it. -/
theorem trW_eqL (Ws : List Word) (W : ℕ → Word) (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u) :
    ∀ (its : List Item) (u : ℕ), (∀ it ∈ its, it.qlen % 8 = 0) →
      8 * u + (its.map Item.slen).sum ≤ 8 * Ws.length → trW Ws u its = trWf W u its
  | [], _, _, _ => rfl
  | it :: its, u, hq, hb => by
    have h8 := hq it (by simp)
    simp only [List.map_cons, List.sum_cons, Item.slen] at hb
    rw [trW, trWf, trW_eqL Ws W hget its _ (fun x hx => hq x (by simp [hx])) (by simp only [Item.slen] at *; omega)]
    refine congrArg (· ++ _) (congrArg (_ :: ·) (List.ext_getElem (by simp; omega) fun j h1 h2 => ?_))
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    exact hget _ _

/-! ## Proof helpers: the segments -/

theorem segOut_tPh4 (W : ℕ → Word) (κ : Bool) (lv : ℕ → Level) (b u : ℕ) (sh : Sh) (hs : sh ≠ .seed) :
    segOut W κ b (tPh4 lv u sh) = trWf W (b + u) (sh.itemsL lv) := by
  cases sh with
  | seed => exact absurd rfl hs
  | absorb g len => exact segOut_tItems W κ b _ u
  | squeezes n ch =>
    rw [tPh4, segOut, Sh.itemsL, show List.replicate n Item.squeeze = (List.replicate n [Item.squeeze]).flatten by
      simp, trWf_rep]
    refine List.flatMap_congr fun j _ => ?_
    rw [segOut_tItems, show wsum [Item.squeeze] = 10 from rfl]
    congr 1; ring
  | uni g => exact segOut_tItems W κ b _ u
  | rounds g n deg inK =>
    rw [tPh4, segOut, Sh.itemsL, trWf_rep]
    refine List.flatMap_congr fun j _ => ?_
    rw [segOut_tItems]; congr 1; ring
  | queries i =>
    rw [tPh4, segOut, Sh.itemsL, trWf_rep]
    refine List.flatMap_congr fun j _ => ?_
    rw [segOut, segOut_tItems, posItemsL, show Item.col i :: (List.range (lv i).sib).map (Item.node i) =
      [Item.col i] ++ (List.range (lv i).sib).map (Item.node i) from rfl, trWf_append,
      trWf_congr W ((List.range (lv i).sib).map (Item.node i))
        (List.replicate (lv i).sib [Item.node i 0]).flatten _
        (by simp [Function.comp_def, Item.qlen, List.map_const']),
      trWf_rep, segOut]
    refine congrArg₂ _ (by congr 1; ring) (List.flatMap_congr fun h _ => ?_)
    rw [segOut_tItems, show wsum [Item.node i 0] = 14 by simp [wsum, Item.slen, Item.qlen],
      show wsum [Item.col i] = (Item.col i).slen / 8 by simp [wsum]]
    congr 1; ring

theorem segOut_tSegs4 (W : ℕ → Word) (κ : Bool) (lv : ℕ → Level) (b : ℕ) : ∀ (shs : List Sh) (u : ℕ),
    (∀ sh ∈ shs, sh ≠ .seed) → segOut W κ b (tSegs4 lv u shs) = trWf W (b + u) (shs.flatMap (Sh.itemsL lv))
  | [], _, _ => rfl
  | sh :: shs, u, h => by
    rw [tSegs4, segOut, segOut_tPh4 W κ lv b u sh (h sh (by simp)),
      segOut_tSegs4 W κ lv b shs _ fun x hx => h x (by simp [hx]), List.flatMap_cons, trWf_append,
      Nat.add_assoc]

theorem itemsOf_cons {S : Seq} (h : (phasesOf S).head?.map Prod.snd = some .seed) :
    itemsOf S = .seed :: (restSh4 S).flatMap (Sh.itemsL S.lv) := by
  unfold itemsOf restSh4
  cases hp : phasesOf S with
  | nil => rw [hp] at h; exact absurd h (by simp)
  | cons p ps =>
    rw [hp] at h
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h
    simp only [List.flatMap_cons, List.map_cons, List.tail_cons, List.flatMap_map, h, Sh.itemsL]
    rfl

/-! ## Load-bearing lemma -/

/-- **A segment's trace in words** (`logWords`) is `trSeg4 S`'s over its stream words, when `S`'s
items are aligned and the stream holds them. -/
theorem logWords_trSeg4 (S : Seq) (hS : TrOk4 S) (Ws : List Word) (W : ℕ → Word) (κ : Bool)
    (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u)
    (hlen : 160 + (((restSh4 S).flatMap (Sh.itemsL S.lv)).map Item.slen).sum ≤ 8 * Ws.length) :
    logWords (readItems (wordsBytes Ws) 1 (itemsOf S)) = segOut W κ 0 (trSeg4 S) := by
  obtain ⟨h0, hns, hq⟩ := hS
  have hL : 20 ≤ Ws.length := by omega
  show toWord (readItems (wordsBytes Ws) 1 (itemsOf S)).length ::
    (readItems (wordsBytes Ws) 1 (itemsOf S)).flatMap entryW = _
  rw [readItems_length, trSeg4, segOut, segOut, segOut, ← entryW_seedL Ws W κ hget hL,
    segOut_tSegs4 W κ S.lv 0 _ 20 hns, Nat.zero_add]
  refine congrArg (toWord (itemsOf S).length :: ·) ?_
  rw [itemsOf_cons h0, readItems, List.flatMap_cons, show 1 + Item.seed.slen = 8 * 20 from rfl,
    readItems_wordsL Ws _ 20 hq (by omega), trW_eqL Ws W hget _ 20 hq (by omega)]
  rfl

/-- **`seq4`'s items are aligned.** -/
theorem trOk4_seq4 : TrOk4 seq4 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have h : ((restSh4 seq4).flatMap (Sh.itemsL seq4.lv)).all (fun it => it.qlen % 8 == 0) = true := by
    decide +kernel
  intro it hit
  simpa using List.all_eq_true.1 h it hit

/-! ## Controls -/

/-- (−) **`TrOk4` is not trivial**: `seq4` with a 33-byte `E4end` absorb (a query of `73 ≢ 0 (mod 8)`
bytes) fails it; (+) `seq4` passes (`trOk4_seq4`). -/
theorem trOk4_ctl : ¬ TrOk4 { seq4 with e4end := 33 } := by
  intro h
  have hb : (((restSh4 { seq4 with e4end := 33 }).flatMap (Sh.itemsL { seq4 with e4end := 33 }.lv)).all
      fun it => it.qlen % 8 == 0) = false := by decide +kernel
  rw [List.all_eq_false] at hb
  obtain ⟨it, hit, hne⟩ := hb
  exact hne (by simpa using h.2.2 it hit)

end FR.X

end G6_FRXTr4

section G6_FRXPf4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.5, §6.2 step 5; stage S-H4, pass 9, item 1:
-- the proofs' output words). 3.x analogue: `FRNodeReadP.proof_words` (3.x's `items`, `reassemble`,
-- one slot's stream words); here `reassemble4 S`, `itemsOf S`, any word list.

/-!
# A slot proof's output words over a word stream, at any item sequence

`reassemble4 S tr` (the slots' `pf4`) is, field by field, the phases' contributions
`ctb4`. On a trace read off a word stream (`tr = readItems (wordsBytes Ws) 1 (itemsOf S)`), every
contribution is a slice of stream words (A.5, A.7):

* the seed's `hdr` is stream words `10 … 15`;
* an absorb's message (`absorb`, `uni`, a round's) starts 6 words after its item; round `j` sits
  `j · wsum` words after the first;
* position `p`'s columns start 2 words after its column item, `p · wsum (posItemsL)` apart;
* a sibling is words 6–9 or 2–5 of its node item, by the position's bit `h` (bit `m mod 64` of
  answer word `⌊m/64⌋`, `m = (p mod per)·logN + h`), or four zero words above the kind's height.

Only the siblings (field `fSibs`, the last) depend on the child's kind, through its ladder `m`
(`trM4`: byte `71` of the seed query, the low byte of stream word `10`). **`proof_words4`**:
`bl (reassemble4 S tr) = wordsBytes (segOut W κ 0 (pSeg4 S m))` when `trM4 tr = m`, under the
decided `PfOk4 S` (aligned items, every `queries` phase after its `P2`) and `LadOk4 S m`.
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4

/-! ## Specification: the proof's segments -/

/-- Stream offset of item `k` of `S` (3.x's `streamOff`). -/
def sOff4 (S : Seq) (k : ℕ) : ℕ := 1 + (((itemsOf S).take k).map Item.slen).sum

/-- Stream word of item `ix`. -/
def wo4 (S : Seq) (ix : ℕ) : ℕ := sOff4 S ix / 8

/-- The item index of the last position-answer (`P2`) phase. -/
def nextA4 (ix ixA : ℕ) : Sh → ℕ
  | .squeezes _ (.pos _) => ix
  | _ => ixA

/-- **Level `i`'s siblings** at ladder `m`: `S`'s counts (`t`, slots `sib`), the kind's `logN`,
`per`, height. -/
def sibS4 (S : Seq) (m i ix ixA : ℕ) : Seg :=
  .sib (wo4 S ix + (Item.col i).slen / 8) (wsum (posItemsL S.lv i)) (S.lv i).t (S.lv i).sib (wo4 S ixA + 6)
    (S.lvK m i).logN (S.lvK m i).per (S.lvK m i).sib

/-- **A phase's segment for field `f`** (a later phase, items from `ix`). -/
def pPh4 (S : Seq) (m f ix ixA : ℕ) : Sh → Seg
  | .seed => .nil
  | .absorb g len => if f = g then .cp (wo4 S ix + 6) (len / 8) else .nil
  | .squeezes _ _ => .nil
  | .uni g => if f = g then .cp (wo4 S ix + 6) (uniBytes / 8) else .nil
  | .rounds g n _ inK => if f = g then
      .rep n (wsum [.absorb (roundBytes inK), .squeeze]) (.cp (wo4 S ix + 6) (roundBytes inK / 8)) else .nil
  | .queries i =>
    if f = fCols then .rep (S.lv i).t (wsum (posItemsL S.lv i)) (.cp (wo4 S ix + 2) (colBytes i / 8))
    else if f = fSibs then sibS4 S m i ix ixA else .nil

/-- The later phases' segments for field `f`. -/
def pRest4 (S : Seq) (m f : ℕ) : ℕ → ℕ → List Sh → Seg
  | _, _, [] => .nil
  | ix, ixA, sh :: shs =>
    .cat (pPh4 S m f ix ixA sh) (pRest4 S m f (ix + (sh.itemsL S.lv).length) (nextA4 ix ixA sh) shs)

/-- **Field `f`'s segment**: the seed's `hdr` (stream words `10 … 15`) for `fHdr`, the later phases. -/
def fSeg4 (S : Seq) (m f : ℕ) : Seg := .cat (if f = fHdr then .cp 10 6 else .nil) (pRest4 S m f 1 0 (restSh4 S))

/-- **The proof's segment** at ladder `m` (fields `0 … 19`). -/
def pSeg4 (S : Seq) (m : ℕ) : Seg := catL ((List.range nFields4).map (fSeg4 S m))

/-- A `queries i` phase follows level `i`'s `P2` phase. -/
def qPrev4 (S : Seq) (i : ℕ) : Option Sh → Bool
  | some (.squeezes n (.pos i')) => n == (S.lv i).sq && i' == i
  | _ => false

/-- A phase's condition on the one before: a `queries` phase follows its `P2` phase. -/
def qHead4 (S : Seq) (p : Option Sh) : Sh → Bool
  | .queries i => qPrev4 S i p
  | _ => true

/-- Every `queries` phase follows its `P2` phase. -/
def qOk4 (S : Seq) : Option Sh → List Sh → Bool
  | _, [] => true
  | p, sh :: shs => qHead4 S p sh && qOk4 S (some sh) shs

/-- **`S`'s format is readable as segments** (decided at `seq4`): its items aligned (`TrOk4`), every
`queries` phase after its `P2` phase, every absorb a whole number of words. -/
def PfOk4 (S : Seq) : Prop := TrOk4 S ∧ qOk4 S (some .seed) (restSh4 S) = true

/-- **Ladder `m`'s facts the siblings need** at every queried level. -/
def LadOk4 (S : Seq) (m : ℕ) : Prop :=
  ∀ i < nLevels, 0 < (S.lv i).t → (S.lv i).t ≤ (S.lv i).sq * (S.lvK m i).per ∧ 0 < (S.lvK m i).per ∧
    (S.lvK m i).per * (S.lvK m i).logN ≤ 256 ∧ (S.lvK m i).sib ≤ (S.lvK m i).logN

/-- The ladder of a kind byte (`trM4`'s rule: `L32`'s for a byte of no kind). -/
def mOfB (b : UInt8) : ℕ := ((Snd.CKind.ofByte? b).getD (.seg .L32)).m

/-! ## Proof helpers: items and offsets -/

section Items

variable {S : Seq}

theorem sOff4_drop {ix m : ℕ} {l r : List Item} (hd : (itemsOf S).drop ix = l ++ r) (hm : m ≤ l.length) :
    sOff4 S (ix + m) = sOff4 S ix + ((l.take m).map Item.slen).sum := by
  simp only [sOff4]
  rw [List.take_add, hd, List.take_append_of_le_length hm, List.map_append, List.sum_append]
  omega

theorem drop_cons_item4 {ix : ℕ} {it : Item} {r : List Item} (hd : (itemsOf S).drop ix = it :: r) :
    (itemsOf S)[ix]? = some it ∧ (itemsOf S).drop (ix + 1) = r ∧ sOff4 S (ix + 1) = sOff4 S ix + it.slen := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (·[0]?) hd
    simpa [List.getElem?_drop] using this
  · rw [← List.drop_drop, hd]; rfl
  · rw [sOff4_drop (l := [it]) (r := r) hd (by simp)]; simp

/-- **Block `j` of a repeated block**: its items and its stream offset. -/
theorem drop_rep4 {ix n j : ℕ} {blk r : List Item}
    (hd : (itemsOf S).drop ix = (List.replicate n blk).flatten ++ r) (hj : j < n) :
    (itemsOf S).drop (ix + j * blk.length) = blk ++ ((List.replicate (n - j - 1) blk).flatten ++ r) ∧
      sOff4 S (ix + j * blk.length) = sOff4 S ix + j * (blk.map Item.slen).sum := by
  have hl : j * blk.length ≤ ((List.replicate n blk).flatten).length := by
    simp only [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_⟩
  · rw [← List.drop_drop, hd, List.drop_append_of_le_length hl, drop_flatten_replicate blk n j (by omega)]
    generalize hk : n - j - 1 = k
    rw [show n - j = k + 1 by omega, List.replicate_succ, List.flatten_cons, List.append_assoc]
  · rw [sOff4_drop hd hl, take_flatten_replicate blk n j (by omega), sum_flatten_replicate]

theorem sOff4_slen_le {j : ℕ} {it : Item} (h : (itemsOf S)[j]? = some it) :
    sOff4 S j + it.slen ≤ streamBytesOf S := by
  have hj : j < (itemsOf S).length := (List.getElem?_eq_some_iff.1 h).1
  have hd : (itemsOf S).drop j = it :: (itemsOf S).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, (List.getElem?_eq_some_iff.1 h).2]
  have e := (drop_cons_item4 hd).2.2
  have hT : sOff4 S (j + 1) ≤ sOff4 S (itemsOf S).length := by
    simp only [sOff4]
    have := List.take_append_drop (j + 1) ((itemsOf S).take (itemsOf S).length)
    rw [List.take_take, Nat.min_eq_left (by omega)] at this
    have hs := congrArg (fun l => (l.map Item.slen).sum) this
    simp only [List.map_append, List.sum_append] at hs
    omega
  have hE : sOff4 S (itemsOf S).length = streamBytesOf S := by
    have e3 : Item.slen = fun it => 8 + it.qlen + 32 := funext fun _ => rfl
    simp only [sOff4, List.take_length, streamBytesOf, e3]
  omega

theorem sOff4_mod8 (hS : TrOk4 S) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ (itemsOf S).length) : sOff4 S j % 8 = 0 := by
  obtain ⟨h0, -, hq⟩ := hS
  have hc := itemsOf_cons h0
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have e : ∀ (l : List Item), (∀ it ∈ l, it.qlen % 8 = 0) → (l.map Item.slen).sum % 8 = 0 := by
    intro l hl; induction l with
    | nil => rfl
    | cons x l ih =>
      have := hl x (by simp)
      simp only [List.map_cons, List.sum_cons, Item.slen]
      have := ih fun y hy => hl y (by simp [hy]); omega
  simp only [sOff4]
  rw [hc, List.take_succ_cons, List.map_cons, List.sum_cons]
  have := e ((List.flatMap (Sh.itemsL S.lv) (restSh4 S)).take k) fun it hit => hq it (List.mem_of_mem_take hit)
  simp only [Item.slen, Item.qlen] at this ⊢; omega

theorem mem_rest4 {j : ℕ} {it : Item} (hS : TrOk4 S) (h1 : 1 ≤ j) (h : (itemsOf S)[j]? = some it) :
    it ∈ (restSh4 S).flatMap (Sh.itemsL S.lv) := by
  rw [itemsOf_cons hS.1] at h
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact List.mem_of_getElem? h

theorem items4_zero (hS : TrOk4 S) : (itemsOf S)[0]? = some .seed := by rw [itemsOf_cons hS.1]; rfl

theorem one_le_of4 (hS : TrOk4 S) {j : ℕ} {it : Item} (h : (itemsOf S)[j]? = some it) (hs : it ≠ .seed) :
    1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [items4_zero hS] at h; cases h; exact absurd rfl hs
  · exact hj

end Items

/-! ## Proof helpers: the slices of a word stream -/

section Slices

variable {S : Seq} (Ws : List Word) (W : ℕ → Word) (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u)
  (hB : streamBytesOf S ≤ 8 * Ws.length)

/-- The trace read off the word stream. -/
abbrev trOf (S : Seq) (Ws : List Word) : Trace := readItems (wordsBytes Ws) 1 (itemsOf S)

theorem trOf_getD (S : Seq) (Ws : List Word) {j : ℕ} (hj : j < (itemsOf S).length) :
    (trOf S Ws).toArray.getD j (ByteArray.empty, 0) = entryAt (wordsBytes Ws) (sOff4 S j) (itemsOf S)[j] := by
  have hl : j < (trOf S Ws).length := by rw [readItems_length]; exact hj
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hl, Option.getD_some]
  show (readItems (wordsBytes Ws) 1 (itemsOf S))[j]'(by rw [readItems_length]; exact hj) = _
  rw [readItems_getElem _ _ _ _ hj]; rfl

include hget hB in
/-- **A query slice is a slice of stream words** (aligned, whole words). -/
theorem qBytes4 {j off n : ℕ} {it : Item} (hj : (itemsOf S)[j]? = some it) (hn : off + n ≤ it.qlen)
    (ha : (sOff4 S j + 8 + off) % 8 = 0) (h8 : n % 8 = 0) :
    bl (qBytes (trOf S Ws).toArray j off n) =
      wordsBytes ((List.range (n / 8)).map fun i => W ((sOff4 S j + 8 + off) / 8 + i)) := by
  have hl : j < (itemsOf S).length := (List.getElem?_eq_some_iff.1 hj).1
  have hit : (itemsOf S)[j] = it := (List.getElem?_eq_some_iff.1 hj).2
  have hb := sOff4_slen_le hj
  simp only [Item.slen] at hb
  rw [qBytes, trOf_getD S Ws hl, entryAt, bl, toList_extract]
  simp only [Nat.add_sub_cancel_left, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by rw [hit]; omega),
    show (sOff4 S j + 8 + off) = 8 * ((sOff4 S j + 8 + off) / 8) by omega,
    show n = 8 * (n / 8) by omega, Nat.add_comm, wordsBytes_drop, wordsBytes_take,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 8), Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]
  congr 1
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  exact hget _ _

/-- A fitted list of the right length is itself. -/
theorem fitL_self {n : ℕ} {l : List UInt8} (h : l.length = n) : N4s.fitL n l = l := by
  rw [N4s.fitL, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

include hget hB in
/-- A fitted query slice (`qB4`) as a copy segment at base `b`. -/
theorem cpSlice4 (κ : Bool) {j off n : ℕ} {it : Item} (hj : (itemsOf S)[j]? = some it) (hn : off + n ≤ it.qlen)
    (h8 : n % 8 = 0) (b o : ℕ) (hv : sOff4 S j + 8 + off = 8 * (b + o)) :
    qB4 (trOf S Ws).toArray j off n = wordsBytes (segOut W κ b (.cp o (n / 8))) := by
  have hq := qBytes4 Ws W hget hB hj hn (by omega) h8
  rw [qB4, fitL_self (by rw [hq, wordsBytes_length]; simp; omega), hq, segOut]
  congr 1; refine List.map_congr_left fun x _ => ?_; congr 1; omega

end Slices

/-! ## Proof helpers: the siblings -/

section Sibs

variable {S : Seq} (Ws : List Word) (W : ℕ → Word) (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u)
  (hB : streamBytesOf S ≤ 8 * Ws.length)

include hget hB in
/-- **An answer's bits are its stream words' bits.** -/
theorem ans_bit4 (hS : TrOk4 S) {j : ℕ} (hj : (itemsOf S)[j]? = some .squeeze) {m : ℕ} (hm : m < 256) :
    (natLE ((trOf S Ws).toArray.getD j (ByteArray.empty, 0)).2).testBit m =
      (W (wo4 S j + 6 + m / 64)).toNat.testBit (m % 64) := by
  have hl : j < (itemsOf S).length := (List.getElem?_eq_some_iff.1 hj).1
  have hit : (itemsOf S)[j] = .squeeze := (List.getElem?_eq_some_iff.1 hj).2
  have hb := sOff4_slen_le hj
  have h1 := one_le_of4 hS hj (by decide)
  have ha := sOff4_mod8 hS h1 hl.le
  have hWl : (wordsBytes Ws).length = 8 * Ws.length := by rw [wordsBytes_length]
  simp only [Item.slen, Item.qlen] at hb
  rw [trOf_getD S Ws hl, hit, entryAt, natLE_eq_ofLE, digest_toList _ _ (by simp only [Item.qlen]; omega),
    show sOff4 S j + 8 + Item.squeeze.qlen = 8 * (wo4 S j + 6) by simp only [wo4, Item.qlen]; omega,
    show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wordsBytes_take, testBit_ofLE_wordsBytes,
    List.getD_eq_getElem _ _ (by simp only [wo4, List.length_take, List.length_drop]; omega),
    List.getElem_take, List.getElem_drop, hget]

theorem testBit_posOf4 (S : Seq) (m i : ℕ) (ans : List Digest) (p h : ℕ) (hh : h < (S.lvK m i).logN) :
    (posOf4 S m i ans p).testBit h =
      (natLE (ans.getD (p / (S.lvK m i).per) 0)).testBit (p % (S.lvK m i).per * (S.lvK m i).logN + h) := by
  simp only [posOf4, idxOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hh, decide_true,
    Bool.true_and]
  rw [Nat.add_comm, Nat.mul_comm]

include hget hB in
/-- **One sibling** (`sib4`) is `sibW`'s words. -/
theorem sib_one4 (m : ℕ) {i jn p h o Sw ansW : ℕ} {ans : List Digest}
    (hj : (itemsOf S)[jn]? = some (.node i h)) (hoff : sOff4 S jn = 8 * (o + Sw * p + 14 * h))
    (hans : ∀ k < 256, (natLE (ans.getD (p / (S.lvK m i).per) 0)).testBit k =
      (W (ansW + 10 * (p / (S.lvK m i).per) + k / 64)).toNat.testBit (k % 64))
    (hpl : (S.lvK m i).per * (S.lvK m i).logN ≤ 256) (hsl : (S.lvK m i).sib ≤ (S.lvK m i).logN)
    (hper : 0 < (S.lvK m i).per) :
    sib4 S m i h (posOf4 S m i ans p) ((trOf S Ws).toArray.getD jn (ByteArray.empty, 0)).1 =
      wordsBytes (sibW W 0 o Sw ansW (S.lvK m i).logN (S.lvK m i).per (S.lvK m i).sib p h) := by
  unfold sib4 sibW
  by_cases hh : h < (S.lvK m i).sib
  · rw [if_pos hh, if_pos hh]
    have hr : p % (S.lvK m i).per < (S.lvK m i).per := Nat.mod_lt _ hper
    have hm : p % (S.lvK m i).per * (S.lvK m i).logN + h < 256 := by
      have : (p % (S.lvK m i).per + 1) * (S.lvK m i).logN ≤ (S.lvK m i).per * (S.lvK m i).logN :=
        Nat.mul_le_mul_right _ hr
      nlinarith
    have hiff : posOf4 S m i ans p / 2 ^ h % 2 = 0 ↔
        (W (0 + ansW + 10 * (p / (S.lvK m i).per) + (p % (S.lvK m i).per * (S.lvK m i).logN + h) / 64)).toNat /
          2 ^ ((p % (S.lvK m i).per * (S.lvK m i).logN + h) % 64) % 2 = 0 := by
      rw [div_two_pow_mod_two, div_two_pow_mod_two, testBit_posOf4 S m i ans p h (by omega), hans _ hm,
        Nat.zero_add]
    by_cases hb : posOf4 S m i ans p / 2 ^ h % 2 = 0
    · rw [if_pos hb, if_pos (hiff.1 hb)]
      have := cpSlice4 Ws W hget hB false (off := 40) (n := 32) hj (by simp [Item.qlen]) (by decide) 0
        (o + Sw * p + 14 * h + 6) (by omega)
      rw [qB4] at this
      rw [show ((trOf S Ws).toArray.getD jn (ByteArray.empty, 0)).1.extract 40 72 =
        qBytes (trOf S Ws).toArray jn 40 32 from rfl, this]
      simp only [segOut, Nat.zero_add]
    · rw [if_neg hb, if_neg (fun h' => hb (hiff.2 h'))]
      have := cpSlice4 Ws W hget hB false (off := 8) (n := 32) hj (by simp [Item.qlen]) (by decide) 0
        (o + Sw * p + 14 * h + 2) (by omega)
      rw [qB4] at this
      rw [show ((trOf S Ws).toArray.getD jn (ByteArray.empty, 0)).1.extract 8 40 =
        qBytes (trOf S Ws).toArray jn 8 32 from rfl, this]
      simp only [segOut, Nat.zero_add]
  · rw [if_neg hh, if_neg hh]; decide

end Sibs

/-! ## Proof helpers: one phase -/

/-- What the walk knows about the last phase: after a `P2` phase of `n` answers at `ixA`, the
answers are its items' and the items from `ixA` are its squeezes. -/
def PrevInv4 (S : Seq) (a : Array (ByteArray × Digest)) (prev : Option Sh) (ix ixA : ℕ) (ans : List Digest) :
    Prop :=
  ∀ n i, prev = some (.squeezes n (.pos i)) → ixA + n = ix ∧
    ans = (List.range n).map (fun j => (a.getD (ixA + j) (ByteArray.empty, 0)).2) ∧
    (itemsOf S).drop ixA = (List.replicate n [Item.squeeze]).flatten ++ (itemsOf S).drop ix

theorem qPrev4_eq {S : Seq} {i : ℕ} {p : Option Sh} (h : qPrev4 S i p = true) :
    p = some (.squeezes (S.lv i).sq (.pos i)) := by
  unfold qPrev4 at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2]
  · exact absurd h (by simp)

theorem lv_t_out (S : Seq) {i : ℕ} (hi : ¬ i < nLevels) : (S.lv i).t = 0 := by
  simp only [Seq.lv, Seq.lvK]
  rw [List.getD_eq_default _ _ (by simp [ladderOfR, nLevels] at hi ⊢; omega)]

theorem posItemsL_slen (S : Seq) (i : ℕ) :
    ((posItemsL S.lv i).map Item.slen).sum = 8 * wsum (posItemsL S.lv i) := by
  have h1 : (Item.col i).slen % 8 = 0 := by
    simp only [Item.slen, Item.qlen]; have := colBytes_mod i; omega
  have e : ∀ l : List ℕ, (∀ x ∈ l, x = 112) → l.sum = 8 * (l.map (· / 8)).sum := by
    intro l hl; induction l with
    | nil => rfl
    | cons x l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons, hl x (by simp), ih fun y hy => hl y (by simp [hy])]
      omega
  simp only [posItemsL, wsum, List.map_cons, List.sum_cons, List.map_map]
  rw [e ((List.range (S.lv i).sib).map (Item.slen ∘ Item.node i)) (by simp [Item.slen, Item.qlen]),
    List.map_map]
  have : (Item.col i).slen = 8 * ((Item.col i).slen / 8) := by omega
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  simp only [Function.comp_def]; ring

section Phase

variable {S : Seq} (Ws : List Word) (W : ℕ → Word) (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u)
  (hB : streamBytesOf S ≤ 8 * Ws.length) (hS : TrOk4 S) (κ : Bool) (m : ℕ) (hL : LadOk4 S m)

theorem mod8_of (hS : TrOk4 S) {j : ℕ} {it : Item} (h1 : 1 ≤ j) (h : (itemsOf S)[j]? = some it) :
    sOff4 S j % 8 = 0 :=
  sOff4_mod8 hS h1 (List.getElem?_eq_some_iff.1 h).1.le

include hget hB hS hL in
/-- **One later phase**: its contribution to field `f` is its segment's words. -/
theorem pPh4_spec (f : ℕ) {ix ixA : ℕ} {ans : List Digest} {sh : Sh} {r : List Item}
    {prev : Option Sh} (hd : (itemsOf S).drop ix = sh.itemsL S.lv ++ r) (h1 : 1 ≤ ix) (hns : sh ≠ .seed)
    (hq : qHead4 S prev sh = true)
    (hP : PrevInv4 S (trOf S Ws).toArray prev ix ixA ans) :
    ctb4 S m (trOf S Ws).toArray ix ans sh f = wordsBytes (segOut W κ 0 (pPh4 S m f ix ixA sh)) := by
  cases sh with
  | seed => exact absurd rfl hns
  | squeezes n ch => rfl
  | absorb g len =>
    obtain ⟨e1, -, -⟩ := drop_cons_item4 hd
    have ha := mod8_of hS h1 e1
    have hq := hS.2.2 _ (mem_rest4 hS h1 e1)
    simp only [Item.qlen] at hq
    by_cases hf : f = g
    · simp only [ctb4, pPh4, hf, if_true]
      exact cpSlice4 Ws W hget hB κ e1 (by simp [Item.qlen]) (by omega) 0 _ (by simp only [wo4]; omega)
    · simp only [ctb4, pPh4, hf, if_false]; rfl
  | uni g =>
    obtain ⟨e1, -, -⟩ := drop_cons_item4 hd
    have ha := mod8_of hS h1 e1
    by_cases hf : f = g
    · simp only [ctb4, pPh4, hf, if_true]
      exact cpSlice4 Ws W hget hB κ e1 (by simp [Item.qlen]) (by decide) 0 _ (by simp only [wo4]; omega)
    · simp only [ctb4, pPh4, hf, if_false]; rfl
  | rounds g n deg inK =>
    by_cases hf : f = g
    · simp only [ctb4, pPh4, hf, if_true, segOut, wordsBytes_flatMap]
      refine List.flatMap_congr fun j hj => ?_
      obtain ⟨d1, d2⟩ := drop_rep4 (blk := [.absorb (roundBytes inK), .squeeze]) hd (List.mem_range.1 hj)
      obtain ⟨e1, -, -⟩ := drop_cons_item4 d1
      have ha := mod8_of hS (by omega) e1
      simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at d2 e1 ha
      rw [show ix + 2 * j = ix + j * (0 + 1 + 1) by ring]
      rw [d2] at ha
      refine cpSlice4 Ws W hget hB κ e1 (by simp [Item.qlen]) (by cases inK <;> decide) _ _ ?_
      rw [d2]
      cases inK <;> simp only [wo4, wsum, roundBytes, Item.slen, Item.qlen, Bool.false_eq_true,
        ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at ha ⊢ <;> omega
    · simp only [ctb4, pPh4, hf, if_false]; rfl
  | queries i =>
    have hS' := posItemsL_slen S i
    have hlen : (posItemsL S.lv i).length = 1 + (S.lv i).sib := by simp [posItemsL, Nat.add_comm]
    have pos : ∀ p < (S.lv i).t, (itemsOf S)[ix + (1 + (S.lv i).sib) * p]? = some (.col i) ∧
        (itemsOf S).drop (ix + (1 + (S.lv i).sib) * p + 1) =
          (List.range (S.lv i).sib).map (Item.node i) ++
            ((List.replicate ((S.lv i).t - p - 1) (posItemsL S.lv i)).flatten ++ r) ∧
        sOff4 S (ix + (1 + (S.lv i).sib) * p) = 8 * (wo4 S ix + wsum (posItemsL S.lv i) * p) ∧
        sOff4 S (ix + (1 + (S.lv i).sib) * p + 1) =
          sOff4 S (ix + (1 + (S.lv i).sib) * p) + (Item.col i).slen := fun p hp => by
      obtain ⟨d1, d2⟩ := drop_rep4 (blk := posItemsL S.lv i) hd hp
      rw [hlen, Nat.mul_comm] at d1 d2
      obtain ⟨e1, e2, e3⟩ := drop_cons_item4 (show (itemsOf S).drop (ix + (1 + (S.lv i).sib) * p) =
        .col i :: ((List.range (S.lv i).sib).map (Item.node i) ++
          ((List.replicate ((S.lv i).t - p - 1) (posItemsL S.lv i)).flatten ++ r)) from d1)
      have ha := mod8_of hS (by omega) e1
      refine ⟨e1, e2, ?_, e3⟩
      rw [d2, hS', show p * (8 * wsum (posItemsL S.lv i)) = 8 * (wsum (posItemsL S.lv i) * p) by ring] at ha ⊢
      simp only [wo4]; omega
    by_cases hc : f = fCols
    · simp only [ctb4, pPh4, hc, if_true, segOut, wordsBytes_flatMap]
      refine List.flatMap_congr fun p hp => ?_
      obtain ⟨e1, -, e3, -⟩ := pos p (List.mem_range.1 hp)
      exact cpSlice4 Ws W hget hB κ e1 (by simp [Item.qlen]) (colBytes_mod i) _ _ (by rw [e3]; omega)
    by_cases hs : f = fSibs
    · simp only [ctb4, pPh4, hs, show fSibs ≠ fCols by decide, if_true, if_false]
      rw [sibS4, segOut, wordsBytes_flatMap]
      refine List.flatMap_congr fun p hp => ?_
      have hp := List.mem_range.1 hp
      have hi : i < nLevels := by
        by_contra hi; rw [lv_t_out S hi] at hp; omega
      obtain ⟨l1, l2, l3, l4⟩ := hL i hi (by omega)
      obtain ⟨-, e2, e3, e4⟩ := pos p hp
      obtain ⟨a1, a2, a3⟩ := hP _ _ (qPrev4_eq (i := i) hq)
      have hqa : p / (S.lvK m i).per < (S.lv i).sq := by
        rw [Nat.div_lt_iff_lt_mul l2]; omega
      obtain ⟨b1, b2⟩ := drop_rep4 (blk := [Item.squeeze]) a3 hqa
      obtain ⟨c1, -, -⟩ := drop_cons_item4 b1
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil] at b2 c1
      have hans : ∀ k < 256, (natLE (ans.getD (p / (S.lvK m i).per) 0)).testBit k =
          (W (wo4 S ixA + 6 + 10 * (p / (S.lvK m i).per) + k / 64)).toNat.testBit (k % 64) := by
        intro k hk
        rw [a2, List.getD_eq_getElem _ _ (by simpa using hqa), List.getElem_map, List.getElem_range,
          ans_bit4 Ws W hget hB hS c1 hk]
        congr 4; simp only [wo4, b2, Item.slen, Item.qlen]; omega
      rw [wordsBytes_flatMap]
      refine List.flatMap_congr fun h hh => ?_
      have hh := List.mem_range.1 hh
      have hn : (itemsOf S)[ix + (1 + (S.lv i).sib) * p + 1 + h]? = some (.node i h) := by
        rw [← List.getElem?_drop, e2, List.getElem?_append_left (by simpa using hh)]
        simp [hh]
      have ho := sOff4_drop e2 (m := h) (by simpa using hh.le)
      rw [nodes_take i _ h hh.le] at ho
      refine sib_one4 Ws W hget hB m hn ?_ hans l3 l4 l2
      rw [ho, e4, e3]
      have : (Item.col i).slen % 8 = 0 := by simp only [Item.slen, Item.qlen]; have := colBytes_mod i; omega
      omega
    · simp only [ctb4, pPh4, hc, hs, if_false]; rfl

include hget hB hS hL in
/-- **The later phases** contribute their segments' words to field `f`. -/
theorem pRest4_spec (f : ℕ) : ∀ (shs : List Sh) (ix ixA : ℕ) (ans : List Digest) (prev : Option Sh),
    (itemsOf S).drop ix = shs.flatMap (Sh.itemsL S.lv) → 1 ≤ ix → (∀ sh ∈ shs, sh ≠ .seed) →
    qOk4 S prev shs = true → PrevInv4 S (trOf S Ws).toArray prev ix ixA ans →
    ctbs4 S m (trOf S Ws).toArray ix ans shs f = wordsBytes (segOut W κ 0 (pRest4 S m f ix ixA shs))
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | sh :: shs, ix, ixA, ans, prev, hd, h1, hns, hq, hP => by
    simp only [qOk4, Bool.and_eq_true] at hq
    rw [List.flatMap_cons] at hd
    have hd' : (itemsOf S).drop (ix + (sh.itemsL S.lv).length) = shs.flatMap (Sh.itemsL S.lv) := by
      rw [← List.drop_drop, hd, List.drop_left]
    rw [ctbs4, pRest4, segOut, wordsBytes_append,
      pPh4_spec Ws W hget hB hS κ m hL f hd h1 (hns sh (by simp)) hq.1 hP,
      pRest4_spec f shs _ (nextA4 ix ixA sh) _ (some sh) hd' (by omega) (fun x hx => hns x (by simp [hx]))
        hq.2 ?_]
    intro n i hsh
    cases hsh
    refine ⟨by simp [nextA4, Sh.itemsL], rfl, ?_⟩
    simp only [nextA4]
    rw [hd, flatten_rep_single, hd']; rfl

end Phase

/-! ## Load-bearing lemmas -/

/-- **The child's ladder is its stream word 10's low byte's** (`trM4`: byte `71` of the seed query,
stream byte `80`). -/
theorem trM4_eq (S : Seq) (hS : TrOk4 S) (Ws : List Word) (W : ℕ → Word)
    (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u) (hB : streamBytesOf S ≤ 8 * Ws.length) :
    trM4 (trOf S Ws).toArray = mOfB (W 10).toNat.toUInt8 := by
  have h0 := items4_zero hS
  have hb := sOff4_slen_le h0
  have hl : 0 < (itemsOf S).length := (List.getElem?_eq_some_iff.1 h0).1
  have hWl : (wordsBytes Ws).length = 8 * Ws.length := by rw [wordsBytes_length]
  simp only [Item.slen, Item.qlen] at hb
  have hq : ((trOf S Ws).toArray.getD 0 (ByteArray.empty, 0)).1.data[71]? = some (W 10).toNat.toUInt8 := by
    rw [trOf_getD S Ws hl, show (itemsOf S)[0] = Item.seed from (List.getElem?_eq_some_iff.1 h0).2, entryAt]
    simp only [List.getElem?_toArray, List.getElem?_take, List.getElem?_drop, Item.qlen]
    rw [if_pos (by norm_num), show sOff4 S 0 = 1 from rfl, List.getElem?_eq_getElem (by simp only [sOff4] at hb; omega),
      ← List.getD_eq_getElem _ 0, ← wordByte_eq_getD, wordByte,
      List.getD_eq_getElem _ _ (by simp only [sOff4] at hb; omega), hget]
    norm_num
  rw [trM4, hq, Option.bind_some]; rfl

variable {S : Seq} {m : ℕ}

/-- **A slot proof's bytes are stream-word segments** (`reassemble4`, all 20 fields). -/
theorem proof_words4 (hP : PfOk4 S) (hL : LadOk4 S m) (Ws : List Word) (W : ℕ → Word)
    (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u) (hB : streamBytesOf S ≤ 8 * Ws.length) (κ : Bool)
    (hm : trM4 (trOf S Ws).toArray = m) :
    bl (reassemble4 S (trOf S Ws)) = wordsBytes (segOut W κ 0 (pSeg4 S m)) := by
  obtain ⟨hS, hq⟩ := hP
  have hsh : (phasesOf S).map Prod.snd = .seed :: restSh4 S := by
    have h0 := hS.1
    unfold restSh4
    cases hp : phasesOf S with
    | nil => rw [hp] at h0; exact absurd h0 (by simp)
    | cons p ps =>
      rw [hp] at h0
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h0
      simp [h0]
  show (((List.range nFields4).flatMap fun f => ctbs4 S (trM4 (trOf S Ws).toArray) (trOf S Ws).toArray 0 []
    ((phasesOf S).map Prod.snd) f)).toArray.toList = _
  rw [List.toList_toArray, hm, pSeg4, segOut_catL, List.flatMap_map, wordsBytes_flatMap]
  refine List.flatMap_congr fun f _ => ?_
  rw [hsh, ctbs4, fSeg4, segOut, wordsBytes_append]
  have h1 : (itemsOf S).drop (0 + (Sh.seed.itemsL S.lv).length) = (restSh4 S).flatMap (Sh.itemsL S.lv) := by
    rw [show 0 + (Sh.seed.itemsL S.lv).length = 1 from rfl, itemsOf_cons hS.1]; rfl
  refine congrArg₂ (· ++ ·) ?_ (pRest4_spec Ws W hget hB hS κ m hL f (restSh4 S) 1 0 [] (some .seed) h1 le_rfl
    hS.2.1 hq fun n i h => by cases h)
  by_cases hf : f = fHdr
  · simp only [ctb4, hf, if_true]
    exact cpSlice4 Ws W hget hB κ (items4_zero hS) (by simp [Item.qlen]) (by decide) 0 10 rfl
  · simp only [ctb4, hf, if_false]; rfl

/-- **`seq4`'s format is readable as segments.** -/
theorem pfOk4_seq4 : PfOk4 seq4 := ⟨trOk4_seq4, by decide +kernel⟩

/-- **Every ladder of a 4.1 child** (`m ∈ {30, 31, 32}`) meets the siblings' facts at `seq4`. -/
theorem ladOk4_seq4 {m : ℕ} (hm : m = 30 ∨ m = 31 ∨ m = 32) : LadOk4 seq4 m := by
  intro i hi
  simp only [nLevels] at hi
  rcases hm with rfl | rfl | rfl <;> interval_cases i <;> decide

/-- The ladder of every kind byte is `30`, `31` or `32`. -/
theorem mOfB_mem (b : UInt8) : mOfB b = 30 ∨ mOfB b = 31 ∨ mOfB b = 32 := by
  unfold mOfB
  cases h : Snd.CKind.ofByte? b with
  | none => right; right; rfl
  | some k => cases k with
    | seg κ => cases κ <;> simp [Snd.CKind.m, SegKind.m]
    | node κ => cases κ <;> simp [Snd.CKind.m, NodeKind.m]

/-! ## Controls -/

/-- (−) **`qOk4` is not trivial**: a `queries` phase not right after its `P2` phase is rejected;
(+) `seq4`'s table passes. -/
theorem qOk4_ctl : qOk4 seq4 (some .seed) [.queries 0] = false ∧ qOk4 seq4 (some .seed) (restSh4 seq4) = true :=
  ⟨by decide, pfOk4_seq4.2⟩

/-- (value) **The ladder bytes**: `L30`'s byte reads ladder 30, `N2`'s 31, `N4`'s 32, `'A'` (no
kind) 32. -/
theorem mOfB_ctl : mOfB SegKind.L30.byte = 30 ∧ mOfB NodeKind.N2.byte = 31 ∧ mOfB NodeKind.N4.byte = 32 ∧
    mOfB aggByte = 32 := by decide

end FR.X

end G6_FRXPf4
