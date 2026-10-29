-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 9, item 1:
-- the node witness's output words, pure). 3.x analogue: `FRNodeReadP.signedWords_readSigned`,
-- `witWords_readWit` (one slot stream per child, no aggregate).
import FRXPf4
import FRNodeSound4R

/-!
# The node witness's output words, as segments over each segment's words

Signed child `σ`'s chain stream (`chainBytes4 κ σ k w`, `k` segments) holds segment `i`'s trace from
byte `1 + i·strideB` (revision 4.4.1, R-A′: `strideB = 64·sBlk`, a trace and a spacer entry). Its
**virtual words** `vS κ σ k i w` are the stream's `segB` bytes from `i·strideB` in words (whole chain
words: `strideB ≡ 0 mod 8`), so segment `i`'s trace is `trOf seq4 (vS …)` (**`segTr_eq`**: the bytes
before the trace and after it are not read). The output words of the node witness `readW4 sigH κ L es`
are then, per signed child, segments over those words (`FRXPf4`, `FRXTr4`), the aggregate header's
words and the signature's (`FRXSig4W`):

* **`signedWords_prev`** (a previous node, `κ.hasPrev`, child `0`): `|π|`, `pSeg4` at the ladder of
  word 10, `trSeg4`, then the signature's words;
* **`signedWords_agg`** (aggregate `a`, `k = kSel`): `|π_A| = 48 + k·piSize`, the header's six words,
  the `k` proofs' segments, the count `k·|items| + (k − 1)`, the `k` traces' bodies (`trBody4`), each
  after its spacer entry (`i ≥ 1`: `entryW (spEntry (spAns … i))`, `V_A`'s trace), the signature;
* **`witWords_readW4`**: the tag, both statements' cells' words, both children.
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

/-! ## Specification -/

/-- **Segment `i`'s virtual words**: `segB` bytes of signed child `σ`'s chain stream from
`i·strideB`, in words. -/
noncomputable def vS (κ : NodeKind) (σ k i : ℕ) (w : Circ.Asg) : List Word :=
  packBytes (((N4c.chainBytes4 κ σ k w).drop (i * N4c.strideB)).take N4c.segB)

/-- A trace's segment without its count word (an aggregate's traces share one count). -/
def trBody4 (S : Seq) : Seg := .cat seedSeg (tSegs4 S.lv 20 (restSh4 S))

/-- **The aggregate header's words** (`aggHdr k n e`): `'A' ‖ k ‖ 0⁶`, `n`, `e`. -/
def hdrWords (k n : ℕ) (e : Digest) : List Word := toWord (0x41 + 256 * k) :: toWord n :: packBytes e.toList

/-! ## Proof helpers: reading a trace off part of a stream -/

theorem getD_drop' (B : List UInt8) (D i : ℕ) : (B.drop D).getD i 0 = B.getD (D + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem entryAt_drop (B : List UInt8) (D o : ℕ) (it : Item) : entryAt B (D + o) it = entryAt (B.drop D) o it := by
  simp only [entryAt, List.drop_drop, getD_drop', Nat.add_assoc]

theorem readItems_drop (B : List UInt8) (D : ℕ) : ∀ (its : List Item) (o : ℕ),
    readItems B (D + o) its = readItems (B.drop D) o its
  | [], _ => rfl
  | it :: its, o => by
    rw [readItems, readItems, entryAt_drop, Nat.add_assoc, readItems_drop B D its]

theorem readItems_take (B : List UInt8) (N : ℕ) : ∀ (its : List Item) (o : ℕ),
    o + (its.map Item.slen).sum ≤ N → readItems (B.take N) o its = readItems B o its
  | [], _, _ => rfl
  | it :: its, o, h => by
    simp only [List.map_cons, List.sum_cons] at h
    rw [readItems, readItems, readItems_take B N its _ (by omega)]
    congr 1
    simp only [entryAt, Item.slen] at h ⊢
    refine Prod.ext ?_ ?_
    · simp only [List.drop_take, List.take_take]; congr 3; omega
    · refine Vector.ext fun j hj => ?_
      simp only [Vector.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_take]
      rw [if_pos (by omega)]

theorem wordsBytes_packBytes8 {b : List UInt8} (h : b.length % 8 = 0) : wordsBytes (packBytes b) = b := by
  have h1 := unpack_packBytes b
  have h2 : (wordsBytes (packBytes b)).length = b.length := by
    rw [wordsBytes_length, packBytes_length]; omega
  calc wordsBytes (packBytes b) = (wordsBytes (packBytes b)).take b.length := (List.take_of_length_le (by omega)).symm
    _ = b := h1

theorem segB_mod : N4c.segB % 8 = 0 := by decide

theorem chainBytes4_length (κ : NodeKind) (σ k : ℕ) (w : Circ.Asg) :
    (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := Stream.streamBytes_length _ _

theorem slen_eq : Item.slen = fun it => 8 + it.qlen + 32 := funext fun _ => rfl

theorem slen_sum_seq4 : 1 + ((itemsOf seq4).map Item.slen).sum = N4c.segB := by
  rw [N4c.segB_eq, streamBytesOf, slen_eq]

/-- `S`'s stream: the tag, the seed's `159` bytes, the later items. -/
theorem streamBytesOf_rest {S : Seq} (hS : TrOk4 S) :
    streamBytesOf S = 160 + (((restSh4 S).flatMap (Sh.itemsL S.lv)).map Item.slen).sum := by
  rw [streamBytesOf, ← slen_eq, itemsOf_cons hS.1, List.map_cons, List.sum_cons]
  simp only [Item.slen, Item.qlen]; omega

/-- **Segment `i`'s trace is read off its virtual words**, when the stream holds it. -/
theorem segTr_eq (κ : NodeKind) (σ k i : ℕ) (w : Circ.Asg)
    (hD : i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k) :
    N4s.segTr κ σ k i w = trOf seq4 (vS κ σ k i w) := by
  have hl : (((N4c.chainBytes4 κ σ k w).drop (i * N4c.strideB)).take N4c.segB).length = N4c.segB := by
    simp only [List.length_take, List.length_drop, chainBytes4_length]; omega
  rw [N4s.segTr, trOf, vS, wordsBytes_packBytes8 (by rw [hl]; exact segB_mod),
    readItems_take _ _ _ _ (by rw [slen_sum_seq4]), Nat.add_comm, readItems_drop]

theorem vS_length (κ : NodeKind) (σ k i : ℕ) (w : Circ.Asg)
    (hD : i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k) : (vS κ σ k i w).length = N4c.segB / 8 := by
  rw [vS, packBytes_length]
  simp only [List.length_take, List.length_drop, chainBytes4_length]
  have := segB_mod; omega

/-! ## A segment's proof and trace in words -/

section Seg

variable (κ : NodeKind) (σ k i : ℕ) (w : Circ.Asg) (hD : i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k)
  (V : ℕ → Word) (hV : ∀ u (hu : u < (vS κ σ k i w).length), (vS κ σ k i w)[u] = V u)

include hD in
theorem hB_vS : streamBytesOf seq4 ≤ 8 * (vS κ σ k i w).length := by
  rw [vS_length κ σ k i w hD, ← N4c.segB_eq]; have := segB_mod; omega

include hD hV in
/-- **Segment `i`'s proof in words** (`pf4`, at the ladder of virtual word 10). -/
theorem pf4_words (b : Bool) :
    bl (pf4 (N4s.segTr κ σ k i w)) = wordsBytes (segOut V b 0 (pSeg4 seq4 (mOfB (V 10).toNat.toUInt8))) := by
  rw [segTr_eq κ σ k i w hD, pf4]
  exact proof_words4 pfOk4_seq4 (ladOk4_seq4 (mOfB_mem _)) _ V hV (hB_vS κ σ k i w hD) b
    (trM4_eq seq4 trOk4_seq4 _ V hV (hB_vS κ σ k i w hD))

include hD hV in
/-- **Segment `i`'s trace in words.** -/
theorem logWords_segTr (b : Bool) : logWords (N4s.segTr κ σ k i w) = segOut V b 0 (trSeg4 seq4) := by
  rw [segTr_eq κ σ k i w hD]
  refine logWords_trSeg4 seq4 trOk4_seq4 _ V b hV ?_
  have h := hB_vS κ σ k i w hD
  rwa [streamBytesOf_rest trOk4_seq4] at h

include hD hV in
/-- **Segment `i`'s trace entries in words** (its trace's words without the count). -/
theorem entries_segTr (b : Bool) :
    (N4s.segTr κ σ k i w).flatMap entryW = segOut V b 0 (trBody4 seq4) := by
  have h := logWords_segTr κ σ k i w hD V hV b
  simp only [trSeg4, segOut] at h
  exact (List.cons.inj h).2

end Seg

/-! ## Proof helpers: the proofs' and the header's bytes -/

theorem pf4_length (tr : Trace) : (pf4 tr).data.toList.length = piSizeOf seq4 := by
  rw [Array.length_toList]; exact reassemble4_size seq4 tr

theorem slotPf_eq (κ : NodeKind) (v : ℕ) (w : Circ.Asg) :
    N4s.slotPf pf4 κ v w = bl (pf4 (N4s.slotTr4 κ v w)) := fitL_self (pf4_length _)

theorem sum_bytes_lt (f : ℕ → UInt8) : ∀ n, ((List.range n).map fun i => (f i).toNat * 256 ^ i).sum < 256 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, pow_succ]
    have h1 := sum_bytes_lt f n
    have h2 : (f n).toNat ≤ 255 := by have := (f n).toNat_lt; omega
    have h3 : (f n).toNat * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ h2
    nlinarith

theorem hAn_lt (κ : NodeKind) (a : ℕ) (w : Circ.Asg) : N4s.hAn κ a w < 2 ^ 64 := by
  have := sum_bytes_lt (fun i => (N4s.hA κ a w).getD (33 + i) 0) 8
  unfold N4s.hAn; norm_num at this ⊢; exact this

theorem wordBytes_toWord {x : ℕ} (hx : x < 2 ^ 64) : wordBytes (toWord x) = enc64 x := by
  rw [wordBytes, toNat_toWord hx]

/-- **The header's bytes are its words'** (`k ≤ 4`, `n < 2^64`). -/
theorem aggHdr_words {k n : ℕ} (hk : k ≤ 4) (hn : n < 2 ^ 64) (e : Digest) :
    aggHdr k n e = wordsBytes (hdrWords k n e) := by
  have he : wordsBytes (packBytes e.toList) = e.toList := wordsBytes_packBytes8 (by simp)
  rw [hdrWords, wordsBytes_cons, wordsBytes_cons, he, wordBytes_toWord (by omega), wordBytes_toWord hn, aggHdr]
  have : [aggByte, k.toUInt8] ++ List.replicate 6 0 = enc64 (0x41 + 256 * k) := by
    interval_cases k <;> decide
  rw [this, List.append_assoc]

/-! ## A signed child's words -/

theorem sgnX_π (sg : NodeKind → ℕ → Circ.Asg → Sig) (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) :
    (sgnX sg κ σ w).π = ((N4s.rd4 pf4).sgn κ σ w).π := rfl

theorem sgnX_tr (sg : NodeKind → ℕ → Circ.Asg → Sig) (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) :
    (sgnX sg κ σ w).tr = ((N4s.rd4 pf4).sgn κ σ w).tr := rfl

theorem aggPf_eq (κ : NodeKind) (a : ℕ) (w : Circ.Asg) : N4s.aggPf pf4 κ a w =
    ⟨(aggHdr (N4s.kAct κ a w) (N4s.hAn κ a w) (N4s.hAe κ a w) ++
    ((List.range (N4s.kAct κ a w)).map fun i => N4s.slotPf pf4 κ (N4c.sub κ a i) w).flatten).toArray⟩ := rfl

/-- **A previous node's words** (`κ.hasPrev`, child `0`): `|π|`, the proof's segment at the ladder of
word 10, the trace's, the signature's. -/
theorem signedWords_prev (κ : NodeKind) (hκ : κ.hasPrev = true) (w : Circ.Asg) (V : ℕ → Word)
    (hV : ∀ u (hu : u < (vS κ 0 0 0 w).length), (vS κ 0 0 0 w)[u] = V u) :
    signedWords (sgnX sigH κ 0 w) = toWord (piSizeOf seq4) ::
      (segOut V false 0 (pSeg4 seq4 (mOfB (V 10).toNat.toUInt8)) ++ segOut V false 0 (trSeg4 seq4)) ++
      sigWords (sigH κ 0 w) := by
  have hD : 0 * N4c.strideB + N4c.segB ≤ N4c.streamB κ 0 0 := by
    simp [N4c.streamB, N4c.isAgg, hκ]
  have hp : isPrevSlot κ 0 = true := by simp [isPrevSlot, hκ]
  have hs : N4s.slotTr4 κ 0 w = N4s.segTr κ 0 0 0 w := by rw [N4s.slotTr4, if_pos hp]
  have hn : N4c.isAgg κ 0 = false := by simp [N4c.isAgg, hκ]
  have e1 : (sgnX sigH κ 0 w).π = ⟨(bl (pf4 (N4s.segTr κ 0 0 0 w))).toArray⟩ := by
    simp only [sgnX, N4s.rd4, N4s.sgn4, hn, if_false, Bool.false_eq_true, slotPf_eq, hs]
  have e2 : (sgnX sigH κ 0 w).tr = N4s.segTr κ 0 0 0 w := by
    simp only [sgnX, N4s.rd4, N4s.sgn4, hn, if_false, Bool.false_eq_true, hs]
  have hl : (bl (pf4 (N4s.segTr κ 0 0 0 w))).length = piSizeOf seq4 := pf4_length _
  rw [signedWords, e1, e2, show (sgnX sigH κ 0 w).σ = sigH κ 0 w from rfl, logWords_segTr κ 0 0 0 w hD V hV false]
  simp only [bytesWords, hl]
  rw [pf4_words κ 0 0 0 w hD V hV false, packBytes_wordsBytes]
  simp only [List.cons_append, List.append_assoc]

theorem logWords_flatten (l : List Trace) :
    logWords l.flatten = toWord (l.map List.length).sum :: l.flatMap fun t => t.flatMap entryW := by
  show toWord l.flatten.length :: l.flatten.flatMap entryW = _
  rw [List.length_flatten]
  congr 1
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.flatten_cons, List.flatMap_append, ih, List.flatMap_cons]

/-- **The spacer entry's query words** (`bytesWords spacerQ`: the length `89`, then 12 words). -/
def spW : List Word := bytesWords spacerQ.data.toList

/-- **Segment `i`'s trace pieces in `V_A`'s trace**: the spacer entry before segment `i ≥ 1`, then the
segment's entries. -/
theorem entries_spSeg (ans : ℕ → Digest) (i : ℕ) (t : Trace) :
    ((if i = 0 then [] else [spEntry (ans i)]) ++ t).flatMap entryW =
      (if i = 0 then [] else spW ++ packBytes (ans i).toList) ++ t.flatMap entryW := by
  rw [List.flatMap_append]
  split_ifs
  · rfl
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]; rfl

theorem flatMap_flatten' {α β : Type} (l : List (List α)) (f : α → List β) :
    l.flatten.flatMap f = l.flatMap fun t => t.flatMap f := by
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.flatten_cons, List.flatMap_append, ih, List.flatMap_cons]

theorem aggTr_count (κ : NodeKind) (σ k : ℕ) (w : Circ.Asg) (ans : ℕ → Digest) :
    (aggTrace ans ((List.range k).map fun i => N4s.segTr κ σ k i w)).length = k * (itemsOf seq4).length + (k - 1) :=
  aggTrace_length ans _ _ (fun i => by simp only [N4s.segTr, readItems_length]) k

/-- **An aggregate's words** (aggregate `a`, signed child `aggChild κ a`, `k = kSel κ a w`
segments): `|π_A|`, the header's words, the `k` proofs', the count `k·|items| + (k − 1)`, the `k` traces'
bodies each after its spacer entry (`i ≥ 1`), the signature's. -/
theorem signedWords_agg (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) (w : Circ.Asg) (V : ℕ → ℕ → Word)
    (hV : ∀ i < kSel κ a w, ∀ u (hu : u < (vS κ (N4c.aggChild κ a) (kSel κ a w) i w).length),
      (vS κ (N4c.aggChild κ a) (kSel κ a w) i w)[u] = V i u) :
    signedWords (sgnX sigH κ (N4c.aggChild κ a) w) =
      toWord (48 + kSel κ a w * piSizeOf seq4) :: (hdrWords (kSel κ a w) (N4s.hAn κ a w) (N4s.hAe κ a w) ++
        (List.range (kSel κ a w)).flatMap fun i => segOut (V i) false 0 (pSeg4 seq4 (mOfB (V i 10).toNat.toUInt8))) ++
      (toWord (kSel κ a w * (itemsOf seq4).length + (kSel κ a w - 1)) ::
        (List.range (kSel κ a w)).flatMap fun i =>
          (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) (kSel κ a w) w i).toList) ++
            segOut (V i) false 0 (trBody4 seq4)) ++
      sigWords (sigH κ (N4c.aggChild κ a) w) := by
  have hk : N4s.kAct κ a w ≤ κ.maxK := N4s.kAct_le κ a w
  rw [kSel_eq] at hV ⊢
  generalize hkk : N4s.kAct κ a w = k at hV hk
  generalize hσ : N4c.aggChild κ a = σ at hV ⊢
  have hm4 : κ.maxK ≤ 4 := by cases κ <;> decide
  have hD : ∀ i < k, i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k := fun i hi => by
    rw [← hσ]
    simp only [N4c.streamB, N4c.isAgg_aggChild, if_true]
    rw [(N4c.aggB_blocks (by omega : 1 ≤ k)).2.2]
    have h1 : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
    have h2 : N4c.strideB = N4c.segB + 128 := by decide
    rw [Nat.add_one_mul] at h1; omega
  have hs : ∀ i ∈ List.range k, N4s.slotTr4 κ (N4c.sub κ a i) w = N4s.segTr κ σ k i w :=
    fun i hi => by rw [N4s.slotTr4_sub κ ha (by have := List.mem_range.1 hi; omega), hkk, hσ]
  have hsg : (N4s.rd4 pf4).sgn κ σ w = ⟨N4s.aggPf pf4 κ a w,
      aggTrace (N4s.spAns κ σ k w) ((List.range k).map fun i => N4s.slotTr4 κ (N4c.sub κ a i) w),
      N4s.readSig4 κ σ w⟩ := by
    rw [← hσ, show (N4s.rd4 pf4).sgn = N4s.sgn4 pf4 from rfl, N4s.sgn4_agg pf4 κ ha, hkk]
  have hmP : ((List.range k).map fun i => N4s.slotPf pf4 κ (N4c.sub κ a i) w) =
      (List.range k).map fun i => bl (pf4 (N4s.segTr κ σ k i w)) :=
    List.map_congr_left fun i hi => by rw [slotPf_eq, hs i hi]
  have hmT : ((List.range k).map fun i => N4s.slotTr4 κ (N4c.sub κ a i) w) =
      (List.range k).map fun i => N4s.segTr κ σ k i w := List.map_congr_left hs
  have e1 : (sgnX sigH κ σ w).π = ⟨(aggHdr k (N4s.hAn κ a w) (N4s.hAe κ a w) ++
      ((List.range k).map fun i => bl (pf4 (N4s.segTr κ σ k i w))).flatten).toArray⟩ := by
    rw [sgnX_π, hsg, aggPf_eq, hkk, hmP]
  have e2 : (sgnX sigH κ σ w).tr = aggTrace (N4s.spAns κ σ k w) ((List.range k).map fun i => N4s.segTr κ σ k i w) := by
    rw [sgnX_tr, hsg, hmT]
  have hpf : ((List.range k).map fun i => bl (pf4 (N4s.segTr κ σ k i w))).flatten =
      wordsBytes ((List.range k).flatMap fun i => segOut (V i) false 0 (pSeg4 seq4 (mOfB (V i 10).toNat.toUInt8))) := by
    rw [wordsBytes_flatMap, List.flatMap_def, List.map_congr_left fun i hi => pf4_words κ σ k i w
      (hD i (List.mem_range.1 hi)) (V i) (hV i (List.mem_range.1 hi)) false]
  have hlen : (aggHdr k (N4s.hAn κ a w) (N4s.hAe κ a w) ++
      ((List.range k).map fun i => bl (pf4 (N4s.segTr κ σ k i w))).flatten).length = 48 + k * piSizeOf seq4 := by
    rw [List.length_append, N4s.aggHdr_length, List.length_flatten, List.map_map]
    simp only [Function.comp_def, pf4_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  have ht : (aggTrace (N4s.spAns κ σ k w) ((List.range k).map fun i => N4s.segTr κ σ k i w)).flatMap entryW =
      (List.range k).flatMap fun i => (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ σ k w i).toList) ++
        segOut (V i) false 0 (trBody4 seq4) := by
    rw [aggTrace_range, flatMap_flatten', List.flatMap_map]
    refine List.flatMap_congr fun i hi => ?_
    rw [entries_spSeg, entries_segTr κ σ k i w (hD i (List.mem_range.1 hi)) (V i) (hV i (List.mem_range.1 hi)) false]
  have hh : packBytes (aggHdr k (N4s.hAn κ a w) (N4s.hAe κ a w) ++
      ((List.range k).map fun i => bl (pf4 (N4s.segTr κ σ k i w))).flatten) =
      hdrWords k (N4s.hAn κ a w) (N4s.hAe κ a w) ++
        (List.range k).flatMap fun i => segOut (V i) false 0 (pSeg4 seq4 (mOfB (V i 10).toNat.toUInt8)) := by
    rw [hpf, aggHdr_words (by omega) (hAn_lt κ a w), ← wordsBytes_append, packBytes_wordsBytes]
  have hb : bytesWords (sgnX sigH κ σ w).π.data.toList = toWord (48 + k * piSizeOf seq4) ::
      (hdrWords k (N4s.hAn κ a w) (N4s.hAe κ a w) ++
        (List.range k).flatMap fun i => segOut (V i) false 0 (pSeg4 seq4 (mOfB (V i 10).toNat.toUInt8))) := by
    rw [e1, bytesWords, ← hh, ← hlen]
  have hl : logWords (sgnX sigH κ σ w).tr = toWord (k * (itemsOf seq4).length + (k - 1)) ::
      (List.range k).flatMap fun i => (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ σ k w i).toList) ++
        segOut (V i) false 0 (trBody4 seq4) := by
    show toWord (sgnX sigH κ σ w).tr.length :: (sgnX sigH κ σ w).tr.flatMap entryW = _
    rw [e2, aggTr_count, ht]
  show bytesWords (sgnX sigH κ σ w).π.data.toList ++ logWords (sgnX sigH κ σ w).tr ++ sigWords (sigH κ σ w) = _
  rw [hb, hl]

/-- **The node witness's words**: the tag, both statements' cells' words, both signed children. -/
theorem witWords_readW4 (κ : NodeKind) (L es : Log) :
    witWords (readW4 sigH κ L es) = toWord 1 ::
      (elemWords (wF κ L es (N4c.stC κ 0 0)) ++ elemWords (wF κ L es (N4c.stC κ 0 1)) ++
        (elemWords (wF κ L es (N4c.stC κ 1 0)) ++ elemWords (wF κ L es (N4c.stC κ 1 1))) ++
        signedWords (sgnX sigH κ 0 (wF κ L es)) ++ signedWords (sgnX sigH κ 1 (wF κ L es))) := by
  rw [readW4, witWords, stD, stD, packBytes_digestOf, packBytes_digestOf]
  simp only [List.cons_append, List.append_assoc]

/-! ## The witness fits the output format -/

theorem slotPf_length (κ : NodeKind) (v : ℕ) (w : Circ.Asg) :
    (N4s.slotPf pf4 κ v w).length = piSizeOf seq4 := N4s.fitL_length _ _

/-- **Signed child `σ` fits the output format.** -/
theorem sgnX_fits (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) : (sgnX sigH κ σ w).Fits := by
  have hq : ∀ v, ∀ e ∈ N4s.slotTr4 κ v w, e.1.size < 2 ^ 64 := fun v e he =>
    lt_of_le_of_lt (N4s.slotTr4_qcap κ v w e he) (by decide)
  have hk := N4s.kAct_le κ (N4c.aggOf κ σ) w
  have hm4 : κ.maxK ≤ 4 := by cases κ <;> decide
  have hp : piSizeOf seq4 = 876304 := piSizeOf_seq4
  refine ⟨?_, ?_, ?_, show idxH κ σ w < 2 ^ 64 from ofLE_lt64 (by simp),
    show (sigH κ σ w).ots.length = _ by simp [sigH], show (sigH κ σ w).path.length = _ by simp [sigH]⟩
  · rw [sgnX_π, show (N4s.rd4 pf4).sgn = N4s.sgn4 pf4 from rfl, N4s.sgn4]
    split_ifs
    · rw [aggPf_eq]
      simp only [ByteArray.size, List.size_toArray, List.length_append, N4s.aggHdr_length, List.length_flatten,
        List.map_map, Function.comp_def, slotPf_length, List.map_const', List.length_range, List.sum_replicate,
        smul_eq_mul]
      have : N4s.kAct κ (N4c.aggOf κ σ) w * piSizeOf seq4 ≤ 4 * 876304 := by rw [hp]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    · simp only [ByteArray.size, List.size_toArray, slotPf_length, hp]; norm_num
  · rw [sgnX_tr, show (N4s.rd4 pf4).sgn = N4s.sgn4 pf4 from rfl, N4s.sgn4]
    split_ifs
    · rw [aggTrace_length _ _ 8783 (fun i => N4s.slotTr4_length κ _ w)]
      have : N4s.kAct κ (N4c.aggOf κ σ) w * 8783 ≤ 4 * 8783 := Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [N4s.slotTr4_length]; norm_num
  · rw [sgnX_tr, show (N4s.rd4 pf4).sgn = N4s.sgn4 pf4 from rfl, N4s.sgn4]
    split_ifs
    · intro e he
      rcases mem_aggTrace he with ⟨i, -, het⟩ | ⟨i, rfl⟩
      · exact hq _ e het
      · show spacerQ.size < 2 ^ 64; rw [spacerQ_size]; norm_num
    · exact hq 0

/-- **The node witness the decoder outputs fits the output format** (`decodeWit_witWords`). -/
theorem readW4_fits (κ : NodeKind) (L es : Log) : (readW4 sigH κ L es).Fits :=
  ⟨sgnX_fits κ 0 _, sgnX_fits κ 1 _⟩

end FR.X
