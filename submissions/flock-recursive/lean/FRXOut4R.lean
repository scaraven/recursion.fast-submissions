-- G6: this module also holds the former modules `FRXOut4W`, `FRXOut4C` (one section each, in import order).
import FRXPf4
import FRNodeRun4
import FRXSpec

section G6_FRXOut4W

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 9, item 1:
-- the node witness's output words, pure). 3.x analogue: `FRNodeReadP.signedWords_readSigned`,
-- `witWords_readWit` (one slot stream per child, no aggregate).

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

end G6_FRXOut4W

section G6_FRXOut4C

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 10,
-- item 1: a signed child's chain words and the aggregate header's words as H message words, pure).

/-!
# Chain words and header words as H message words

Signed child `σ`'s chain stream (`chainBytes4 κ σ k w`) is H's message byte stream over the blocks
`blkOf κ σ k i` (the main chain's, the last one redirected to `finBlk`). Its **chain words**
`chW κ σ k w n` are H message words (`hMW`, `FRXSig4W`) of those blocks:

* **`chainBytes4_getD`**: chain byte `p` is byte `p mod 8` of chain word `⌊p/8⌋`;
* **`vS_get`**: segment `i`'s virtual word `u` is chain word `i·(strideB/8) + u` (revision 4.4.1's
  stride is whole words);
* **`spAns_words`**: spacer `i`'s answer is four shift-1 pairs of chain words from `i·(strideB/8) − 4`
  (it sits at stream bytes `i·strideB − 31 … i·strideB`);
* **`hAe_words`**, **`hAn_word`**: the aggregate header's `e` and `n` are shift-1 pairs of the
  `c_A` block's message words.
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

/-! ## Specification -/

/-- **Chain word `n`** of signed child `σ`'s stream (`k` segments): H message word `n mod 8` of
stream block `⌊n/8⌋`'s block. -/
def chW (κ : NodeKind) (σ k : ℕ) (w : Circ.Asg) (n : ℕ) : Word :=
  hMW w (8 * N4c.blkOf κ σ k (n / 8) + n % 8)

/-! ## Shifted pairs at shift `0` -/

theorem shWd_zero (W : ℕ → Word) (n : ℕ) : shWd W 0 n = W n := by
  apply BitVec.eq_of_toNat_eq
  simp [shWd]

/-- **The word of the bytes `8n + s + k`** (`k < 8`) of a word stream is the shifted pair at
`(s, n)`, for every `s < 8`. -/
theorem wOf_shift (W : ℕ → Word) {s : ℕ} (hs : s < 8) (n : ℕ) :
    wOf (fun k => (wordBytes (W ((8 * n + s + k) / 8))).getD ((8 * n + s + k) % 8) 0) = shWd W s n := by
  refine wOf_eq fun k hk => ?_
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · rw [shWd_zero, show (8 * n + 0 + k) / 8 = n by omega, show (8 * n + 0 + k) % 8 = k by omega]
  rw [shWd_byte W hs0 hs n hk]
  split_ifs with h
  · rw [show (8 * n + s + k) / 8 = n by omega, show (8 * n + s + k) % 8 = s + k by omega]
  · rw [show (8 * n + s + k) / 8 = n + 1 by omega, show (8 * n + s + k) % 8 = k + s - 8 by omega]

/-! ## Chain bytes and words -/

theorem streamBytes_getD' (f : ℕ → Block.Pos → Bool) {L p : ℕ} (hp : p < L) :
    (Stream.streamBytes f L).getD p 0 = (Block.msgBytes (f (p / 64))).getD (p % 64) 0 := by
  rw [Block.msgBytes_getD _ (Nat.mod_lt _ (by norm_num))]
  simp only [Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some]

/-- **Chain byte `p`** is byte `p mod 8` of chain word `⌊p/8⌋`. -/
theorem chainBytes4_getD (κ : NodeKind) (σ k : ℕ) (w : Circ.Asg) {p : ℕ} (hp : p < N4c.streamB κ σ k) :
    (N4c.chainBytes4 κ σ k w).getD p 0 = (wordBytes (chW κ σ k w (p / 8))).getD (p % 8) 0 := by
  have e1 : p / 8 / 8 = p / 64 := by rw [Nat.div_div_eq_div_mul]
  rw [N4c.chainBytes4, streamBytes_getD' _ hp, chW, hMW_byte w _ (Nat.mod_lt _ (by norm_num)), hMBs, e1,
    show (8 * (8 * N4c.blkOf κ σ k (p / 64) + p / 8 % 8) + p % 8) / 64 = N4c.blkOf κ σ k (p / 64) by omega,
    show (8 * (8 * N4c.blkOf κ σ k (p / 64) + p / 8 % 8) + p % 8) % 64 = p % 64 by omega,
    hMB_eq w _ (Nat.mod_lt _ (by norm_num))]
  rfl

theorem getD_packBytes {b : List UInt8} {j : ℕ} (hj : 8 * j + 8 ≤ b.length) (hl : j < (packBytes b).length) :
    (packBytes b)[j] = wOf fun k => b.getD (8 * j + k) 0 := by
  simp only [packBytes, List.getElem_map, List.getElem_range, wOf]
  congr 2
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  simp only [List.length_take, List.length_drop, List.length_map, List.length_range] at h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 8 * j + k < b.length by omega),
    Option.getD_some]

theorem strideB_8 : N4c.strideB = 8 * (N4c.strideB / 8) := by decide

/-- **Segment `i`'s virtual word `u`** is chain word `i·(strideB/8) + u`. -/
theorem vS_get (κ : NodeKind) (σ k i : ℕ) (w : Circ.Asg)
    (hD : i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k) {u : ℕ} (hu : u < (vS κ σ k i w).length) :
    (vS κ σ k i w)[u] = chW κ σ k w (i * (N4c.strideB / 8) + u) := by
  have hl := vS_length κ σ k i w hD
  have h8 := segB_mod
  have hcl := chainBytes4_length κ σ k w
  have hu2 : u < N4c.segB / 8 := hl ▸ hu
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = i * (N4c.strideB / 8) := ⟨_, rfl⟩
  have hD8 : i * N4c.strideB = 8 * Q := by
    rw [hQ]; have h := strideB_8; generalize N4c.strideB / 8 = d at h ⊢; rw [h]; ring
  rw [hD8] at hD
  have hb : (List.take N4c.segB (List.drop (i * N4c.strideB) (N4c.chainBytes4 κ σ k w))).length =
      N4c.segB := by simp only [List.length_take, List.length_drop]; omega
  simp only [vS] at hu ⊢
  rw [getD_packBytes (by omega) hu, ← shWd_zero (chW κ σ k w), ← wOf_shift _ (by norm_num : 0 < 8)]
  refine wOf_congr fun x hx => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega), List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, chainBytes4_getD κ σ k w (by omega), hD8, ← hQ,
    show 8 * Q + (8 * u + x) = 8 * (Q + u) + 0 + x by omega]

/-- **Spacer `i`'s answer** (`1 ≤ i`, the spacer inside the stream): four shift-1 pairs of chain words
from `i·(strideB/8) − 4`. -/
theorem spAns_words (κ : NodeKind) (σ k : ℕ) (w : Circ.Asg) {i : ℕ} (hi1 : 1 ≤ i)
    (hD : i * N4c.strideB < N4c.streamB κ σ k) :
    packBytes (N4s.spAns κ σ k w i).toList =
      (List.range 4).map fun j => shWd (chW κ σ k w) 1 (i * (N4c.strideB / 8) - 4 + j) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = i * (N4c.strideB / 8) := ⟨_, rfl⟩
  have hD8 : i * N4c.strideB = 8 * Q := by
    rw [hQ]; have h := strideB_8; generalize N4c.strideB / 8 = d at h ⊢; rw [h]; ring
  have hQ4 : 16 ≤ Q := by
    rw [hQ]; have : N4c.strideB / 8 ≤ i * (N4c.strideB / 8) := Nat.le_mul_of_pos_left _ hi1
    have : 16 ≤ N4c.strideB / 8 := by decide
    omega
  rw [hD8] at hD
  rw [← hQ]
  have hl : (packBytes (N4s.spAns κ σ k w i).toList).length = 4 := packBytes_digest_length _
  refine List.ext_getElem (by rw [hl]; simp) fun j h1 h2 => ?_
  have hj : j < 4 := by rw [hl] at h1; exact h1
  rw [getD_packBytes (by simp; omega) h1, List.getElem_map, List.getElem_range, ← wOf_shift _ (by norm_num : 1 < 8)]
  refine wOf_congr fun x hx => ?_
  have hp : 8 * Q - 128 + 8 + N4s.spItem.qlen + (8 * j + x) = 8 * (Q - 4 + j) + 1 + x := by
    simp only [N4s.spItem, Item.qlen]; omega
  simp only [N4s.spAns, N4s.spAnsB, Read.entryAt]
  rw [List.getD_eq_getElem?_getD, Vector.toList_ofFn, List.getElem?_ofFn, dif_pos (by omega), Option.getD_some]
  show (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB - 128 + 8 + N4s.spItem.qlen + (8 * j + x)) 0 = _
  rw [hD8, hp, chainBytes4_getD κ σ k w (by omega)]

/-! ## The aggregate header's words -/

theorem hA_getD (κ : NodeKind) (a : ℕ) (w : Circ.Asg) {p : ℕ} (hp : p < 41) :
    (N4s.hA κ a w).getD p 0 = hMB w (N4c.cAB κ a) p := by
  rw [N4s.hA, streamBytes_getD' _ hp, hMB_eq w _ (by omega), Nat.mod_eq_of_lt (show p < 64 by omega)]

/-- **The header's `e`**: four shift-1 pairs from word `8·c_A`. -/
theorem hAe_words (κ : NodeKind) (a : ℕ) (w : Circ.Asg) :
    packBytes (N4s.hAe κ a w).toList = (List.range 4).map fun j => shWd (hMW w) 1 (8 * N4c.cAB κ a + j) := by
  refine packBytes_hMBs w (by norm_num) (by norm_num) _ fun i hi => ?_
  rw [N4s.hAe, Vector.getElem_ofFn, hA_getD κ a w (by omega),
    show 8 * (8 * N4c.cAB κ a) + 1 + i = 64 * N4c.cAB κ a + (1 + i) by ring, hMBs_blk _ _ (by omega)]

theorem ofLE_append' (l₁ l₂ : List UInt8) : ofLE (l₁ ++ l₂) = ofLE l₁ + 256 ^ l₁.length * ofLE l₂ := by
  induction l₁ with
  | nil => simp [ofLE]
  | cons a l ih =>
    have e : ∀ m, ofLE (a :: m) = a.toNat + 256 * ofLE m := fun _ => rfl
    rw [List.cons_append, e, e, ih, List.length_cons, pow_succ]; ring

theorem ofLE_range8 (f : ℕ → UInt8) : ∀ n,
    ofLE ((List.range n).map f) = ((List.range n).map fun i => (f i).toNat * 256 ^ i).sum
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ofLE_append', ofLE_range8 f n,
      List.length_map, List.length_range]
    simp [ofLE]; ring

/-- **The header's `n`**: the shift-1 pair at word `8·c_A + 4`. -/
theorem hAn_word (κ : NodeKind) (a : ℕ) (w : Circ.Asg) :
    toWord (N4s.hAn κ a w) = shWd (hMW w) 1 (8 * N4c.cAB κ a + 4) := by
  rw [← wOf_hMBs w (by norm_num) (by norm_num), wOf, ofLE_range8 _ 8, N4s.hAn]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hi8 := List.mem_range.1 hi
  rw [hA_getD κ a w (by omega), show 8 * (8 * N4c.cAB κ a + 4) + 1 + i = 64 * N4c.cAB κ a + (33 + i) by
    ring, hMBs_blk _ _ (by omega)]

end FR.X

end G6_FRXOut4C

section G6_FRXOut4R

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; stage S-H4, pass 10, item 2: the
-- node output's machine pieces). 3.x analogue: `FRXOutRun` (one slot stream, no shift, no aggregate).

/-!
# The node output's machine pieces

After the decode, H's message words are heap words at `hAddr κ n` (`FRXSig4W`), the shape `apH κ`
over the base `hBase κ`. A signed child's chain words are H words of the blocks `blkOf` (the last one
redirected to `finBlk`), so

* **the chain loader** `ldC κ` reads chain word `n` at H word `n + cb + [⌊n/8⌋ = jL]·Δ` (registers
  `qCB`, `qJ`, `qDl`: the chain's base, its last block, the redirect);
* **the copy loop** `cpSeg κ` writes segment `i`'s `segB/8` virtual words into the buffer at `bufB`
  (shape `apB`): word `u` is the loader's word `C(q + u)`, `q = i·strideB/8` (**`cpSeg_sem`**; revision
  4.4.1's stride is whole chain words, so no shift: 4.1's realign loop is gone). The heap below `bufB`
  is kept, so the decode's cells stay readable.

The emitters over the buffer are 3.x's `segIR` unchanged (`FRXOut.segIR_sem`, linear in the
buffer's shape).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers (below `FRXOut`'s, which the segments write) -/

/-- The chain word index. -/ def qN : ℕ := 100
/-- The buffer index. -/ def qU : ℕ := 101
/-- `8s`. -/ def qA : ℕ := 102
/-- `63 − 8s`. -/ def qB : ℕ := 103
/-- The chain's last stream block. -/ def qJ : ℕ := 104
/-- The redirect `Δ`. -/ def qDl : ℕ := 105
/-- `8 ·` the chain's first block. -/ def qCB : ℕ := 106
/-- The segment count `k`. -/ def qK : ℕ := 107
/-- The segment index `i`. -/ def qI : ℕ := 108
/-- The copy loop's counter. -/ def qLc : ℕ := 109
/-- The copy loop's count. -/ def qLn : ℕ := 110
/-- The segment loop's counter. -/ def qSc : ℕ := 111
/-- Scratch. -/ def qT1 : ℕ := 112
/-- Scratch. -/ def qT2 : ℕ := 113
/-- The loader's index. -/ def qM : ℕ := 120

/-! ## Shapes, bases -/

/-- **H's shape** at node kind `κ`: 3.x's stream shape at level 0's row stride. -/
def apH (κ : NodeKind) : AP := ⟨3, 3, 2, T4.mLog (.node κ) 0 + 1⟩

/-- **H's base**: row 4 of level 0's decoded rows (`hAddr_eq`). -/
def hBase (κ : NodeKind) : ℕ := map4.l0.ob + 2 ^ (T4.mLog (.node κ) 0 + 1) * 3

/-- The buffer's shape. -/
def apB : AP := ⟨3, 3, 2, 20⟩

/-- **The buffer's base**: level 0's word region (free after the decode). -/
def bufB : ℕ := 134217728

/-- The buffer's words per segment (`segB / 8`). -/
def nW : ℕ := 193888

/-- Buffer word `u`'s address. -/
def bufA (u : ℕ) : ℕ := bufB + u / 2 % 4 * 2 ^ 20 + u / 8 * 4 + u % 2

/-! ## The chain loader and the copy loop -/

/-- **The chain loader**: `oX :=` H word `qM + qCB + [qM >>> 3 = qJ]·qDl`. -/
def ldC (κ : NodeKind) : XIR :=
  .seq (.blk [.const oK (toWord 3), .op .shr qT1 qM oK, .op .eq qT1 qT1 qJ, .op .mul qT1 qT1 qDl,
    .op .add oU qM qCB, .op .add oU oU qT1]) (ldw (apH κ))

/-- **One copied word**: chain word `qN` (the loader) stored at buffer word `qU`. -/
def cpBody (κ : NodeKind) : XIR :=
  .seq (.blk [.const oR (toWord (hBase κ)), .op .or qM qN qN]) (.seq (ldC κ)
  (.seq (.blk [.const oR (toWord bufB), .op .or oU qU qU])
  (.seq (.blk (ldPs apB)) (.seq (.store oAd oX) (.blk [.op .add qN qN cOne, .op .add qU qU cOne])))))

/-- **Segment `qI`'s copy**: `q := qI·(strideB/8)` (whole chain words: `strideB ≡ 0 mod 8`), then
`nW` words. -/
def cpSeg (κ : NodeKind) : XIR :=
  .seq (.blk [.const qT1 (toWord (N4c.strideB / 8)), .op .mul qN qI qT1, .const qU 0, .const qLn (toWord nW)])
    (.loopK qLc qLn (toWord nW) (cpBody κ))

/-! ## Proof helpers: addresses -/

theorem addrH_toNat {st R u : ℕ} (hst : st ≤ 20) (hR : R < 2 ^ 62) (hu : u < 2 ^ 64) :
    (addrW ⟨3, 3, 2, st⟩ (toWord R) (toWord u)).toNat = R + u / 2 % 4 * 2 ^ st + u / 8 * 4 + u % 2 := by
  have h20 : 2 ^ st ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hst
  simp only [addrW]
  have h4 : u / 2 % 4 * 2 ^ st ≤ 3 * 2 ^ 20 := Nat.mul_le_mul (by omega) h20
  rw [shr_toWord hu (by norm_num), show (3 : ℕ) = 2 ^ 2 - 1 from rfl,
    and_mask_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hu) (by norm_num),
    shl_toWord (by omega) (by norm_num; omega), shr_toWord hu (by norm_num),
    shl_toWord (by norm_num) (by omega), and_one_toWord hu, add_toWord, add_toWord, add_toWord,
    toNat_toWord (by norm_num; omega)]
  norm_num

theorem mLog0_le (κ : NodeKind) : T4.mLog (.node κ) 0 + 1 ≤ 20 := by cases κ <;> decide

theorem hAddr_apH (κ : NodeKind) {n : ℕ} (hn : n < 2 ^ 64) :
    (addrW (apH κ) (toWord (hBase κ)) (toWord n)).toNat = hAddr κ n := by
  rw [apH, addrH_toNat (mLog0_le κ) (by cases κ <;> decide) hn, hAddr_eq, hBase]; ring

theorem bufA_apB {u : ℕ} (hu : u < 2 ^ 64) : (addrW apB (toWord bufB) (toWord u)).toNat = bufA u := by
  rw [apB, addrH_toNat le_rfl (by decide) hu, bufA]

theorem hAddr_lt (κ : NodeKind) {n : ℕ} (hn : n / 8 * 128 + 8 ≤ 2 ^ (κ.m - 7)) : hAddr κ n < bufB := by
  rw [hAddr_eq]
  have h4 : n / 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  cases κ <;> simp only [NodeKind.m, bufB] at hn ⊢ <;>
    simp only [show T4.mLog (.node .N2) 0 = 18 from rfl, show T4.mLog (.node .N4) 0 = 19 from rfl,
      show T4.mLog (.node .N8) 0 = 19 from rfl] <;> omega

theorem regs_hAddr (κ : NodeKind) (n : ℕ) : regs ≤ hAddr κ n := by
  rw [hAddr_eq]; simp only [regs]; omega

theorem bufA_inj {u v : ℕ} (hu : u < nW) (hv : v < nW) (h : bufA u = bufA v) : u = v := by
  simp only [bufA, nW] at *
  have b1 : u / 8 * 4 + u % 2 < 2 ^ 20 := by omega
  have b2 : v / 8 * 4 + v % 2 < 2 ^ 20 := by omega
  have h1 : u / 2 % 4 = v / 2 % 4 := by omega
  have h2 : u / 8 = v / 8 := by omega
  omega

theorem bufA_ge (u : ℕ) : bufB ≤ bufA u := by simp only [bufA]; omega

theorem bufA_lt {u : ℕ} (hu : u < nW) : bufA u < bufB + 2 ^ 22 := by simp only [bufA, nW] at *; omega

/-! ## The output phase's frame -/

/-- **The output phase's frame**: the invariant, the size, and the heap below the buffer as
`M₀`'s (the decode's cells). -/
structure OF (M₀ : Mem) (s : St) : Prop where
  inv : Inv s.M
  size : s.M.size = M₀.size
  low : ∀ y, regs ≤ y → y < bufB → rd s.M y = rd M₀ y

theorem of_loK {M₀ : Mem} (I : Array Word) {P : XIR} (hL : LoK P) (hw : WF P) {s : St} (h : OF M₀ s) :
    OF M₀ (semXIR I P s) :=
  ⟨inv_sem I hw h.inv, (size_sem I P s).trans h.size, fun y h1 h2 => (hframeK I P s hL y h1).trans (h.low y h1 h2)⟩

theorem of_decS {M₀ : Mem} {c : ℕ} (hc4 : 4 ≤ c) (hc : c < regs) {s : St} (h : OF M₀ s) : OF M₀ (decS c s) :=
  ⟨inv_decS h.inv hc4, (size_decS c s).trans h.size, fun y h1 h2 => (rd_decS (by omega) s).trans (h.low y h1 h2)⟩

/-! ## The chain loader's semantics -/

/-- **The H word the loader reads** for chain word `n`: `n + cb`, plus `Δ` in block `jL`. -/
def ldIx (cb jL Δ n : ℕ) : ℕ := n + cb + if n / 8 = jL then Δ else 0

theorem eq_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.eq.eval (toWord a) (toWord b) = if a = b then 1 else 0 := by
  simp only [XOp.eval, toWord_eq_iff ha hb]

theorem ite_mul_toWord (p : Prop) [Decidable p] (d : ℕ) :
    XOp.mul.eval (if p then 1 else 0) (toWord d) = toWord (if p then d else 0) := by
  split_ifs <;> simp [XOp.eval, toWord]

theorem ldC_sem (I : Array Word) (κ : NodeKind) (s : St) (hM : Inv s.M) {n cb jL Δ : ℕ}
    (hR : rd s.M oR = toWord (hBase κ)) (hn : rd s.M qM = toWord n) (hcb : rd s.M qCB = toWord cb)
    (hj : rd s.M qJ = toWord jL) (hd : rd s.M qDl = toWord Δ) (hb : n + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) :
    rd (semXIR I (ldC κ) s).M oX = rd s.M (hAddr κ (ldIx cb jL Δ n)) ∧ (semXIR I (ldC κ) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs
  rw [ldC, semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const oK (toWord 3), .op .shr qT1 qM oK, .op .eq qT1 qT1 qJ, .op .mul qT1 qT1 qDl,
    .op .add oU qM qCB, .op .add oU oU qT1] with hps
  have hu : rd (runPrims ps s.M) oU = toWord (ldIx cb jL Δ n) := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, qT1, qM, qJ, qDl, qCB] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hn, hj, hd, hcb, shr_toWord (by omega) (by norm_num), eq_toWord (by omega) hjl, ite_mul_toWord,
      add_toWord, add_toWord, ldIx]
    norm_num
  have hr : rd (runPrims ps s.M) oR = toWord (hBase κ) := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, qT1, oR] at *; omega)) only [rd_set_ne]
    exact hR
  have hh : ∀ y, regs ≤ y → rd (runPrims ps s.M) y = rd s.M y := fun y hy =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [regs] at hy
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst, oK, oU, qT1] at he <;> omega) _
  have hI : ldIx cb jL Δ n < 2 ^ 64 := by unfold ldIx; split_ifs <;> omega
  have hA : (addrW (apH κ) (rd (runPrims ps s.M) oR) (rd (runPrims ps s.M) oU)).toNat = hAddr κ (ldIx cb jL Δ n) := by
    rw [hr, hu, hAddr_apH κ hI]
  have hM1 : Inv (runPrims ps s.M) := inv_sem I (P := .blk ps) (fun p hp => by
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prim.dst, oK, oU, qT1]) hM
  obtain ⟨l1, l2⟩ := ldw_sem I (apH κ) ⟨runPrims ps s.M, s.o⟩ hM1 (by rw [hA]; exact regs_hAddr κ _)
  exact ⟨by rw [l1, hA, hh _ (regs_hAddr κ _)], l2⟩

theorem wf_ldC (κ : NodeKind) : WF (ldC κ) :=
  ⟨by simp +decide [WF], wf_ldw _⟩

theorem loK_ldC (κ : NodeKind) : LoK (ldC κ) :=
  ⟨by simp +decide [LoK, regs], loK_ldw _⟩

theorem keep_ldC (I : Array Word) (κ : NodeKind) {t : St} (hM : Inv t.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX]) : rd (semXIR I (ldC κ) t).M r = rd t.M r :=
  keep_of I (wf_ldC κ) hM hr (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    simp [wrL, ldC, ldw, ldPs, Prim.dst, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, eq_comm])

/-- The address block's value (`ldw_sem`'s first half). -/
theorem ldPs_oAd (ap : AP) (M : Mem) (hM : Inv M) :
    rd (runPrims (ldPs ap) M) oAd = addrW ap (rd M oR) (rd M oU) := by
  have hs := hM.1
  have h1 := one_cOne hM
  simp only [regs] at hs
  simp only [ldPs, runPrims, List.foldl, Prim.run]
  simp (disch := (simp only [size_set, oK, oT1, oT2, oT3, oAd, oX, oU, oR, cOne]; omega))
    only [rd_set_self, rd_set_ne, h1]
  simp only [addrW]

theorem ldPs_keep (ap : AP) (M : Mem) {r : ℕ} (h : r ∉ [oK, oT1, oT2, oT3, oAd]) :
    rd (runPrims (ldPs ap) M) r = rd M r :=
  rd_runPrims_of_not_writes (fun p hp he => by
    simp only [ldPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prim.dst] at he <;> subst he <;> simp at h) _

/-! ## Shifts (the shifted pair's, `FRXOut4E.shwC`) -/

theorem shl_shl_one (x : Word) {sh : ℕ} (hs : sh < 8) :
    XOp.shl.eval (XOp.shl.eval x 1) (toWord (63 - 8 * sh)) = x <<< (64 - 8 * sh) := by
  rw [shl_c _ _ (by omega)]
  simp only [XOp.eval]
  rw [show ((1 : Word).toNat % 64) = 1 from rfl, ← BitVec.shiftLeft_add]
  congr 1; omega

theorem shr_8s (x : Word) {sh : ℕ} (hs : sh < 8) : XOp.shr.eval x (toWord (8 * sh)) = x >>> (8 * sh) :=
  shr_c _ _ (by omega)

/-! ## The copy loop's semantics -/

/-- **The copy loop's invariant** after `j` words. -/
structure CpInv (κ : NodeKind) (M₀ : Mem) (o : Array Word) (cb jL Δ q j : ℕ) (t : St) : Prop where
  of : OF M₀ t
  o : t.o = o
  n : rd t.M qN = toWord (q + j)
  u : rd t.M qU = toWord j
  cbR : rd t.M qCB = toWord cb
  jlR : rd t.M qJ = toWord jL
  dR : rd t.M qDl = toWord Δ
  buf : ∀ u < j, rd t.M (bufA u) = rd M₀ (hAddr κ (ldIx cb jL Δ (q + u)))

/-- **One copied word.** -/
theorem cpBody_step (I : Array Word) (κ : NodeKind) {M₀ : Mem} {o : Array Word} {cb jL Δ q j : ℕ}
    (hb : q + nW + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) (hj : j < nW) (hsz : bufB + 2 ^ 22 ≤ M₀.size)
    (hlow : ∀ n < q + nW, hAddr κ (ldIx cb jL Δ n) < bufB)
    {t : St} (h : CpInv κ M₀ o cb jL Δ q j t) :
    CpInv κ M₀ o cb jL Δ q (j + 1) (decS qLc (semXIR I (cpBody κ) t)) := by
  obtain ⟨hO, ho, hn, hu, hcb, hjj, hd, hbuf⟩ := h
  have hs := hO.inv.1
  simp only [regs] at hs
  set G : ℕ → Word := fun n => rd M₀ (hAddr κ (ldIx cb jL Δ n)) with hG
  -- block 1
  rw [cpBody, semXIR_seq, semXIR_blk]
  set M1 := runPrims [.const oR (toWord (hBase κ)), .op .or qM qN qN] t.M with hM1d
  have k1 : ∀ r, r ≠ oR → r ≠ qM → rd M1 r = rd t.M r := fun r h1 h2 => by
    simp only [hM1d, runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have r1 : rd M1 oR = toWord (hBase κ) := by
    simp only [hM1d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oR, qM] at *; omega)) only [rd_set_self, rd_set_ne]
  have m1 : rd M1 qM = toWord (q + j) := by
    simp only [hM1d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oR, qM, qN] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [or_self_eval, hn]
  have i1 : Inv M1 := inv_sem I (P := .blk [.const oR (toWord (hBase κ)), .op .or qM qN qN])
    (by simp +decide [WF, Prim.dst, oR, qM]) hO.inv
  have hh1 : ∀ y, regs ≤ y → rd M1 y = rd t.M y := fun y hy => k1 y (by simp only [oR, regs] at *; omega)
    (by simp only [qM, regs] at *; omega)
  -- the load
  obtain ⟨x1, o1⟩ := ldC_sem I κ ⟨M1, t.o⟩ i1 r1 m1 (by rw [k1 _ (by decide) (by decide)]; exact hcb)
    (by rw [k1 _ (by decide) (by decide)]; exact hjj) (by rw [k1 _ (by decide) (by decide)]; exact hd)
    (by omega) hjl
  rw [semXIR_seq]
  generalize hs2 : semXIR I (ldC κ) ⟨M1, t.o⟩ = s2 at x1 o1
  have i2 : Inv s2.M := hs2 ▸ inv_sem I (wf_ldC κ) i1
  have k2 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX] → rd s2.M r = rd M1 r := fun r hr hn =>
    hs2 ▸ keep_ldC I κ i1 hr hn
  have hh2 : ∀ y, regs ≤ y → rd s2.M y = rd t.M y := fun y hy => by
    rw [← hs2, hframeK I _ _ (loK_ldC κ) y hy]; exact hh1 y hy
  have sz2 : s2.M.size = t.M.size := by rw [← hs2, size_sem]; exact size_runPrims _ _
  have v1 : rd s2.M oX = G (q + j) := by
    rw [x1, hh1 _ (regs_hAddr κ _), hO.low _ (regs_hAddr κ _) (hlow _ (by omega))]
  have k12 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX, qM, oR] → rd s2.M r = rd t.M r :=
    fun r hr hn => by
      rw [k2 r hr (fun h => hn (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; tauto)),
        k1 r (fun h => hn (by simp [h])) (fun h => hn (by simp [h]))]
  -- block 2: the buffer address's registers
  rw [semXIR_seq, semXIR_blk]
  have hs2' := i2.1
  simp only [regs] at hs2'
  set M5 := runPrims [.const oR (toWord bufB), .op .or oU qU qU] s2.M with hM5d
  have r5 : rd M5 oR = toWord bufB := by
    simp only [hM5d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oR, oU] at *; omega)) only [rd_set_self, rd_set_ne]
  have u5 : rd M5 oU = toWord j := by
    simp only [hM5d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oR, oU, qU] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [or_self_eval, k12 qU (by decide) (by decide), hu]
  have i5 : Inv M5 := inv_sem I (P := .blk [.const oR (toWord bufB), .op .or oU qU qU])
    (by simp +decide [WF, Prim.dst, oR, oU]) i2
  have k5 : ∀ r, r ∉ [oR, oU] → rd M5 r = rd s2.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rcases hp with rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp at hr) _
  have x5 : rd M5 oX = G (q + j) := by rw [k5 _ (by decide), v1]
  -- the address block, the store
  rw [semXIR_seq, semXIR_blk, semXIR_seq]
  have i6 : Inv (runPrims (ldPs apB) M5) := inv_sem I (P := .blk (ldPs apB)) (s := ⟨M5, s2.o⟩) (by
    simp +decide only [ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]) i5
  have ad6 : rd (runPrims (ldPs apB) M5) oAd = toWord (bufA j) := by
    rw [ldPs_oAd apB M5 i5, r5, u5]
    have := bufA_apB (u := j) (by simp only [nW] at hj; omega)
    rw [← this, toWord_toNat]
  have x6 : rd (runPrims (ldPs apB) M5) oX = G (q + j) := by
    rw [ldPs_keep apB M5 (by decide), x5]
  have hBA := bufA_lt hj
  have hBA' := bufA_ge j
  simp only [semXIR]
  set M7 := storeM (runPrims (ldPs apB) M5) oAd oX with hM7d
  have st7 : ∀ i, i ≠ cTmp → rd M7 i = if i = bufA j then G (q + j) else rd (runPrims (ldPs apB) M5) i :=
    fun i hi => by
      rw [hM7d, rd_storeM i6 ad6 (by simp only [regs, bufB] at *; omega) (by simp only [bufB] at *; omega)
        (by rw [size_runPrims, size_runPrims, sz2, hO.size]; omega) (by decide) (by decide) hi, x6]
  have i7 : Inv M7 := inv_sem I (P := .store oAd oX) (s := ⟨runPrims (ldPs apB) M5, s2.o⟩) (show oAd ≠ cTmp by decide) i6
  -- block 3 and the decrement
  refine ⟨⟨inv_decS (inv_sem I (P := .blk [.op .add qN qN cOne, .op .add qU qU cOne]) (s := ⟨M7, s2.o⟩)
      (by simp +decide [WF, Prim.dst, qN, qU]) i7) (by decide), ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [decS, size_set, size_runPrims, hM7d, hM5d, size_storeM, sz2, hO.size]
  · intro y hy1 hy2
    rw [rd_decS (by simp only [qLc, regs] at *; omega)]
    rw [rd_runPrims_of_not_writes (fun p hp he => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [Prim.dst, qN, qU, regs] at he hy1 <;> omega)]
    rw [st7 y (by simp only [cTmp, regs] at *; omega), if_neg (by omega), ldPs_keep apB M5 (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, oK, oT1, oT2, oT3, oAd, regs] at *; omega),
      k5 y (by simp only [List.mem_cons, List.mem_nil_iff, or_false, oR, oU, regs] at *; omega), hh2 y hy1,
      hO.low y hy1 hy2]
  · simp only [decS, ho, o1]
  all_goals
    have kf : ∀ r, r < regs → r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX, qM, oR, cTmp] →
        rd M7 r = rd t.M r := fun r hr hn => by
      have hm : ∀ x ∈ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX, qM, oR, cTmp], r ≠ x := fun x hx h => hn (h ▸ hx)
      have n1 := hm oK (by simp); have n2 := hm qT1 (by simp); have n3 := hm oU (by simp)
      have n4 := hm oT1 (by simp); have n5 := hm oT2 (by simp); have n6 := hm oT3 (by simp)
      have n7 := hm oAd (by simp); have n8 := hm oX (by simp); have n9 := hm qM (by simp)
      have n10 := hm oR (by simp); have n11 := hm cTmp (by simp)
      rw [st7 r n11, if_neg (by simp only [regs, bufB] at *; omega),
        ldPs_keep apB M5 (by simp [n1, n4, n5, n6, n7]), k5 r (by simp [n3, n10]),
        k12 r hr (by simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10])]
    have hs7 : 256 ≤ M7.size := by
      simp only [hM7d, size_storeM, size_runPrims, hM5d, sz2]; omega
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [kf qN (by decide) (by decide), hn, kf cOne (by decide) (by decide), one_cOne hO.inv, add_one_toWord]
    rfl
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [kf qU (by decide) (by decide), hu, kf cOne (by decide) (by decide), one_cOne hO.inv, add_one_toWord]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qCB] at *; omega)) only [rd_set_ne]
    rw [kf qCB (by decide) (by decide), hcb]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qJ] at *; omega)) only [rd_set_ne]
    rw [kf qJ (by decide) (by decide), hjj]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qDl] at *; omega)) only [rd_set_ne]
    rw [kf qDl (by decide) (by decide), hd]
  · intro u hu1
    have hbu := bufA_ge u
    rw [rd_decS (by simp only [qLc, bufB] at *; omega)]
    rw [rd_runPrims_of_not_writes (fun p hp he => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [Prim.dst, qN, qU, bufB] at he hbu <;> omega)]
    rw [st7 _ (by simp only [cTmp, bufB] at *; omega)]
    by_cases huj : u = j
    · rw [if_pos (by rw [huj])]; rw [huj]
    · rw [if_neg (fun he => huj (bufA_inj (by omega) hj he)), ldPs_keep apB M5 (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, oK, oT1, oT2, oT3, oAd, bufB] at *; omega),
        k5 _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false, oR, oU, bufB] at *; omega),
        hh2 _ (by simp only [regs, bufB] at *; omega), hbuf u (by omega)]

theorem of_entryK {M₀ : Mem} {c n : ℕ} {K : Word} (hc : 4 < c) (hcr : c < regs) {s : St} (h : OF M₀ s) :
    OF M₀ ⟨entryK c n K s.M, s.o⟩ :=
  ⟨inv_entryK h.inv hc, (size_entryK ..).trans h.size, fun y h1 h2 =>
    (entryK_frame _ (by omega) (by simp only [cTmp, regs] at *; omega)).trans (h.low y h1 h2)⟩

theorem cpInv_entryK {κ : NodeKind} {M₀ : Mem} {o : Array Word} {cb jL Δ q : ℕ} {M : Mem} {K : Word}
    (h : CpInv κ M₀ o cb jL Δ q 0 ⟨M, o⟩) : CpInv κ M₀ o cb jL Δ q 0 ⟨entryK qLc qLn K M, o⟩ := by
  obtain ⟨hO, -, hn, hu, hc, hj, hd, -⟩ := h
  have e : ∀ r, r ≠ qLc → r ≠ cTmp → rd (entryK qLc qLn K M) r = rd M r := fun r h1 h2 =>
    entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  exact ⟨of_entryK (by decide) (by decide) hO, rfl, by rw [e _ (by decide) (by decide)]; exact hn,
    by rw [e _ (by decide) (by decide)]; exact hu, by rw [e _ (by decide) (by decide)]; exact hc,
    by rw [e _ (by decide) (by decide)]; exact hj, by rw [e _ (by decide) (by decide)]; exact hd,
    fun u hu => absurd hu (Nat.not_lt_zero u)⟩

theorem wf_cpBody (κ : NodeKind) : WF (cpBody κ) := by
  refine ⟨by simp [WF, Prim.dst, oR, qM], wf_ldC κ, by simp [WF, Prim.dst, oR, oU], ?_,
    show oAd ≠ cTmp by decide, by simp [WF, Prim.dst, qN, qU]⟩
  simp +decide only [ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem wf_cpSeg (κ : NodeKind) : WF (cpSeg κ) := by
  refine ⟨by simp +decide [WF], ⟨by decide, by decide, fun h => ?_, wf_cpBody κ⟩⟩
  have := writes_wrL _ _ h
  simp +decide [wrL, cpBody, ldC, ldw, ldPs, Prim.dst] at this

/-- **The copy loop** (`q = i·(strideB/8)`): buffer word `u < nW` is the loader's word `C (q + u)` (H
word `ldIx cb jL Δ (q + u)`); the heap below the buffer and the output are kept. -/
theorem cpSeg_sem (I : Array Word) (κ : NodeKind) {M₀ : Mem} {s : St} (hO : OF M₀ s)
    (hsz : bufB + 2 ^ 22 ≤ M₀.size) {i cb jL Δ : ℕ} (hi4 : i ≤ 4)
    (hi : rd s.M qI = toWord i) (hcb : rd s.M qCB = toWord cb) (hjr : rd s.M qJ = toWord jL)
    (hd : rd s.M qDl = toWord Δ) (hb : 2 ^ 23 + nW + 1 + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64)
    (hlow : ∀ n ≤ i * (N4c.strideB / 8) + nW, hAddr κ (ldIx cb jL Δ n) < bufB) :
    OF M₀ (semXIR I (cpSeg κ) s) ∧ (semXIR I (cpSeg κ) s).o = s.o ∧
      ∀ u < nW, rd (semXIR I (cpSeg κ) s).M (bufA u) = rd M₀ (hAddr κ (ldIx cb jL Δ (i * (N4c.strideB / 8) + u))) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  have hD : i * (N4c.strideB / 8) < 2 ^ 23 := by simp only [N4c.strideB, N4c.segB, N4c.spacerB]; omega
  rw [cpSeg, semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const qT1 (toWord (N4c.strideB / 8)), .op .mul qN qI qT1, .const qU 0,
    .const qLn (toWord nW)] with hps
  have kp : ∀ r, r ∉ [qT1, qN, qU, qLn] → rd (runPrims ps s.M) r = rd s.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rcases hp with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp at hr) _
  have v : rd (runPrims ps s.M) qN = toWord (i * (N4c.strideB / 8)) ∧ rd (runPrims ps s.M) qU = toWord 0 ∧
      rd (runPrims ps s.M) qLn = toWord nW := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qT1, qN, qU, qLn, qI] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hi, mul_toWord]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨vn, vu, vl⟩ := v
  have i1 : Inv (runPrims ps s.M) := inv_sem I (P := .blk ps) (s := s) (by simp +decide [hps, WF]) hO.inv
  have O1 : OF M₀ ⟨runPrims ps s.M, s.o⟩ := of_loK I (P := .blk ps) (by simp +decide [hps, LoK, regs])
    (by simp +decide [hps, WF]) hO
  have h0 : CpInv κ M₀ s.o cb jL Δ (i * (N4c.strideB / 8)) 0 ⟨runPrims ps s.M, s.o⟩ :=
    ⟨O1, rfl, by rw [vn, Nat.add_zero], vu, by rw [kp _ (by decide)]; exact hcb,
      by rw [kp _ (by decide)]; exact hjr, by rw [kp _ (by decide)]; exact hd,
      fun u hu => absurd hu (Nat.not_lt_zero u)⟩
  have L := loopK_emit I (c := qLc) (n := qLn) (K := nW) (b := cpBody κ)
    (fun j t => CpInv κ M₀ s.o cb jL Δ (i * (N4c.strideB / 8)) j t) (fun _ => []) ⟨runPrims ps s.M, s.o⟩ i1
    (by decide) (by decide) (by decide) (by simp only [nW]; norm_num) vl (cpInv_entryK h0)
    (fun j t hj ht => ⟨by
        have e := (cpBody_step I κ (by omega) hjl hj hsz (fun n hn => hlow n (by omega)) ht).o
        simp only [decS] at e; rw [e, ht.o]; simp, cpBody_step I κ (by omega) hjl hj hsz
        (fun n hn => hlow n (by omega)) ht⟩)
  obtain ⟨-, Q⟩ := L
  exact ⟨Q.of, Q.o, fun u hu => Q.buf u hu⟩

end FR.X

end G6_FRXOut4R
