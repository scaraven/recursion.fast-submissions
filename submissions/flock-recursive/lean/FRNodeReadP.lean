-- New for `flock-recursive` (BLUEPRINT A.5, §6.2 step 5, §6.5 `output_spec`; stage S-H2,
-- track L-ext, S-H2l).
import FRNodeReadS

/-!
# The child proof's words: `reassemble` as stream-word segments

`reassemble_eq` gives the bytes of `reassemble tr` field by field: per field `f`, the phases'
contributions `ctb`. On the trace read off the stream (`readTrace w σ`), every contribution is
a slice of stream words (A.5, A.7):

* the seed's `hdr` is stream words `10 … 15`;
* an absorb's message (`absorb`, `uni`, a round's message) starts 6 words after its item;
  a round `j` of a `rounds` phase sits `j·S` words after the first (`S = (slen₁ + slen₂)/8`);
* the columns of position `p` start 2 words after the column item, `p·S` words apart;
* a sibling is words 6–9 (right half) or 2–5 (left half) of its node item, chosen by the
  position's bit `h`, or four zero words at a dummy depth. The position (`posOf`) is bits
  `[r·logN, (r+1)·logN)` (`r = p mod per`) of answer `⌊p / per⌋` of the preceding `P2` phase, so
  its bit `h` is bit `m mod 64` of that answer's stream word `⌊m/64⌋` (`m = r·logN + h`).

The segment `pSeg` (`FRNodeReadS.Seg`) lists these slices. The child's kind (`traceKind`: byte
80 of the stream, the low byte of word 10) only changes the siblings (its ladder's `logN`,
`per`, `sib`), so `pSeg` branches on the flag `kflag (W 10)` there (`kite`).

**`proof_words`**: `bl (reassemble (readTrace w σ)) = wordsBytes (segOut W κ 0 pSeg)`, and
**`reassemble_size`**: the proof has `piSize` bytes.
-/

namespace FR.Read

open RecursionFast

/-! ## Specification: the proof's segments -/

/-- Stream word of item `ix` (`streamOff ix / 8`). -/
def wo (ix : ℕ) : ℕ := streamOff ix / 8

/-- The item index of the last position-answer (`P2`) phase. -/
def nextA (ix ixA : ℕ) : Shape → ℕ
  | .squeezes _ (.pos _) => ix
  | _ => ixA

/-- **Level `i`'s siblings** for a child of kind `k`: node items from the first position's first
node item, positions `wsum (posItems i)` words apart, answers from `ixA`'s answer word. -/
def sibS (k : Kind) (i ix ixA : ℕ) : Seg :=
  .sib (wo ix + (Item.col i).slen / 8) (wsum (posItems i)) (lvlStar i).t (lvlStar i).sib (wo ixA + 6)
    (lvl k i).logN (lvl k i).per (lvl k i).sib

/-- **A phase's segment for field `f`** (a later phase, items from `ix`). -/
def pPh (f ix ixA : ℕ) : Shape → Seg
  | .seed => .nil
  | .absorb g len => if f = g then .cp (wo ix + 6) (len / 8) else .nil
  | .squeezes _ _ => .nil
  | .uni g => if f = g then .cp (wo ix + 6) (uniBytes / 8) else .nil
  | .rounds g n _ inK _ => if f = g then
      .rep n (wsum [.absorb (roundBytes inK), .squeeze]) (.cp (wo ix + 6) (roundBytes inK / 8)) else .nil
  | .queries i =>
    if f = fCols then .rep (lvlStar i).t (wsum (posItems i)) (.cp (wo ix + 2) (colBytes i / 8))
    else if f = fSibs then .kite (sibS .N30 i ix ixA) (sibS .L32 i ix ixA) else .nil

/-- The later phases' segments for field `f`. -/
def pRest (f : ℕ) : ℕ → ℕ → List Shape → Seg
  | _, _, [] => .nil
  | ix, ixA, sh :: shs => .cat (pPh f ix ixA sh) (pRest f (ix + sh.items.length) (nextA ix ixA sh) shs)

/-- **The proof's segment**: per field, the seed's `hdr` (stream words `10 … 15`) and the later
phases. -/
def pSeg : Seg :=
  catL ((List.range nFields).map fun f => .cat (if f = fHdr then .cp 10 6 else .nil) (pRest f 1 0 restSh))

/-- **The kind flag** of a child's stream word 10: its low byte is `'N'` or `'P'`. -/
def kflag (x : Word) : Bool := x &&& 0xFF == 0x4E || x &&& 0xFF == 0x50

/-- The ladder kind a flag selects. -/
def kOf (κ : Bool) : Kind := if κ then .N30 else .L32

/-! ## Proof helpers: items and offsets -/

theorem wordsBytes_append (a b : List Word) : wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
  List.flatMap_append

theorem wordsBytes_flatMap {α : Type} (l : List α) (g : α → List Word) :
    wordsBytes (l.flatMap g) = l.flatMap fun x => wordsBytes (g x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, wordsBytes_append, ih, List.flatMap_cons]

theorem streamOff_drop {ix m : ℕ} {l r : List Item} (hd : items.drop ix = l ++ r) (hm : m ≤ l.length) :
    streamOff (ix + m) = streamOff ix + ((l.take m).map Item.slen).sum := by
  simp only [streamOff]
  rw [List.take_add, hd, List.take_append_of_le_length hm, List.map_append, List.sum_append]
  omega

theorem drop_cons_item {ix : ℕ} {it : Item} {r : List Item} (hd : items.drop ix = it :: r) :
    items[ix]? = some it ∧ items.drop (ix + 1) = r ∧ streamOff (ix + 1) = streamOff ix + it.slen := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (·[0]?) hd
    simpa [List.getElem?_drop] using this
  · rw [← List.drop_drop, hd]; rfl
  · rw [streamOff_drop (l := [it]) (r := r) hd (by simp)]; simp

theorem take_flatten_replicate (blk : List Item) : ∀ (n j : ℕ), j ≤ n →
    ((List.replicate n blk).flatten).take (j * blk.length) = (List.replicate j blk).flatten
  | _, 0, _ => by simp
  | n + 1, j + 1, h => by
    rw [List.replicate_succ, List.flatten_cons, Nat.succ_mul, Nat.add_comm, List.take_add,
      List.take_left' rfl, List.drop_left' rfl, take_flatten_replicate blk n j (by omega),
      List.replicate_succ, List.flatten_cons]
  | 0, _ + 1, h => by omega

theorem drop_flatten_replicate (blk : List Item) : ∀ (n j : ℕ), j ≤ n →
    ((List.replicate n blk).flatten).drop (j * blk.length) = (List.replicate (n - j) blk).flatten
  | _, 0, _ => by simp
  | n + 1, j + 1, h => by
    rw [List.replicate_succ, List.flatten_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
      List.drop_left' rfl, drop_flatten_replicate blk n j (by omega), Nat.add_sub_add_right]
  | 0, _ + 1, h => by omega

theorem sum_flatten_replicate (blk : List Item) (j : ℕ) :
    (((List.replicate j blk).flatten).map Item.slen).sum = j * (blk.map Item.slen).sum := by
  induction j with
  | zero => simp
  | succ j ih => rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih]; ring

/-- **Block `j` of a repeated block**: its items and its stream offset. -/
theorem drop_rep {ix n j : ℕ} {blk r : List Item} (hd : items.drop ix = (List.replicate n blk).flatten ++ r)
    (hj : j < n) :
    items.drop (ix + j * blk.length) = blk ++ ((List.replicate (n - j - 1) blk).flatten ++ r) ∧
      streamOff (ix + j * blk.length) = streamOff ix + j * (blk.map Item.slen).sum := by
  have hl : j * blk.length ≤ ((List.replicate n blk).flatten).length := by
    simp only [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_⟩
  · rw [← List.drop_drop, hd, List.drop_append_of_le_length hl, drop_flatten_replicate blk n j (by omega)]
    generalize hk : n - j - 1 = k
    rw [show n - j = k + 1 by omega, List.replicate_succ, List.flatten_cons, List.append_assoc]
  · rw [streamOff_drop hd hl, take_flatten_replicate blk n j (by omega), sum_flatten_replicate]

theorem mem_tail_of {j : ℕ} {it : Item} (h1 : 1 ≤ j) (h : items[j]? = some it) : it ∈ items.tail := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [← List.getElem?_tail] at h
  exact List.mem_of_getElem? h

theorem streamOff_slen_le {j : ℕ} {it : Item} (h : items[j]? = some it) :
    streamOff j + it.slen ≤ streamBytes := by
  have hj : j < items.length := (List.getElem?_eq_some_iff.1 h).1
  have hd : items.drop j = it :: items.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, (List.getElem?_eq_some_iff.1 h).2]
  have e := (drop_cons_item hd).2.2
  have e2 := streamOff_drop (ix := j + 1) (m := 0) (l := []) (r := items.drop (j + 1)) rfl le_rfl
  have hT : streamOff (j + 1) ≤ streamOff items.length := by
    simp only [streamOff]
    have := List.take_append_drop (j + 1) (items.take items.length)
    rw [List.take_take, Nat.min_eq_left (by omega)] at this
    have hs := congrArg (fun l => (l.map Item.slen).sum) this
    simp only [List.map_append, List.sum_append] at hs
    omega
  have hE : streamOff items.length = streamBytes := by
    have e3 : Item.slen = fun it => 8 + it.qlen + 32 := funext fun _ => rfl
    simp only [streamOff, List.take_length, streamBytes, e3]
  omega

theorem streamOff_mod8 {j : ℕ} {it : Item} (h1 : 1 ≤ j) (h : items[j]? = some it) : streamOff j % 8 = 0 := by
  have hj : j < items.length := (List.getElem?_eq_some_iff.1 h).1
  have := streamOff_aligned j h1 (by omega)
  omega

/-- **A query slice of the read trace is a slice of stream words.** -/
theorem qB (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (hW : ∀ u < 185168, W u = streamWord w σ u)
    {j off n : ℕ} {it : Item} (hj : items[j]? = some it) (hn : off + n ≤ it.qlen)
    (ha : (streamOff j + 8 + off) % 8 = 0) (h8 : n % 8 = 0) :
    bl (qBytes (readTrace w σ).toArray j off n) =
      wordsBytes ((List.range (n / 8)).map fun i => W ((streamOff j + 8 + off) / 8 + i)) := by
  have hl : j < items.length := (List.getElem?_eq_some_iff.1 hj).1
  have hit : items[j] = it := (List.getElem?_eq_some_iff.1 hj).2
  have hb := streamOff_slen_le hj
  rw [streamBytes_eq] at hb
  simp only [Item.slen] at hb
  rw [qBytes_readTrace w σ j off n hl (by rw [hit]; exact hn),
    show streamOff j + 8 + off = 8 * ((streamOff j + 8 + off) / 8) by omega,
    show n = 8 * (n / 8) by omega, stream_slice, Nat.mul_div_cancel_left _ (by norm_num : 0 < 8),
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 8), streamWords_slice w σ W hW (by omega)]

/-! ## Proof helpers: bits of an answer -/

theorem ofLE_eq_sum : ∀ l : List UInt8, ofLE l = ∑ t ∈ Finset.range l.length, (l.getD t 0).toNat * 256 ^ t
  | [] => rfl
  | d :: l => by
    rw [ofLE_cons, ofLE_eq_sum l, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Nat.add_comm]; congr 1
    refine Finset.sum_congr rfl fun t _ => by ring

theorem natLE_eq_ofLE (d : Digest) : natLE d = ofLE d.toList := by
  rw [ofLE_eq_sum, Vector.length_toList, natLE, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [List.getD_eq_getElem _ _ (by simp), Vector.getElem_toList]

theorem testBit_ofLE_wordsBytes : ∀ (ws : List Word) (m : ℕ),
    (ofLE (wordsBytes ws)).testBit m = (ws.getD (m / 64) 0).toNat.testBit (m % 64)
  | [], m => by simp [wordsBytes, ofLE]
  | x :: ws, m => by
    rw [wordsBytes_cons, ofLE_append, wordBytes_length, ofLE_wordBytes, show (256 : ℕ) ^ 8 = 2 ^ 64 by norm_num,
      Nat.add_comm, Nat.testBit_two_pow_mul_add _ x.isLt]
    by_cases hm : m < 64
    · simp [hm, Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
    · rw [if_neg hm, testBit_ofLE_wordsBytes ws (m - 64)]
      rw [show m / 64 = (m - 64) / 64 + 1 by omega, List.getD_cons_succ,
        show (m - 64) % 64 = m % 64 by omega]

theorem div_two_pow_mod_two (x k : ℕ) : x / 2 ^ k % 2 = 0 ↔ ¬ x.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp

theorem testBit_posOf (k : Kind) (i : ℕ) (ans : List Digest) (p h : ℕ) (hh : h < (lvl k i).logN) :
    (posOf k i ans p).testBit h =
      (natLE (ans.getD (p / (lvl k i).per) 0)).testBit (p % (lvl k i).per * (lvl k i).logN + h) := by
  simp only [posOf, idxOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hh, decide_true,
    Bool.true_and]
  rw [Nat.add_comm, Nat.mul_comm]

/-! ## Proof helpers: the level constants -/

theorem lvlStar_out {i : ℕ} (hi : ¬ i < 5) : lvlStar i = ⟨0, 1, 0, 0⟩ := by
  simp only [lvlStar, lvl, ladder]
  exact List.getD_eq_default _ _ (by simp [ladder32]; omega)

/-- The ladder facts the siblings need, for both ladders. -/
theorem lvl_ok (κ : Bool) (i : ℕ) (ht : 0 < (lvlStar i).t) :
    (lvlStar i).t ≤ (lvlStar i).sq * (lvl (kOf κ) i).per ∧ 0 < (lvl (kOf κ) i).per ∧
      (lvl (kOf κ) i).per * (lvl (kOf κ) i).logN ≤ 256 ∧ (lvl (kOf κ) i).sib ≤ (lvl (kOf κ) i).logN := by
  by_cases hi : i < 5
  · interval_cases i <;> cases κ <;> decide
  · rw [lvlStar_out hi] at ht; exact absurd ht (by decide)

theorem colBytes_mod (i : ℕ) : colBytes i % 8 = 0 := by unfold colBytes; omega

theorem posItems_slen (i : ℕ) : ((posItems i).map Item.slen).sum = 8 * wsum (posItems i) := by
  have h1 : (Item.col i).slen % 8 = 0 := by
    simp only [Item.slen, Item.qlen]; have := colBytes_mod i; omega
  have e : ∀ l : List ℕ, (∀ x ∈ l, x = 112) → l.sum = 8 * (l.map (· / 8)).sum := by
    intro l hl; induction l with
    | nil => rfl
    | cons x l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons, hl x (by simp), ih fun y hy => hl y (by simp [hy])]
      omega
  simp only [posItems, wsum, List.map_cons, List.sum_cons, List.map_map]
  rw [e ((List.range (lvlStar i).sib).map (Item.slen ∘ Item.node i)) (by simp [Item.slen, Item.qlen]),
    List.map_map]
  have : (Item.col i).slen = 8 * ((Item.col i).slen / 8) := by omega
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  simp only [Function.comp_def]; ring

theorem nodes_take (i s h : ℕ) (hh : h ≤ s) :
    ((((List.range s).map (Item.node i)).take h).map Item.slen).sum = 112 * h := by
  rw [← List.map_take, List.map_map, List.take_range, show Item.slen ∘ Item.node i = fun _ => 112 from rfl,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, Nat.min_eq_left hh, Nat.mul_comm]

theorem items_zero : items[0]? = some .seed := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 qlen_mod.1
  rw [ht]; rfl

theorem one_le_of {j : ℕ} {it : Item} (h : items[j]? = some it) (hs : it ≠ .seed) : 1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [items_zero] at h; cases h; exact absurd rfl hs
  · exact hj

theorem flatten_rep_single (n : ℕ) (it : Item) : (List.replicate n [it]).flatten = List.replicate n it := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl

/-! ## Proof helpers: the slices -/

section Slices

variable {w : ℕ → F} {σ : ℕ} {W : ℕ → Word} (κ : Bool) (hW : ∀ u < 185168, W u = streamWord w σ u)
include hW

/-- A query slice as a copy segment at base `b`. -/
theorem cpSlice {j off n : ℕ} {it : Item} (hj : items[j]? = some it) (hn : off + n ≤ it.qlen)
    (h8 : n % 8 = 0) (b o : ℕ) (hv : streamOff j + 8 + off = 8 * (b + o)) :
    bl (qBytes (readTrace w σ).toArray j off n) = wordsBytes (segOut W κ b (.cp o (n / 8))) := by
  rw [qB w σ W hW hj hn (by omega) h8, segOut]
  congr 1; refine List.map_congr_left fun x _ => ?_; congr 1; omega

/-- **An answer's bits are its stream words' bits.** -/
theorem ans_bit {j : ℕ} (hj : items[j]? = some .squeeze) {m : ℕ} (hm : m < 256) :
    (natLE ((readTrace w σ).toArray.getD j (ByteArray.empty, 0)).2).testBit m =
      (W (wo j + 6 + m / 64)).toNat.testBit (m % 64) := by
  have hl : j < items.length := (List.getElem?_eq_some_iff.1 hj).1
  have hit : items[j] = .squeeze := (List.getElem?_eq_some_iff.1 hj).2
  have hb := streamOff_slen_le hj
  have h1 := one_le_of hj (by decide)
  have ha := streamOff_mod8 h1 hj
  have hB := stream_length w σ
  rw [streamBytes_eq] at hb hB
  simp only [Item.slen, Item.qlen] at hb
  rw [readTrace_getD w σ j hl, hit, entryAt, natLE_eq_ofLE, digest_toList _ _ (by simp only [Item.qlen]; omega),
    show streamOff j + 8 + Item.squeeze.qlen = 8 * (wo j + 6) by simp only [wo, Item.qlen]; omega,
    show (32 : ℕ) = 8 * 4 from rfl, stream_slice, streamWords_slice w σ W hW (by simp only [wo]; omega),
    testBit_ofLE_wordsBytes, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
    List.getElem_range]

/-- **One sibling** (`sibling`) is `sibW`'s words. -/
theorem sib_one (k : Kind) {i jn p h o S ansW : ℕ} {ans : List Digest}
    (hj : items[jn]? = some (.node i h)) (hoff : streamOff jn = 8 * (o + S * p + 14 * h))
    (hans : ∀ m < 256, (natLE (ans.getD (p / (lvl k i).per) 0)).testBit m =
      (W (ansW + 10 * (p / (lvl k i).per) + m / 64)).toNat.testBit (m % 64))
    (hpl : (lvl k i).per * (lvl k i).logN ≤ 256) (hsl : (lvl k i).sib ≤ (lvl k i).logN)
    (hper : 0 < (lvl k i).per) :
    bl (sibling k i h (posOf k i ans p) ((readTrace w σ).toArray.getD jn (ByteArray.empty, 0)).1) =
      wordsBytes (sibW W 0 o S ansW (lvl k i).logN (lvl k i).per (lvl k i).sib p h) := by
  unfold sibling sibW
  by_cases hh : h < (lvl k i).sib
  · rw [if_pos hh, if_pos hh]
    have hr : p % (lvl k i).per < (lvl k i).per := Nat.mod_lt _ hper
    have hm : p % (lvl k i).per * (lvl k i).logN + h < 256 := by
      have : (p % (lvl k i).per + 1) * (lvl k i).logN ≤ (lvl k i).per * (lvl k i).logN :=
        Nat.mul_le_mul_right _ hr
      nlinarith
    have hiff : posOf k i ans p / 2 ^ h % 2 = 0 ↔
        (W (0 + ansW + 10 * (p / (lvl k i).per) + (p % (lvl k i).per * (lvl k i).logN + h) / 64)).toNat /
          2 ^ ((p % (lvl k i).per * (lvl k i).logN + h) % 64) % 2 = 0 := by
      rw [div_two_pow_mod_two, div_two_pow_mod_two, testBit_posOf k i ans p h (by omega), hans _ hm,
        Nat.zero_add]
    have hq : ((readTrace w σ).toArray.getD jn (ByteArray.empty, 0)).1.extract 40 72 =
        qBytes (readTrace w σ).toArray jn 40 32 := rfl
    have hq' : ((readTrace w σ).toArray.getD jn (ByteArray.empty, 0)).1.extract 8 40 =
        qBytes (readTrace w σ).toArray jn 8 32 := rfl
    by_cases hb : posOf k i ans p / 2 ^ h % 2 = 0
    · rw [if_pos hb, if_pos (hiff.1 hb), hq, cpSlice false hW (off := 40) (n := 32) hj (by simp [Item.qlen])
        (by decide) 0 (o + S * p + 14 * h + 6) (by omega)]
      simp only [segOut, Nat.zero_add]
    · rw [if_neg hb, if_neg (fun h' => hb (hiff.2 h')), hq', cpSlice false hW (off := 8) (n := 32) hj
        (by simp [Item.qlen]) (by decide) 0 (o + S * p + 14 * h + 2) (by omega)]
      simp only [segOut, Nat.zero_add]
  · rw [if_neg hh, if_neg hh]; decide

end Slices

/-! ## Proof helpers: one phase -/

/-- What the walk knows about the last phase: after a `P2` phase of `n` answers at `ixA`, the
answers are its items' and the items from `ixA` are its squeezes. -/
def PrevInv (a : Array (ByteArray × Digest)) (prev : Option Shape) (ix ixA : ℕ) (ans : List Digest) :
    Prop :=
  ∀ n i, prev = some (.squeezes n (.pos i)) → ixA + n = ix ∧
    ans = (List.range n).map (fun j => (a.getD (ixA + j) (ByteArray.empty, 0)).2) ∧
    items.drop ixA = (List.replicate n [Item.squeeze]).flatten ++ items.drop ix

/-- A `queries i` phase follows level `i`'s `P2` phase. -/
def qPrev (i : ℕ) : Option Shape → Bool
  | some (.squeezes n (.pos i')) => n == (lvlStar i).sq && i' == i
  | _ => false

/-- A phase's condition on the one before: a `queries` phase follows its `P2` phase. -/
def qHead (p : Option Shape) : Shape → Bool
  | .queries i => qPrev i p
  | _ => true

/-- Every `queries` phase of the list follows its `P2` phase. -/
def qOk : Option Shape → List Shape → Bool
  | _, [] => true
  | p, sh :: shs => qHead p sh && qOk (some sh) shs

theorem qPrev_eq {i : ℕ} {p : Option Shape} (h : qPrev i p = true) :
    p = some (.squeezes (lvlStar i).sq (.pos i)) := by
  unfold qPrev at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2]
  · exact absurd h (by simp)

theorem qOk_restSh : qOk (some .seed) restSh = true := by decide +kernel

section Phase

variable {w : ℕ → F} {σ : ℕ} {W : ℕ → Word} (κ : Bool) (hW : ∀ u < 185168, W u = streamWord w σ u)
  (hκ : ∀ i, lvl (traceKind (readTrace w σ).toArray) i = lvl (kOf κ) i)
include hW hκ

/-- **One later phase**: its contribution to field `f` is its segment's words. -/
theorem pPh_spec (f : ℕ) {ix ixA : ℕ} {ans : List Digest} {sh : Shape} {r : List Item}
    {prev : Option Shape} (hd : items.drop ix = sh.items ++ r) (h1 : 1 ≤ ix) (hns : sh ≠ .seed)
    (hq : qHead prev sh = true)
    (hP : PrevInv (readTrace w σ).toArray prev ix ixA ans) :
    ctb (traceKind (readTrace w σ).toArray) (readTrace w σ).toArray ix ans sh f =
      wordsBytes (segOut W κ 0 (pPh f ix ixA sh)) := by
  cases sh with
  | seed => exact absurd rfl hns
  | squeezes n ch => rfl
  | absorb g len =>
    obtain ⟨e1, -, -⟩ := drop_cons_item hd
    have ha := streamOff_mod8 h1 e1
    have hq := qlen_mod.2.2 _ (mem_tail_of h1 e1)
    simp only [Item.qlen] at hq
    by_cases hf : f = g
    · simp only [ctb, pPh, hf, if_true]
      exact cpSlice κ hW e1 (by simp [Item.qlen]) (by omega) 0 _ (by simp only [wo]; omega)
    · simp only [ctb, pPh, hf, if_false]; rfl
  | uni g =>
    obtain ⟨e1, -, -⟩ := drop_cons_item hd
    have ha := streamOff_mod8 h1 e1
    by_cases hf : f = g
    · simp only [ctb, pPh, hf, if_true]
      exact cpSlice κ hW e1 (by simp [Item.qlen]) (by decide) 0 _ (by simp only [wo]; omega)
    · simp only [ctb, pPh, hf, if_false]; rfl
  | rounds g n deg inK real =>
    by_cases hf : f = g
    · simp only [ctb, pPh, hf, if_true, segOut, wordsBytes_flatMap]
      refine List.flatMap_congr fun j hj => ?_
      obtain ⟨d1, d2⟩ := drop_rep (blk := [.absorb (roundBytes inK), .squeeze]) hd (List.mem_range.1 hj)
      obtain ⟨e1, -, -⟩ := drop_cons_item d1
      have ha := streamOff_mod8 (by omega) e1
      simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at d2 e1 ha
      rw [show ix + 2 * j = ix + j * (0 + 1 + 1) by ring]
      rw [d2] at ha
      refine cpSlice κ hW e1 (by simp [Item.qlen]) (by cases inK <;> decide) _ _ ?_
      rw [d2]
      cases inK <;> simp only [wo, wsum, roundBytes, Item.slen, Item.qlen, Bool.false_eq_true,
        ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at ha ⊢ <;> omega
    · simp only [ctb, pPh, hf, if_false]; rfl
  | queries i =>
    have hS := posItems_slen i
    have hlen : (posItems i).length = 1 + (lvlStar i).sib := by simp [posItems, Nat.add_comm]
    -- position `p`'s items and offsets
    have pos : ∀ p < (lvlStar i).t, items[ix + (1 + (lvlStar i).sib) * p]? = some (.col i) ∧
        items.drop (ix + (1 + (lvlStar i).sib) * p + 1) =
          (List.range (lvlStar i).sib).map (Item.node i) ++
            ((List.replicate ((lvlStar i).t - p - 1) (posItems i)).flatten ++ r) ∧
        streamOff (ix + (1 + (lvlStar i).sib) * p) = 8 * (wo ix + wsum (posItems i) * p) ∧
        streamOff (ix + (1 + (lvlStar i).sib) * p + 1) =
          streamOff (ix + (1 + (lvlStar i).sib) * p) + (Item.col i).slen := fun p hp => by
      obtain ⟨d1, d2⟩ := drop_rep (blk := posItems i) hd hp
      rw [hlen, Nat.mul_comm] at d1 d2
      obtain ⟨e1, e2, e3⟩ := drop_cons_item (show items.drop (ix + (1 + (lvlStar i).sib) * p) =
        .col i :: ((List.range (lvlStar i).sib).map (Item.node i) ++
          ((List.replicate ((lvlStar i).t - p - 1) (posItems i)).flatten ++ r)) from d1)
      have ha := streamOff_mod8 (by omega) e1
      refine ⟨e1, e2, ?_, e3⟩
      rw [d2, hS, show p * (8 * wsum (posItems i)) = 8 * (wsum (posItems i) * p) by ring] at ha ⊢
      simp only [wo]; omega
    by_cases hc : f = fCols
    · simp only [ctb, pPh, hc, if_true, segOut, wordsBytes_flatMap]
      refine List.flatMap_congr fun p hp => ?_
      obtain ⟨e1, -, e3, -⟩ := pos p (List.mem_range.1 hp)
      exact cpSlice κ hW e1 (by simp [Item.qlen]) (colBytes_mod i) _ _ (by rw [e3]; omega)
    by_cases hs : f = fSibs
    · simp only [ctb, pPh, hs, show fSibs ≠ fCols by decide, if_true, if_false]
      have hk : segOut W κ 0 (.kite (sibS .N30 i ix ixA) (sibS .L32 i ix ixA)) =
          segOut W κ 0 (sibS (kOf κ) i ix ixA) := by cases κ <;> rfl
      have e1 : ∀ h j q, sibling (traceKind (readTrace w σ).toArray) i h j q = sibling (kOf κ) i h j q :=
        fun h j q => by simp only [sibling, hκ]
      have e2 : ∀ p, posOf (traceKind (readTrace w σ).toArray) i ans p = posOf (kOf κ) i ans p :=
        fun p => by simp only [posOf, hκ]
      simp only [e1, e2]
      rw [hk, sibS, segOut, wordsBytes_flatMap]
      refine List.flatMap_congr fun p hp => ?_
      have hp := List.mem_range.1 hp
      obtain ⟨l1, l2, l3, l4⟩ := lvl_ok κ i (by omega)
      obtain ⟨-, e2, e3, e4⟩ := pos p hp
      -- the position answers
      obtain ⟨a1, a2, a3⟩ := hP _ _ (qPrev_eq (i := i) hq)
      have hqa : p / (lvl (kOf κ) i).per < (lvlStar i).sq := by
        rw [Nat.div_lt_iff_lt_mul l2]; omega
      obtain ⟨b1, b2⟩ := drop_rep (blk := [Item.squeeze]) a3 hqa
      obtain ⟨c1, -, -⟩ := drop_cons_item b1
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil] at b2 c1
      have hans : ∀ m < 256, (natLE (ans.getD (p / (lvl (kOf κ) i).per) 0)).testBit m =
          (W (wo ixA + 6 + 10 * (p / (lvl (kOf κ) i).per) + m / 64)).toNat.testBit (m % 64) := by
        intro m hm
        rw [a2, List.getD_eq_getElem _ _ (by simpa using hqa), List.getElem_map, List.getElem_range,
          ans_bit hW c1 hm]
        congr 4; simp only [wo, b2, Item.slen, Item.qlen]; omega
      rw [wordsBytes_flatMap]
      refine List.flatMap_congr fun h hh => ?_
      have hh := List.mem_range.1 hh
      have hn : items[ix + (1 + (lvlStar i).sib) * p + 1 + h]? = some (.node i h) := by
        rw [← List.getElem?_drop, e2, List.getElem?_append_left (by simpa using hh)]
        simp [hh]
      have ho := streamOff_drop e2 (m := h) (by simpa using hh.le)
      rw [nodes_take i _ h hh.le] at ho
      refine sib_one hW (kOf κ) hn ?_ hans l3 l4 l2
      rw [ho, e4, e3]
      have : (Item.col i).slen % 8 = 0 := by simp only [Item.slen, Item.qlen]; have := colBytes_mod i; omega
      omega
    · simp only [ctb, pPh, hc, hs, if_false]; rfl

/-- **The later phases** contribute their segments' words to field `f`. -/
theorem pRest_spec (f : ℕ) : ∀ (shs : List Shape) (ix ixA : ℕ) (ans : List Digest) (prev : Option Shape),
    items.drop ix = shs.flatMap Shape.items → 1 ≤ ix → (∀ sh ∈ shs, sh ≠ .seed) → qOk prev shs = true →
    PrevInv (readTrace w σ).toArray prev ix ixA ans →
    ctbs (traceKind (readTrace w σ).toArray) (readTrace w σ).toArray ix ans shs f =
      wordsBytes (segOut W κ 0 (pRest f ix ixA shs))
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | sh :: shs, ix, ixA, ans, prev, hd, h1, hns, hq, hP => by
    simp only [qOk, Bool.and_eq_true] at hq
    rw [List.flatMap_cons] at hd
    have hd' : items.drop (ix + sh.items.length) = shs.flatMap Shape.items := by
      rw [← List.drop_drop, hd, List.drop_left]
    rw [ctbs, pRest, segOut, wordsBytes_append,
      pPh_spec κ hW hκ f hd h1 (hns sh (by simp)) hq.1 hP,
      pRest_spec f shs _ (nextA ix ixA sh) _ (some sh) hd' (by omega) (fun x hx => hns x (by simp [hx]))
        hq.2 ?_]
    intro n i hsh
    cases hsh
    refine ⟨by simp [nextA, Shape.items], rfl, ?_⟩
    simp only [nextA]
    rw [hd, flatten_rep_single, hd']; rfl

end Phase

/-! ## Load-bearing lemmas -/

/-- **The child's kind selects the flag's ladder**: byte 80 of the stream (the seed's kind byte,
`traceKind`) is the low byte of stream word 10. -/
theorem traceKind_lvl (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (hW : ∀ u < 185168, W u = streamWord w σ u)
    (i : ℕ) : lvl (traceKind (readTrace w σ).toArray) i = lvl (kOf (kflag (W 10))) i := by
  have hB := stream_length w σ
  rw [streamBytes_eq] at hB
  have h0 : (0 : ℕ) < items.length := by rw [items_length]; norm_num
  have hq : ((readTrace w σ).toArray.getD 0 (ByteArray.empty, 0)).1.data[71]? =
      some (((W 10).toNat).toUInt8) := by
    rw [readTrace_getD w σ 0 h0, show items[0] = Item.seed from
      (List.getElem?_eq_some_iff.1 items_zero).2, entryAt]
    simp only [List.getElem?_toArray, List.getElem?_take, List.getElem?_drop, Item.qlen]
    rw [if_pos (by norm_num), show streamOff 0 = 1 from rfl, List.getElem?_eq_getElem (by omega),
      ← List.getD_eq_getElem _ 0, stream_getD w σ 80 (by rw [streamBytes_eq]; norm_num), hW 10 (by norm_num)]
    simp
  have hb : ∀ x : Word, (x &&& 0xFF).toNat = x.toNat.toUInt8.toNat := fun x => by
    simp [BitVec.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 8]
  have hv : ∀ (x : Word) (c : UInt8), (x &&& 0xFF == BitVec.ofNat 64 c.toNat) = (x.toNat.toUInt8 == c) := by
    intro x c
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, hb, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := c.toNat_lt; omega), UInt8.toNat_inj]
  have hk : kflag (W 10) = ((W 10).toNat.toUInt8 == 0x4E || (W 10).toNat.toUInt8 == 0x50) := by
    rw [kflag, ← hv _ 0x4E, ← hv _ 0x50]; rfl
  rw [traceKind, hq, Option.bind_some, hk]
  generalize (W 10).toNat.toUInt8 = b
  unfold Kind.ofByte?
  by_cases e1 : b = 0x4C
  · subst e1; first | rfl | simp [kOf, lvl, ladder]
  by_cases e2 : b = 0x50
  · subst e2; first | rfl | simp [kOf, lvl, ladder]
  by_cases e3 : b = 0x4E
  · subst e3; first | rfl | simp [kOf, lvl, ladder]
  simp [e1, e2, e3, kOf]

/-- **The child proof's bytes are stream-word segments** (`reassemble` on the read trace). -/
theorem proof_words (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (hW : ∀ u < 185168, W u = streamWord w σ u) :
    bl (reassemble (readTrace w σ)) = wordsBytes (segOut W (kflag (W 10)) 0 pSeg) := by
  have hκ := traceKind_lvl w σ W hW
  rw [reassemble_eq, pSeg, segOut_catL, List.flatMap_map, wordsBytes_flatMap]
  refine List.flatMap_congr fun f _ => ?_
  rw [phases_shape, ctbs, segOut, wordsBytes_append]
  have h1 : items.drop (0 + Shape.seed.items.length) = restSh.flatMap Shape.items := by
    rw [show 0 + Shape.seed.items.length = 1 from rfl, List.drop_one, items_tail]
  refine congrArg₂ (· ++ ·) ?_ (pRest_spec _ hW hκ f restSh 1 0 [] (some .seed) h1 le_rfl
    restSh_noSeed qOk_restSh fun n i h => by cases h)
  by_cases hf : f = fHdr
  · simp only [ctb, hf, if_true]
    exact cpSlice _ hW items_zero (by simp [Item.qlen]) (by decide) 0 10 rfl
  · simp only [ctb, hf, if_false]; rfl

theorem segLen_pSeg (κ : Bool) : segLen κ pSeg = 99738 := by cases κ <;> decide +kernel

/-- **The child proof has `piSize` bytes.** -/
theorem reassemble_size (w : ℕ → F) (σ : ℕ) : (reassemble (readTrace w σ)).size = piSize := by
  have h := congrArg List.length (proof_words w σ (streamWord w σ) fun _ _ => rfl)
  rw [wordsBytes_length, segOut_length, segLen_pSeg, bl, Array.length_toList] at h
  rw [ByteArray.size, h, piSize_eq]

/-! ## The witness's words -/

/-- **A child's segment over its stream**: `|π| = piSize`, the proof, the trace. -/
def slotSeg : Seg := .cat (.wd (toWord piSize)) (.cat pSeg trSeg)

/-- **A signed child's words** (`signedWords`): `slotSeg` over its stream words, then `sigSeg`
over its L words. -/
theorem signedWords_readSigned (w : ℕ → F) (σ : ℕ) (W WL : ℕ → Word)
    (hW : ∀ u < 185168, W u = streamWord w σ u) (hWL : ∀ v < 598, WL v = lWord w σ v) :
    signedWords (readSigned σ w) = segOut W (kflag (W 10)) 0 slotSeg ++ segOut WL false 0 sigSeg := by
  have hl : (bl (reassemble (readTrace w σ))).length = piSize := by
    rw [bl, Array.length_toList]; exact reassemble_size w σ
  simp only [signedWords, readSigned]
  rw [bytesWords, show (reassemble (readTrace w σ)).data.toList = bl (reassemble (readTrace w σ)) from rfl,
    hl, proof_words w σ W hW, packBytes_wordsBytes, logWords_trSeg w σ W (kflag (W 10)) hW,
    sigWords_sigSeg w σ WL false hWL, slotSeg, segOut, segOut, segOut]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- **The node witness's words** (`witWords (readWit w)`): the tag, the two statements (stream
words 6–9 of each slot), then each slot's `slotSeg` and `sigSeg`. -/
theorem witWords_readWit (w : ℕ → F) (W₁ W₂ L₁ L₂ : ℕ → Word)
    (h₁ : ∀ u < 185168, W₁ u = streamWord w 1 u) (h₂ : ∀ u < 185168, W₂ u = streamWord w 2 u)
    (g₁ : ∀ v < 598, L₁ v = lWord w 1 v) (g₂ : ∀ v < 598, L₂ v = lWord w 2 v) :
    witWords (readWit w) = toWord 1 :: (segOut W₁ false 0 (.cp 6 4) ++ segOut W₂ false 0 (.cp 6 4) ++
      (segOut W₁ (kflag (W₁ 10)) 0 slotSeg ++ segOut L₁ false 0 sigSeg) ++
      (segOut W₂ (kflag (W₂ 10)) 0 slotSeg ++ segOut L₂ false 0 sigSeg)) := by
  rw [readWit, witWords, stmtWords w 1 W₁ false h₁, stmtWords w 2 W₂ false h₂,
    signedWords_readSigned w 1 W₁ L₁ h₁ g₁, signedWords_readSigned w 2 W₂ L₂ h₂ g₂]
  simp only [List.cons_append, List.append_assoc]

theorem readItems_size (B : List UInt8) : ∀ (o : ℕ) (its : List Item), ∀ e ∈ readItems B o its,
    e.1.size ≤ B.length
  | _, [], e, he => by simp [readItems] at he
  | o, it :: its, e, he => by
    rw [readItems, List.mem_cons] at he
    rcases he with rfl | he
    · simp only [entryAt, ByteArray.size, List.size_toArray, List.length_take, List.length_drop]; omega
    · exact readItems_size B _ its e he

/-- **The witness fits the output format** (`decodeWit_witWords`'s hypothesis). -/
theorem readWit_fits (w : ℕ → F) : (readWit w).Fits := by
  have hs : ∀ σ, (readSigned σ w).Fits := fun σ => by
    refine ⟨?_, ?_, fun e he => ?_, ?_, ?_, ?_⟩
    · show (reassemble (readTrace w σ)).size < 2 ^ 64
      rw [reassemble_size, piSize_eq]; norm_num
    · show (readTrace w σ).length < 2 ^ 64
      rw [readTrace_length]; norm_num
    · have := readItems_size _ _ _ e he
      rw [stream_length, streamBytes_eq] at this; omega
    · exact (w (lCell σ 0)).c₀.val.toNat_lt
    · simp [readSigned, readSig]
    · simp [readSigned, readSig]
  exact ⟨hs 1, hs 2⟩

/-! ## Controls -/

namespace ReadControls

/-- A word source with `1` at index `k`, zeros elsewhere. -/
def ind (k : ℕ) : ℕ → Word := fun u => if u = k then 1 else 0

/-- **`cp` reads at `b + o`** (positive: word 6 is the first of `cp 6 4`), not one off (negative). -/
theorem segOut_cp_ctl : segOut (ind 6) false 0 (.cp 6 4) = [1, 0, 0, 0] ∧
    segOut (ind 6) false 0 (.cp 7 4) = [0, 0, 0, 0] ∧ segOut (ind 6) false 2 (.cp 4 1) = [1] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`rep` moves the base by `s`** (positive), and a `kite` follows the flag (negative: the other
branch is not taken). -/
theorem segOut_rep_kite_ctl : segOut (ind 5) false 0 (.rep 3 5 (.cp 0 1)) = [0, 1, 0] ∧
    segOut (ind 0) true 0 (.kite (.cp 0 1) (.wd 7)) = [1] ∧ segOut (ind 0) false 0 (.kite (.cp 0 1) (.wd 7)) = [7] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`sibW` chooses the half by the position's bit** (bit `0`, read from answer word 100: node
words 6–9, not 2–5; bit `1`: words 2–5), and a dummy depth (`sK = 0`) gives zeros. -/
theorem sibW_ctl : sibW (ind 6) 0 0 0 100 1 1 0 0 0 = [0, 0, 0, 0] ∧
    sibW (ind 6) 0 0 0 100 1 1 1 0 0 = [1, 0, 0, 0] ∧ sibW (ind 2) 0 0 0 100 1 1 1 0 0 = [0, 0, 0, 0] ∧
    sibW (fun u => if u = 100 ∨ u = 2 then 1 else 0) 0 0 0 100 1 1 1 0 0 = [1, 0, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The kind flag reads the low byte only**: `'N'` and `'P'` set it, `'L'` does not, and a
high byte does not matter. -/
theorem kflag_ctl : kflag 0x4E = true ∧ kflag 0x50 = true ∧ kflag 0x4C = false ∧ kflag 0x14E = true ∧
    kflag 0x4E00 = false := by decide

/-- The two ladders differ where the flag matters (level 0's `logN`: 18 vs 20). -/
theorem kOf_ctl : (lvl (kOf true) 0).logN = 18 ∧ (lvl (kOf false) 0).logN = 20 := by decide

/-- **`trWf` emits the length word as a constant and reads `qlen/8 + 4` words** (a squeeze: 10
words), a longer query more. -/
theorem trWf_ctl : (trWf (ind 0) 0 [.squeeze]).length = 10 ∧ (trWf (ind 0) 0 [.absorb 8]).length = 11 ∧
    (trWf (ind 0) 0 [.squeeze]).head? = some (toWord 40) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`qOk`**: the phase table passes (`qOk_restSh`); a `queries` phase with no `P2` before it
fails. -/
theorem qOk_ctl : qOk (some .seed) restSh = true ∧ qOk (some .seed) [.queries 0] = false :=
  ⟨qOk_restSh, by decide⟩

/-- `PrevInv` holds trivially after a non-`P2` phase, and constrains after one. -/
theorem prevInv_ctl : PrevInv #[] (some .seed) 1 0 [] ∧ ¬ PrevInv #[] (some (.squeezes 1 (.pos 0))) 0 0 [] := by
  refine ⟨fun n i h => ?_, fun h => ?_⟩
  · injection h with h; cases h
  · have := (h 1 0 rfl).1; omega

/-- **The witness's words start with the node tag `1`**, whatever `w` (`decodeWit` reads a node). -/
theorem witWords_tag (w : ℕ → F) : (witWords (readWit w)).head? = some (toWord 1) := by
  simp [readWit, witWords]

end ReadControls

end FR.Read
