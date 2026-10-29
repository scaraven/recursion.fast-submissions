-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.5, §6.2 step 5; stage S-H4, pass 9, item 1:
-- the proofs' output words). 3.x analogue: `FRNodeReadP.proof_words` (3.x's `items`, `reassemble`,
-- one slot's stream words); here `reassemble4 S`, `itemsOf S`, any word list.
import FRXTr4

/-!
# A slot proof's output words over a word stream, at any item sequence

`reassemble4 S 0 tr` (the slots' `pf4` on main) is, field by field, the phases' contributions
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
`bl (reassemble4 S 0 tr) = wordsBytes (segOut W κ 0 (pSeg4 S m))` when `trM4 tr = m`, under the
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

/-- **The proof's segment** at ladder `m` (fields `0 … 17`). -/
def pSeg4 (S : Seq) (m : ℕ) : Seg := catL ((List.range nFields).map (fSeg4 S m))

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

/-- **A slot proof's bytes are stream-word segments** (`reassemble4` on main, row 18 empty). -/
theorem proof_words4 (hP : PfOk4 S) (hL : LadOk4 S m) (Ws : List Word) (W : ℕ → Word)
    (hget : ∀ u (hu : u < Ws.length), Ws[u] = W u) (hB : streamBytesOf S ≤ 8 * Ws.length) (κ : Bool)
    (hm : trM4 (trOf S Ws).toArray = m) :
    bl (reassemble4 S 0 (trOf S Ws)) = wordsBytes (segOut W κ 0 (pSeg4 S m)) := by
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
  have hfit : N4s.fitL 0 (ctbs4 S (trM4 (trOf S Ws).toArray) (trOf S Ws).toArray 0 []
      ((phasesOf S).map Prod.snd) 18) = [] := rfl
  show (((List.range nFields).flatMap fun f => ctbs4 S (trM4 (trOf S Ws).toArray) (trOf S Ws).toArray 0 []
    ((phasesOf S).map Prod.snd) f) ++ _).toArray.toList = _
  rw [hfit, List.append_nil, List.toList_toArray, hm, pSeg4, segOut_catL, List.flatMap_map, wordsBytes_flatMap]
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
