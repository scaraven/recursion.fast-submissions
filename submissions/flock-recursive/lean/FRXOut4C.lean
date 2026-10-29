-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 10,
-- item 1: a signed child's chain words and the aggregate header's words as H message words, pure).
import FRXOut4W
import FRXSig4W

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
