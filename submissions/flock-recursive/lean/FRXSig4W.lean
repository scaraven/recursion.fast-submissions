-- New for `flock-recursive` (BLUEPRINT revision 4.3, §6.2 step 5, (A)(ii); stage S-H4, pass 8,
-- item 2, the signature's half: its output words over H's message words). 3.x analogue:
-- `FRNodeReadW.sigWords_readSig` (L words), `FRNodeReadS.shw_bytes` (one byte of shift).
import FRXSig4

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
