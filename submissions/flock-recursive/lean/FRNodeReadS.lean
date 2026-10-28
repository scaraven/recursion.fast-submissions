-- New for `flock-recursive` (BLUEPRINT §6.2 step 5, §6.5 `output_spec`; stage S-H2, track L-ext,
-- S-H2l).
import FRNodeReadW

/-!
# Output segments: the trace, the seed entry, the signature, the statements

The node extractor emits `witWords (readWit w)` from `f⁽⁰⁾` (BLUEPRINT §6.2 step 5). The output
program reads **word sources**: slot `σ`'s stream words `W u = streamWord w σ u` and its L words
`(elemWords (w (lCell σ (v / 2)))).getD (v % 2) 0`. A small language of **segments** (`Seg`) says
which words it emits, at a base offset `b`:

* `wd x`: the constant word `x`; `cp o n`: the `n` words `W (b + o + j)`;
* `rep c s x`: `x` at the bases `b + s j`, `j < c`; `cat`, `nil`;
* `shw o`, `sh8 o`: the seed's shifted words (`(W o >>> 8) + (W (o + 1) <<< 56)`, `W o >>> 8`):
  the seed entry starts at stream byte 1, so its query's words straddle two stream words;
* `kite x y`: `x` on a child of kind `N30`/`P30` (the flag `κ`), else `y`;
* `sib …`: the Merkle siblings of one level (`sibW`), each chosen by its position bit, read off
  the position answer's words.

`segOut W κ b s` is the list a segment denotes. This module proves, from the stream:

* **`logWords_tSegs`**: `logWords (readTrace w σ)` is `segOut` of `trSeg` (the count, the seed
  entry `seedSeg`, then one `rep` per phase over its items' length words and stream words);
  the length words are constants (`toWord qlen`), not stream words (the ruling of S-H2k §5);
* **`sigWords_sigSeg`**: the signature is `segOut` of `sigSeg` over the L words;
* **`stmtWords`**: a child statement's words are stream words 6–9.
-/

namespace FR.Read

open RecursionFast

/-! ## Specification: segments -/

/-- An output segment over a word source. -/
inductive Seg where
  /-- Nothing. -/
  | nil
  /-- One segment, then the other. -/
  | cat (a b : Seg)
  /-- A constant word. -/
  | wd (x : Word)
  /-- `n` source words from `b + o`. -/
  | cp (o n : ℕ)
  /-- `c` copies of the body, the base advancing by `s`. -/
  | rep (c s : ℕ) (body : Seg)
  /-- The word of bytes `1 … 8` of source words `o, o + 1`. -/
  | shw (o : ℕ)
  /-- The word of bytes `1 … 7` of source word `o`. -/
  | sh8 (o : ℕ)
  /-- By the child's kind: the first for `N30`/`P30`, the second for `L32`. -/
  | kite (a b : Seg)
  /-- One level's Merkle siblings (`sibW`). -/
  | sib (o S t sS ansW logN per sK : ℕ)

/-- **One sibling's words** (`sibling`): position `p`, depth `h`. The position's bit `h` is bit
`m = (p mod per)·logN + h` of answer `⌊p / per⌋` (answer words from `ansW`, 10 words apart); the
node query's words start at `o + S p + 14 h`; the right half (words 6–9) for bit `0`, the left
(words 2–5) for bit `1`, zeros at a dummy depth (`h ≥ sK`). -/
def sibW (W : ℕ → Word) (b o S ansW logN per sK p h : ℕ) : List Word :=
  if h < sK then
    if (W (b + ansW + 10 * (p / per) + (p % per * logN + h) / 64)).toNat /
        2 ^ ((p % per * logN + h) % 64) % 2 = 0 then
      (List.range 4).map fun j => W (b + o + S * p + 14 * h + 6 + j)
    else (List.range 4).map fun j => W (b + o + S * p + 14 * h + 2 + j)
  else [0, 0, 0, 0]

/-- **The words a segment denotes**, from base `b`, for the kind flag `κ`. -/
def segOut (W : ℕ → Word) (κ : Bool) : ℕ → Seg → List Word
  | _, .nil => []
  | b, .cat x y => segOut W κ b x ++ segOut W κ b y
  | _, .wd x => [x]
  | b, .cp o n => (List.range n).map fun j => W (b + o + j)
  | b, .rep c s x => (List.range c).flatMap fun j => segOut W κ (b + s * j) x
  | b, .shw o => [(W (b + o) >>> 8) + (W (b + o + 1) <<< 56)]
  | b, .sh8 o => [W (b + o) >>> 8]
  | b, .kite x y => if κ then segOut W κ b x else segOut W κ b y
  | b, .sib o S t sS ansW logN per sK =>
    (List.range t).flatMap fun p => (List.range sS).flatMap fun h => sibW W b o S ansW logN per sK p h

/-- The number of words a segment denotes. -/
def segLen (κ : Bool) : Seg → ℕ
  | .nil => 0
  | .cat x y => segLen κ x + segLen κ y
  | .wd _ | .shw _ | .sh8 _ => 1
  | .cp _ n => n
  | .rep c _ x => c * segLen κ x
  | .kite x y => if κ then segLen κ x else segLen κ y
  | .sib _ _ t sS _ _ _ _ => t * sS * 4

/-- A list of segments in turn. -/
def catL : List Seg → Seg
  | [] => .nil
  | x :: xs => .cat x (catL xs)

/-! ## Specification: the trace's segments -/

/-- An item's words in the stream (`slen / 8`), summed. -/
def wsum (its : List Item) : ℕ := (its.map fun it => it.slen / 8).sum

/-- **The output words of items from stream word `u`** (`trW` over a word function): per item its
length word, then its query's and answer's `qlen/8 + 4` words after the length word. -/
def trWf (W : ℕ → Word) : ℕ → List Item → List Word
  | _, [] => []
  | u, it :: its => (toWord it.qlen :: (List.range (it.qlen / 8 + 4)).map fun j => W (u + 1 + j)) ++
      trWf W (u + it.slen / 8) its

/-- Items at stream word `u`: per item a constant length word and a copy. -/
def tItems : ℕ → List Item → Seg
  | _, [] => .nil
  | u, it :: its => .cat (.cat (.wd (toWord it.qlen)) (.cp (u + 1) (it.qlen / 8 + 4)))
      (tItems (u + it.slen / 8) its)

/-- **A phase's trace segment** at stream word `u` (a later phase; the seed is `seedSeg`). -/
def tPh (u : ℕ) : Shape → Seg
  | .seed => .nil
  | .absorb _ len => tItems u [.absorb len]
  | .squeezes n _ => .rep n 10 (tItems u [.squeeze])
  | .uni _ => tItems u [.absorb uniBytes, .squeeze]
  | .rounds _ n _ inK _ => .rep n (wsum [.absorb (roundBytes inK), .squeeze])
      (tItems u [.absorb (roundBytes inK), .squeeze])
  | .queries i => .rep (lvlStar i).t (wsum (posItems i))
      (.cat (tItems u [.col i]) (.rep (lvlStar i).sib 14 (tItems (u + (Item.col i).slen / 8) [.node i 0])))

/-- The phases' trace segments from stream word `u`. -/
def tSegs : ℕ → List Shape → Seg
  | _, [] => .nil
  | u, sh :: shs => .cat (tPh u sh) (tSegs (u + wsum sh.items) shs)

/-- **The seed entry's segment**: `|q| = 119`, the query's 15 words (stream bytes `9 … 127`,
straddling stream words `1 … 15`), the answer (stream words `16 … 19`). -/
def seedSeg : Seg :=
  .cat (.wd (toWord 119)) (.cat (.rep 14 1 (.shw 1)) (.cat (.sh8 15) (.cp 16 4)))

/-- The later phases (all but the seed). -/
def restSh : List Shape := (phases.map Phase.shape).tail

/-- **A trace's segment**: the count, the seed entry, the later phases from stream word 20. -/
def trSeg : Seg := .cat (.wd (toWord 8891)) (.cat seedSeg (tSegs 20 restSh))

/-- **The signature's segment** over the L words: `idx` (`c₀` of element 0), then elements
`1 … 298`. -/
def sigSeg : Seg := .cat (.cp 0 1) (.cp 2 596)

/-- Slot `σ`'s L words: coefficient `v mod 2` of L element `⌊v/2⌋`. -/
def lWord (w : ℕ → F) (σ v : ℕ) : Word := (elemWords (w (lCell σ (v / 2)))).getD (v % 2) 0

/-! ## Proof helpers -/

theorem segOut_length (W : ℕ → Word) (κ : Bool) : ∀ (s : Seg) (b : ℕ),
    (segOut W κ b s).length = segLen κ s
  | .nil, _ => rfl
  | .cat x y, b => by simp [segOut, segLen, segOut_length W κ x, segOut_length W κ y]
  | .wd _, _ => rfl
  | .cp _ _, _ => by simp [segOut, segLen]
  | .rep c s x, b => by
    simp [segOut, segLen, List.length_flatMap, segOut_length W κ x]
  | .shw _, _ => rfl
  | .sh8 _, _ => rfl
  | .kite x y, b => by cases κ <;> simp [segOut, segLen, segOut_length W _ x, segOut_length W _ y]
  | .sib o S t sS ansW logN per sK, b => by
    have h4 : ∀ p h, (sibW W b o S ansW logN per sK p h).length = 4 := fun p h => by
      unfold sibW; split_ifs <;> simp
    simp [segOut, segLen, List.length_flatMap, h4, Nat.mul_assoc]

theorem segOut_catL (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ l : List Seg,
    segOut W κ b (catL l) = l.flatMap (segOut W κ b)
  | [] => rfl
  | x :: xs => by rw [catL, segOut, segOut_catL W κ b xs, List.flatMap_cons]

theorem take_drop_map_range (f : ℕ → Word) {N a n : ℕ} (h : a + n ≤ N) :
    (((List.range N).map f).drop a).take n = (List.range n).map fun j => f (a + j) := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]

theorem trW_eq (f W : ℕ → Word) (N : ℕ) (hW : ∀ u < N, W u = f u) : ∀ (its : List Item) (u : ℕ),
    (∀ it ∈ its, it.qlen % 8 = 0) → 8 * u + (its.map Item.slen).sum ≤ 8 * N →
    trW ((List.range N).map f) u its = trWf W u its
  | [], _, _, _ => rfl
  | it :: its, u, hq, hb => by
    have h8 := hq it (by simp)
    simp only [List.map_cons, List.sum_cons, Item.slen] at hb
    rw [trW, trWf, take_drop_map_range f (by omega),
      trW_eq f W N hW its _ (fun x hx => hq x (by simp [hx])) (by simp only [Item.slen] at *; omega)]
    refine congrArg (· ++ _) (congrArg (_ :: ·) (List.map_congr_left fun j hj => (hW _ ?_).symm))
    have := List.mem_range.1 hj
    omega

theorem trWf_append (W : ℕ → Word) : ∀ (l₁ l₂ : List Item) (u : ℕ),
    trWf W u (l₁ ++ l₂) = trWf W u l₁ ++ trWf W (u + wsum l₁) l₂
  | [], _, u => by simp [trWf, wsum]
  | it :: l₁, l₂, u => by
    rw [List.cons_append, trWf, trWf, trWf_append W l₁ l₂, List.append_assoc]
    simp only [wsum, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem wsum_flatten_replicate (c : ℕ) (blk : List Item) :
    wsum (List.replicate c blk).flatten = c * wsum blk := by
  induction c with
  | zero => simp [wsum]
  | succ c ih =>
    rw [List.replicate_succ, List.flatten_cons, wsum, List.map_append, List.sum_append, ← wsum, ← wsum,
      ih]
    ring

theorem trWf_rep (W : ℕ → Word) (blk : List Item) : ∀ (c u : ℕ),
    trWf W u (List.replicate c blk).flatten =
      (List.range c).flatMap fun j => trWf W (u + wsum blk * j) blk
  | 0, _ => rfl
  | c + 1, u => by
    rw [List.replicate_succ', List.flatten_append, trWf_append, trWf_rep W blk c u, List.range_succ,
      List.flatMap_append, wsum_flatten_replicate]
    simp [Nat.mul_comm]

/-- `trWf` depends on the items only through their query lengths. -/
theorem trWf_congr (W : ℕ → Word) : ∀ (l l' : List Item) (u : ℕ), l.map Item.qlen = l'.map Item.qlen →
    trWf W u l = trWf W u l'
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | it :: l, it' :: l', u, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [trWf, trWf, h.1, Item.slen, Item.slen, h.1, trWf_congr W l l' _ h.2]

theorem segOut_tItems (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ (its : List Item) (u : ℕ),
    segOut W κ b (tItems u its) = trWf W (b + u) its
  | [], _ => rfl
  | it :: its, u => by
    rw [tItems, segOut, segOut, segOut, segOut, segOut_tItems W κ b its, trWf, ← Nat.add_assoc]
    simp only [List.singleton_append, List.cons_append, List.nil_append, Nat.add_assoc]

theorem segOut_tPh (W : ℕ → Word) (κ : Bool) (b u : ℕ) (sh : Shape) (hs : sh ≠ .seed) :
    segOut W κ b (tPh u sh) = trWf W (b + u) sh.items := by
  cases sh with
  | seed => exact absurd rfl hs
  | absorb g len => exact segOut_tItems W κ b _ u
  | squeezes n ch =>
    rw [tPh, segOut, Shape.items, show List.replicate n Item.squeeze = (List.replicate n [Item.squeeze]).flatten by
      simp, trWf_rep]
    refine List.flatMap_congr fun j _ => ?_
    rw [segOut_tItems, show wsum [Item.squeeze] = 10 from rfl]
    congr 1; ring
  | uni g => exact segOut_tItems W κ b _ u
  | rounds g n deg inK real =>
    rw [tPh, segOut, Shape.items, trWf_rep]
    refine List.flatMap_congr fun j _ => ?_
    rw [segOut_tItems]; congr 1; ring
  | queries i =>
    rw [tPh, segOut, Shape.items, trWf_rep]
    refine List.flatMap_congr fun j _ => ?_
    rw [segOut, segOut_tItems, posItems, show Item.col i :: (List.range (lvlStar i).sib).map (Item.node i) =
      [Item.col i] ++ (List.range (lvlStar i).sib).map (Item.node i) from rfl, trWf_append,
      trWf_congr W ((List.range (lvlStar i).sib).map (Item.node i))
        (List.replicate (lvlStar i).sib [Item.node i 0]).flatten _
        (by simp [Function.comp_def, Item.qlen, List.map_const']),
      trWf_rep, segOut]
    refine congrArg₂ _ (by congr 1; ring) (List.flatMap_congr fun h _ => ?_)
    rw [segOut_tItems, show wsum [Item.node i 0] = 14 by simp [wsum, Item.slen, Item.qlen],
      show wsum [Item.col i] = (Item.col i).slen / 8 by simp [wsum]]
    congr 1; ring

theorem segOut_tSegs (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ (shs : List Shape) (u : ℕ),
    (∀ sh ∈ shs, sh ≠ .seed) → segOut W κ b (tSegs u shs) = trWf W (b + u) (shs.flatMap Shape.items)
  | [], _, _ => rfl
  | sh :: shs, u, h => by
    rw [tSegs, segOut, segOut_tPh W κ b u sh (h sh (by simp)),
      segOut_tSegs W κ b shs _ fun x hx => h x (by simp [hx]), List.flatMap_cons, trWf_append,
      Nat.add_assoc]

theorem phases_shape : phases.map Phase.shape = .seed :: restSh := rfl

theorem items_tail : items.tail = restSh.flatMap Shape.items := by
  rw [items, ← List.flatMap_map, phases_shape, List.flatMap_cons]; rfl

theorem restSh_noSeed : ∀ sh ∈ restSh, sh ≠ .seed := by
  have h : (restSh.map fun sh => match sh with | .seed => true | _ => false).all (· = false) := by
    decide +kernel
  intro sh hsh hs
  subst hs
  have := List.all_eq_true.1 h _ (List.mem_map_of_mem hsh)
  simp at this

/-! ## The seed entry -/

theorem ofLE_append : ∀ (l₁ l₂ : List UInt8), ofLE (l₁ ++ l₂) = ofLE l₁ + 256 ^ l₁.length * ofLE l₂
  | [], _ => by simp [ofLE]
  | d :: l₁, l₂ => by
    rw [List.cons_append, ofLE_cons, ofLE_cons, ofLE_append l₁ l₂, List.length_cons, pow_succ]; ring

theorem enc64_drop1 (n : ℕ) : (enc64 n).drop 1 = List.ofFn fun i : Fin 7 => (n / 256 / 256 ^ i.val).toUInt8 := by
  refine List.ext_getElem (by simp [enc64]) fun i h1 h2 => ?_
  simp only [enc64, List.getElem_drop, List.getElem_ofFn, Nat.div_div_eq_div_mul, ← pow_succ']
  congr 3; omega

/-- **A word straddling two stream words**: bytes `1 … 8` of `x ‖ y`. -/
theorem shw_bytes (x y : Word) :
    toWord (ofLE (((wordBytes x).drop 1) ++ (wordBytes y).take 1)) = (x >>> 8) + (y <<< 56) := by
  have hx := x.isLt
  have hy := y.isLt
  rw [ofLE_append, wordBytes, wordBytes, enc64_drop1, ofLE_ofFn, List.length_ofFn]
  have e1 : (enc64 y.toNat).take 1 = [(y.toNat).toUInt8] := by simp [enc64, List.ofFn_succ]
  rw [e1, ofLE_cons, show ofLE [] = 0 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [toWord, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.toUInt8, UInt8.toNat_ofNat]
  have h1 : x.toNat / 256 % 256 ^ 7 = x.toNat / 2 ^ 8 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : y.toNat * 2 ^ 56 % 2 ^ 64 = y.toNat % 256 * 2 ^ 56 := by
    rw [show (2 : ℕ) ^ 64 = 256 * 2 ^ 56 by norm_num, Nat.mul_mod_mul_right]
  rw [h2]
  have h3 : x.toNat / 2 ^ 8 < 2 ^ 56 := by omega
  have h4 : y.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt (by omega : x.toNat / 2 ^ 8 + y.toNat % 256 * 2 ^ 56 < 2 ^ 64)]
  norm_num
  omega

/-- The last word of the seed's query: bytes `1 … 7` of a stream word. -/
theorem sh8_bytes (x : Word) : toWord (ofLE ((wordBytes x).drop 1)) = x >>> 8 := by
  have hx := x.isLt
  rw [wordBytes, enc64_drop1, ofLE_ofFn]
  apply BitVec.eq_of_toNat_eq
  simp only [toWord, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat / 256 % 256 ^ 7 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat / 256 < 256 ^ 7)]

theorem wordsBytes_cons (x : Word) (ws : List Word) : wordsBytes (x :: ws) = wordBytes x ++ wordsBytes ws :=
  rfl

/-- Stream bytes `8a + 1 … 8a + 8` are bytes `1 … 8` of words `a, a + 1`. -/
theorem take_drop1_88 (l₁ l₂ r : List UInt8) (h₁ : l₁.length = 8) (h₂ : l₂.length = 8) :
    ((l₁ ++ (l₂ ++ r)).drop 1).take 8 = l₁.drop 1 ++ l₂.take 1 := by
  rw [List.drop_append_of_le_length (by omega), List.take_append,
    List.take_of_length_le (by simp; omega), List.length_drop, h₁,
    List.take_append_of_le_length (by omega)]

/-- Stream bytes `8a + 1 … 8a + 8` are bytes `1 … 8` of words `a, a + 1`. -/
theorem straddle (ws : List Word) (a : ℕ) (ha : a + 1 < ws.length) :
    ((wordsBytes ws).drop (8 * a + 1)).take 8 = (wordBytes ws[a]).drop 1 ++ (wordBytes ws[a + 1]).take 1 := by
  rw [← List.drop_drop, wordsBytes_drop,
    List.drop_eq_getElem_cons (show a < ws.length by omega),
    List.drop_eq_getElem_cons (show a + 1 < ws.length by omega), wordsBytes_cons, wordsBytes_cons, take_drop1_88 _ _ _ (wordBytes_length _) (wordBytes_length _)]

theorem lastByte7 (ws : List Word) (a : ℕ) (ha : a < ws.length) :
    ((wordsBytes ws).drop (8 * a + 1)).take 7 = (wordBytes ws[a]).drop 1 := by
  rw [← List.drop_drop, wordsBytes_drop,
    List.drop_eq_getElem_cons (show a < ws.length by omega), wordsBytes_cons,
    List.drop_append_of_le_length (by simp [wordBytes_length]),
    List.take_append_of_le_length (by simp [wordBytes_length])]
  exact List.take_of_length_le (by simp [wordBytes_length])

theorem streamWords_getElem (w : ℕ → F) (σ u : ℕ) (hu : u < (streamWords w σ).length) :
    (streamWords w σ)[u] = streamWord w σ u := by
  simp [streamWords]

/-- **An aligned stream slice in words**: stream words `[u, u + n)` are `W (u + j)`. -/
theorem streamWords_slice (w : ℕ → F) (σ : ℕ) (W : ℕ → Word)
    (hW : ∀ u < 185168, W u = streamWord w σ u) {u n : ℕ} (h : u + n ≤ 185168) :
    ((streamWords w σ).drop u).take n = (List.range n).map fun j => W (u + j) := by
  rw [streamWords, streamBytes_eq, take_drop_map_range _ h]
  exact List.map_congr_left fun j hj => (hW _ (by have := List.mem_range.1 hj; omega)).symm

theorem flatMap_single {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun x => [f x]) = l.map f := by
  induction l <;> simp_all

/-- **The seed entry's words** are `seedSeg`'s over the stream words. -/
theorem entryW_seed (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (κ : Bool)
    (hW : ∀ u < 185168, W u = streamWord w σ u) :
    entryW (entryAt (stream w σ) 1 .seed) = segOut W κ 0 seedSeg := by
  have hL := streamWords_length w σ
  have hget : ∀ u (hu : u < (streamWords w σ).length), (streamWords w σ)[u] = W u := fun u hu => by
    rw [streamWords_getElem, hW u (by omega)]
  generalize hws : streamWords w σ = ws at hL hget
  have hst : stream w σ = wordsBytes ws := by rw [stream, hws]
  have hB : (wordsBytes ws).length = 1481344 := by rw [wordsBytes_length, hL]
  have e0 : entryW (entryAt (stream w σ) 1 .seed) = bytesWords (((wordsBytes ws).drop 9).take 119) ++
      packBytes (Vector.ofFn fun i : Fin 32 => (wordsBytes ws).getD (128 + i) 0).toList := by
    rw [hst, entryW, entryAt, List.toList_toArray]; rfl
  have hl : (((wordsBytes ws).drop 9).take 119).length = 119 := by simp [hB]
  have hP : packBytes (((wordsBytes ws).drop 9).take 119) =
      ((List.range 14).map fun j => (W (j + 1) >>> 8) + (W (j + 1 + 1) <<< 56)) ++ [W 15 >>> 8] := by
    rw [packBytes, hl, show (119 + 7) / 8 = 14 + 1 from rfl, List.range_succ, List.map_append]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun j hj => ?_
      have hj := List.mem_range.1 hj
      rw [List.drop_take, List.take_take, List.drop_drop, show min 8 (119 - 8 * j) = 8 by omega,
        show 9 + 8 * j = 8 * (j + 1) + 1 by omega, straddle ws (j + 1) (by omega), shw_bytes,
        hget _ (by omega), hget _ (by omega)]
    · rw [List.map_singleton, List.drop_take, List.take_take, List.drop_drop,
        show min 8 (119 - 8 * 14) = 7 from rfl, show 9 + 8 * 14 = 8 * 15 + 1 from rfl,
        lastByte7 ws 15 (by omega), sh8_bytes, hget _ (by omega)]
  have hA : packBytes (Vector.ofFn fun i : Fin 32 => (wordsBytes ws).getD (128 + i) 0).toList =
      (List.range 4).map fun j => W (16 + j) := by
    rw [digest_toList _ _ (by rw [hB]; norm_num), show (128 : ℕ) = 8 * 16 from rfl, wordsBytes_drop,
      show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_take, packBytes_wordsBytes, ← hws,
      streamWords_slice w σ W hW (by norm_num)]
  rw [e0, bytesWords, hl, hP, hA]
  simp only [seedSeg, segOut, Nat.zero_add, Nat.one_mul, flatMap_single]
  simp

/-! ## Load-bearing lemmas -/

/-- **A child's trace in words** (`logWords`) is `trSeg`'s over its stream words. -/
theorem logWords_trSeg (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (κ : Bool)
    (hW : ∀ u < 185168, W u = streamWord w σ u) :
    logWords (readTrace w σ) = segOut W κ 0 trSeg := by
  have hq : ∀ it ∈ items.tail, it.qlen % 8 = 0 := fun it h => by have := qlen_mod.2.2 it h; omega
  have hb : 8 * 20 + (items.tail.map Item.slen).sum ≤ 8 * 185168 := by
    have := tail_slen_le; rw [streamBytes_eq] at this; omega
  rw [logWords_readTrace, trSeg, segOut, segOut, segOut, ← entryW_seed w σ W κ hW,
    segOut_tSegs W κ 0 restSh 20 restSh_noSeed, ← items_tail, Nat.zero_add, streamWords,
    streamBytes_eq, trW_eq (streamWord w σ) W 185168 hW items.tail 20 hq hb]
  rfl

theorem elemWords_lCell (w : ℕ → F) (σ k : ℕ) :
    elemWords (w (lCell σ k)) = [lWord w σ (2 * k), lWord w σ (2 * k + 1)] := by
  simp only [lWord, show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega,
    show 2 * k % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega, elemWords]
  rfl

theorem lPairs (w : ℕ → F) (σ a : ℕ) : ∀ n, ((List.range n).flatMap fun j =>
    elemWords (w (lCell σ (a + 2 * j))) ++ elemWords (w (lCell σ (a + 1 + 2 * j)))) =
      (List.range (4 * n)).map fun j => lWord w σ (2 * a + j)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, lPairs w σ a n, show 4 * (n + 1) = 4 * n + 4 by ring,
      List.range_add, List.map_append, List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, elemWords_lCell]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      Function.comp_apply, List.nil_append, List.cons_append, List.singleton_append]
    refine congrArg _ ?_
    simp only [List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> congr 1 <;> ring

/-- **A child's signature in words** (`sigWords`) is `sigSeg`'s over its L words. -/
theorem sigWords_sigSeg (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (κ : Bool)
    (hW : ∀ v < 598, W v = lWord w σ v) :
    sigWords (readSig w σ) = segOut W κ 0 sigSeg := by
  rw [sigWords_readSig]
  have e1 := lPairs w σ 1 wotsLen
  have e2 := lPairs w σ (1 + 2 * wotsLen) sigHeight
  have f1 : ((List.range wotsLen).flatMap fun j => elemWords (w (lCell σ (1 + 2 * j))) ++
      elemWords (w (lCell σ (2 + 2 * j)))) = (List.range (4 * wotsLen)).map fun j => lWord w σ (2 * 1 + j) :=
    e1
  have f2 : ((List.range sigHeight).flatMap fun t => elemWords (w (lCell σ (1 + 2 * wotsLen + 2 * t))) ++
      elemWords (w (lCell σ (2 + 2 * wotsLen + 2 * t)))) =
      (List.range (4 * sigHeight)).map fun j => lWord w σ (2 * (1 + 2 * wotsLen) + j) := by
    rw [← e2]; refine List.flatMap_congr fun t _ => ?_; congr 4
  rw [f1, f2]
  simp only [sigSeg, segOut, List.range_one, List.map_singleton, List.singleton_append]
  have hr : (List.range 596).map (fun j => W (0 + 2 + j)) =
      (List.range 532).map (fun j => W (2 + j)) ++ (List.range 64).map (fun j => W (2 + (532 + j))) := by
    rw [show (596 : ℕ) = 532 + 64 from rfl, List.range_add, List.map_append, List.map_map]; rfl
  rw [hr, show 4 * wotsLen = 532 from rfl, show 4 * sigHeight = 64 from rfl,
    show 2 * (1 + 2 * wotsLen) = 534 from rfl]
  have h0 : toWord (w (lCell σ 0)).c₀.val.toNat = W (0 + 0 + 0) := by
    rw [hW 0 (by norm_num), lWord]
    apply BitVec.eq_of_toNat_eq
    simp [toWord, elemWords]
  have h1 : (List.range 532).map (fun j => lWord w σ (2 * 1 + j)) =
      (List.range 532).map (fun j => W (2 + j)) :=
    List.map_congr_left fun j hj => by have := List.mem_range.1 hj; rw [hW _ (by omega)]
  have h2 : (List.range 64).map (fun j => lWord w σ (534 + j)) =
      (List.range 64).map (fun j => W (2 + (532 + j))) :=
    List.map_congr_left fun j hj => by
      have := List.mem_range.1 hj; rw [hW _ (by omega), show 2 + (532 + j) = 534 + j by omega]
  rw [h0, h1, h2, List.cons_append]

/-- **A child statement's words** are stream words 6–9 (`readStmt`: stream elements 3–4). -/
theorem stmtWords (w : ℕ → F) (σ : ℕ) (W : ℕ → Word) (κ : Bool)
    (hW : ∀ u < 185168, W u = streamWord w σ u) :
    packBytes (readStmt w σ).toList = segOut W κ 0 (.cp 6 4) := by
  rw [readStmt, packBytes_digestOf]
  simp only [segOut, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hW _ (by norm_num), hW _ (by norm_num), hW _ (by norm_num), hW _ (by norm_num)]
  simp [streamWord, elemWords]

end FR.Read
