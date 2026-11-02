-- G6: this module also holds the former modules `FRNodeReadS`, `FRNodeReadP` (one section each, in import order).
import FRNodeReadCore
import FRXRead

section G6_FRNodeReadS

-- New for `flock-recursive` (BLUEPRINT §6.2 step 5, §6.5 `output_spec`; stage S-H2, track L-ext,
-- S-H2l).

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

end G6_FRNodeReadS

section G6_FRNodeReadP

-- New for `flock-recursive` (BLUEPRINT A.5, §6.2 step 5, §6.5 `output_spec`; stage S-H2,
-- track L-ext, S-H2l).

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

end G6_FRNodeReadP

section G6_FRXOut

-- New for `flock-recursive` (BLUEPRINT §6.2 step 5, §6.5 `output_spec`; stage S-H2, track L-ext,
-- S-H2l).

/-!
# The output segments compiled: `segIR`

`FRNodeReadS.Seg` describes the words the node extractor emits, over a word source. Here a
segment is compiled to `XIR` (`segIR ap d`), with no store: every word is read from the heap by
one computed load (`ldw ap`). The source word `n` sits at the address

`addrW ap R n = R + (((n >>> 1) &&& m₁) <<< st) + ((n >>> s₃) <<< s₄) + (n &&& 1)`

(`ap = (m₁, s₃, s₄, st)`; 3.x's shapes have `st = 18`): the stream words of a slot (`apS`) and its L words (`apL`) are both of this
shape over `f⁽⁰⁾`'s rows at `ob0` (`FRXOutRun`). The base offset of a segment is register
`oBd d` at nesting depth `d`; a `rep` at depth `d` counts in `oCd d` and moves the base of depth
`d + 1`.

* **`segIR_sem`**: from a state in context (`Ctx`: the heap is `M₀`'s, `oR = R`, the kind flag),
  the compiled segment appends `segOut (src M₀ ap R) κ b s` to the output, where
  `src M₀ ap R n` is the heap word at `addrW ap R n`;
* `wf_segIR`, `loK_segIR` (no store), `noLoopT_segIR`, and `ctx_segIR` (the context is kept).
-/

namespace FR.X

open RecursionFast FR.Read

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers -/

/-- The source index. -/ def oU : ℕ := 200
/-- The source base `R`. -/ def oR : ℕ := 201
/-- The word read or emitted. -/ def oX : ℕ := 202
/-- The load address. -/ def oAd : ℕ := 203
/-- Address scratch. -/ def oT1 : ℕ := 204
/-- Address scratch. -/ def oT2 : ℕ := 205
/-- Address scratch. -/ def oT3 : ℕ := 206
/-- Constants. -/ def oK : ℕ := 207
/-- The seed's second word. -/ def oY : ℕ := 208
/-- The kind flag (`kite`). -/ def oKF : ℕ := 209
/-- The copy counter. -/ def oCp : ℕ := 210
/-- The copy count. -/ def oNp : ℕ := 211
/-- The position counter. -/ def oSp : ℕ := 212
/-- The position count. -/ def oSn : ℕ := 213
/-- The depth counter. -/ def oSh : ℕ := 214
/-- The depth count. -/ def oShn : ℕ := 215
/-- The position's node pointer. -/ def oN : ℕ := 216
/-- The depth's node pointer. -/ def oNh : ℕ := 217
/-- The answer pointer. -/ def oA : ℕ := 218
/-- `(p mod per)·logN`. -/ def oRm : ℕ := 219
/-- `p mod per`. -/ def oRc : ℕ := 220
/-- The depth `h`. -/ def oH : ℕ := 221
/-- The bit index `m`. -/ def oM : ℕ := 222
/-- The bit. -/ def oB2 : ℕ := 223
/-- A flag. -/ def oFl : ℕ := 224
/-- A `rep`'s counter at depth `d`. -/ def oCd (d : ℕ) : ℕ := 226 + 3 * d
/-- A `rep`'s count at depth `d`. -/ def oNd (d : ℕ) : ℕ := 227 + 3 * d
/-- The base at depth `d`. -/ def oBd (d : ℕ) : ℕ := 228 + 3 * d

/-! ## Specification: the address block and the compiled segments -/

/-- An address shape `(m₁, s₃, s₄)` at row shift `st` (3.x: `18`, `f⁽⁰⁾`'s row stride `2^18`;
revision 4.1: `mLog 0 + 1`). -/
structure AP where
  m1 : ℕ
  s3 : ℕ
  s4 : ℕ
  st : ℕ

/-- **The address of source word `x`** from the base `R`, as the machine computes it. -/
def addrW (ap : AP) (R x : Word) : Word :=
  XOp.add.eval (XOp.add.eval (XOp.add.eval R
    (XOp.shl.eval (XOp.and.eval (XOp.shr.eval x (toWord 1)) (toWord ap.m1)) (toWord ap.st)))
    (XOp.shl.eval (XOp.shr.eval x (toWord ap.s3)) (toWord ap.s4))) (XOp.and.eval x 1)

/-- **The source**: word `n` is the heap word at `addrW ap R n`. -/
def src (M : Mem) (ap : AP) (R : ℕ) (n : ℕ) : Word := rd M (addrW ap (toWord R) (toWord n)).toNat

/-- The address block: `oAd := addrW ap oR oU`. -/
def ldPs (ap : AP) : List Prim :=
  [.const oK (toWord 1), .op .shr oT1 oU oK, .const oK (toWord ap.m1), .op .and oT1 oT1 oK,
   .const oK (toWord ap.st), .op .shl oT1 oT1 oK, .const oK (toWord ap.s3), .op .shr oT2 oU oK,
   .const oK (toWord ap.s4), .op .shl oT2 oT2 oK, .op .and oT3 oU cOne, .op .add oAd oR oT1,
   .op .add oAd oAd oT2, .op .add oAd oAd oT3]

/-- **One source word**: `oX := M[addrW ap oR oU]`. -/
def ldw (ap : AP) : XIR := .seq (.blk (ldPs ap)) (.load oX oAd)

/-- **A copy** of `n` source words from `rb + o`. -/
def cpIR (ap : AP) (rb o n : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)])
    (.loopK oCp oNp (toWord n) (.seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne]))))

/-- Four zero words. -/
def zeros4 : XIR := .seq (.blk [.const oX 0]) (.seq (.out oX) (.seq (.out oX) (.seq (.out oX) (.out oX))))

/-- A sibling at a real depth: the bit `m = oRm + oH` of the answer at `oA`, then the left half
(node words 2–5) for bit `1`, the right half (6–9) for bit `0`. -/
def sibHit (ap : AP) : XIR :=
  .seq (.blk [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU])
    (.seq (ldw ap) (.seq (.blk [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne])
      (.ite oB2 (cpIR ap oNh 2 4) (cpIR ap oNh 6 4))))

/-- One depth `h`: a sibling below `sK`, zeros above; `h += 1`, the node pointer moves 14. -/
def sibH (ap : AP) (sK : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord sK), .op .ltu oFl oH oK])
    (.seq (.ite oFl (sibHit ap) zeros4) (.blk [.op .add oH oH cOne, .const oK 14, .op .add oNh oNh oK]))

/-- One position `p`: its `sS` depths, then `p + 1`: the node pointer moves `S`, `p mod per`
and `(p mod per)·logN` step, and wrap to the next answer (10 words on) at `per`. -/
def sibP (ap : AP) (S sS logN per sK : ℕ) : XIR :=
  .seq (.blk [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)])
    (.seq (.loopK oSh oShn (toWord sS) (sibH ap sK))
      (.seq (.blk [.const oK (toWord S), .op .add oN oN oK, .const oK (toWord logN), .op .add oRm oRm oK,
          .op .add oRc oRc cOne, .const oK (toWord per), .op .eq oFl oRc oK])
        (.ite oFl (.blk [.const oRc 0, .const oRm 0, .const oK 10, .op .add oA oA oK]) (.blk []))))

/-- **One level's siblings** (`Seg.sib`) from base register `rb`. -/
def sibIR (ap : AP) (rb o S t sS ansW logN per sK : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW), .op .add oA rb oK,
      .const oRm 0, .const oRc 0, .const oSn (toWord t)])
    (.loopK oSp oSn (toWord t) (sibP ap S sS logN per sK))

/-- **A compiled segment** at depth `d` (base register `oBd d`). -/
def segIR (ap : AP) : ℕ → Seg → XIR
  | _, .nil => .blk []
  | d, .cat x y => .seq (segIR ap d x) (segIR ap d y)
  | _, .wd x => .seq (.blk [.const oX x]) (.out oX)
  | d, .cp o n => cpIR ap (oBd d) o n
  | d, .rep c s x => .seq (.blk [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)])
      (.loopK (oCd d) (oNd d) (toWord c)
        (.seq (segIR ap (d + 1) x) (.blk [.const oK (toWord s), .op .add (oBd (d + 1)) (oBd (d + 1)) oK])))
  | d, .shw o => .seq (.blk [.const oK (toWord o), .op .add oU (oBd d) oK])
      (.seq (ldw ap) (.seq (.blk [.op .or oY oX oX, .op .add oU oU cOne]) (.seq (ldw ap)
        (.seq (.blk [.const oK (toWord 56), .op .shl oX oX oK, .const oK (toWord 8), .op .shr oY oY oK,
          .op .add oX oY oX])
          (.out oX)))))
  | d, .sh8 o => .seq (.blk [.const oK (toWord o), .op .add oU (oBd d) oK])
      (.seq (ldw ap) (.seq (.blk [.const oK (toWord 8), .op .shr oX oX oK]) (.out oX)))
  | d, .kite x y => .ite oKF (segIR ap d x) (segIR ap d y)
  | d, .sib o S t sS ansW logN per sK => sibIR ap (oBd d) o S t sS ansW logN per sK

/-- The `rep` nesting depth. -/
def depthSeg : Seg → ℕ
  | .cat x y | .kite x y => max (depthSeg x) (depthSeg y)
  | .rep _ _ x => depthSeg x + 1
  | _ => 0

/-- The counts fit a word with room (`< 2^32`), and a level's `per` is positive. -/
def okSeg : Seg → Bool
  | .cat x y | .kite x y => okSeg x && okSeg y
  | .rep c _ x => decide (c < 2 ^ 32) && okSeg x
  | .cp _ n => decide (n < 2 ^ 32)
  | .sib _ _ t sS _ logN per sK => decide (t < 2 ^ 32) && decide (sS < 2 ^ 32) &&
      decide (logN < 2 ^ 32) && decide (per < 2 ^ 32) && decide (sK < 2 ^ 32) && decide (0 < per)
  | _ => true

/-- **The machine's context** for a segment: the heap is `M₀`'s, `oR = R`, the kind flag is `κ`. -/
structure Ctx (M₀ : Mem) (R : ℕ) (κ : Bool) (s : St) : Prop where
  inv : Inv s.M
  size : s.M.size = M₀.size
  heap : ∀ y, regs ≤ y → rd s.M y = rd M₀ y
  r : rd s.M oR = toWord R
  k : rd s.M oKF = 0 ↔ κ = false

/-- The registers a segment at depth `d` keeps: `oR`, `oKF`, the outer `rep`s' and its base. -/
def Prot (d r : ℕ) : Prop := r = oR ∨ r = oKF ∨ (226 ≤ r ∧ r < 226 + 3 * d) ∨ r = 228 + 3 * d

/-! ## Proof helpers: what the code writes -/

/-- The cells a program names as destinations, as a list. -/
def wrL : XIR → List ℕ
  | .blk ps => ps.map Prim.dst
  | .load d _ | .input d _ => [d]
  | .store .. => [cTmp]
  | .out _ => []
  | .seq p q | .ite _ p q => wrL p ++ wrL q
  | .loopK c _ _ b => c :: cTmp :: wrL b
  | .loopT c _ _ b => c :: wrL b

theorem writes_wrL : ∀ (P : XIR) (r : ℕ), Writes P r → r ∈ wrL P
  | .blk ps, r, ⟨p, hp, he⟩ => List.mem_map.2 ⟨p, hp, he⟩
  | .load _ _, _, h | .input _ _, _, h | .store _ _, _, h => List.mem_singleton.2 h
  | .out _, _, h => h.elim
  | .seq p q, r, h | .ite _ p q, r, h => List.mem_append.2 (h.imp (writes_wrL p r) (writes_wrL q r))
  | .loopK c _ _ b, r, h => by
    rcases h with rfl | rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (writes_wrL b r h))
  | .loopT c _ _ b, r, h => by
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (writes_wrL b r h)

/-- Leaf code writes only leaf registers (and the compiler's `cTmp`). -/
def LW (r : ℕ) : Prop := r = cTmp ∨ (200 ≤ r ∧ r ≤ 224 ∧ r ≠ 201 ∧ r ≠ 209)

/-- The registers a segment at depth `d` may write: the leaf registers, and the `rep` registers
from depth `d` on. -/
def OW (d r : ℕ) : Prop :=
  LW r ∨ ∃ e, d ≤ e ∧ (r = 226 + 3 * e ∨ r = 227 + 3 * e ∨ r = 231 + 3 * e)

theorem lw_cpIR (ap : AP) (rb o n r : ℕ) (h : Writes (cpIR ap rb o n) r) : LW r := by
  have := writes_wrL _ _ h
  simp only [cpIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at this
  simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oNp, oCp, cTmp] at this ⊢; omega

theorem lw_sibIR (ap : AP) (rb o S t sS ansW logN per sK r : ℕ)
    (h : Writes (sibIR ap rb o S t sS ansW logN per sK) r) : LW r := by
  have := writes_wrL _ _ h
  simp only [sibIR, sibP, sibH, sibHit, zeros4, cpIR, ldw, ldPs, wrL, List.map_cons, List.map_nil,
    Prim.dst, List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff,
    or_false, List.mem_append] at this
  simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oNp, oCp, cTmp, oN, oA, oRm, oRc, oSn, oSp, oNh, oH,
    oShn, oSh, oFl, oM, oB2] at *; omega

theorem ow_segIR (ap : AP) : ∀ (seg : Seg) (d r : ℕ), Writes (segIR ap d seg) r → OW d r
  | .nil, _, _, h => by simp [segIR, Writes] at h
  | .cat x y, d, r, h => h.elim (ow_segIR ap x d r) (ow_segIR ap y d r)
  | .kite x y, d, r, h => h.elim (ow_segIR ap x d r) (ow_segIR ap y d r)
  | .wd _, _, r, h => by
    simp [segIR, Writes, Prim.dst] at h; exact .inl (.inr (by simp only [oX] at *; omega))
  | .cp o n, d, r, h => .inl (lw_cpIR ap _ o n r h)
  | .sib .., d, r, h => .inl (lw_sibIR ap _ _ _ _ _ _ _ _ _ r h)
  | .shw o, d, r, h => by
    have := writes_wrL _ _ h
    simp only [segIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
    left; simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oY, cTmp] at *; omega
  | .sh8 o, d, r, h => by
    have := writes_wrL _ _ h
    simp only [segIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
    left; simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, cTmp] at *; omega
  | .rep c s x, d, r, h => by
    simp only [segIR, Writes, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with ⟨p, hp, rfl⟩ | rfl | rfl | h | ⟨p, hp, rfl⟩
    · rcases hp with rfl | rfl
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oBd]; omega⟩
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oNd]⟩
    · exact .inr ⟨d, le_rfl, by simp [oCd]⟩
    · exact .inl (.inl rfl)
    · rcases ow_segIR ap x (d + 1) r h with h | ⟨e, he, h⟩
      · exact .inl h
      · exact .inr ⟨e, by omega, h⟩
    · rcases hp with rfl | rfl
      · exact .inl (.inr (by simp [Prim.dst, oK]))
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oBd]; omega⟩

theorem not_ow_prot {d r : ℕ} (hp : Prot d r) (hw : OW d r) : False := by
  simp only [Prot, OW, LW, oR, oKF, cTmp] at hp hw
  rcases hw with h | ⟨e, he, h⟩ <;> omega

/-- **A segment keeps its protected registers.** -/
theorem noW_segIR (ap : AP) (seg : Seg) (d r : ℕ) (hp : Prot d r) : ¬ Writes (segIR ap d seg) r :=
  fun h => not_ow_prot hp (ow_segIR ap seg d r h)

/-! ## Proof helpers: well formed, no store, the context -/

theorem wf_ldw (ap : AP) : WF (ldw ap) := by
  simp +decide only [ldw, ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem wf_cpIR (ap : AP) (rb o n : ℕ) : WF (cpIR ap rb o n) := by
  refine ⟨by simp +decide only [WF, Prim.dst, oK, oU, oNp, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], ⟨by simp [oCp, oNp, cTmp], by simp [oCp, regs], fun h => ?_,
    wf_ldw ap, trivial, by simp +decide only [WF, Prim.dst, oU]⟩⟩
  have := writes_wrL _ _ h
  simp [wrL, ldw, ldPs, Prim.dst, oCp, oK, oT1, oT2, oT3, oAd, oX, oU] at this

theorem wf_sibIR (ap : AP) (rb o S t sS ansW logN per sK : ℕ) : WF (sibIR ap rb o S t sS ansW logN per sK) := by
  have hw : ∀ c P, (∀ r, Writes P r → r ∈ wrL P) → c ∉ wrL P → ¬ Writes P c := fun c P h hc hw => hc (h c hw)
  refine ⟨by simp +decide only [WF, Prim.dst, oK, oN, oA, oRm, oRc, oSn, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], ⟨by simp [oSp, oSn, cTmp], by simp [oSp, regs],
    hw _ _ (writes_wrL _) (by simp [wrL, sibP, sibH, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oSp, oK, oT1,
      oT2, oT3, oAd, oX, oU, oNp, oCp, oN, oA, oRm, oRc, oNh, oH, oShn, oSh, oFl, oM, oB2, cTmp]), ?_⟩⟩
  refine ⟨by simp +decide only [WF, Prim.dst, oNh, oH, oShn, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], ⟨⟨by simp [oSh, oShn, cTmp], by simp [oSh, regs],
    hw _ _ (writes_wrL _) (by simp [wrL, sibH, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oSh, oK, oT1,
      oT2, oT3, oAd, oX, oU, oNp, oCp, oNh, oH, oFl, oM, oB2, oRm, cTmp]), ?_⟩, ?_⟩⟩
  · exact ⟨by simp +decide only [WF, Prim.dst, oK, oFl, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], ⟨⟨by simp +decide only [
    WF, Prim.dst, oM, oK, oU], wf_ldw ap,
      by simp +decide only [WF, Prim.dst, oB2], wf_cpIR .., wf_cpIR ..⟩, by simp +decide only [
        zeros4, WF, Prim.dst, oX, and_true]⟩,
      by simp +decide only [WF, Prim.dst, oH, oK, oNh]⟩
  · exact ⟨by simp +decide only [WF, Prim.dst, oK, oN, oRm, oRc, oFl, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], by simp +decide only [WF, Prim.dst, oK, oA, oRc, oRm, and_true]⟩

theorem wf_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), depthSeg seg + d ≤ 9 → WF (segIR ap d seg)
  | .nil, _, _ => by simp +decide only [segIR, WF]
  | .cat x y, d, h => ⟨wf_segIR ap x d (by simp [depthSeg] at h; omega),
      wf_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .kite x y, d, h => ⟨wf_segIR ap x d (by simp [depthSeg] at h; omega),
      wf_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .wd _, _, _ => by simp +decide only [segIR, WF, Prim.dst, oX, List.mem_cons, List.mem_nil_iff,
    forall_eq, or_false, and_true]
  | .cp .., _, _ => wf_cpIR ..
  | .sib .., _, _ => wf_sibIR ..
  | .shw _, _, _ => ⟨by simp +decide only [WF, Prim.dst, oK, oU, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], wf_ldw ap, by simp +decide only [
    WF, Prim.dst, oY, oU], wf_ldw ap,
      by simp +decide only [WF, Prim.dst, oK, oX, oY], trivial⟩
  | .sh8 _, _, _ => ⟨by simp +decide only [WF, Prim.dst, oK, oU, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], wf_ldw ap, by simp +decide only [
    WF, Prim.dst, oK, oX], trivial⟩
  | .rep c s x, d, h => by
    simp only [depthSeg] at h
    refine ⟨by simp +decide only [WF, Prim.dst, oBd, oNd, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false]; omega, ⟨by simp [oCd, oNd, cTmp]; omega,
      by simp [oCd, regs]; omega, fun hw => ?_, wf_segIR ap x (d + 1) (by omega),
      by simp [WF, Prim.dst, oK, oBd]; omega⟩⟩
    rcases hw with hw | ⟨p, hp, he⟩
    · exact noW_segIR ap x (d + 1) _ (.inr (.inr (.inl ⟨by simp only [oCd]; omega, by simp only [oCd]; omega⟩))) hw
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp [Prim.dst, oK, oCd, oBd] at he
      all_goals omega

theorem loK_ldw (ap : AP) : LoK (ldw ap) := by
  simp +decide only [ldw, ldPs, LoK, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem loK_cpIR (ap : AP) (rb o n : ℕ) : LoK (cpIR ap rb o n) :=
  ⟨by simp +decide only [LoK, Prim.dst, oK, oU, oNp, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], by simp [oCp, regs], loK_ldw ap, trivial,
    by simp +decide only [LoK, Prim.dst, oU, regs]⟩

theorem loK_sibIR (ap : AP) (rb o S t sS ansW logN per sK : ℕ) : LoK (sibIR ap rb o S t sS ansW logN per sK) := by
  simp +decide only [sibIR, sibP, sibH, sibHit, zeros4, LoK, Prim.dst, oK, oN, oA, oRm, oRc, oSn,
    oSp, oNh, oH, oShn, oSh, oFl, oM, oU, oB2, oX, regs, loK_ldw, loK_cpIR, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem loK_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), depthSeg seg + d ≤ 9 → LoK (segIR ap d seg)
  | .nil, _, _ => by simp +decide only [segIR, LoK]
  | .cat x y, d, h => ⟨loK_segIR ap x d (by simp [depthSeg] at h; omega),
      loK_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .kite x y, d, h => ⟨loK_segIR ap x d (by simp [depthSeg] at h; omega),
      loK_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .wd _, _, _ => by simp +decide only [segIR, LoK, Prim.dst, oX, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq, or_false, and_true]
  | .cp .., _, _ => loK_cpIR ..
  | .sib .., _, _ => loK_sibIR ..
  | .shw _, _, _ => ⟨by simp +decide only [LoK, Prim.dst, oK, oU, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], loK_ldw ap, by simp +decide only [LoK, Prim.dst, oY, oU, regs],
      loK_ldw ap, by simp +decide only [LoK, Prim.dst, oK, oX, oY, regs], trivial⟩
  | .sh8 _, _, _ => ⟨by simp +decide only [LoK, Prim.dst, oK, oU, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], loK_ldw ap, by simp +decide only [LoK, Prim.dst, oK, oX, regs],
      trivial⟩
  | .rep c s x, d, h => by
    simp only [depthSeg] at h
    exact ⟨by simp +decide only [LoK, Prim.dst, oBd, oNd, regs, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false]; omega, by simp [oCd, regs]; omega,
      loK_segIR ap x (d + 1) (by omega), by simp [LoK, Prim.dst, oK, oBd, regs]; omega⟩

theorem noLoopT_cpIR (ap : AP) (rb o n : ℕ) : NoLoopT (cpIR ap rb o n) := by
  simp [cpIR, ldw, NoLoopT]

theorem noLoopT_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), NoLoopT (segIR ap d seg)
  | .nil, _ | .wd _, _ | .shw _, _ | .sh8 _, _ => by simp [segIR, ldw, NoLoopT]
  | .cat x y, d | .kite x y, d => ⟨noLoopT_segIR ap x d, noLoopT_segIR ap y d⟩
  | .cp .., _ => noLoopT_cpIR ..
  | .sib .., _ => by simp [segIR, sibIR, sibP, sibH, sibHit, zeros4, ldw, cpIR, NoLoopT]
  | .rep c s x, d => ⟨trivial, noLoopT_segIR ap x (d + 1), trivial⟩

theorem ctx_sem {M₀ : Mem} {R : ℕ} {κ : Bool} (I : Array Word) {P : XIR} (hL : LoK P) (hw : WF P)
    (h1 : ¬ Writes P oR) (h2 : ¬ Writes P oKF) {s : St} (hc : Ctx M₀ R κ s) : Ctx M₀ R κ (semXIR I P s) where
  inv := inv_sem I hw hc.inv
  size := (size_sem I P s).trans hc.size
  heap y hy := (hframeK I P s hL y hy).trans (hc.heap y hy)
  r := (frame I P s hw hc.inv oR (by simp [oR, regs]) h1).trans hc.r
  k := by rw [frame I P s hw hc.inv oKF (by simp [oKF, regs]) h2]; exact hc.k

/-- **A segment keeps the context.** -/
theorem ctx_segIR {M₀ : Mem} {R : ℕ} {κ : Bool} (I : Array Word) (ap : AP) (seg : Seg) (d : ℕ)
    (hd : depthSeg seg + d ≤ 9) {s : St} (hc : Ctx M₀ R κ s) : Ctx M₀ R κ (semXIR I (segIR ap d seg) s) :=
  ctx_sem I (loK_segIR ap seg d hd) (wf_segIR ap seg d hd) (noW_segIR ap seg d _ (.inl rfl))
    (noW_segIR ap seg d _ (.inr (.inl rfl))) hc

/-! ## Proof helpers: loops that emit -/

theorem iterL_emit (I : Array Word) {b : XIR} {c K : ℕ} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (hf : ∀ j s, j < K → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    ∀ m j s, j + m ≤ K → Q j s → (iterL (semXIR I b) c m s).o.toList =
      s.o.toList ++ (List.range m).flatMap (fun i => out (j + i)) ∧ Q (j + m) (iterL (semXIR I b) c m s)
  | 0, j, s, _, h => ⟨by simp only [iterL, List.range_zero, List.flatMap_nil, List.append_nil], h⟩
  | m + 1, j, s, hm, h => by
    obtain ⟨h1, h2⟩ := hf j s (by omega) h
    obtain ⟨g1, g2⟩ := iterL_emit I Q out hf m (j + 1) _ (by omega) h2
    refine ⟨?_, by rw [show j + (m + 1) = j + 1 + m by omega]; exact g2⟩
    rw [iterL, g1, show (decS c (semXIR I b s)).o = (semXIR I b s).o from rfl, h1, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map, List.append_assoc, Nat.add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1, Nat.succ_eq_add_one, Nat.add_zero]

/-- **A counted loop that emits** `out j` in iteration `j`, under an invariant `Q`. -/
theorem loopK_emit (I : Array Word) {c n K : ℕ} {b : XIR} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (s : St) (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hK : K < 2 ^ 64)
    (hN : rd s.M n = toWord K) (h0 : Q 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hf : ∀ j s, j < K → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    (semXIR I (.loopK c n (toWord K) b) s).o.toList = s.o.toList ++ (List.range K).flatMap out ∧
      Q K (semXIR I (.loopK c n (toWord K) b) s) := by
  have e : (rd (entryK c n (toWord K) s.M) c).toNat = K := by
    rw [entryK_count hM hc hcr hn hN, toNat_toWord hK]
  have := iterL_emit I Q out hf K 0 _ (by omega) h0
  simp only [Nat.zero_add] at this
  have e2 : semXIR I (.loopK c n (toWord K) b) s =
      iterL (semXIR I b) c K ⟨entryK c n (toWord K) s.M, s.o⟩ := by
    simp only [semXIR]; rw [e]
  rw [e2]; exact this

theorem ctx_decS {M₀ : Mem} {R : ℕ} {κ : Bool} {c : ℕ} (hc4 : 4 ≤ c) (hc : c < regs) (h1 : c ≠ oR)
    (h2 : c ≠ oKF) {s : St} (h : Ctx M₀ R κ s) : Ctx M₀ R κ (decS c s) where
  inv := inv_decS h.inv hc4
  size := (size_decS c s).trans h.size
  heap y hy := (rd_decS (by omega) s).trans (h.heap y hy)
  r := (rd_decS h1 s).trans h.r
  k := by rw [rd_decS h2]; exact h.k

theorem ctx_entryK {M₀ : Mem} {R : ℕ} {κ : Bool} {c n : ℕ} {K : Word} (hc4 : 4 < c) (hc : c < regs)
    (h1 : c ≠ oR) (h2 : c ≠ oKF) {s : St} (h : Ctx M₀ R κ s) : Ctx M₀ R κ ⟨entryK c n K s.M, s.o⟩ where
  inv := inv_entryK h.inv hc4
  size := (size_entryK ..).trans h.size
  heap y hy := (entryK_frame _ (by omega) (by simp only [cTmp, regs] at *; omega)).trans (h.heap y hy)
  r := (entryK_frame _ h1 (by simp [cTmp, oR])).trans h.r
  k := by rw [show rd (entryK c n K s.M) oKF = rd s.M oKF from entryK_frame _ h2 (by simp [cTmp, oKF])]; exact h.k

/-! ## Proof helpers: one source word -/

theorem one_cOne {M : Mem} (h : Inv M) : rd M cOne = 1 := h.2 0 (by decide)

/-- **The address block reads the source word** at `addrW ap rR rU`. -/
theorem ldw_sem (I : Array Word) (ap : AP) (s : St) (hM : Inv s.M)
    (hA : regs ≤ (addrW ap (rd s.M oR) (rd s.M oU)).toNat) :
    rd (semXIR I (ldw ap) s).M oX = rd s.M (addrW ap (rd s.M oR) (rd s.M oU)).toNat ∧
      (semXIR I (ldw ap) s).o = s.o := by
  have hs := hM.1
  have h1 := one_cOne hM
  simp only [regs] at hs hA
  have hv : rd (runPrims (ldPs ap) s.M) oAd = addrW ap (rd s.M oR) (rd s.M oU) := by
    simp only [ldPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oT1, oT2, oT3, oAd, oX, oU, oR, cOne]; omega))
      only [rd_set_self, rd_set_ne, h1]
    simp only [addrW]
  have hh : ∀ a, regs ≤ a → rd (runPrims (ldPs ap) s.M) a = rd s.M a := fun a ha =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [ldPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [regs] at ha
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Prim.dst, oK, oT1, oT2, oT3, oAd] at he <;> omega) _
  constructor
  · simp only [ldw, semXIR]
    rw [rd_set_self (by rw [size_runPrims]; simp only [oX]; omega), hv, hh _ (by simp only [regs]; omega)]
  · simp only [ldw, semXIR]

theorem nw_of {P : XIR} {i : ℕ} (h : i ∉ wrL P) : ¬ Writes P i := fun hw => h (writes_wrL P i hw)

theorem loK_blk {ps : List Prim} (h : ∀ p ∈ ps, p.dst < regs) : LoK (.blk ps) := h

theorem wf_blk' {ps : List Prim} (h : ∀ p ∈ ps, 4 ≤ p.dst) : WF (.blk ps) := h

/-- The source word at the address of a register value. -/
theorem ldw_src (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {u : ℕ}
    (hu : rd s.M oU = toWord u) :
    rd (semXIR I (ldw ap) s).M oX = src M₀ ap R u ∧ (semXIR I (ldw ap) s).o = s.o := by
  have hA' : regs ≤ (addrW ap (rd s.M oR) (rd s.M oU)).toNat := by rw [hc.r, hu]; exact hA _
  obtain ⟨h1, h2⟩ := ldw_sem I ap s hc.inv hA'
  refine ⟨?_, h2⟩
  rw [h1, hc.heap _ hA', hc.r, hu]; rfl

theorem ctx_ldw (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool} {s : St} (hc : Ctx M₀ R κ s) :
    Ctx M₀ R κ (semXIR I (ldw ap) s) :=
  ctx_sem I (loK_ldw ap) (wf_ldw ap) (nw_of (by simp [wrL, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oR]))
    (nw_of (by simp [wrL, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oKF])) hc

theorem ldw_keep (I : Array Word) (ap : AP) (s : St) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ [oK, oT1, oT2, oT3, oAd, oX]) : rd (semXIR I (ldw ap) s).M r = rd s.M r :=
  frame I _ s (wf_ldw ap) hM r hr (nw_of (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    simp [wrL, ldw, ldPs, Prim.dst, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, eq_comm]))

/-- **The copy loop** emits `n` source words from `b + o` (`b` in `rb`). -/
theorem cpIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) {rb o n b : ℕ} (hrb : rb ≠ oK) (hn : n < 2 ^ 64)
    (s : St) (hc : Ctx M₀ R κ s) (hb : rd s.M rb = toWord b) :
    (semXIR I (cpIR ap rb o n) s).o.toList =
      s.o.toList ++ (List.range n).map (fun j => src M₀ ap R (b + o + j)) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  have hb1 : semXIR I (.blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)]) s =
      ⟨runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M, s.o⟩ := rfl
  have r1 : rd (runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M) oU =
      toWord (b + o) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oNp] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hb, add_toWord]
  have r2 : rd (runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M) oNp =
      toWord n := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oNp] at *; omega)) only [rd_set_self]
  have c1 := ctx_sem (M₀ := M₀) I (P := .blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)])
    (loK_blk (by simp [Prim.dst, oK, oU, oNp, regs])) (wf_blk' (by simp [Prim.dst, oK, oU, oNp]))
    (nw_of (by simp [wrL, Prim.dst, oK, oU, oNp, oR])) (nw_of (by simp [wrL, Prim.dst, oK, oU, oNp, oKF])) hc
  rw [hb1] at c1
  rw [show semXIR I (cpIR ap rb o n) s = semXIR I (.loopK oCp oNp (toWord n)
      (.seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne]))))
      ⟨runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M, s.o⟩ from rfl]
  generalize runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M = M1 at r1 r2 c1 ⊢
  have := loopK_emit I (c := oCp) (n := oNp) (K := n)
    (b := .seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne])))
    (fun j s' => Ctx M₀ R κ s' ∧ rd s'.M oU = toWord (b + o + j)) (fun j => [src M₀ ap R (b + o + j)])
    ⟨M1, s.o⟩ c1.inv (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oNp]) hn r2
    ⟨ctx_entryK (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oR]) (by simp [oCp, oKF]) c1,
      by rw [entryK_frame _ (by simp [oCp, oU]) (by simp [oU, cTmp])]; exact r1⟩
    (fun j s' _ ⟨q1, q2⟩ => by
      obtain ⟨l1, l2⟩ := ldw_src I ap hA s' q1 q2
      have k2 := ctx_ldw I ap (s := s') q1
      have u2 := ldw_keep I ap s' q1.inv (r := oU) (by simp [oU, regs]) (by simp [oU, oK, oT1, oT2, oT3, oAd, oX])
      simp only [semXIR_seq]
      generalize semXIR I (ldw ap) s' = s2 at l1 l2 k2 u2 ⊢
      have hs2 := k2.inv.1
      simp only [regs] at hs2
      refine ⟨by simp [semXIR, l2, l1], ⟨ctx_decS (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oR])
        (by simp [oCp, oKF]) ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
      · exact inv_runPrims (by simp [Prim.dst, oU]) k2.inv
      · simp [semXIR, k2.size]
      · intro y hy
        simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp only [regs, oU] at *; omega)]; exact k2.heap y hy
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp [oU, oR])]; exact k2.r
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp [oU, oKF])]; exact k2.k
      · rw [rd_decS (by simp [oCp, oU])]
        simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [oU]; omega), u2, q2, one_cOne k2.inv, add_one_toWord, Nat.add_assoc])
  rw [this.1, flatMap_single]

theorem ctx_blk {M₀ : Mem} {R : ℕ} {κ : Bool} {ps : List Prim}
    (h : ∀ p ∈ ps, 4 ≤ p.dst ∧ p.dst < regs ∧ p.dst ≠ oR ∧ p.dst ≠ oKF) {s : St} (hc : Ctx M₀ R κ s) :
    Ctx M₀ R κ ⟨runPrims ps s.M, s.o⟩ :=
  ctx_sem (P := .blk ps) #[] (fun p hp => (h p hp).2.1) (fun p hp => (h p hp).1)
    (fun ⟨p, hp, he⟩ => (h p hp).2.2.1 he) (fun ⟨p, hp, he⟩ => (h p hp).2.2.2 he) hc

theorem semXIR_blk (I : Array Word) (ps : List Prim) (s : St) : semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ :=
  rfl

theorem shr_c (x : Word) (k : ℕ) (hk : k < 64) : XOp.shr.eval x (toWord k) = x >>> k := by
  simp only [XOp.eval]; congr 1; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hk]

theorem shl_c (x : Word) (k : ℕ) (hk : k < 64) : XOp.shl.eval x (toWord k) = x <<< k := by
  simp only [XOp.eval]; congr 1; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hk]

/-! ## Proof helpers: the siblings -/

theorem keep_of (I : Array Word) {P : XIR} {s : St} (hw : WF P) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ wrL P) : rd (semXIR I P s).M r = rd s.M r :=
  frame I P s hw hM r hr (nw_of h)

theorem bit_shr_word (x : Word) (k : ℕ) (hk : k < 64) :
    (x >>> k &&& 1 = 0) ↔ x.toNat / 2 ^ k % 2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1 : Word).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp

theorem succ_divmod {p per : ℕ} (hper : 0 < per) :
    (p % per + 1 = per → (p + 1) % per = 0 ∧ (p + 1) / per = p / per + 1) ∧
    (p % per + 1 ≠ per → (p + 1) % per = p % per + 1 ∧ (p + 1) / per = p / per) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < per ∧ p = r + per * q :=
    ⟨p / per, p % per, Nat.mod_lt _ hper, by rw [Nat.add_comm]; exact (Nat.div_add_mod p per).symm⟩
  have e1 : (r + per * q) % per = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have e2 : (r + per * q) / per = q := by rw [Nat.add_mul_div_left _ _ hper, Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [e1, e2]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show r + per * q + 1 = 0 + per * (q + 1) by rw [← h]; ring, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ hper]
    simp
  · rw [show r + per * q + 1 = (r + 1) + per * q by ring, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ hper, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
    exact ⟨rfl, rfl⟩

/-- **A sibling at a real depth**: the bit `m = rm + h` of the answer at `a`, then the node's
right (bit `0`) or left half. -/
theorem sibHit_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {nh a rm h : ℕ}
    (hm : rm + h < 2 ^ 64) (h1 : rd s.M oNh = toWord nh) (h2 : rd s.M oA = toWord a)
    (h3 : rd s.M oRm = toWord rm) (h4 : rd s.M oH = toWord h) :
    (semXIR I (sibHit ap) s).o.toList = s.o.toList ++
      if (src M₀ ap R (a + (rm + h) / 64)).toNat / 2 ^ ((rm + h) % 64) % 2 = 0 then
        (List.range 4).map fun j => src M₀ ap R (nh + 6 + j)
      else (List.range 4).map fun j => src M₀ ap R (nh + 2 + j) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [sibHit, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU])
    (by simp [Prim.dst, oK, oU, oM, oR, oKF, regs]) hc
  have u1 : rd (runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU] s.M) oU =
      toWord (a + (rm + h) / 64) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oM, oRm, oH, oA] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [h2, h3, h4, add_toWord, show (6 : Word) = toWord 6 from rfl, shr_toWord hm (by norm_num), add_toWord]
    rfl
  have m1 : rd (runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU] s.M) oM =
      toWord (rm + h) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oM, oRm, oH, oA] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [h3, h4, add_toWord]
  have n1 : rd (runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU] s.M) oNh =
      toWord nh := by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oM, oK, oU, oNh])]; exact h1
  obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
  have c2 := ctx_ldw I ap c1
  have m2 := ldw_keep I ap _ c1.inv (r := oM) (by simp [oM, regs]) (by simp [oM, oK, oT1, oT2, oT3, oAd, oX])
  have n2 := ldw_keep I ap _ c1.inv (r := oNh) (by simp [oNh, regs]) (by simp [oNh, oK, oT1, oT2, oT3, oAd, oX])
  generalize semXIR I (ldw ap) ⟨runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK,
    .op .add oU oA oU] s.M, s.o⟩ = s2 at l1 l2 c2 m2 n2
  rw [m1] at m2; rw [n1] at n2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  have c3 := ctx_blk (ps := [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne]) (by simp [Prim.dst, oB2, oR, oKF, regs]) c2
  have bit : rd (runPrims [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne] s2.M) oB2 =
      (src M₀ ap R (a + (rm + h) / 64) >>> ((rm + h) % 64)) &&& 1 := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oB2, oX, oM, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, m2, one_cOne c2.inv]
    simp only [XOp.eval]; rw [toNat_toWord hm]
  have nb : rd (runPrims [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne] s2.M) oNh = toWord nh := by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oB2, oNh])]; exact n2
  rw [semXIR_ite, bit]
  have ho : (⟨runPrims [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne] s2.M, s2.o⟩ : St).o = s.o := l2
  by_cases hb : (src M₀ ap R (a + (rm + h) / 64)).toNat / 2 ^ ((rm + h) % 64) % 2 = 0
  · rw [if_pos ((bit_shr_word _ _ (Nat.mod_lt _ (by norm_num))).2 hb), if_pos hb,
      cpIR_sem I ap hA (by simp [oNh, oK]) (by norm_num) _ c3 nb, ho]
  · rw [if_neg (fun h' => hb ((bit_shr_word _ _ (Nat.mod_lt _ (by norm_num))).1 h')), if_neg hb,
      cpIR_sem I ap hA (by simp [oNh, oK]) (by norm_num) _ c3 nb, ho]

theorem wf_sibHit (ap : AP) : WF (sibHit ap) :=
  ⟨by simp +decide only [WF, Prim.dst, oM, oK, oU], wf_ldw ap, by simp +decide only [
    WF, Prim.dst, oB2], wf_cpIR .., wf_cpIR ..⟩

theorem wf_zeros4 : WF zeros4 := by simp +decide only [zeros4, WF, Prim.dst, oX, and_true]

theorem loK_sibHit (ap : AP) : LoK (sibHit ap) :=
  ⟨by simp +decide only [LoK, Prim.dst, oM, oK, oU, regs], loK_ldw ap, by simp +decide only [
    LoK, Prim.dst, oB2, regs], loK_cpIR .., loK_cpIR ..⟩

theorem loK_zeros4 : LoK zeros4 := by simp +decide only [zeros4, LoK, Prim.dst, oX, regs, and_true]

/-- The registers a depth step leaves alone. -/
theorem sibHit_wr : ∀ r ∈ [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn], r ∉ wrL (.ite oFl (sibHit ap) zeros4) := by
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [wrL, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oA, oRm, oN, oRc, oH, oNh, oM, oK, oU, oB2, oT1, oT2, oT3,
    oAd, oX, oNp, oCp, cTmp, oSh, oShn, oSp, oSn]

/-- **One depth step** emits `sibW`'s words for `(p, h)` and moves `h` and the node pointer. -/
theorem sibH_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s)
    {b o S ansW logN per sK p h : ℕ} (hm : p % per * logN + h < 2 ^ 64) (hh : h < 2 ^ 32) (hsK : sK < 2 ^ 32)
    (h1 : rd s.M oNh = toWord (b + o + S * p + 14 * h)) (h2 : rd s.M oA = toWord (b + ansW + 10 * (p / per)))
    (h3 : rd s.M oRm = toWord (p % per * logN)) (h4 : rd s.M oH = toWord h) :
    (semXIR I (sibH ap sK) s).o.toList = s.o.toList ++ sibW (src M₀ ap R) b o S ansW logN per sK p h ∧
      Ctx M₀ R κ (semXIR I (sibH ap sK) s) ∧
      rd (semXIR I (sibH ap sK) s).M oNh = toWord (b + o + S * p + 14 * (h + 1)) ∧
      rd (semXIR I (sibH ap sK) s).M oH = toWord (h + 1) ∧
      ∀ r ∈ [oA, oRm, oN, oRc, oSh, oShn, oSp, oSn], rd (semXIR I (sibH ap sK) s).M r = rd s.M r := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [sibH, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oK (toWord sK), .op .ltu oFl oH oK]) (by simp [Prim.dst, oK, oFl, oR, oKF, regs]) hc
  have f1 : rd (runPrims [.const oK (toWord sK), .op .ltu oFl oH oK] s.M) oFl = if h < sK then 1 else 0 := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oFl, oH] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [h4]
    simp only [XOp.eval]
    by_cases e : h < sK
    · rw [if_pos ((toWord_lt_toWord (by omega) (by omega)).2 e), if_pos e]
    · rw [if_neg (fun h' => e ((toWord_lt_toWord (by omega) (by omega)).1 h')), if_neg e]
  have k1 : ∀ r ∈ [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn],
      rd (runPrims [.const oK (toWord sK), .op .ltu oFl oH oK] s.M) r = rd s.M r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact rd_runPrims_of_not_writes (by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, oK, oFl, oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn]) _
  generalize runPrims [.const oK (toWord sK), .op .ltu oFl oH oK] s.M = M1 at c1 f1 k1
  have hw2 : WF (.ite oFl (sibHit ap) zeros4) := ⟨wf_sibHit ap, wf_zeros4⟩
  have c2 := ctx_sem I (P := .ite oFl (sibHit ap) zeros4) ⟨loK_sibHit ap, loK_zeros4⟩ hw2
    (nw_of (by
      simp [wrL, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oR, oM, oK, oU, oB2, oT1, oT2, oT3, oAd, oX, oNp, oCp, cTmp]))
    (nw_of (by
      simp [wrL, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oKF, oM, oK, oU, oB2, oT1, oT2, oT3, oAd, oX, oNp, oCp,
        cTmp])) c1
  have k2 : ∀ r ∈ [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn],
      rd (semXIR I (.ite oFl (sibHit ap) zeros4) ⟨M1, s.o⟩).M r = rd s.M r := fun r hr =>
    (keep_of I hw2 c1.inv (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn, regs]) (sibHit_wr r hr)).trans (k1 r hr)
  have o2 : (semXIR I (.ite oFl (sibHit ap) zeros4) ⟨M1, s.o⟩).o.toList =
      s.o.toList ++ sibW (src M₀ ap R) b o S ansW logN per sK p h := by
    rw [semXIR_ite, f1]
    unfold sibW
    by_cases hh' : h < sK
    · rw [if_pos hh', if_neg (by decide), if_pos hh']
      have := sibHit_sem I ap hA ⟨M1, s.o⟩ c1 (nh := b + o + S * p + 14 * h) (a := b + ansW + 10 * (p / per))
        (rm := p % per * logN) (h := h) hm (by rw [k1 _ (by simp)]; exact h1) (by rw [k1 _ (by simp)]; exact h2)
        (by rw [k1 _ (by simp)]; exact h3) (by rw [k1 _ (by simp)]; exact h4)
      exact this
    · rw [if_neg hh', if_pos rfl, if_neg hh']
      have hx : oX < M1.size := by
        have := c1.size; have := hc.size; simp only [oX] at *; omega
      simp [zeros4, semXIR, runPrims, Prim.run, rd_set_self hx]
  generalize semXIR I (.ite oFl (sibHit ap) zeros4) ⟨M1, s.o⟩ = s2 at c2 k2 o2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  refine ⟨o2, ctx_blk (by simp [Prim.dst, oH, oK, oNh, oR, oKF, regs]) c2, ?_, ?_, fun r hr => ?_⟩
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oH, oNh] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [k2 _ (by simp), h1, show (14 : Word) = toWord 14 from rfl, add_toWord]; congr 1
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oH, oNh] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [k2 _ (by simp), h4, one_cOne c2.inv, add_one_toWord]
  · rw [rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, oK, oH, oNh, oA, oRm, oN, oRc, oSh, oShn, oSp, oSn]), k2 r (by simp at hr ⊢; tauto)]

theorem toWord_eq_iff {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : toWord a = toWord b ↔ a = b :=
  ⟨fun h => by rw [← toNat_toWord ha, ← toNat_toWord hb, h], fun h => h ▸ rfl⟩

/-- The sibling registers of position `p`. -/
def PosR (b o S ansW logN per p : ℕ) (M : Mem) : Prop :=
  rd M oN = toWord (b + o + S * p) ∧ rd M oA = toWord (b + ansW + 10 * (p / per)) ∧
    rd M oRm = toWord (p % per * logN) ∧ rd M oRc = toWord (p % per)

/-- **One position**: its `sS` depths' sibling words, then the registers of position `p + 1`. -/
theorem sibP_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s)
    {b o S sS ansW logN per sK p : ℕ} (hp : p < 2 ^ 32) (hsS : sS < 2 ^ 32) (hl : logN < 2 ^ 32)
    (hpr : per < 2 ^ 32) (hsK : sK < 2 ^ 32) (hper : 0 < per) (hR : PosR b o S ansW logN per p s.M) :
    (semXIR I (sibP ap S sS logN per sK) s).o.toList = s.o.toList ++
      (List.range sS).flatMap (sibW (src M₀ ap R) b o S ansW logN per sK p) ∧
      Ctx M₀ R κ (semXIR I (sibP ap S sS logN per sK) s) ∧
      PosR b o S ansW logN per (p + 1) (semXIR I (sibP ap S sS logN per sK) s).M := by
  obtain ⟨r1, r2, r3, r4⟩ := hR
  have hs := hc.inv.1
  simp only [regs] at hs
  have hr : p % per < per := Nat.mod_lt _ hper
  have hml : ∀ h < 2 ^ 32, p % per * logN + h < 2 ^ 64 := fun h hh => by
    have : p % per * logN ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  simp only [sibP, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)])
    (by simp [Prim.dst, oNh, oH, oShn, oR, oKF, regs]) hc
  have v1 : rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) oNh =
      toWord (b + o + S * p + 14 * 0) ∧ rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) oH =
      toWord 0 ∧ rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) oShn = toWord sS := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oNh, oH, oShn, oN] at *; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨?_, ?_, ?_⟩ <;> simp [or_self_eval, r1, toWord]
  have k1 : ∀ r ∈ [oA, oRm, oN, oRc], rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) r =
      rd s.M r := fun r hr => rd_runPrims_of_not_writes (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [Prim.dst, oNh, oH, oShn, oA, oRm, oN, oRc]) _
  generalize runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M = M1 at c1 v1 k1
  -- the depths
  have L := loopK_emit I (c := oSh) (n := oShn) (K := sS) (b := sibH ap sK)
    (fun h s' => Ctx M₀ R κ s' ∧ rd s'.M oNh = toWord (b + o + S * p + 14 * h) ∧ rd s'.M oH = toWord h ∧
      ∀ r ∈ [oA, oRm, oN, oRc], rd s'.M r = rd s.M r)
    (sibW (src M₀ ap R) b o S ansW logN per sK p) ⟨M1, s.o⟩ c1.inv (by simp [oSh]) (by simp [oSh, regs])
    (by simp [oSh, oShn]) (by omega) v1.2.2
    ⟨ctx_entryK (by simp [oSh]) (by simp [oSh, regs]) (by simp [oSh, oR]) (by simp [oSh, oKF]) c1,
      by rw [entryK_frame _ (by simp [oSh, oNh]) (by simp [oNh, cTmp])]; exact v1.1,
      by rw [entryK_frame _ (by simp [oSh, oH]) (by simp [oH, cTmp])]; exact v1.2.1,
      fun r hr => by
        rw [entryK_frame _ ?_ ?_, k1 r hr]
        all_goals simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        all_goals rcases hr with rfl | rfl | rfl | rfl <;> simp [oSh, oA, oRm, oN, oRc, cTmp]⟩
    (fun h s' hh ⟨q1, q2, q3, q4⟩ => by
      obtain ⟨g1, g2, g3, g4, g5⟩ := sibH_sem I ap hA s' q1 (b := b) (o := o) (S := S) (ansW := ansW)
        (logN := logN) (per := per) (sK := sK) (p := p) (h := h) (hml h (by omega)) (by omega) hsK q2
        (by rw [q4 _ (by simp)]; exact r2) (by rw [q4 _ (by simp)]; exact r3) q3
      refine ⟨g1, ctx_decS (by simp [oSh]) (by simp [oSh, regs]) (by simp [oSh, oR]) (by simp [oSh, oKF]) g2,
        by rw [rd_decS (by simp [oSh, oNh])]; exact g3, by rw [rd_decS (by simp [oSh, oH])]; exact g4,
        fun r hr => ?_⟩
      have hr' : r ≠ oSh := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp [oSh, oA, oRm, oN, oRc]
      have hr2 : r ∈ [oA, oRm, oN, oRc, oSh, oShn, oSp, oSn] := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr ⊢
        rcases hr with h | h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inl h)))
      rw [rd_decS (Ne.symm hr'), g5 r hr2, q4 r hr])
  obtain ⟨L1, L2, -, -, L5⟩ := L
  generalize semXIR I (.loopK oSh oShn (toWord sS) (sibH ap sK)) ⟨M1, s.o⟩ = s3 at L1 L2 L5
  have hs3 := L2.inv.1
  simp only [regs] at hs3
  -- the step to position `p + 1`
  have c4 := ctx_blk (ps := [.const oK (toWord S), .op .add oN oN oK, .const oK (toWord logN), .op .add oRm oRm oK,
      .op .add oRc oRc cOne, .const oK (toWord per), .op .eq oFl oRc oK])
    (by simp [Prim.dst, oK, oN, oRm, oRc, oFl, oR, oKF, regs]) L2
  have w4 : ∀ r ∈ [oN, oRm, oRc, oFl, oA], rd (runPrims [.const oK (toWord S), .op .add oN oN oK,
      .const oK (toWord logN), .op .add oRm oRm oK, .op .add oRc oRc cOne, .const oK (toWord per),
      .op .eq oFl oRc oK] s3.M) r =
      if r = oN then toWord (b + o + S * p + S) else if r = oRm then toWord (p % per * logN + logN)
      else if r = oRc then toWord (p % per + 1)
      else if r = oFl then (if p % per + 1 = per then 1 else 0) else toWord (b + ansW + 10 * (p / per)) := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    simp only [runPrims, List.foldl, Prim.run]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (simp only [size_set, oK, oN, oRm, oRc, oFl, oA, cOne] at *; omega)) only
      [rd_set_self, rd_set_ne, if_true, if_false, show oRm ≠ oN by decide, show oRc ≠ oN by decide,
        show oRc ≠ oRm by decide, show oFl ≠ oN by decide, show oFl ≠ oRm by decide, show oFl ≠ oRc by decide,
        show oA ≠ oN by decide, show oA ≠ oRm by decide, show oA ≠ oRc by decide, show oA ≠ oFl by decide]
    · rw [L5 _ (by simp), r1, add_toWord]
    · rw [L5 _ (by simp), r3, add_toWord]
    · rw [L5 _ (by simp), r4, one_cOne L2.inv, add_one_toWord]
    · rw [L5 _ (by simp), r4, one_cOne L2.inv, add_one_toWord]
      simp only [XOp.eval]
      by_cases e : p % per + 1 = per
      · rw [if_pos ((toWord_eq_iff (by omega) (by omega)).2 e), if_pos e]
      · rw [if_neg (fun h' => e ((toWord_eq_iff (by omega) (by omega)).1 h')), if_neg e]
    · rw [L5 _ (by simp), r2]
  generalize runPrims [.const oK (toWord S), .op .add oN oN oK, .const oK (toWord logN), .op .add oRm oRm oK,
    .op .add oRc oRc cOne, .const oK (toWord per), .op .eq oFl oRc oK] s3.M = M4 at c4 w4
  have hs4 := c4.inv.1
  simp only [regs] at hs4
  obtain ⟨d1, d2⟩ := succ_divmod (p := p) hper
  rw [semXIR_ite, w4 _ (by simp)]
  simp only [show oFl ≠ oN by decide, show oFl ≠ oRm by decide, show oFl ≠ oRc by decide, if_false, if_true]
  by_cases e : p % per + 1 = per
  · rw [if_pos e, if_neg (by decide), semXIR_blk]
    obtain ⟨e1, e2⟩ := d1 e
    refine ⟨L1, ctx_blk (by simp [Prim.dst, oK, oRm, oRc, oA, oR, oKF, regs]) c4, ?_, ?_, ?_, ?_⟩ <;>
    simp only [runPrims, List.foldl, Prim.run] <;>
    simp (disch := (simp only [size_set, oK, oN, oRm, oRc, oFl, oA] at *; omega)) only [rd_set_self, rd_set_ne]
    · rw [w4 _ (by simp), if_pos rfl]; congr 1; ring
    · rw [w4 _ (by simp)]; simp only [show oA ≠ oN by decide, show oA ≠ oRm by decide, show oA ≠ oRc by decide,
        show oA ≠ oFl by decide, if_false]
      rw [show (10 : Word) = toWord 10 from rfl, add_toWord, e2]; congr 1
    · rw [e1, Nat.zero_mul]; rfl
    · rw [e1]; rfl
  · rw [if_neg e, if_pos rfl, semXIR_blk]
    obtain ⟨e1, e2⟩ := d2 e
    refine ⟨L1, ctx_blk (by simp) c4, ?_, ?_, ?_, ?_⟩ <;> simp only [runPrims, List.foldl]
    · rw [w4 _ (by simp), if_pos rfl]; congr 1; ring
    · rw [w4 _ (by simp)]; simp only [show oA ≠ oN by decide, show oA ≠ oRm by decide, show oA ≠ oRc by decide,
        show oA ≠ oFl by decide, if_false]
      rw [e2]
    · rw [w4 _ (by simp)]; simp only [show oRm ≠ oN by decide, if_false, if_true, e1]; congr 1; ring
    · rw [w4 _ (by simp)]; simp only [show oRc ≠ oN by decide, show oRc ≠ oRm by decide, if_false, if_true, e1]

/-- **One level's siblings** (`Seg.sib`): `sibW`'s words for every position and depth. -/
theorem sibIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s)
    {rb b o S t sS ansW logN per sK : ℕ} (hrb : rb ≠ oK ∧ rb ≠ oN) (ht : t < 2 ^ 32) (hsS : sS < 2 ^ 32)
    (hl : logN < 2 ^ 32) (hpr : per < 2 ^ 32) (hsK : sK < 2 ^ 32) (hper : 0 < per) (hb : rd s.M rb = toWord b) :
    (semXIR I (sibIR ap rb o S t sS ansW logN per sK) s).o.toList = s.o.toList ++
      (List.range t).flatMap fun p => (List.range sS).flatMap (sibW (src M₀ ap R) b o S ansW logN per sK p) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [sibIR, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW), .op .add oA rb oK,
      .const oRm 0, .const oRc 0, .const oSn (toWord t)]) (by simp [Prim.dst, oK, oN, oA, oRm, oRc, oSn, oR, oKF, regs]) hc
  have v1 : PosR b o S ansW logN per 0 (runPrims [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW),
      .op .add oA rb oK, .const oRm 0, .const oRc 0, .const oSn (toWord t)] s.M) ∧
      rd (runPrims [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW),
      .op .add oA rb oK, .const oRm 0, .const oRc 0, .const oSn (toWord t)] s.M) oSn = toWord t := by
    simp only [PosR, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oN, oA, oRm, oRc, oSn] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hb, add_toWord, add_toWord]
    simp [toWord]
  generalize runPrims [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW), .op .add oA rb oK,
    .const oRm 0, .const oRc 0, .const oSn (toWord t)] s.M = M1 at c1 v1
  have L := loopK_emit I (c := oSp) (n := oSn) (K := t) (b := sibP ap S sS logN per sK)
    (fun p s' => Ctx M₀ R κ s' ∧ PosR b o S ansW logN per p s'.M)
    (fun p => (List.range sS).flatMap (sibW (src M₀ ap R) b o S ansW logN per sK p)) ⟨M1, s.o⟩ c1.inv
    (by simp [oSp]) (by simp [oSp, regs]) (by simp [oSp, oSn]) (by omega) v1.2
    ⟨ctx_entryK (by simp [oSp]) (by simp [oSp, regs]) (by simp [oSp, oR]) (by simp [oSp, oKF]) c1, by
      obtain ⟨a1, a2, a3, a4⟩ := v1.1
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [entryK_frame _ (by simp [oSp, oN]) (by simp [oN, cTmp])]; exact a1)
        | (rw [entryK_frame _ (by simp [oSp, oA]) (by simp [oA, cTmp])]; exact a2)
        | (rw [entryK_frame _ (by simp [oSp, oRm]) (by simp [oRm, cTmp])]; exact a3)
        | (rw [entryK_frame _ (by simp [oSp, oRc]) (by simp [oRc, cTmp])]; exact a4)⟩
    (fun p s' hp ⟨q1, q2⟩ => by
      obtain ⟨g1, g2, g3⟩ := sibP_sem I ap hA s' q1 (sK := sK) (by omega) hsS hl hpr hsK hper q2
      obtain ⟨a1, a2, a3, a4⟩ := g3
      exact ⟨g1, ctx_decS (by simp [oSp]) (by simp [oSp, regs]) (by simp [oSp, oR]) (by simp [oSp, oKF]) g2,
        by rw [rd_decS (by simp [oSp, oN])]; exact a1, by rw [rd_decS (by simp [oSp, oA])]; exact a2,
        by rw [rd_decS (by simp [oSp, oRm])]; exact a3, by rw [rd_decS (by simp [oSp, oRc])]; exact a4⟩)
  exact L.1

/-- **A compiled segment emits its words** (`segOut` over the source `src M₀ ap R`). -/
theorem segIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) :
    ∀ (seg : Seg) (d b : ℕ) (s : St), okSeg seg = true → depthSeg seg + d ≤ 9 → Ctx M₀ R κ s →
      rd s.M (oBd d) = toWord b →
      (semXIR I (segIR ap d seg) s).o.toList = s.o.toList ++ segOut (src M₀ ap R) κ b seg
  | .nil, _, _, s, _, _, _, _ => by simp [segIR, segOut, semXIR_blk]
  | .cat x y, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true] at hok
    simp only [depthSeg] at hd
    have h1 := segIR_sem I ap hA x d b s hok.1 (by omega) hc hb
    have c1 := ctx_segIR I ap x d (by omega) hc
    have k1 : rd (semXIR I (segIR ap d x) s).M (oBd d) = toWord b :=
      (frame I _ s (wf_segIR ap x d (by omega)) hc.inv _ (by simp only [oBd, regs]; omega)
        (noW_segIR ap x d _ (.inr (.inr (.inr rfl))))).trans hb
    rw [segIR, semXIR_seq, segIR_sem I ap hA y d b _ hok.2 (by omega) c1 k1, h1, segOut, List.append_assoc]
  | .kite x y, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true] at hok
    simp only [depthSeg] at hd
    rw [segIR, semXIR_ite, segOut]
    cases κ
    · rw [if_pos (hc.k.2 rfl), if_neg (by decide)]
      exact segIR_sem I ap hA y d b s hok.2 (by omega) hc hb
    · rw [if_neg (fun h => absurd (hc.k.1 h) (by decide)), if_pos rfl]
      exact segIR_sem I ap hA x d b s hok.1 (by omega) hc hb
  | .wd x, _, _, s, _, _, hc, _ => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp [segIR, segOut, semXIR, runPrims, Prim.run, rd_set_self (show oX < s.M.size by simp only [oX]; omega)]
  | .cp o n, d, b, s, hok, _, hc, hb => by
    simp only [okSeg, decide_eq_true_eq] at hok
    have := cpIR_sem I ap hA (rb := oBd d) (o := o) (n := n) (b := b) (by simp [oBd, oK]; omega) (by omega) s hc hb
    rw [segIR, segOut]; exact this
  | .sib o S t sS ansW logN per sK, d, b, s, hok, _, hc, hb => by
    simp only [okSeg, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    rw [segIR, segOut]
    exact sibIR_sem I ap hA s hc (by simp only [oBd, oK, oN]; omega) h1 h2 h3 h4 h5 h6 hb
  | .shw o, d, b, s, _, _, hc, hb => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp only [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oU (oBd d) oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M) oU = toWord (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU, oBd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    have u2 := ldw_keep I ap _ c1.inv (r := oU) (by simp [oU, regs]) (by simp [oU, oK, oT1, oT2, oT3, oAd, oX])
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M, s.o⟩ = s2 at l1 l2 c2 u2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    have c3 := ctx_blk (ps := [.op .or oY oX oX, .op .add oU oU cOne]) (by simp [Prim.dst, oY, oU, oR, oKF, regs]) c2
    have u3 : rd (runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M) oU = toWord (b + o + 1) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [u2, u1, one_cOne c2.inv, add_one_toWord]
    have y3 : rd (runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M) oY = src M₀ ap R (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [l1, or_self_eval]
    obtain ⟨l4, l5⟩ := ldw_src I ap hA _ c3 u3
    have y4 := ldw_keep I ap _ c3.inv (r := oY) (by simp [oY, regs]) (by simp [oY, oK, oT1, oT2, oT3, oAd, oX])
    generalize h4 : semXIR I (ldw ap) ⟨runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M, s2.o⟩ = s4 at l4 l5 y4
    have c4 : Ctx M₀ R κ s4 := by rw [← h4]; exact ctx_ldw I ap c3
    have hs4 := c4.inv.1
    simp only [regs] at hs4
    simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, l5, l2, segOut]
    simp (disch := (simp only [size_set, oY, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l4, y4, y3, shl_c _ _ (by norm_num), shr_c _ _ (by norm_num)]
    rfl
  | .sh8 o, d, b, s, _, _, hc, hb => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp only [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oU (oBd d) oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M) oU = toWord (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU, oBd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M, s.o⟩ = s2 at l1 l2 c2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, l2, segOut]
    simp (disch := (simp only [size_set, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, shr_c _ _ (by norm_num)]
  | .rep c s' x, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [depthSeg] at hd
    have hs := hc.inv.1
    simp only [regs] at hs
    rw [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)])
      (by simp [Prim.dst, oBd, oNd, oR, oKF, regs]; omega) hc
    have b1 : rd (runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M)
        (oBd (d + 1)) = toWord b := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oNd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [or_self_eval, hb]
    have n1 : rd (runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M)
        (oNd d) = toWord c := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oNd] at *; omega)) only [rd_set_self, rd_set_ne]
    generalize runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M = M1 at c1 b1 n1 ⊢
    have := loopK_emit I (c := oCd d) (n := oNd d) (K := c)
      (b := .seq (segIR ap (d + 1) x) (.blk [.const oK (toWord s'), .op .add (oBd (d + 1)) (oBd (d + 1)) oK]))
      (fun j s'' => Ctx M₀ R κ s'' ∧ rd s''.M (oBd (d + 1)) = toWord (b + s' * j))
      (fun j => segOut (src M₀ ap R) κ (b + s' * j) x) ⟨M1, s.o⟩ c1.inv
      (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega) (by simp only [oCd, oNd]; omega)
      (by omega) n1
      ⟨ctx_entryK (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega) (by simp only [oCd, oR]; omega)
        (by simp only [oCd, oKF]; omega) c1,
        by rw [entryK_frame _ (by simp only [oCd, oBd]; omega) (by simp only [oBd, cTmp]; omega)]; simpa using b1⟩
      (fun j s'' _ ⟨q1, q2⟩ => by
        have h1 := segIR_sem I ap hA x (d + 1) (b + s' * j) s'' hok.2 (by omega) q1 q2
        have c2 := ctx_segIR I ap x (d + 1) (by omega) q1
        have k2 : rd (semXIR I (segIR ap (d + 1) x) s'').M (oBd (d + 1)) = toWord (b + s' * j) :=
          (frame I _ s'' (wf_segIR ap x (d + 1) (by omega)) q1.inv _ (by simp only [oBd, regs]; omega)
            (noW_segIR ap x (d + 1) _ (.inr (.inr (.inr rfl))))).trans q2
        simp only [semXIR_seq, semXIR_blk]
        generalize semXIR I (segIR ap (d + 1) x) s'' = s3 at h1 c2 k2 ⊢
        have hs3 := c2.inv.1
        simp only [regs] at hs3
        refine ⟨h1, ctx_decS (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega)
          (by simp only [oCd, oR]; omega) (by simp only [oCd, oKF]; omega)
          (ctx_blk (by simp [Prim.dst, oK, oBd, oR, oKF, regs]; omega) c2), ?_⟩
        rw [rd_decS (by simp only [oCd, oBd]; omega)]
        simp only [runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, oBd, oK] at *; omega)) only [rd_set_self, rd_set_ne]
        rw [k2, add_toWord]; congr 1; ring)
    rw [this.1, segOut]

end FR.X

end G6_FRXOut
