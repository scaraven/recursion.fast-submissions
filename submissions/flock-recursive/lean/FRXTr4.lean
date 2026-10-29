-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5; stage S-H4, pass 9, item 1:
-- the traces' output words). 3.x analogue: `FRNodeReadW.readItems_words`, `FRNodeReadS.logWords_trSeg`
-- (over one slot's stream words and 3.x's `items`); here over any word list and `itemsOf S`.
import FRXOut
import FRXSig4W

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
