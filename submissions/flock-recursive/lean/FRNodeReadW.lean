-- New for `flock-recursive` (BLUEPRINT A.5, §6.2 step 5, §6.5 `output_spec`; stage S-H2,
-- track L-ext, S-H2k).
import FRNodeRead

/-!
# `reassemble` field by field

`FRFormat.reassemble` walks the phase table with a state of 18 growing fields. For the
extractor's output program the proof's bytes are wanted in the serialised order, field by field.
**`reassemble_eq`**: the bytes of `reassemble tr` are, for `f = 0 … 17` in turn, the
contributions to field `f` of the phases in order (`ctbs`): each phase's contribution `ctb` is
read off its items at the item index the walk has reached (`ix`), with the position answers of
the last `P2` phase (`ans`).
-/

namespace FR.Read

open RecursionFast

/-! ## Specification: a phase's contribution to a field -/

/-- The bytes of a byte array. -/
abbrev bl (b : ByteArray) : List UInt8 := b.data.toList

/-- **Phase `sh`'s bytes for field `f`**, its items starting at item `ix`, with the position
answers `ans` (A.5; `rsPhase` field by field). -/
def ctb (k : Kind) (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest) :
    Shape → ℕ → List UInt8
  | .seed, f => if f = fHdr then bl (qBytes a ix 71 48) else []
  | .absorb g len, f => if f = g then bl (qBytes a ix 40 len) else []
  | .squeezes _ _, _ => []
  | .uni g, f => if f = g then bl (qBytes a ix 40 uniBytes) else []
  | .rounds g n _ inK _, f =>
    if f = g then (List.range n).flatMap fun j => bl (qBytes a (ix + 2 * j) 40 (roundBytes inK))
    else []
  | .queries i, f =>
    if f = fCols then (List.range (lvlStar i).t).flatMap fun p =>
      bl (qBytes a (ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i))
    else if f = fSibs then (List.range (lvlStar i).t).flatMap fun p =>
      (List.range (lvlStar i).sib).flatMap fun h =>
        bl (sibling k i h (posOf k i ans p)
          ((a.getD (ix + (1 + (lvlStar i).sib) * p + 1 + h) (ByteArray.empty, 0)).1))
    else []

/-- The position answers after phase `sh` (a `P2` phase's squeeze answers, else unchanged). -/
def ansOf (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest) : Shape → List Digest
  | .squeezes n (.pos _) => (List.range n).map fun j => (a.getD (ix + j) (ByteArray.empty, 0)).2
  | _ => ans

/-- **The phases' bytes for field `f`**, from item `ix` with the answers `ans`. -/
def ctbs (k : Kind) (a : Array (ByteArray × Digest)) : ℕ → List Digest → List Shape → ℕ → List UInt8
  | _, _, [], _ => []
  | ix, ans, sh :: shs, f =>
    ctb k a ix ans sh f ++ ctbs k a (ix + sh.items.length) (ansOf a ix ans sh) shs f

/-- The fields a phase writes are fields of the proof. -/
def FieldsOk : Shape → Prop
  | .absorb g _ => g < nFields
  | .uni g => g < nFields
  | .rounds g _ _ _ _ => g < nFields
  | _ => True

/-! ## Proof helpers: the walk's state -/

/-- Field `f`'s bytes so far. -/
def cont (s : RSt) (f : ℕ) : List UInt8 := bl (s.out.getD f ByteArray.empty)

theorem cont_put (s : RSt) {g : ℕ} (hg : g < s.out.size) (b : ByteArray) (f : ℕ) :
    cont (s.put g b) f = cont s f ++ if f = g then bl b else [] := by
  simp only [cont, RSt.put, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hf : f = g
  · subst hf; simp [hg]
  · simp [Ne.symm hf, hf]

/-- A walk step that appends `C ix ans p f` to every field `f` and keeps the rest. -/
def Appends (body : RSt → ℕ → RSt) (C : ℕ → List Digest → ℕ → ℕ → List UInt8) : Prop :=
  ∀ s p, s.out.size = nFields → (body s p).out.size = nFields ∧ (body s p).ix = s.ix ∧
    (body s p).ans = s.ans ∧ ∀ f, cont (body s p) f = cont s f ++ C s.ix s.ans p f

theorem foldl_appends {body : RSt → ℕ → RSt} {C : ℕ → List Digest → ℕ → ℕ → List UInt8}
    (h : Appends body C) : ∀ (l : List ℕ) (s : RSt), s.out.size = nFields →
    (l.foldl body s).out.size = nFields ∧ (l.foldl body s).ix = s.ix ∧
      (l.foldl body s).ans = s.ans ∧
      ∀ f, cont (l.foldl body s) f = cont s f ++ l.flatMap fun p => C s.ix s.ans p f
  | [], s, hs => ⟨hs, rfl, rfl, fun f => by simp⟩
  | p :: l, s, hs => by
    obtain ⟨h1, h2, h3, h4⟩ := h s p hs
    obtain ⟨g1, g2, g3, g4⟩ := foldl_appends h l (body s p) h1
    refine ⟨g1, g2.trans h2, g3.trans h3, fun f => ?_⟩
    rw [List.foldl_cons, g4, h4, h2, h3, List.flatMap_cons, List.append_assoc]

theorem appends_put (g : ℕ) (hg : g < nFields) (Q : ℕ → List Digest → ℕ → ByteArray) :
    Appends (fun s p => s.put g (Q s.ix s.ans p)) fun ix ans p f => if f = g then bl (Q ix ans p) else [] :=
  fun s p hs => ⟨by simp [RSt.put, hs], rfl, rfl, fun f => cont_put s (hs ▸ hg) _ f⟩

theorem flatMap_ite {α : Type} (l : List α) (c : Prop) [Decidable c] (F : α → List UInt8) :
    (l.flatMap fun x => if c then F x else []) = if c then l.flatMap F else [] := by
  split_ifs <;> simp

/-- **One phase of the walk** appends `ctb` to every field. -/
theorem rsPhase_spec (k : Kind) (a : Array (ByteArray × Digest)) (s : RSt) (sh : Shape)
    (hs : s.out.size = nFields) (hok : FieldsOk sh) :
    (rsPhase k a s sh).out.size = nFields ∧ (rsPhase k a s sh).ix = s.ix + sh.items.length ∧
      (rsPhase k a s sh).ans = ansOf a s.ix s.ans sh ∧
      ∀ f, cont (rsPhase k a s sh) f = cont s f ++ ctb k a s.ix s.ans sh f := by
  have hF : fHdr < s.out.size := by rw [hs]; decide
  cases sh with
  | seed => exact ⟨by simp [rsPhase, RSt.put, hs], by simp [rsPhase, RSt.put, Shape.items],
      rfl, fun f => cont_put s hF _ f⟩
  | absorb g len => exact ⟨by simp [rsPhase, RSt.put, hs], by simp [rsPhase, RSt.put, Shape.items],
      rfl, fun f => cont_put s (hs ▸ hok) _ f⟩
  | squeezes n ch =>
    refine ⟨by cases ch <;> simp [rsPhase, hs], by cases ch <;> simp [rsPhase, Shape.items],
      by cases ch <;> simp [rsPhase, ansOf], fun f => by cases ch <;> simp [rsPhase, cont, ctb]⟩
  | uni g => exact ⟨by simp [rsPhase, RSt.put, hs], by simp [rsPhase, RSt.put, Shape.items],
      rfl, fun f => cont_put s (hs ▸ hok) _ f⟩
  | rounds g n deg inK real =>
    obtain ⟨g1, g2, g3, g4⟩ := foldl_appends (appends_put g hok
      fun ix _ j => qBytes a (ix + 2 * j) 40 (roundBytes inK)) (List.range n) s hs
    refine ⟨g1, by simp [rsPhase, Shape.items]; omega, g3, fun f => ?_⟩
    simp only [rsPhase, cont] at g4 ⊢
    rw [g4, ctb, flatMap_ite]
  | queries i =>
    -- the inner walk over the Merkle-node queries of one position
    have hin : ∀ (j base : ℕ), Appends (fun s h => s.put fSibs (sibling k i h j
        ((a.getD (base + 1 + h) (ByteArray.empty, 0)).1))) fun _ _ h f =>
          if f = fSibs then bl (sibling k i h j ((a.getD (base + 1 + h) (ByteArray.empty, 0)).1))
          else [] := fun j base =>
      appends_put fSibs (by decide) fun _ _ h => sibling k i h j ((a.getD (base + 1 + h) (ByteArray.empty, 0)).1)
    have hout : Appends (fun s p =>
        (List.range (lvlStar i).sib).foldl (fun s' h => s'.put fSibs (sibling k i h
          (posOf k i s.ans p) ((a.getD (s.ix + (1 + (lvlStar i).sib) * p + 1 + h)
            (ByteArray.empty, 0)).1)))
          (s.put fCols (qBytes a (s.ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i))))
        fun ix ans p f =>
          (if f = fCols then bl (qBytes a (ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i)) else []) ++
          (List.range (lvlStar i).sib).flatMap fun h =>
            if f = fSibs then bl (sibling k i h (posOf k i ans p)
              ((a.getD (ix + (1 + (lvlStar i).sib) * p + 1 + h) (ByteArray.empty, 0)).1)) else [] := by
      intro s p hs
      obtain ⟨h1, h2, h3, h4⟩ := appends_put fCols (by decide)
        (fun ix _ p => qBytes a (ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i)) s p hs
      obtain ⟨g1, g2, g3, g4⟩ := foldl_appends (hin (posOf k i s.ans p)
        (s.ix + (1 + (lvlStar i).sib) * p)) (List.range (lvlStar i).sib) _ h1
      refine ⟨g1, g2.trans h2, g3.trans h3, fun f => ?_⟩
      rw [g4, h4, List.append_assoc]
    obtain ⟨g1, g2, g3, g4⟩ := foldl_appends hout (List.range (lvlStar i).t) s hs
    refine ⟨g1, by simp [rsPhase, Shape.items, posItems, Nat.mul_comm]; left; omega, g3, fun f => ?_⟩
    simp only [rsPhase, cont] at g4 ⊢
    rw [g4, ctb]
    congr 1
    by_cases hc : f = fCols
    · subst hc
      have e : ∀ l : List ℕ, l.flatMap (fun _ => ([] : List UInt8)) = [] := fun l => by
        induction l <;> simp_all
      simp [fCols, fSibs, e]
    · by_cases hd : f = fSibs
      · subst hd; simp [fCols, fSibs]
      · simp [hc, hd]

/-- **The walk over shapes** appends `ctbs` to every field. -/
theorem foldl_rsPhase (k : Kind) (a : Array (ByteArray × Digest)) : ∀ (shs : List Shape) (s : RSt),
    s.out.size = nFields → (∀ sh ∈ shs, FieldsOk sh) →
    (shs.foldl (rsPhase k a) s).out.size = nFields ∧
      ∀ f, cont (shs.foldl (rsPhase k a) s) f = cont s f ++ ctbs k a s.ix s.ans shs f
  | [], s, hs, _ => ⟨hs, fun f => by simp [ctbs]⟩
  | sh :: shs, s, hs, hok => by
    obtain ⟨h1, h2, h3, h4⟩ := rsPhase_spec k a s sh hs (hok sh (by simp))
    obtain ⟨g1, g4⟩ := foldl_rsPhase k a shs _ h1 fun x hx => hok x (by simp [hx])
    refine ⟨g1, fun f => ?_⟩
    rw [List.foldl_cons, g4, h4, h2, h3, ctbs, List.append_assoc]

/-- The field a phase names (`0` for the others). -/
def fieldOf : Shape → ℕ
  | .absorb g _ => g
  | .uni g => g
  | .rounds g _ _ _ _ => g
  | _ => 0

theorem phases_fieldsOk : ∀ sh ∈ phases.map Phase.shape, FieldsOk sh := by
  have h : ((phases.map Phase.shape).map fieldOf).all (· < nFields) = true := by decide +kernel
  intro sh hsh
  have := of_decide_eq_true (List.all_eq_true.1 h (fieldOf sh) (List.mem_map_of_mem hsh))
  clear h hsh
  cases sh <;> first | exact this | trivial

theorem flatMap_getD_range (l : List ByteArray) :
    (l.flatMap bl) = (List.range l.length).flatMap fun f => bl (l.getD f ByteArray.empty) := by
  conv_lhs => rw [show l = (List.range l.length).map (fun f => l.getD f ByteArray.empty) from
    List.ext_getElem (by simp) fun i h1 h2 => by simp [List.getElem?_eq_getElem h1]]
  rw [List.flatMap_map]

/-! ## Load-bearing lemma -/

/-- **`reassemble` field by field** (A.5): its bytes are, for each field `f < 18` in order, the
phases' contributions to `f` (`ctbs` from item `0`, no answers yet). -/
theorem reassemble_eq (tr : Trace) :
    bl (reassemble tr) = (List.range nFields).flatMap
      (ctbs (traceKind tr.toArray) tr.toArray 0 [] (phases.map Phase.shape)) := by
  have hs : (⟨Array.replicate nFields ByteArray.empty, 0, []⟩ : RSt).out.size = nFields := by simp
  have e : reassemble tr = serialise ((phases.map Phase.shape).foldl
      (rsPhase (traceKind tr.toArray) tr.toArray) ⟨Array.replicate nFields ByteArray.empty, 0, []⟩).out.toList := by
    rw [List.foldl_map]; rfl
  obtain ⟨g1, g4⟩ := foldl_rsPhase (traceKind tr.toArray) tr.toArray (phases.map Phase.shape) _ hs
    phases_fieldsOk
  rw [e]
  generalize (phases.map Phase.shape).foldl (rsPhase (traceKind tr.toArray) tr.toArray)
    ⟨Array.replicate nFields ByteArray.empty, 0, []⟩ = s at g1 g4
  have hser : bl (serialise s.out.toList) = s.out.toList.flatMap bl := by simp [serialise, bl]
  rw [hser, flatMap_getD_range, Array.length_toList, g1]
  refine List.flatMap_congr fun f hf => ?_
  have h4 := g4 f
  have h0 : cont ⟨Array.replicate nFields ByteArray.empty, 0, []⟩ f = [] := by
    simp only [cont, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split_ifs <;> rfl
  rw [h0, List.nil_append] at h4
  rw [← h4, cont, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-! ## The trace's entries on the stream -/

theorem readItems_getElem (B : List UInt8) : ∀ (its : List Item) (o j : ℕ) (hj : j < its.length),
    (readItems B o its)[j]'(by rw [readItems_length]; exact hj) =
      entryAt B (o + ((its.take j).map Item.slen).sum) its[j]
  | [], _, _, hj => absurd hj (by simp)
  | it :: its, o, 0, _ => by simp [readItems]
  | it :: its, o, j + 1, hj => by
    simp only [readItems, List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [readItems_getElem B its _ j (by simpa using hj), Nat.add_assoc]

/-- **Entry `j` of slot `σ`'s trace** is item `j` read at its stream offset `streamOff j`. -/
theorem readTrace_getD (w : ℕ → F) (σ j : ℕ) (hj : j < items.length) :
    (readTrace w σ).toArray.getD j (ByteArray.empty, 0) = entryAt (stream w σ) (streamOff j) items[j] := by
  have hl : j < (readTrace w σ).length := by rw [readTrace, readItems_length]; exact hj
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hl,
    Option.getD_some]
  show (readItems (stream w σ) 1 items)[j]'(by rw [readItems_length]; exact hj) = _
  rw [readItems_getElem _ _ _ _ hj]; rfl

/-- **A query slice is a stream slice**: bytes `[off, off + n)` of item `j`'s query are stream
bytes `[streamOff j + 8 + off, … + n)` (inside the query). -/
theorem qBytes_readTrace (w : ℕ → F) (σ j off n : ℕ) (hj : j < items.length)
    (hn : off + n ≤ items[j].qlen) :
    bl (qBytes (readTrace w σ).toArray j off n) = ((stream w σ).drop (streamOff j + 8 + off)).take n := by
  rw [qBytes, readTrace_getD w σ j hj, entryAt, bl, toList_extract]
  simp only [List.toList_toArray, Nat.add_sub_cancel_left, List.drop_take, List.take_take,
    List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

/-! ## Words -/

theorem wordsBytes_drop : ∀ (W : List Word) (u : ℕ), (wordsBytes W).drop (8 * u) = wordsBytes (W.drop u)
  | [], _ => by simp [wordsBytes]
  | _ :: _, 0 => rfl
  | x :: W, u + 1 => by
    rw [show wordsBytes (x :: W) = wordBytes x ++ wordsBytes W from rfl, Nat.mul_succ,
      Nat.add_comm, ← List.drop_drop, List.drop_left' (wordBytes_length x), List.drop_succ_cons,
      wordsBytes_drop W u]

theorem wordsBytes_take : ∀ (W : List Word) (m : ℕ), (wordsBytes W).take (8 * m) = wordsBytes (W.take m)
  | [], _ => by simp [wordsBytes]
  | _ :: _, 0 => by simp [wordsBytes]
  | x :: W, m + 1 => by
    rw [show wordsBytes (x :: W) = wordBytes x ++ wordsBytes W from rfl, Nat.mul_succ,
      Nat.add_comm, List.take_append, wordBytes_length, List.take_of_length_le (by simp [wordBytes_length]),
      Nat.add_sub_cancel_left, wordsBytes_take W m, List.take_succ_cons]
    rfl

/-- **An aligned stream slice is a slice of the stream's words.** -/
theorem stream_slice (w : ℕ → F) (σ u m : ℕ) :
    ((stream w σ).drop (8 * u)).take (8 * m) = wordsBytes (((streamWords w σ).drop u).take m) := by
  rw [stream, wordsBytes_drop, wordsBytes_take]


/-- A trace entry's output words (`logWords`' per-entry part). -/
def entryW (e : ByteArray × Digest) : List Word := bytesWords e.1.data.toList ++ packBytes e.2.toList

/-- **The output words of aligned items** from stream word `u` on: per item its length word,
then its query's and answer's words (`qlen/8 + 4` stream words after the length word). -/
def trW (W : List Word) : ℕ → List Item → List Word
  | _, [] => []
  | u, it :: its => (toWord it.qlen :: (W.drop (u + 1)).take (it.qlen / 8 + 4)) ++
      trW W (u + it.slen / 8) its

theorem digest_toList (B : List UInt8) (o : ℕ) (h : o + 32 ≤ B.length) :
    (Vector.ofFn fun i : Fin 32 => B.getD (o + i) 0).toList = (B.drop o).take 32 := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- **An aligned item's output words** are its length word and stream words. -/
theorem entryW_aligned (w : ℕ → F) (σ o : ℕ) (it : Item) (ho : o % 8 = 0) (hq : it.qlen % 8 = 0)
    (hb : o + it.slen ≤ streamBytes) :
    entryW (entryAt (stream w σ) o it) =
      toWord it.qlen :: ((streamWords w σ).drop (o / 8 + 1)).take (it.qlen / 8 + 4) := by
  have hB : (stream w σ).length = 1481344 := (stream_length w σ).trans streamBytes_eq
  have hW : (streamWords w σ).length = 185168 := streamWords_length w σ
  rw [streamBytes_eq] at hb
  simp only [Item.slen] at hb
  have e1 : ((stream w σ).drop (o + 8)).take it.qlen =
      wordsBytes (((streamWords w σ).drop (o / 8 + 1)).take (it.qlen / 8)) := by
    rw [← stream_slice, show 8 * (o / 8 + 1) = o + 8 by omega, show 8 * (it.qlen / 8) = it.qlen by omega]
  have e2 : (Vector.ofFn fun i : Fin 32 => (stream w σ).getD (o + 8 + it.qlen + i) 0).toList =
      wordsBytes (((streamWords w σ).drop (o / 8 + 1 + it.qlen / 8)).take 4) := by
    rw [digest_toList _ _ (by omega), ← stream_slice,
      show 8 * (o / 8 + 1 + it.qlen / 8) = o + 8 + it.qlen by omega]
  show bytesWords (List.take it.qlen (List.drop (o + 8) (stream w σ))).toArray.toList ++
    packBytes (Vector.ofFn fun i : Fin 32 => (stream w σ).getD (o + 8 + it.qlen + i) 0).toList = _
  rw [List.toList_toArray, e1, e2, bytesWords, packBytes_wordsBytes, packBytes_wordsBytes,
    wordsBytes_length, List.length_take, List.length_drop, hW, List.cons_append, List.take_add,
    List.drop_drop, Nat.add_comm (o / 8 + 1) (it.qlen / 8),
    show 8 * min (it.qlen / 8) (185168 - (o / 8 + 1)) = it.qlen by omega]

/-- **The trace's words over aligned items.** -/
theorem readItems_words (w : ℕ → F) (σ : ℕ) : ∀ (its : List Item) (o : ℕ), o % 8 = 0 →
    (∀ it ∈ its, it.qlen % 8 = 0) → o + (its.map Item.slen).sum ≤ streamBytes →
    (readItems (stream w σ) o its).flatMap entryW = trW (streamWords w σ) (o / 8) its
  | [], _, _, _, _ => rfl
  | it :: its, o, ho, hq, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    have h8 : it.slen % 8 = 0 := by have := hq it (by simp); simp only [Item.slen]; omega
    rw [readItems, List.flatMap_cons, trW, entryW_aligned w σ o it ho (hq it (by simp)) (by omega),
      readItems_words w σ its (o + it.slen) (by omega) (fun x hx => hq x (by simp [hx])) (by omega),
      show (o + it.slen) / 8 = o / 8 + it.slen / 8 by omega]

/-- The later items fill the stream after the seed's 160 bytes. -/
theorem tail_slen_le : 160 + (items.tail.map Item.slen).sum ≤ streamBytes := by decide +kernel

theorem items_cons : items = .seed :: items.tail := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 qlen_mod.1
  rw [ht, List.tail_cons]

/-- **Slot `σ`'s trace in words** (`logWords`): the count, the seed's entry (at stream offset 1,
not word-aligned), then every later item's length word and stream words from stream word 20. -/
theorem logWords_readTrace (w : ℕ → F) (σ : ℕ) :
    logWords (readTrace w σ) = toWord 8891 :: (entryW (entryAt (stream w σ) 1 .seed) ++
      trW (streamWords w σ) 20 items.tail) := by
  have hq : ∀ it ∈ items.tail, it.qlen % 8 = 0 := fun it h => by have := qlen_mod.2.2 it h; omega
  have hw := readItems_words w σ items.tail 160 rfl hq tail_slen_le
  show toWord (readTrace w σ).length :: (readTrace w σ).flatMap entryW = _
  rw [readTrace_length]
  refine congrArg (toWord 8891 :: ·) ?_
  rw [readTrace]; conv_lhs => rw [items_cons]
  rw [readItems, List.flatMap_cons, show 1 + Item.seed.slen = 160 from rfl, hw]

/-! ## The signature's words -/

theorem digestW_toList {ws : List Word} (h : ws.length = 4) : (digestW ws).toList = wordsBytes ws := by
  refine List.ext_getElem (by simp [wordsBytes_length, h]) fun i h1 h2 => ?_
  simp [digestW, List.getElem?_eq_getElem h2]

theorem packBytes_digestOf (w : ℕ → F) (e₀ e₁ : ℕ) :
    packBytes (digestOf w e₀ e₁).toList = elemWords (w e₀) ++ elemWords (w e₁) := by
  rw [digestOf, digestW_toList (by simp [elemWords]), packBytes_wordsBytes]

/-- **Slot `σ`'s signature words**: `idx`, then two elements' words per chain value and per path
digest, read from L in order. -/
theorem sigWords_readSig (w : ℕ → F) (σ : ℕ) :
    sigWords (readSig w σ) = toWord (w (lCell σ 0)).c₀.val.toNat ::
      ((List.range wotsLen).flatMap fun j =>
        elemWords (w (lCell σ (1 + 2 * j))) ++ elemWords (w (lCell σ (2 + 2 * j)))) ++
      (List.range sigHeight).flatMap fun t => elemWords (w (lCell σ (1 + 2 * wotsLen + 2 * t))) ++
        elemWords (w (lCell σ (2 + 2 * wotsLen + 2 * t))) := by
  simp only [sigWords, readSig, List.flatMap_map, packBytes_digestOf]

end FR.Read
