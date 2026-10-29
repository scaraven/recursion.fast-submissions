-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11 … B-15; §6.4, §6.5; stage S-H3).
import FRX4Prog
import FRSoundness4Frame

/-!
# The revision 4.1 extractor `E4X`, `computes4`, and the laws `FRSoundness4Frame` needs

* **The denotation per kind** (`den` of `ext4IRWith nd`, on every log, `|π| < 2^64`):
  `den4_W` (a `W` proof: its packed words), `den4_bad` (nothing), `den4_agg` (an aggregate:
  `witWords (aggLeaf π)`, with `aggLeaf π = .leaf (bytesAt π 64 32) (Rev4.rdLE64 π 8)`), and `den4_node`
  (a node: what `nd` outputs from the parse's state).
* **`E4X nd A`** (B-15 on revision 4.1's kinds): `Ed4 nd`, the decoded denotation, on the contract's
  domain `InDomE`; outside it `Eout4 A`: `W` decoded, `A` its leaf, a node searched under the key
  it carries (`FRXSearch.search`), `bad` none. **`computes4`**: `Computes (ext4With nd) (E4X nd A)
  fuel` for every node branch under `DecOk4` and every `A`.
* **`extOff_E4X`**: `E4X` meets `FRSoundness4Frame.ExtOff` (`W` decoded on every size, an aggregate's
  `aggWit` returned).
* **`nodeExt_E4X`**: `NodeExtLog` for `E4X`, from `NodeSoundLog` (outside the domain, through the
  search) and **`NodeDecLaw4`**, the node branch's law on the domain: on an accepted node run on a
  good log, with the transcript `es` the run reads and the chain links `Links` (S-H2's `E_node`
  hypotheses, a parameter here), `nd`'s output decodes to `readW κ L es`, and that is a witness.
  This is the interface the revision 4.1 node decoder must meet; it is not discharged here (the
  3.x decoder exceeds the fuel at `m = 31/32`, `FRX4Prog`'s header).
* `ks4_E4X`: `FRSoundness4Frame.ks4_of` at `S.E = E4X nd S.acc`.
-/

namespace FR.X.X4

open RecursionFast FR.X

/-! ## Packed words of short byte windows -/

theorem ofLE_zeros : ∀ n, ofLE (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, ofLE_cons, ofLE_zeros n]; rfl

theorem ofLE_append_zeros (l : List UInt8) (n : ℕ) : ofLE (l ++ List.replicate n 0) = ofLE l := by
  rw [ofLE_append, ofLE_zeros]; simp

/-- Zero bytes appended do not change the packed words. -/
theorem packBytes_pad (l : List UInt8) (z j : ℕ) :
    (packBytes (l ++ List.replicate z 0)).getD j 0 = (packBytes l).getD j 0 := by
  rw [packBytes_getD, packBytes_getD, List.length_append, List.length_replicate]
  by_cases h : 8 * j < l.length
  · rw [if_pos (by omega), if_pos h, List.drop_append_of_le_length (by omega),
      List.take_append, List.take_replicate, ofLE_append_zeros]
  · rw [if_neg h]
    split_ifs with h2
    · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        List.drop_replicate, List.take_replicate, ofLE_zeros]; rfl
    · rfl

theorem bytesAt_pad (q : ByteArray) (o n : ℕ) :
    (bytesAt q o n).toList = ((q.data.toList ++ List.replicate (o + n) 0).drop o).take n := by
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  have hk : k < n := by simpa using h1
  rw [Vector.getElem_toList, getElem_bytesAt _ _ _ _ hk, List.getElem_take, List.getElem_drop,
    List.getElem_append]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default _ _ (by omega), List.getElem_replicate]

/-- **A 32-byte window at a word boundary packs to four of the string's words**, on every size
(missing bytes read `0`, missing words are `0`). -/
theorem packBytes_bytesAt' (q : ByteArray) (a : ℕ) {m : ℕ} (hm : m < 4) :
    (packBytes (bytesAt q (8 * a) 32).toList).getD m 0 = (packBytes q.data.toList).getD (a + m) 0 := by
  rw [bytesAt_pad, show 32 = 8 * 4 from rfl, packBytes_take8 _ hm, packBytes_drop8, packBytes_pad]

theorem packBytes_bytesAt4 (q : ByteArray) (a : ℕ) :
    packBytes (bytesAt q (8 * a) 32).toList = [(packBytes q.data.toList).getD a 0,
      (packBytes q.data.toList).getD (a + 1) 0, (packBytes q.data.toList).getD (a + 2) 0,
      (packBytes q.data.toList).getD (a + 3) 0] := by
  rw [packBytes_digest_eq4, packBytes_bytesAt' q a (by decide), packBytes_bytesAt' q a (by decide),
    packBytes_bytesAt' q a (by decide), packBytes_bytesAt' q a (by decide), Nat.add_zero]

theorem bytesAt_succ (q : ByteArray) (o n : ℕ) :
    (bytesAt q o (n + 1)).toList = byteAt q o :: (bytesAt q (o + 1) n).toList := by
  simp only [bytesAt, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
  congr 1
  congr 1
  funext i
  rw [show o + (↑i + 1) = o + 1 + ↑i by omega]

theorem ofLE_bytesAt (q : ByteArray) : ∀ (n o : ℕ),
    ofLE (bytesAt q o n).toList = ((List.range n).map fun i => (byteAt q (o + i)).toNat * 256 ^ i).sum
  | 0, _ => rfl
  | n + 1, o => by
    rw [bytesAt_succ, ofLE_cons, ofLE_bytesAt q n (o + 1), List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map, ← List.sum_map_mul_left]
    congr 1
    · simp
    · refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [show o + (i + 1) = o + 1 + i by omega, pow_succ]
      ring

theorem rdLE64_eq (π : Proof) (o : ℕ) : Rev4.rdLE64 π o = ofLE (bytesAt π o 8).toList := by
  rw [ofLE_bytesAt]; rfl

theorem rdLE64_lt (π : Proof) (o : ℕ) : Rev4.rdLE64 π o < 2 ^ 64 := by
  rw [rdLE64_eq]
  have := ofLE_lt (bytesAt π o 8).toList
  simpa using this

/-- `n`'s word is the string's word `a`. -/
theorem toWord_rdLE64 (π : Proof) (a : ℕ) :
    toWord (Rev4.rdLE64 π (8 * a)) = (packBytes π.data.toList).getD a 0 := by
  rw [rdLE64_eq, bytesAt_pad, ← packBytes_pad π.data.toList (8 * a + 8) a, packBytes_getD,
    if_pos (by simp; omega)]

/-! ## The aggregate leaf -/

/-- **The leaf witness of an aggregate proof**: the first segment's start (bytes `64 … 95`) and
`n` (bytes `8 … 15`). -/
def aggLeaf (π : Proof) : Wit := .leaf (bytesAt π 64 32) (Rev4.rdLE64 π 8)

/-- `aggWit` returns `aggLeaf`'s fields (segments of `piSizeOf seq4 ≥ 48` bytes). -/
theorem aggWit_eq {π : Proof} {s : Digest} {n : ℕ} (h : Rev4.aggWit (Rev4.piSizeOf Rev4.seq4) π = some (s, n)) :
    aggLeaf π = .leaf s n := by
  generalize hps : Rev4.piSizeOf Rev4.seq4 = S at h
  replace hps : S = 876176 := hps ▸ Rev4.piSizeOf_seq4
  simp only [Rev4.aggWit, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨v, ⟨π₁, hh, hv⟩, hvn⟩ := h
  simp only [Prod.mk.injEq] at hvn
  obtain ⟨rfl, rfl⟩ := hvn
  rw [aggLeaf]
  refine congrArg (Wit.leaf · _) ?_
  simp only [Rev4.aggSegs] at hh
  rcases hk : (byteAt π 1).toNat with _ | k
  · rw [hk] at hh; simp at hh
  · rw [hk, List.range_succ_eq_map, List.map_cons, List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [Rev4.segView, Option.map_eq_some_iff] at hv
    obtain ⟨κ, -, rfl⟩ := hv
    refine Vector.ext fun i hi => ?_
    rw [getElem_bytesAt _ _ _ _ hi, getElem_bytesAt _ _ _ _ hi, toList_extract, hps]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega)]
    congr 2
    omega

/-! ## The flags on an extractor tape -/

section Tape
variable (c : Digest) (π : Proof) (L : Log)

theorem tape4 : (extractorInput c π L).toArray.getD 4 0 = toWord π.size := by
  rw [getD_toArray, tape_getD4]

/-- With a nonempty proof, the low byte of tape word 5 is the proof's first byte. -/
theorem bOf_tape (hπ : 0 < π.size) (v : Word) (hv : v.toNat < 256) :
    bOf (extractorInput c π L).toArray v = if (byteAt π 0).toNat = v.toNat then 1 else 0 := by
  have h0 : π.data[0]? = some (byteAt π 0) := by
    rw [byteAt_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by exact hπ)]; rfl
  have hb := tape_byte0 c π L h0
  rw [bOf, isW, getD_toArray]
  congr 1
  apply propext
  rw [← BitVec.toNat_inj, lowByte, ← hb, toNat_toUInt8]

end Tape

/-! ## The kinds by their first byte -/

section Kinds
variable {π : Proof}

theorem kindOf4_eq (π : Proof) : Rev4.kindOf4 π =
    if byteAt π 0 = Rev4.aggByte then .agg else match Rev4.NodeKind.ofByte? (byteAt π 0) with
      | some κ => if π.size = Rev4.piSizeOf Rev4.seq4 then .node κ else .bad
      | none => if (Rev4.SegKind.ofByte? (byteAt π 0)).isSome then .bad else .W := rfl

theorem kindOf4_agg (h : Rev4.kindOf4 π = .agg) : byteAt π 0 = Rev4.aggByte := by
  rw [kindOf4_eq] at h
  generalize byteAt π 0 = b at h ⊢
  by_contra h1
  rw [if_neg h1] at h
  cases hn : Rev4.NodeKind.ofByte? b <;> rw [hn] at h <;> simp only at h <;> split_ifs at h

theorem nodeOfByte_eq {b : UInt8} {κ : Rev4.NodeKind} (h : Rev4.NodeKind.ofByte? b = some κ) :
    b = κ.byte := by
  unfold Rev4.NodeKind.ofByte? at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> assumption

theorem kindOf4_node {κ : Rev4.NodeKind} (h : Rev4.kindOf4 π = .node κ) :
    byteAt π 0 = κ.byte ∧ π.size = 876176 := by
  rw [kindOf4_eq] at h
  generalize byteAt π 0 = b at h ⊢
  by_cases h1 : b = Rev4.aggByte
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    cases hn : Rev4.NodeKind.ofByte? b with
    | none => rw [hn] at h; simp only at h; split_ifs at h
    | some κ' =>
      rw [hn] at h; simp only at h
      split_ifs at h with hs
      cases h
      exact ⟨nodeOfByte_eq hn, hs.trans Rev4.piSizeOf_seq4⟩

theorem kindOf4_W (h : Rev4.kindOf4 π = .W) : byteAt π 0 ≠ Rev4.aggByte ∧
    (∀ κ : Rev4.NodeKind, byteAt π 0 ≠ κ.byte) ∧ ∀ κ : Rev4.SegKind, byteAt π 0 ≠ κ.byte := by
  rw [kindOf4_eq] at h
  generalize byteAt π 0 = b at h ⊢
  by_cases h1 : b = Rev4.aggByte
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    cases hn : Rev4.NodeKind.ofByte? b with
    | some κ' => rw [hn] at h; simp only at h; split_ifs at h
    | none =>
      rw [hn] at h; simp only at h
      split_ifs at h with h2
      refine ⟨h1, fun κ he => ?_, fun κ he => h2 ?_⟩
      · rw [he, Rev4.NodeKind.ofByte?_byte] at hn; cases hn
      · rw [he, Rev4.SegKind.ofByte?_byte]; rfl

theorem segOfByte_eq {b : UInt8} {κ : Rev4.SegKind} (h : Rev4.SegKind.ofByte? b = some κ) :
    b = κ.byte := by
  unfold Rev4.SegKind.ofByte? at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> assumption

theorem kindOf4_bad (h : Rev4.kindOf4 π = .bad) :
    (∃ κ : Rev4.NodeKind, byteAt π 0 = κ.byte ∧ π.size ≠ 876176) ∨
      ∃ κ : Rev4.SegKind, byteAt π 0 = κ.byte := by
  rw [kindOf4_eq] at h
  have hps := Rev4.piSizeOf_seq4
  generalize byteAt π 0 = b at h ⊢
  by_cases h1 : b = Rev4.aggByte
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    cases hn : Rev4.NodeKind.ofByte? b with
    | some κ' =>
      rw [hn] at h; simp only at h
      split_ifs at h with hs
      exact .inl ⟨κ', nodeOfByte_eq hn, hps ▸ hs⟩
    | none =>
      rw [hn] at h; simp only at h
      split_ifs at h with h2
      obtain ⟨κ, hκ⟩ := Option.isSome_iff_exists.1 h2
      exact .inr ⟨κ, segOfByte_eq hκ⟩

theorem pos_of_byte {b : UInt8} (h : byteAt π 0 = b) (hb : b ≠ 0) : 0 < π.size := by
  by_contra h0
  rw [byteAt, dif_neg (by omega)] at h
  exact hb h.symm

end Kinds

/-! ## The flags after the parse, per kind -/

theorem pos_toWord {n : ℕ} (h : n < 2 ^ 64) : ((0 : Word) < toWord n) ↔ 0 < n := by
  rw [BitVec.lt_def, toNat_toWord h]; rfl

section Flags
variable (c : Digest) (π : Proof) (L : Log)

/-- The state after the parse, on the extractor's tape. -/
def st1 : St := semXIR (extractorInput c π L).toArray parse4
  (initSt (memX4 + mpwX * (extractorInput c π L).length))

theorem inv_st1 : Inv (st1 c π L).M :=
  inv_sem _ wf_parse4 (inv_initSt (Nat.le_add_right_of_le (by simp only [regs, memX4]; norm_num)))

theorem st1_o : (st1 c π L).o = #[] := by rw [st1, parse4_o, initSt_o]

theorem bOf_byte (hπ : 0 < π.size) (v : Word) (n : ℕ) (hv : v.toNat = n) (hn : n < 256) :
    bOf (extractorInput c π L).toArray v = if (byteAt π 0).toNat = n then 1 else 0 := by
  rw [bOf_tape c π L hπ v (by omega), hv]

theorem flagK_W (hW : Rev4.kindOf4 π = .W) (hs : π.size < 2 ^ 64) : rd (st1 c π L).M rIsK = 0 := by
  rw [st1, parse4_K _ _ (inv_initSt (Nat.le_add_right_of_le (by simp only [regs, memX4]; norm_num))),
    tape4]
  rcases Nat.eq_zero_or_pos π.size with h0 | hp
  · rw [if_neg (by rw [pos_toWord hs]; omega)]; exact BitVec.and_zero
  · obtain ⟨hA, hN, hS⟩ := kindOf4_W hW
    have ne : ∀ u : UInt8, byteAt π 0 ≠ u → (byteAt π 0).toNat ≠ u.toNat := fun u h e =>
      h (UInt8.toNat_inj.1 e)
    have := ne _ hA; have := ne _ (hN .N2); have := ne _ (hN .N4); have := ne _ (hN .N8)
    have := ne _ (hS .L30); have := ne _ (hS .L31); have := ne _ (hS .L32)
    simp only [Rev4.aggByte, Rev4.NodeKind.byte, Rev4.SegKind.byte, UInt8.toNat_ofNat] at *
    rw [bOf_byte c π L hp _ 80 rfl (by norm_num), bOf_byte c π L hp _ 75 rfl (by norm_num),
      bOf_byte c π L hp _ 76 rfl (by norm_num), bOf_byte c π L hp _ 65 rfl (by norm_num),
      bOf_byte c π L hp _ 77 rfl (by norm_num), bOf_byte c π L hp _ 78 rfl (by norm_num),
      bOf_byte c π L hp _ 79 rfl (by norm_num)]
    simp_all

/-- The flags after the parse on a nonempty proof, by its first byte `n`. -/
theorem flags (hs : π.size < 2 ^ 64) (hp : 0 < π.size) :
    rd (st1 c π L).M rIsK = (((((if (byteAt π 0).toNat = 80 then 1 else 0) |||
      (if (byteAt π 0).toNat = 75 then 1 else 0)) ||| (if (byteAt π 0).toNat = 76 then 1 else 0)) |||
      (if (byteAt π 0).toNat = 65 then 1 else 0)) |||
      (((if (byteAt π 0).toNat = 77 then 1 else 0) ||| (if (byteAt π 0).toNat = 78 then 1 else 0)) |||
        (if (byteAt π 0).toNat = 79 then 1 else 0))) &&& 1 ∧
    rd (st1 c π L).M rIsA = (if (byteAt π 0).toNat = 65 then 1 else 0) ∧
    rd (st1 c π L).M rIsN = ((if (byteAt π 0).toNat = 77 then 1 else 0) |||
      (if (byteAt π 0).toNat = 78 then 1 else 0)) ||| (if (byteAt π 0).toNat = 79 then 1 else 0) ∧
    rd (st1 c π L).M rIsSz = isW (toWord π.size) (BitVec.ofNat 64 876176) ∧
    rd (st1 c π L).M rLen = toWord π.size := by
  have h0 : Inv (initSt (memX4 + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le (by simp only [regs, memX4]; norm_num))
  have hb := fun v n hv hn => bOf_byte c π L hp v n hv hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [st1, parse4_K _ _ h0, tape4, if_pos ((pos_toWord hs).2 hp), hb _ 80 rfl (by norm_num),
      hb _ 75 rfl (by norm_num), hb _ 76 rfl (by norm_num), hb _ 65 rfl (by norm_num),
      hb _ 77 rfl (by norm_num), hb _ 78 rfl (by norm_num), hb _ 79 rfl (by norm_num)]
  · rw [st1, parse4_A _ _ h0, hb _ 65 rfl (by norm_num)]
  · rw [st1, parse4_N _ _ h0, hb _ 77 rfl (by norm_num), hb _ 78 rfl (by norm_num),
      hb _ 79 rfl (by norm_num)]
  · rw [st1, parse4_sz _ _ h0, tape4]
  · rw [st1, parse4_len _ _ h0, tape4]

theorem isW_sz (hs : π.size < 2 ^ 64) :
    isW (toWord π.size) (BitVec.ofNat 64 876176) = if π.size = 876176 then 1 else 0 := by
  rw [isW]
  congr 1
  apply propext
  rw [← BitVec.toNat_inj, toNat_toWord hs, BitVec.toNat_ofNat]

end Flags

/-! ## The denotation per kind -/

section Den
variable (nd : XIR) (c : Digest) (π : Proof) (L : Log)

/-- The branch after the parse. -/
def br4 (nd : XIR) : XIR := .ite rIsK (.ite rIsA aggIR (.ite rIsN (.ite rIsSz nd (.blk [])) (.blk []))) wIR

theorem den4_split : den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) =
    (semXIR (extractorInput c π L).toArray (br4 nd) (st1 c π L)).o.toList := by
  simp only [den, ext4IRWith, semXIR_seq, st1, br4]

/-- **A `W` proof**: the denotation is its packed words, on every log. -/
theorem den4_W (hW : Rev4.kindOf4 π = .W) (hs : π.size < 2 ^ 64) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) = packBytes π.data.toList := by
  rw [den4_split, br4, semXIR_ite, if_pos (flagK_W c π L hW hs),
    wIR_sem _ _ (inv_st1 c π L) (by rw [tape4, toNat_ceil8 hs]; omega), st1_o, tape4,
    toNat_ceil8 hs, Array.toList_empty, List.nil_append]
  refine List.ext_getElem (by
    simp only [List.length_map, List.length_range, packBytes_length]
    rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
  simp only [List.getElem_map, List.getElem_range, getD_toArray]
  exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)

/-- **A `bad` proof**: no output. -/
theorem den4_bad (hB : Rev4.kindOf4 π = .bad) (hs : π.size < 2 ^ 64) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) = [] := by
  rw [den4_split]
  rcases kindOf4_bad hB with ⟨κ, hb, hz⟩ | ⟨κ, hb⟩
  · have hp := pos_of_byte hb (by cases κ <;> decide)
    obtain ⟨hK, hA, hN, hZ, -⟩ := flags c π L hs hp
    rw [isW_sz π hs, if_neg hz] at hZ
    have hn : (byteAt π 0).toNat = κ.byte.toNat := by rw [hb]
    rw [br4, semXIR_ite, if_neg (by rw [hK, hn]; cases κ <;> decide), semXIR_ite,
      if_pos (by rw [hA, hn]; cases κ <;> decide), semXIR_ite,
      if_neg (by rw [hN, hn]; cases κ <;> decide), semXIR_ite, if_pos hZ]
    simp [semXIR, st1_o]
  · have hp := pos_of_byte hb (by cases κ <;> decide)
    obtain ⟨hK, hA, hN, -, -⟩ := flags c π L hs hp
    have hn : (byteAt π 0).toNat = κ.byte.toNat := by rw [hb]
    rw [br4, semXIR_ite, if_neg (by rw [hK, hn]; cases κ <;> decide), semXIR_ite,
      if_pos (by rw [hA, hn]; cases κ <;> decide), semXIR_ite,
      if_pos (by rw [hN, hn]; cases κ <;> decide)]
    simp [semXIR, st1_o]

/-- **A node proof**: the denotation is the node branch's output from the parse's state. -/
theorem den4_node {κ : Rev4.NodeKind} (hN : Rev4.kindOf4 π = .node κ) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) =
      (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList := by
  obtain ⟨hb, hz⟩ := kindOf4_node hN
  have hs : π.size < 2 ^ 64 := by omega
  have hp := pos_of_byte hb (by cases κ <;> decide)
  obtain ⟨hK, hA, hN', hZ, -⟩ := flags c π L hs hp
  rw [isW_sz π hs, if_pos hz] at hZ
  have hn : (byteAt π 0).toNat = κ.byte.toNat := by rw [hb]
  rw [den4_split, br4, semXIR_ite, if_neg (by rw [hK, hn]; cases κ <;> decide), semXIR_ite,
    if_pos (by rw [hA, hn]; cases κ <;> decide), semXIR_ite,
    if_neg (by rw [hN', hn]; cases κ <;> decide), semXIR_ite, if_neg (by rw [hZ]; decide)]

end Den

/-! ## The aggregate branch -/

theorem outW_sem (I : Array Word) (s : St) (hM : Inv s.M) (j : ℕ) (hj : 8 * j < 2 ^ 64) :
    (semXIR I (outW j) s).o.toList = s.o.toList ++
      [I.getD (5 + j) 0 * (if BitVec.ofNat 64 (8 * j) < rd s.M rLen then 1 else 0)] ∧
    rd (semXIR I (outW j) s).M rLen = rd s.M rLen ∧ Inv (semXIR I (outW j) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, ?_, inv_sem I (wf_outW j) hM⟩
  · simp only [outW, readAt, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | omega | (simp only [size_set, rA, rW, rK, rMk]; omega) |
        (simp only [rA, rW, rK, rMk, rLen]; omega))
      [rd_set_self, rd_set_ne, XOp.eval, Array.toList_push]
    rw [Nat.mod_eq_of_lt (show 5 + j < 18446744073709551616 by omega)]
  · simp only [outW, readAt, semXIR, runPrims, List.foldl, Prim.run, rA, rW, rK, rMk, rLen]
    simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]

theorem mask_word (c : Digest) (π : Proof) (L : Log) (hs : π.size < 2 ^ 64) (j : ℕ) (hj : 8 * j < 2 ^ 64) :
    (extractorInput c π L).toArray.getD (5 + j) 0 *
      (if BitVec.ofNat 64 (8 * j) < toWord π.size then 1 else 0) = (packBytes π.data.toList).getD j 0 := by
  have m1 : ∀ x : Word, x * 1 = x := fun x => by simp
  have m0 : ∀ x : Word, x * 0 = 0 := fun x => by simp
  have hlt : (BitVec.ofNat 64 (8 * j) < toWord π.size) ↔ 8 * j < π.size := by
    rw [BitVec.lt_def, toNat_toWord hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  by_cases h : 8 * j < π.size
  · rw [if_pos (hlt.2 h), m1, getD_toArray, tape_getD_proof c π L (by omega),
      List.getD_eq_getElem]
  · rw [if_neg (fun h' => h (hlt.1 h')), m0, packBytes_getD, if_neg (by
      rw [← WitnessSending.size_eq_length]; omega)]

/-- **An aggregate proof**: the denotation is the leaf witness `aggLeaf π`, on every log. -/
theorem den4_agg (nd : XIR) (c : Digest) (π : Proof) (L : Log) (hA : Rev4.kindOf4 π = .agg)
    (hs : π.size < 2 ^ 64) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) = witWords (aggLeaf π) := by
  have hb := kindOf4_agg hA
  have hp := pos_of_byte hb (by decide)
  have hn : (byteAt π 0).toNat = 65 := by rw [hb]; rfl
  obtain ⟨hK, hA', -, -, hL⟩ := flags c π L hs hp
  rw [den4_split, br4, semXIR_ite, if_neg (by rw [hK, hn]; decide), semXIR_ite,
    if_neg (by rw [hA', hn]; decide)]
  have hM := inv_st1 c π L
  have ho := st1_o c π L
  generalize st1 c π L = s1 at *
  set I := (extractorInput c π L).toArray with hI
  have hs1 := hM.1
  simp only [regs] at hs1
  set s2 : St := ⟨s1.M.setIfInBounds rW 0, s1.o.push 0⟩ with hs2
  have e0 : semXIR I (.seq (.blk [.const rW 0]) (.out rW)) s1 = s2 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, hs2]
    simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rW]
  have h2M : Inv s2.M := inv_sem I (P := .blk [.const rW 0]) (by simp [WF, Prim.dst, rW]) hM
  have h2L : rd s2.M rLen = toWord π.size := by
    simp only [hs2]; rw [rd_set_ne (by simp [rW, rLen]), hL]
  have h2o : s2.o.toList = [0] := by simp [hs2, ho]
  rw [aggIR, semXIR_seq, e0]
  clear_value s2
  obtain ⟨o8, l8, i8⟩ := outW_sem I s2 h2M 8 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 8) s2 = s3 at o8 l8 i8
  obtain ⟨o9, l9, i9⟩ := outW_sem I s3 i8 9 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 9) s3 = s4 at o9 l9 i9
  obtain ⟨o10, l10, i10⟩ := outW_sem I s4 i9 10 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 10) s4 = s5 at o10 l10 i10
  obtain ⟨o11, l11, i11⟩ := outW_sem I s5 i10 11 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 11) s5 = s6 at o11 l11 i11
  obtain ⟨o1, -, -⟩ := outW_sem I s6 i11 1 (by norm_num)
  rw [o1, o11, o10, o9, o8, h2o, l11, l10, l9, l8, h2L, hI, mask_word c π L hs 8 (by norm_num),
    mask_word c π L hs 9 (by norm_num), mask_word c π L hs 10 (by norm_num),
    mask_word c π L hs 11 (by norm_num), mask_word c π L hs 1 (by norm_num)]
  have e1 := packBytes_bytesAt4 π 8
  have e2 := toWord_rdLE64 π 1
  simp only [show 8 * 8 = 64 from rfl, show 8 * 1 = 8 from rfl] at e1 e2
  rw [aggLeaf, witWords, e1, e2]
  rfl

/-! ## The extractor `E4X` -/

/-- **The in-domain extractor**: the decoded denotation of `ext4IRWith nd`. -/
def Ed4 (nd : XIR) : Digest → Proof → Log → Option Wit := Eden memX4 mpwX (ext4IRWith nd)

/-- **The extractor outside the domain** (B-15 on revision 4.1's kinds): `W` decoded, an aggregate's
leaf, a node searched under the key it carries, `bad` none. -/
def Eout4 (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) : Option Wit :=
  match Rev4.kindOf4 π with
  | .W => WitnessSending.decode π
  | .agg => some (aggLeaf π)
  | .node _ => search A (vkOf π) c
  | .bad => none

/-- **The revision 4.1 extractor specification**: `Ed4 nd` on the domain, `Eout4 A` outside it. -/
def E4X (nd : XIR) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) :
    Option Wit :=
  if InDomE c π L then Ed4 nd c π L else Eout4 A c π L

section E
variable {nd : XIR} {A : Digest → Digest → Signed → Bool} {c : Digest} {π : Proof} {L : Log}

theorem size_lt_of_dom (h : InDomE c π L) : π.size < 2 ^ 64 := by
  have := h.1; rw [outCap] at this; omega

/-- `E4X` decodes a `W` proof, on every size. -/
theorem E4X_W (hW : Rev4.kindOf4 π = .W) : E4X nd A c π L = WitnessSending.decode π := by
  by_cases h : InDomE c π L
  · rw [E4X, if_pos h, Ed4, Eden, den4_W nd c π L hW (size_lt_of_dom h)]; rfl
  · rw [E4X, if_neg h, Eout4, hW]

/-- `E4X` returns an aggregate's leaf, on every size. -/
theorem E4X_agg (hA : Rev4.kindOf4 π = .agg) : E4X nd A c π L = some (aggLeaf π) := by
  by_cases h : InDomE c π L
  · rw [E4X, if_pos h, Ed4, Eden, den4_agg nd c π L hA (size_lt_of_dom h), aggLeaf,
      decodeWit_witWords (.leaf (bytesAt π 64 32) (Rev4.rdLE64 π 8)) (rdLE64_lt π 8)]
  · rw [E4X, if_neg h, Eout4, hA]

/-- `E4X` returns nothing on a `bad` proof. -/
theorem E4X_bad (hB : Rev4.kindOf4 π = .bad) : E4X nd A c π L = none := by
  by_cases h : InDomE c π L
  · rw [E4X, if_pos h, Ed4, Eden, den4_bad nd c π L hB (size_lt_of_dom h)]; rfl
  · rw [E4X, if_neg h, Eout4, hB]

/-- On a node proof in the domain, `E4X` is what the node branch outputs. -/
theorem E4X_node {κ : Rev4.NodeKind} (hN : Rev4.kindOf4 π = .node κ) (h : InDomE c π L) :
    E4X nd A c π L = decodeWit (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList := by
  rw [E4X, if_pos h, Ed4, Eden, den4_node nd c π L hN]

/-- Outside the domain a node proof is searched under the key it carries. -/
theorem E4X_node_out {κ : Rev4.NodeKind} (hN : Rev4.kindOf4 π = .node κ) (h : ¬ InDomE c π L) :
    E4X nd A c π L = search A (vkOf π) c := by
  rw [E4X, if_neg h, Eout4, hN]

/-- **`E4X` meets `ExtOff`** (`FRSoundness4Frame`). -/
theorem extOff_E4X (nd : XIR) (A : Digest → Digest → Signed → Bool) : Rev4.ExtOff (E4X nd A) :=
  ⟨fun _ _ _ hW => E4X_W hW, fun _ π _ s n hA ha => by rw [E4X_agg hA, aggWit_eq ha]⟩

end E

/-! ## Halting within the fuel: `computes4` -/

theorem safe_parse4 (I : Array Word) (t : ℕ) : Safe I t parse4 :=
  .seq (.seq (.blk _) (.input _ _)) (.seq (.seq (.blk _) (.input _ _)) (.blk _))

theorem safe_outW (I : Array Word) (t j : ℕ) : Safe I t (outW j) :=
  .seq (.seq (.blk _) (.input _ _)) (.seq (.blk _) (.out _))

theorem safe_aggIR (I : Array Word) (t : ℕ) : Safe I t aggIR :=
  .seq (.seq (.blk _) (.out _)) (.seq (safe_outW ..) (.seq (safe_outW ..) (.seq (safe_outW ..)
    (.seq (safe_outW ..) (safe_outW ..)))))

theorem outs_aggIR (t : ℕ) : outs aggIR t = 6 := by
  simp [aggIR, outW, readAt, outs]

/-- The loop bounds of the branch after the parse, on every domain tape. -/
theorem boundsOk_br4 {nd : XIR} (hnd : DecOk4 nd) (c : Digest) (π : Proof) (L : Log)
    (h : InDomE c π L) (s1 : St) (hM : Inv s1.M)
    (hz : rd s1.M rIsSz ≠ 0 → π.size = Rev4.piSizeOf Rev4.seq4) :
    BoundsOk (extractorInput c π L).toArray (extractorInput c π L).length (br4 nd) s1 := by
  have hs := size_lt_of_dom h
  have hwf := wf_ext4IRWith hnd.wf
  rw [br4, boundsOk_ite]
  by_cases hK : rd s1.M rIsK = 0
  · rw [if_pos hK]
    exact boundsOk_of_safe (safe_wIR hs (tape4 c π L) (by have := tape_length c π L; omega))
      hwf.2.2 _ hM
  · rw [if_neg hK, boundsOk_ite]
    by_cases hA : rd s1.M rIsA = 0
    · rw [if_pos hA, boundsOk_ite]
      by_cases hN : rd s1.M rIsN = 0
      · rw [if_pos hN]; trivial
      · rw [if_neg hN, boundsOk_ite]
        by_cases hZ : rd s1.M rIsSz = 0
        · rw [if_pos hZ]; trivial
        · rw [if_neg hZ]
          exact boundsOk_of_safe (hnd.safe c π L (hz hZ) h.2.1 h.2.2) hnd.wf _ hM
    · rw [if_neg hA]
      exact boundsOk_of_safe (safe_aggIR _ _) wf_aggIR _ hM

theorem ext4IRWith_eq (nd : XIR) : ext4IRWith nd = .seq parse4 (br4 nd) := rfl

-- `br4` is irreducible here: a `BoundsOk … (br4 nd) s` hypothesis is otherwise unfolded and
-- evaluated on the concrete tape (maximum recursion depth).
attribute [local irreducible] br4 in
/-- **The program halts within the fuel with at most `outCap` words** on every domain tape. -/
theorem halts4 {nd : XIR} (hnd : DecOk4 nd) (c : Digest) (π : Proof) (L : Log)
    (h1 : π.size ≤ 8 * outCap) (h2 : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (h3 : (extractorInput c π L).length ≤ 2 ^ 64) :
    ∃ o, (ext4With nd).run (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap := by
  have h : InDomE c π L := ⟨h1, h2, h3⟩
  have hs := size_lt_of_dom h
  have hreg : regs ≤ memX4 := by simp only [regs, memX4]; norm_num
  have hwf := wf_ext4IRWith hnd.wf
  have h0 : Inv (initSt (memX4 + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  have hden : den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) =
      (semXIR (extractorInput c π L).toArray (ext4IRWith nd)
        (initSt (memX4 + mpwX * (extractorInput c π L).length))).o.toList := rfl
  generalize hs0 : initSt (memX4 + mpwX * (extractorInput c π L).length) = s0 at h0 hden
  have hz := parse4_sz (extractorInput c π L).toArray s0 h0
  rw [tape4, isW_sz π hs] at hz
  have hB0 := boundsOk_br4 hnd c π L h (semXIR (extractorInput c π L).toArray parse4 s0)
    (inv_sem _ wf_parse4 h0) fun hz' => by
      rw [Rev4.piSizeOf_seq4]; by_contra hne; rw [if_neg hne] at hz; exact hz' hz
  generalize hI : (extractorInput c π L).toArray = I at hB0 hden
  have hB : BoundsOk I (extractorInput c π L).length (ext4IRWith nd) s0 := by
    rw [ext4IRWith_eq]
    exact (boundsOk_seq (p := parse4) (q := br4 nd)).2
      ⟨boundsOk_of_safe (safe_parse4 _ _) wf_parse4 _ h0, hB0⟩
  have hrun := run_toProg (P := ext4IRWith nd) (input := extractorInput c π L)
    (f := fuel (extractorInput c π L).length) hreg hwf (by rw [hs0, hI]; exact hB)
    (fuel_covers4 hnd.cost _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  rw [← hden]
  rcases hk : Rev4.kindOf4 π with _ | _ | _ | κ
  · rw [den4_W nd c π L hk hs, packBytes_length, ← WitnessSending.size_eq_length]
    rw [outCap] at h1 ⊢; omega
  · rw [den4_bad nd c π L hk hs]; exact Nat.zero_le _
  · rw [den4_agg nd c π L hk hs]; simp [aggLeaf, witWords, outCap, packBytes_digest_length]
  · rw [den4_node nd c π L hk]
    have hz : π.size = Rev4.piSizeOf Rev4.seq4 := (kindOf4_node hk).2.trans Rev4.piSizeOf_seq4.symm
    have := outs_le (I := (extractorInput c π L).toArray) (extractorInput c π L).length nd _ hnd.wf
      (inv_st1 c π L) (boundsOk_of_safe (hnd.safe c π L hz h2 h3) hnd.wf _ (inv_st1 c π L))
    rw [st1_o, Array.size_empty, Nat.zero_add] at this
    rw [Array.length_toList]; exact this.trans (hnd.outs _)

/-- **`Computes (ext4With nd) (E4X nd A) fuel`**, for every node branch under `DecOk4` and every
`A` (on the domain `E4X nd A = Ed4 nd`). -/
theorem computes4 {nd : XIR} (hnd : DecOk4 nd) (A : Digest → Digest → Signed → Bool) :
    Computes (ext4With nd) (E4X nd A) fuel := fun c π L h1 h2 h3 => by
  obtain ⟨o, ho, hl, hd⟩ := computes_Eof fuel (by simp only [regs, memX4]; norm_num)
    (wf_ext4IRWith hnd.wf) (fun c π L h1 h2 h3 => halts4 hnd c π L h1 h2 h3) c π L h1 h2 h3
  exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem ext4_caps {nd : XIR} (hnd : DecOk4 nd) :
    (∀ t, fuel t ≤ extractorBudget t) ∧ (ext4With nd).body.size ≤ progCap :=
  ⟨fuel_le_budget, size_ext4With hnd.size⟩

/-! ## The node law: `NodeExtLog` for `E4X` -/

/-- **What the revision 4.1 node branch must meet** (S-H2's `E_node` at revision 4.1). The node's
cell map and its chain links are parameters: the revision 4.1 node circuit (block-kind map,
`StmtN`/`NodeResid` with `1 + k` slots) is S-E's and does not exist yet.
* `Links κ L es π c`: S-H2's `E_node` hypotheses at the node kind `κ` and the transcript `es` the
  verifier's run reads off `L`: the chain links `fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)`
  (at `seq4`'s positions), the cap links `capDig es i = capPiL i π`, the final link
  `finalAt es x = finPi π x`, `¬ StateHit L`, and per level `¬ farL` and `A_c = jointAgree` (at
  `ladderOf κ.m`).
* `readW κ L es`: the witness read off `f⁽⁰⁾` (S-H2's `FR.readWit` at revision 4.1: the previous
  node, or for `N8` the first aggregate, and the aggregate child `hdr_A ‖ π₁ ‖ … ‖ π_k` with
  `tr_A = tr₁ ‖ … ‖ tr_k`, read from `FRNodeLayout4`'s H and L regions).
* `out`: on the domain and under the links, the branch outputs `witWords (readW κ L es)` from the
  parse's state, and the witness fits the output format. -/
structure NodeDec4 (nd : XIR) where
  /-- The chain links (S-H2's `E_node` hypotheses at revision 4.1). -/
  Links : Rev4.NodeKind → Log → Log → Proof → Digest → Prop
  /-- The witness read off `f⁽⁰⁾`. -/
  readW : Rev4.NodeKind → Log → Log → Wit
  /-- The decode law. -/
  out : ∀ κ c π L es, Rev4.kindOf4 π = .node κ → InDomE c π L → Links κ L es π c →
    (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList = witWords (readW κ L es) ∧
      (readW κ L es).Fits

/-- **`E4X` on a linked node proof in the domain** is the witness read off `f⁽⁰⁾`. -/
theorem E4X_node_dec {nd : XIR} (D : NodeDec4 nd) {A : Digest → Digest → Signed → Bool}
    {κ : Rev4.NodeKind} {c : Digest} {π : Proof} {L es : Log} (hN : Rev4.kindOf4 π = .node κ)
    (h : InDomE c π L) (hl : D.Links κ L es π c) : E4X nd A c π L = some (D.readW κ L es) := by
  obtain ⟨ho, hf⟩ := D.out κ c π L es hN h hl
  rw [E4X_node hN h, ho, decodeWit_witWords _ hf]

/-- **The node law of `FRSoundness4Frame` for `E4X`**: outside the domain from `NodeSoundLog`
(the search, as `nodeExt_E4`); on the domain from the decode law `D` and `hL`, S-G's side: an
accepted node run on a good log has a transcript `es` meeting the links, and `readW κ L es` is a
witness of the relation (3.x: `rel_readWit`, S-G2/S-G3's link discharge). -/
theorem nodeExt_E4X {nd : XIR} (D : NodeDec4 nd) {Vnode : Rev4.NodeProgs} {vk : Digest}
    {Good : Log → Prop} {S : Submission} (hq : S.qV = Rev4.qV4)
    (hN : Rev4.NodeSoundLog Vnode vk Good (RecursionFast.Rel (S.acc vk)))
    (hL : ∀ κ L c π, Good L → Rev4.kindOf4 π = .node κ → InDomE c π L →
      (Vnode κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ RecursionFast.Rel (S.acc vk) c (D.readW κ L es)) :
    Rev4.NodeExtLog Vnode vk Good (E4X nd S.acc) (RecursionFast.Rel (S.acc vk)) :=
  fun κ L c π hG hk h => by
    by_cases hd : InDomE c π L
    · obtain ⟨es, hl, hr⟩ := hL κ L c π hG hk hd h
      exact ⟨_, E4X_node_dec D hk hd hl, hr⟩
    · obtain ⟨hvk, hw⟩ := hN κ L c π hG hk h
      obtain ⟨w, hs, hr⟩ := search_spec_acc (A := S.acc) (vk := vk)
        (fun _ _ ha => sFits_of_acc (by rw [hq]; decide) ha) hw
      exact ⟨w, by rw [E4X_node_out hk hd, hvk]; exact hs, hr⟩

open scoped NNReal in
/-- **`KS` for revision 4.1's verifier at `S.E = E4X nd S.acc`** (`FRSoundness4Frame.ks4_of`):
the node law from the decode law `D`, `NodeSoundLog` and S-G's links `hL`. -/
theorem ks4_E4X (impl₀ : OpImpl) (implN : Rev4.NodeKind → OpImpl) (cells : Rev4.NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = Rev4.VC4 impl₀ implN cells) (hq : S.qV = Rev4.qV4)
    {nd : XIR} (D : NodeDec4 nd) (hE : S.E = E4X nd S.acc) {ε : ℝ≥0} (μ : Log → ℝ≥0)
    (h0 : μ [] = 0)
    (hstep : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256)
    (hS : Rev4.SegSoundLog (Rev4.VsegC impl₀) vk fun L => L.length ≤ logCap ∧ μ L < 1)
    (hN : Rev4.NodeSoundLog (Rev4.VnodeC implN cells) vk (fun L => L.length ≤ logCap ∧ μ L < 1)
      (RecursionFast.Rel (S.acc vk)))
    (hL : ∀ κ L c π, (L.length ≤ logCap ∧ μ L < 1) → Rev4.kindOf4 π = .node κ → InDomE c π L →
      (Rev4.VnodeC implN cells κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ RecursionFast.Rel (S.acc vk) c (D.readW κ L es)) :
    KS (RecursionFast.Rel (S.acc vk)) (S.V vk) S.E ε S.qV :=
  Rev4.ks4_of impl₀ implN cells S vk hV hq (hE ▸ extOff_E4X nd S.acc) μ h0 hstep hS
    (hE ▸ nodeExt_E4X D hq hN hL)

/-! ## Controls -/

section Controls
variable {A : Digest → Digest → Signed → Bool} (c : Digest) (L : Log)

/-- (+) `E4X` decodes a witness-sending proof (every node branch). -/
theorem E4X_encode (nd : XIR) (w : Wit) :
    E4X nd A c (WitnessSending.encode w) L = WitnessSending.decode (WitnessSending.encode w) :=
  E4X_W (Rev4.kindOf4_encode w)

/-- (−) `E4X` extracts nothing from a bare segment proof (`L32`'s byte), nor from a node byte of
the wrong size. -/
theorem E4X_bad_ctl (nd : XIR) :
    E4X nd A c ⟨#[Rev4.SegKind.L32.byte]⟩ L = none ∧ E4X nd A c ⟨#[Rev4.NodeKind.N4.byte]⟩ L = none :=
  ⟨E4X_bad (by decide), E4X_bad (by decide)⟩

/-- A toy aggregate proof: `'A'`, `k = 1`, `n = 5` (byte 8), the first segment's start byte `7`
(byte 64). -/
def toyA : Proof := ⟨(List.range 96).toArray.map fun i =>
  if i = 0 then 0x41 else if i = 1 then 1 else if i = 8 then 5 else if i = 64 then 7 else 0⟩

/-- (+/−) The aggregate's leaf reads `n` at bytes `8 … 15` (not at `0 … 7`, where `'A'` and `k`
sit) and the start at byte 64 (not 63). -/
theorem aggLeaf_ctl : Rev4.kindOf4 toyA = .agg ∧ Rev4.rdLE64 toyA 8 = 5 ∧ Rev4.rdLE64 toyA 0 ≠ 5 ∧
    (bytesAt toyA 64 32)[0] = 7 ∧ byteAt toyA 63 = 0 := by
  decide +kernel

/-- (+) `E4X` returns the toy aggregate's leaf. -/
theorem E4X_toyA (nd : XIR) : E4X nd A c toyA L = some (aggLeaf toyA) := E4X_agg aggLeaf_ctl.1

/-- (−) **The certificate's current node branch extracts nothing**: with `ndNone`, a node proof in
the domain gives `none` (the revision 4.1 node decoder is missing, `FRX4Prog`'s header). -/
theorem E4X_ndNone_node {κ : Rev4.NodeKind} {π : Proof} (hN : Rev4.kindOf4 π = .node κ)
    (h : InDomE c π L) : E4X ndNone A c π L = none := by
  rw [E4X_node hN h]
  simp [ndNone, semXIR, st1_o]
  rfl

/-- (−) **The decode law is not vacuous**: no `NodeDec4 ndNone` has a linked node input in the
domain (the empty branch outputs nothing, every `witWords` has a tag). -/
theorem not_nodeDec4_ndNone (D : NodeDec4 ndNone) {κ : Rev4.NodeKind} {π : Proof} {es : Log}
    (hN : Rev4.kindOf4 π = .node κ) (h : InDomE c π L) (hl : D.Links κ L es π c) : False := by
  have := (D.out κ c π L es hN h hl).1
  simp only [ndNone, semXIR, runPrims_nil, st1_o, Array.toList_empty] at this
  cases hw : D.readW κ L es <;> rw [hw] at this <;> simp [witWords] at this

/-- (+) A decode law with no linked input is met by every branch (the law constrains only linked
node inputs). -/
def nodeDec4_none (nd : XIR) : NodeDec4 nd :=
  ⟨fun _ _ _ _ _ => False, fun _ _ _ => .leaf 0 0, fun _ _ _ _ _ _ _ h => h.elim⟩

end Controls

end FR.X.X4
