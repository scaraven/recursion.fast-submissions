-- adapted from rf-k/submissions/flock-recursive/lean/FRXRead.lean@8bff272b (sections "One
-- position", "The read at a parametric index base", `read_spec`): `posBody_sem`, `posLoop4`,
-- `readIR4_sem` + `readIR4_frame`, `read_spec`.
-- New for lvm (WP-13b): the column reads of `C_rec` (BLUEPRINT §6.2 step 4), part 3: one
-- position, the position loop and **`readIR_sem`**.
import LvmXLoop

-- ===== merged from `LvmXReadDefs` (GOLF module merge: `LvmXReadDefs.lean` is now a stub importing `LvmXRead2`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXReadDefs.lean@8bff272b (sections
-- "Packed bytes: aligned slices", "First preimages are `ansIdx`", "The tape", "Registers",
-- "The program", "Well formed, cost, size"): `packBytes_getD`, `packBytes_drop8`,
-- `packBytes_take8`, `packBytes_digest_eq4` (from FRXRead), `pre_eq_ansIdx`, `pre_some`,
-- `pre_none`, `entries_getD_q`, `tape_query4`, `ld4IR`, `capPs`, `getIR`, `nodeChkPs`,
-- `childPs`, `nodeBody`, `colIR`, `copyBody`, `copyIR`, `posBody4`, `readIR4`, `wf_lookIR4`,
-- `lookIR4_nw`, `loK_lookIR4` (from FRXRead), `wf_readIR4`, `noLoopT_readIR4`, `outs_readIR4`,
-- `cost_lookIR4`, `cost_readIR4`.
-- New for lvm (WP-13b): the column reads of `C_rec` (BLUEPRINT §6.2 step 4), part 1: the pure
-- first-preimage reading (WP-5's `findA`/`descend`/`leafBytes`/`wordOf`, transcribed), the facts
-- about the tape it uses, the `XIR` program and its cost.

/-!
# The column reads of `C_rec`: the pure reading and the program

`C_rec`'s Merkle tree has `2^15` leaves (positions `p < 2^15`), is binary, and has its cap at
level 7 (`2^7 = 128` cap nodes, carried by π), so 8 levels separate a cap node from a leaf. A
node is the answer of a 64-byte query `left ‖ right`; a leaf digest is the answer of the leaf's
query. A row has 64 `K` words, of which the layout occupies only the last `crOcc = 35` (lane
blocks `0 … 34`; row word `t` is lane block `63 − t`), so a leaf carries those `crOcc` words
(280 bytes, little-endian) and the reader puts `64 − crOcc` zero words in front.

**The reading** (`readRow L cap p`, WP-5's `wordOf` at `ht = 15`, `wd = 64`, `lv = 7` with
`occ 15 64 = crOcc`): from the cap node `cap[p / 2^8]`, 8 times (`n = 7, …, 0`) take the
*first* log entry whose answer is the current digest (`xFindA`); it must be a 64-byte query,
else the position is an erasure; the next digest is its left half when bit `n` of `p` is `0`,
else its right half (`xDescend`). Then the first entry whose answer is the leaf digest (no size
check): the row is `64 − crOcc` zero words followed by the query's first `crOcc` little-endian
8-byte words, missing bytes as zero (`xLeafBytes`, `xRowOf`, `decLE`). A missing entry anywhere
is an erasure: the row of the empty byte string, 64 zero words.

**WP-14's obligation.** The definitions below are WP-5's (branch `lvm/FS`, `LvmCompile.lean`:
`qb`, `dg`, `win`, `findA`, `descend`, `leafBytes`, `rowOf`, `padRow`, `wordOf`), transcribed
under other names at `ht = 15`, `wd = 64`, `lv = 7` with the decoder `decLE`. WP-14 must prove
`readRow L cap p = S.wordOf L ⟨15, 64, 7, cap⟩ p` (`Lvm.FS.Scheme.wordOf`) for WP-5's scheme `S`
with `S.decK = decLE` and `S.occ 15 64 = crOcc`; `readRow_pad` restates `readRow` as `padRow`'s
term, so the proof is by unfolding (`xDescend` against `descend` by induction on the level).

**The program** `readIR bX pL capW wB`: for every `p < 2^15` it writes row word `t < 64` of
position `p` at `wB + 64 p + t` (`64 − crOcc` zero words, then the leaf's first `crOcc` words);
the sorted index at `bX`, `|L|` at tape word `pL`, cap node `c`'s four words at tape word
`capW + 4 c`. Registers `117 … 135` (`crP` … `crAd`); the lookup `lookIR4` uses `64`,
`75 … 116` and the compiler's scratch `4`.

* `readRow_length`, `readRow_erasure`, `readRow_getD`, `readRow_pad`; `crLeafW` (a leaf word as
  the machine copies it) and `crLeafW_readRow` (as a `K` element it is `readRow`'s word
  `64 − crOcc + t`); `crRowW` (a row word as the machine stores it) and `crRowW_readRow`.
* `xFindA_some`, `xFindA_none`: the first preimage is the entry at `ansIdx`; `xDescend_succ`.
* Tape facts: `cr_tape_query` (query words of an entry), `cr_win_getD` (a 32-byte half of a
  64-byte query packs to four of its words).
* `WF`, `NoLoopT` (`safe_readIR`), `outs = 0`, 563 statements; **`cost_readIR`**:
  `14 + 2^15 · 59,964` steps (`cost_crPos = 59,961` per position, `2^30.87` in all).
-/

namespace Lvm.X

open RecursionFast

/-! ## The pure reading (WP-5's, at `ht = 15`, `wd = 64`, `lv = 7`) -/

/-- The bytes of a query (WP-5's `qb`). -/
def xQb (q : ByteArray) : List UInt8 := q.data.toList

/-- The digest of the first 32 bytes of a byte string, zero-padded (WP-5's `dg`). -/
def xDg (b : List UInt8) : Digest := Vector.ofFn fun i => b.getD i 0

/-- The 32-byte window of a query at offset `k` (WP-5's `win`). -/
def xWin (q : ByteArray) (k : ℕ) : Digest := xDg ((xQb q).drop k)

/-- The first entry of the log whose answer is `v` (WP-5's `findA`). -/
def xFindA (L : Log) (v : Digest) : Option (ByteArray × Digest) := L.find? fun e => e.2 = v

/-- Walk down `n` levels from the node `v` towards position `q` (bit `n - 1` of `q` first): the
first entry answering the node must be a 64-byte query; its left half on bit `0`, else its
right (WP-5's `descend`). -/
def xDescend (L : Log) : ℕ → Digest → ℕ → Option Digest
  | 0, v, _ => some v
  | n + 1, v, q => (xFindA L v).bind fun e =>
    if e.1.size = 64 then
      xDescend L n (if q / 2 ^ n % 2 = 0 then xWin e.1 0 else xWin e.1 32) q
    else none

/-- The leaf bytes the log holds under the cap `cap` of `C_rec` at position `p` (`none`: an
erasure); WP-5's `leafBytes L ⟨15, 64, 7, cap⟩ p`. -/
def xLeafBytes (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p % 2 ^ 15 / 2 ^ (15 - 7)]?).bind fun v =>
    (xDescend L (15 - 7) v (p % 2 ^ 15)).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- **The little-endian decoder** of a `K` word: at most 8 bytes, missing bytes zero. -/
def decLE (b : List UInt8) : BF64 := BF64.ofBitVec (toWord (ofLE b))

/-- A row of `w` words from consecutive 8-byte blocks (WP-5's `rowOf`). -/
def xRowOf (dec : List UInt8 → BF64) (w : ℕ) (b : List UInt8) : List BF64 :=
  (List.range w).map fun i => dec ((b.drop (8 * i)).take 8)

/-- **The occupied words of a `C_rec` level-0 row**: a leaf carries the row's last `crOcc` words
(lane blocks `0 … 34`: the 17 stream columns and `σ'`), the reader reads the first `64 − crOcc`
as zero. The record's `recOcc` and the scheme's `occ 15 64`. -/
def crOcc : ℕ := 35

theorem crOcc_le : crOcc ≤ 64 := by decide

/-- **The row the log holds under `C_rec`'s cap at position `p`**: the first-preimage reading,
`64 − crOcc` zero words and then the leaf's first `crOcc` words; an erasure reads as the row of
the empty byte string. WP-14 proves it equal to WP-5's `S.wordOf L ⟨15, 64, 7, cap⟩ p` (with
`S.decK = decLE`, `S.occ 15 64 = crOcc`). -/
def readRow (L : Log) (cap : List Digest) (p : ℕ) : List BF64 :=
  List.replicate (64 - crOcc) 0 ++ xRowOf decLE crOcc ((xLeafBytes L cap p).getD [])

/-- **The word the decoder consumes** (`LvmXDec`'s `wd`): row word `t` at position `p`. -/
def readWd (L : Log) (cap : List Digest) (p t : ℕ) : BF64 := (readRow L cap p).getD t 0

/-! ## Facts about the reading -/

theorem decLE_nil : decLE [] = 0 := rfl

@[simp] theorem readRow_length (L : Log) (cap : List Digest) (p : ℕ) :
    (readRow L cap p).length = 64 := by
  simp [readRow, xRowOf, crOcc]

/-- Word `t < 64` of the row: zero below `64 − crOcc`, else leaf word `t − (64 − crOcc)`. -/
theorem readRow_getD (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 64) :
    (readRow L cap p).getD t 0 = if t < 64 - crOcc then 0 else
      decLE ((((xLeafBytes L cap p).getD []).drop (8 * (t - (64 - crOcc)))).take 8) := by
  have hc := crOcc_le
  rw [List.getD_eq_getElem _ _ (by rw [readRow_length]; exact ht)]
  simp only [readRow, xRowOf]
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp only [List.length_replicate] at h1; (clear * - h2 h1; omega)
  · simp only [List.length_replicate] at h1; omega
  · simp

theorem decLE_zeros : decLE (List.replicate 8 0) = 0 := by decide

/-- **The row is `Scheme.padRow`'s term** at `wd = 64`, `occ = crOcc`: the leaf's bytes after
`8 · (64 − crOcc)` zero bytes, read as 64 words. -/
theorem readRow_pad (L : Log) (cap : List Digest) (p : ℕ) :
    readRow L cap p =
      xRowOf decLE 64 (List.replicate (8 * (64 - crOcc)) 0 ++ (xLeafBytes L cap p).getD []) := by
  have hc := crOcc_le
  apply List.ext_getElem (by simp [xRowOf])
  intro t h1 h2
  have ht : t < 64 := by simpa [xRowOf] using h2
  rw [← List.getD_eq_getElem _ 0 h1, readRow_getD L cap p ht]
  simp only [xRowOf, List.getElem_map, List.getElem_range]
  split_ifs with h
  · rw [List.drop_append_of_le_length (by simp only [List.length_replicate]; (clear * - h; omega)),
      List.take_append_of_le_length (by simp only [List.length_drop, List.length_replicate]; (clear * - h; omega)),
      List.drop_replicate, List.take_replicate, Nat.min_eq_left (by (clear * - h; omega))]
    exact decLE_zeros.symm
  · have hd : (List.replicate (8 * (64 - crOcc)) (0 : UInt8) ++ (xLeafBytes L cap p).getD []).drop
        (8 * t) = ((xLeafBytes L cap p).getD []).drop (8 * (t - (64 - crOcc))) := by
      rw [List.drop_append, List.drop_replicate, Nat.sub_eq_zero_of_le (by (clear * - h; omega)),
        List.replicate_zero, List.nil_append, List.length_replicate,
        show 8 * t - 8 * (64 - crOcc) = 8 * (t - (64 - crOcc)) by (clear * - h; omega)]
    rw [hd]

/-- **An erasure reads as 64 zero words.** -/
theorem readRow_erasure {L : Log} {cap : List Digest} {p : ℕ} (h : xLeafBytes L cap p = none) :
    readRow L cap p = List.replicate 64 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_replicate, ← List.getD_eq_getElem _ 0 h1,
    readRow_getD L cap p (by simpa using h2), h]
  split_ifs
  · rfl
  · simp [decLE_nil]

/-- The first preimage is the entry at `ansIdx`. -/
theorem xFindA_eq_ansIdx (L : Log) (d : Digest) :
    xFindA L d = (ansIdx L d).bind fun k => L[k]? := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [xFindA, ansIdx, List.find?_cons, List.findIdx?_cons] at ih ⊢
    by_cases h : e.2 = d
    · simp [h]
    · simp only [h, decide_false]
      rw [ih]
      cases L.findIdx? (fun e => decide (e.2 = d)) <;> simp

theorem xFindA_some {L : Log} {d : Digest} {k : ℕ} (h : ansIdx L d = some k) :
    ∃ hk : k < L.length, xFindA L d = some L[k] := by
  obtain ⟨hk, -⟩ := ansIdx_lt h
  exact ⟨hk, by rw [xFindA_eq_ansIdx, h, Option.bind_some, List.getElem?_eq_getElem hk]⟩

theorem xFindA_none {L : Log} {d : Digest} (h : ansIdx L d = none) : xFindA L d = none := by
  rw [xFindA_eq_ansIdx, h, Option.bind_none]

/-- **One step down the tree** at level `h + 1`: the first preimage of `d` must be a 64-byte
query; bit `h` of `p` picks its half. -/
def xStep (L : Log) (p h : ℕ) (d : Digest) : Option Digest :=
  (xFindA L d).bind fun e =>
    if e.1.size = 64 then some (if p / 2 ^ h % 2 = 0 then xWin e.1 0 else xWin e.1 32) else none

theorem xDescend_succ (L : Log) (h : ℕ) (d : Digest) (p : ℕ) :
    xDescend L (h + 1) d p = (xStep L p h d).bind fun d' => xDescend L h d' p := by
  simp only [xDescend, xStep, Option.bind_assoc]
  congr 1
  funext e
  split <;> rfl

/-- The reading under a cap node `d0`: 8 steps down to the leaf digest, then the leaf's bytes. -/
def crRd (L : Log) (d0 : Digest) (p : ℕ) : Option (List UInt8) :=
  (xDescend L 8 d0 p).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- On a position of the tree, the leaf bytes are the reading under its cap node. -/
theorem xLeafBytes_eq {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ 15)
    (hpc : p / 256 < cap.length) :
    xLeafBytes L cap p = crRd L (cap[p / 256]'hpc) p := by
  unfold xLeafBytes crRd
  rw [Nat.mod_eq_of_lt hp, show (2 : ℕ) ^ (15 - 7) = 256 from rfl, List.getElem?_eq_getElem hpc]
  all_goals rfl

/-! ## Packed bytes: aligned slices (FR's `packBytes_getD`, `…_drop8`, `…_take8`) -/

theorem cr_pk_getD (l : List UInt8) (j : ℕ) :
    (packBytes l).getD j 0 = if 8 * j < l.length then toWord (ofLE ((l.drop (8 * j)).take 8))
      else 0 := by
  by_cases h : 8 * j < l.length
  · rw [if_pos h, List.getD_eq_getElem _ _ (by rw [packBytes_length]; omega)]
    simp [packBytes]
  · rw [if_neg h, List.getD_eq_default _ _ (by rw [packBytes_length]; omega)]

theorem cr_pk_drop8 (l : List UInt8) (a j : ℕ) :
    (packBytes (l.drop (8 * a))).getD j 0 = (packBytes l).getD (a + j) 0 := by
  rw [cr_pk_getD, cr_pk_getD, List.length_drop, List.drop_drop]
  by_cases h : 8 * (a + j) < l.length
  · rw [if_pos (by omega), if_pos h, show 8 * a + 8 * j = 8 * (a + j) by ring]
  · rw [if_neg (by omega), if_neg h]

theorem cr_pk_take8 (l : List UInt8) {n j : ℕ} (hj : j < n) :
    (packBytes (l.take (8 * n))).getD j 0 = (packBytes l).getD j 0 := by
  rw [cr_pk_getD, cr_pk_getD, List.length_take, List.drop_take, List.take_take]
  by_cases h : 8 * j < l.length
  · rw [if_pos (by omega), if_pos h, Nat.min_eq_left (by (clear * - hj; omega))]
  · rw [if_neg (by (clear * - h; omega)), if_neg h]

/-- A packed word is the little-endian number of its 8 bytes (zero past the end). -/
theorem cr_pk_getD' (l : List UInt8) (j : ℕ) :
    (packBytes l).getD j 0 = toWord (ofLE ((l.drop (8 * j)).take 8)) := by
  rw [cr_pk_getD]
  split
  · rfl
  · next h =>
    have h' : l.length ≤ 8 * j := by omega
    rw [List.drop_eq_nil_of_le h']; rfl

/-- A digest's four packed words as a list. -/
theorem cr_pk_digest_eq4 (d : Digest) : packBytes d.toList =
    [(packBytes d.toList).getD 0 0, (packBytes d.toList).getD 1 0, (packBytes d.toList).getD 2 0,
      (packBytes d.toList).getD 3 0] := by
  have h := packBytes_digest_length d
  match e : packBytes d.toList, h with
  | [a0, a1, a2, a3], _ => rfl

theorem cr_xDg_toList {b : List UInt8} (h : 32 ≤ b.length) : (xDg b).toList = b.take 32 := by
  apply List.ext_getElem (by simp only [xDg, Vector.toList_ofFn, List.length_ofFn, List.length_take]; omega)
  intro i h1 h2
  have hi : i < 32 := by simpa [xDg] using h1
  have hb : i < b.length := by (clear * - h hi; omega)
  simp [xDg, hb]

/-- **A 32-byte window at an aligned offset packs to four of the query's words.** -/
theorem cr_win_getD (q : ByteArray) {a : ℕ} (h : 8 * a + 32 ≤ q.size) {m : ℕ} (hm : m < 4) :
    (packBytes (xWin q (8 * a)).toList).getD m 0 = (packBytes q.data.toList).getD (a + m) 0 := by
  have hl : q.data.toList.length = q.size := Array.length_toList
  rw [xWin, xQb, cr_xDg_toList (b := q.data.toList.drop (8 * a)) (by rw [List.length_drop]; (clear * - h hl; omega)),
    show 32 = 8 * 4 from rfl,
    cr_pk_take8 _ hm, cr_pk_drop8]

/-! ## The words the machine stores -/

/-- **Leaf word `t` of a reading** as the machine copies it: packed word `t` of the leaf bytes,
`0` for an erasure. -/
def crLeafW (o : Option (List UInt8)) (t : ℕ) : Word := (packBytes (o.getD [])).getD t 0

theorem crLeafW_none (t : ℕ) : crLeafW none t = 0 := by
  simp [crLeafW, packBytes]

theorem wK_crLeafW (o : Option (List UInt8)) (t : ℕ) :
    wK (crLeafW o t) = decLE (((o.getD []).drop (8 * t)).take 8) := by
  rw [crLeafW, cr_pk_getD']; rfl

/-- **The copied leaf word as a `K` element is the row's word `64 − crOcc + t`.** -/
theorem crLeafW_readRow (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < crOcc) :
    wK (crLeafW (xLeafBytes L cap p) t) = (readRow L cap p).getD (64 - crOcc + t) 0 := by
  have hc := crOcc_le
  rw [wK_crLeafW, readRow_getD L cap p (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- **Row word `t` of a reading** as the machine stores it: `64 − crOcc` zero words, then the
leaf words `0 … crOcc − 1`. -/
def crRowW (o : Option (List UInt8)) (t : ℕ) : Word :=
  if t < 64 - crOcc then 0 else crLeafW o (t - (64 - crOcc))

theorem crRowW_none (t : ℕ) : crRowW none t = 0 := by
  simp [crRowW, crLeafW_none]

/-- **The stored word as a `K` element is the row's word.** -/
theorem crRowW_readRow (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 64) :
    wK (crRowW (xLeafBytes L cap p) t) = (readRow L cap p).getD t 0 := by
  rw [readRow_getD L cap p ht, crRowW]
  split_ifs
  · rfl
  · rw [wK_crLeafW]

/-! ## The tape: query words -/

theorem cr_size_toList (q : ByteArray) : q.data.toList.length = q.size := Array.length_toList

theorem cr_len_entries (L : Log) : 5 * L.length ≤ entryOff L L.length := by
  have := length_logEntries L
  rwa [entries_length, ← entryOff_length] at this

/-- The query words of an entry within the log's words. -/
theorem cr_entries_getD_q : ∀ (L : Log) (k : ℕ) (hk : k < L.length) (j : ℕ),
    j < (L[k].1.size + 7) / 8 →
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD
      (entryOff L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0
  | e :: L, 0, _, j, hj => by
    have hl : (packBytes e.1.data.toList).length = (e.1.size + 7) / 8 := by
      rw [packBytes_length, cr_size_toList]
    simp only [List.getElem_cons_zero] at hj ⊢
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      Nat.zero_add, bytesWords, List.cons_append]
    rw [List.getD_eq_getElem?_getD, Nat.add_comm, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  | e :: L, k + 1, hk, j, hj => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    have ih := cr_entries_getD_q L k (by simp at hk; omega) j hj
    rw [ho, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entry_length]; (clear * - hk; omega)), ← List.getD_eq_getElem?_getD, entry_length]
    simp only [List.getElem_cons_succ]
    rw [← ih]
    congr 1
    (clear * - hk; omega)

/-- **The tape at entry `k`'s query**: word `j < ⌈|q|/8⌉` of `packBytes q`. -/
theorem cr_tape_query {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    {k : ℕ} (hk : k < L.length) {j : ℕ} (hj : j < (L[k].1.size + 7) / 8) :
    (extractorInput c π L).getD (posE4 pL L k + 1 + j) 0 =
      (packBytes L[k].1.data.toList).getD j 0 := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> (clear * - hs hk; omega)
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, posE4, show pL + 1 + entryOff L k + 1 + j =
      (pL + 1) + (entryOff L k + 1 + j) by (clear * - hk; omega), ← hl, List.getElem?_append_right (by (clear * - hk; omega)),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact cr_entries_getD_q L k hk j hj

/-! ## Registers (user registers `117 … 135`) -/

/-- The position `p`. -/ def crP : ℕ := 117
/-- `1` while the walk has found every entry. -/ def crOk : ℕ := 118
/-- The height loop's counter (the current height). -/ def crHc : ℕ := 119
/-- The height count (`8`). -/ def crNH : ℕ := 120
/-- The entry's tape position. -/ def crX : ℕ := 121
/-- The entry's query length. -/ def crQn : ℕ := 122
/-- Scratch (flags, the child's offset). -/ def crB : ℕ := 123
/-- A tape address. -/ def crTA : ℕ := 124
/-- The store address. -/ def crWA : ℕ := 125
/-- `8 t` in the copy. -/ def cr8 : ℕ := 126
/-- The copy's mask. -/ def crMk : ℕ := 127
/-- The copy's counter. -/ def crCw : ℕ := 128
/-- The copy's count (`64 − crOcc`, then `crOcc`). -/ def crNw : ℕ := 129
/-- The position loop's counter. -/ def crCp : ℕ := 130
/-- The position count (`2^15`). -/ def crNp : ℕ := 131
/-- A tape word. -/ def crV : ℕ := 132
/-- Constant scratch. -/ def crK : ℕ := 133
/-- The leaf's query length, `0` if no leaf was found. -/ def crQe : ℕ := 134
/-- A heap address. -/ def crAd : ℕ := 135

/-! ## The program -/

/-- `rQ0 … rQ3 :=` tape words `crTA … crTA + 3` (`crTA` ends at `+ 3`). -/
def crLd4 : XIR :=
  .seq (.input rQ0 crTA) (.seq (.blk [.op .add crTA crTA cOne]) (.seq (.input rQ1 crTA)
    (.seq (.blk [.op .add crTA crTA cOne]) (.seq (.input rQ2 crTA)
      (.seq (.blk [.op .add crTA crTA cOne]) (.input rQ3 crTA))))))

/-- The cap node of position `p`: `crTA := capW + 4 (p >> 8)`. -/
def crCapPs (capW : ℕ) : List Prim :=
  [.const crK 8, .op .shr crB crP crK, .const crK 2, .op .shl crB crB crK,
   .const crK (toWord capW), .op .add crTA crB crK]

/-- After a successful lookup: `crX := X[lo]` (the entry's position), `crQn := |q|`. -/
def crGet (bX : ℕ) : XIR :=
  .seq (.blk [.const crK (toWord bX), .op .add crAd rLo crK]) (.seq (.load crX crAd)
    (.input crQn crX))

/-- `crB := [|q| = 64]` (a node query). -/
def crChkPs : List Prim := [.const crK 64, .op .eq crB crQn crK]

/-- The child at height `h = crHc − 1`: `crTA := X + 1 + 4 · bit_h(p)`. -/
def crChildPs : List Prim :=
  [.op .sub crB crHc cOne, .op .shr crB crP crB, .op .and crB crB cOne, .const crK 2,
   .op .shl crB crB crK, .op .add crTA crX crB, .op .add crTA crTA cOne]

/-- **One step down the tree**: look up the current digest, check that its first preimage is a
64-byte query, load the half picked by bit `h` of `p`; `crOk := 0` on a missing entry or another
length. -/
def crNode (bX pL : ℕ) : XIR :=
  .ite crOk (.seq (lookIR4 bX pL) (.ite rFd (.seq (crGet bX) (.seq (.blk crChkPs)
    (.ite crB (.seq (.blk crChildPs) crLd4) (.blk [.const crOk 0])))) (.blk [.const crOk 0])))
    (.blk [])

/-- **The leaf**: look up the leaf digest; `crQe := |q|` if found (no length check), else `0`. -/
def crLeaf (bX pL : ℕ) : XIR :=
  .seq (.blk [.const crQe 0]) (.ite crOk (.seq (lookIR4 bX pL) (.ite rFd (.seq (crGet bX)
    (.blk [.op .or crQe crQn crQn])) (.blk []))) (.blk []))

/-- One leaf word: `M[crWA] := [8 t < crQe] · tape[crTA]`; advance. -/
def crCopyBody : XIR :=
  .seq (.input crV crTA) (.seq (.blk [.op .ltu crMk cr8 crQe, .const crK 0, .op .sub crMk crK crMk,
    .op .and crV crV crMk]) (.seq (.store crWA crV)
      (.blk [.op .add crWA crWA cOne, .op .add crTA crTA cOne, .const crK 8, .op .add cr8 cr8 crK])))

/-- One zero word: `M[crWA] := crV` (`crV` holds `0`); advance. -/
def crZeroBody : XIR := .seq (.store crWA crV) (.blk [.op .add crWA crWA cOne])

/-- **The row's zero prefix**: `64 − crOcc` zero words from `crWA`. -/
def crZero : XIR :=
  .seq (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))])
    (.loopK crCw crNw (toWord (64 - crOcc)) crZeroBody)

/-- **The copy**: the row's zero prefix, then the leaf's first `crOcc` words from tape word
`X + 1` (`0` past the query). -/
def crCopy : XIR :=
  .seq crZero
    (.seq (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
      (.loopK crCw crNw (toWord crOcc) crCopyBody))

/-- **One position**: the cap node (from tape word `capW`), 8 steps down, the leaf, its row's
64 words (the zero prefix and the copy), `p += 1`. -/
def crPos (bX pL capW : ℕ) : XIR :=
  .seq (.seq (.blk (crCapPs capW)) crLd4) (.seq (.blk [.const crOk 1, .const crNH (toWord 8)])
    (.seq (.loopK crHc crNH (toWord 8) (crNode bX pL)) (.seq (crLeaf bX pL) (.seq crCopy
      (.blk [.op .add crP crP cOne])))))

/-- **The column reads of `C_rec`**: positions `0 … 2^15 − 1`, row word `t` of position `p` at
`wB + 64 p + t`; the sorted index at `bX`, `|L|` at tape word `pL`, the cap at tape word `capW`. -/
def readIR (bX pL capW wB : ℕ) : XIR :=
  .seq (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 15))])
    (.loopK crCp crNp (toWord (2 ^ 15)) (crPos bX pL capW))

/-! ## Well formed, frames, cost -/

theorem cr_wf_look (bX pL : ℕ) : WF (lookIR4 bX pL) := by
  simp +decide [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt, WF,
    Writes, Prim.dst, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2, rKc,
    rAd, rX, rPa, rKa, rG, rH, rF, cTmp, regs]

/-- `lookIR4` writes only the compiler's scratch, `rA` (`64`) and registers `75 … 116`. -/
theorem cr_look_nw (bX pL : ℕ) {r : ℕ} (h : 117 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) :
    ¬ Writes (lookIR4 bX pL) r := by
  simp [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt, Writes,
    Prim.dst, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2, rKc, rAd,
    rX, rPa, rKa, rG, rH, rF, cTmp]
  omega

theorem cr_loK_look (bX pL : ℕ) : LoK (lookIR4 bX pL) := by
  simp +decide [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt,
    LoK, Prim.dst, regs, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2,
    rKc, rAd, rX, rPa, rKa, rG, rH, rF, and_true, List.cons_append, List.nil_append]

theorem wf_readIR (bX pL capW wB : ℕ) : WF (readIR bX pL capW wB) := by
  have h1 := cr_wf_look bX pL
  have h2 : ¬ Writes (lookIR4 bX pL) 130 := cr_look_nw bX pL (by (clear * -; omega))
  have h3 : ¬ Writes (lookIR4 bX pL) 119 := cr_look_nw bX pL (by (clear * -; omega))
  simp +decide [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf,
    crCopyBody, crCopy, crZero, crZeroBody, WF, Writes, Prim.dst, crP, crOk, crHc, crNH, crX, crQn,
    crB, crTA, crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3,
    cTmp, regs, h1, h2, h3]

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`; every other
cell below `regs` is kept (`frame`). -/
theorem readIR_nw (bX pL capW wB : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) : ¬ Writes (readIR bX pL capW wB) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopy, crZero, crZeroBody, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA,
    crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  (clear * - h; omega)

/-- No tape-length loop: the read's loops are all `loopK`. -/
theorem noLoopT_readIR (bX pL capW wB : ℕ) : NoLoopT (readIR bX pL capW wB) := by
  simp [readIR, crPos, crLd4, crGet, crNode, crLeaf, crCopyBody, crCopy, crZero, crZeroBody,
    lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, NoLoopT]

/-- Loop bounds hold on every tape (no `loopT`). -/
theorem safe_readIR (I : Array Word) (t bX pL capW wB : ℕ) : Safe I t (readIR bX pL capW wB) :=
  safe_of_noLoopT (noLoopT_readIR bX pL capW wB)

/-- The compiled statement count (`progCap` is `2^20`). -/
theorem sizeIR_readIR (bX pL capW wB : ℕ) : sizeIR (readIR bX pL capW wB) = 563 := by
  simp only [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopy, crZero, crZeroBody, lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR,
    ceil8Ps, readAt, sizeIR, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem outs_readIR (bX pL capW wB t : ℕ) : outs (readIR bX pL capW wB) t = 0 := by
  simp [readIR, crPos, crLd4, crGet, crNode, crLeaf, crCopyBody, crCopy, crZero, crZeroBody,
    lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, outs]

/-- The lookup's cost (`LvmXModel`'s `cost_lookIR4`, proved again). -/
theorem cr_cost_look (bX pL t : ℕ) : cost (lookIR4 bX pL) t = 6486 := by
  simp only [lookIR4, bsBody4, foundIR4, ansLtIR, cmpTWord, eqTWord, aposIR, ceil8Ps, readAt, cost,
    blkSteps, List.length_append, List.length_cons, List.length_nil]
  norm_num

/-- **One position's cost**: 8 node steps (`8 + 8 · (6,529 + 3)`), the leaf (`6,500`), the row
(`1,163`: the zero prefix `273` and the copy of `crOcc` words), the cap node and the rest. -/
theorem cost_crPos (bX pL capW t : ℕ) : cost (crPos bX pL capW) t = 59961 := by
  have a1 : (toWord 8).toNat = 8 := toNat_toWord (by norm_num)
  have a2 : (toWord crOcc).toNat = 35 := toNat_toWord (by decide)
  have a3 : (toWord (64 - crOcc)).toNat = 29 := toNat_toWord (by decide)
  simp only [crPos, crCapPs, crLd4, crNode, crGet, crChkPs, crChildPs, crLeaf, crCopy, crZero,
    crZeroBody, crCopyBody, cost, cr_cost_look, blkSteps, List.length_cons, List.length_nil, a1, a2,
    a3]
  norm_num

/-- **The read's cost**: `14 + 2^15 · (59,961 + 3) = 1,964,900,366 ≈ 2^30.87` steps, on every
tape. -/
theorem cost_readIR (bX pL capW wB t : ℕ) :
    cost (readIR bX pL capW wB) t = 14 + 2 ^ 15 * (cost (crPos bX pL capW) t + 3) ∧
    cost (readIR bX pL capW wB) t = 1964900366 := by
  have a1 : (toWord (2 ^ 15)).toNat = 2 ^ 15 := toNat_toWord (by norm_num)
  have e : cost (readIR bX pL capW wB) t = 14 + 2 ^ 15 * (cost (crPos bX pL capW) t + 3) := by
    simp only [readIR, cost, blkSteps, List.length_cons, List.length_nil, a1]
    norm_num <;> (clear * -; omega)
  exact ⟨e, by rw [e, cost_crPos]; norm_num⟩

end Lvm.X
end
-- ===== end of `LvmXReadDefs` =====

-- ===== merged from `LvmXRead` (GOLF module merge: `LvmXRead.lean` is now a stub importing `LvmXRead2`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXRead.lean@8bff272b (sections "The
-- domain and the tape", "Straight-line blocks", "One step down the tree", "The leaf and the
-- copy", "The read at a parametric index base"): `Dom4`, `tp`, `ld4_sem`, `capLd_sem`,
-- `nodeChk_sem`, `child_sem`, `WalkSt`, `cpW`, `mask_ltu`, `Dom4.small`, `Dom4.posE_lt`,
-- `tp_posL4`, `tp_len`, `tp_q`, `nodeFlag`, `child_words`, `cpW_entry`, `look_spec`,
-- `getIR_sem`, `nodeBody_sem`, `nodeWalk`, `nodeLoop`, `colIR_sem`, `copyBody_sem`, `copyLoop`,
-- `copyIR_sem` and their `wf_`/`loK_`/`_nw` lemmas.
-- New for lvm (WP-13b): the column reads of `C_rec` (BLUEPRINT §6.2 step 4), part 2. lvm's
-- nodes are untagged 64-byte queries (a length check, no tag) and its leaves untagged rows (no
-- check; the row is `64 − crOcc` zero words, then the query's first `crOcc` words, zero past
-- the query's `⌈|q|/8⌉`).

/-!
# The column reads: blocks, one step down the tree, the leaf, the copy

On a domain tape of a SNARK proof (`RdDom`) with the sorted index `Xi` at `bX` (`Sorted4`):

* `cr_look_spec`: the lookup of a digest finds the slot of its first preimage (`ansIdx`) or
  sets `rFd = 0`; it keeps the heap and the registers from `117` on.
* `cr_node_sem`: one machine step down the tree is `xStep`; `cr_nodeLoop`: the 8 steps keep the
  walk's state `crWalk` (the reading under the cap node is the reading under the current
  digest, or the walk has stopped and the reading is an erasure).
* `cr_leaf_sem`: after the leaf lookup, `crQe` and `crX` are such that the copy stores the leaf
  words of the reading (`crCpW`, `crLeafW`); `cr_zero_sem`: the row's `64 − crOcc` zero words;
  `cr_copy_sem`: the row of 64 words, the zero prefix and then `crOcc` copied words (`crCpRow`).
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The domain and the tape -/

/-- The tape as the machine reads it. -/
abbrev crTape (c : Digest) (π : Proof) (L : Log) : Array Word := (extractorInput c π L).toArray

/-- A domain tape of a SNARK proof whose `|L|` sits at tape word `pL` (`5 + ⌈|π|/8⌉ = pL`). -/
structure RdDom (pL : ℕ) (c : Digest) (π : Proof) (L : Log) : Prop where
  hs : 5 + (π.size + 7) / 8 = pL
  hq : ∀ e ∈ L, e.1.size < 2 ^ 64
  ht : (extractorInput c π L).length ≤ 2 ^ 64

/-! ## Straight-line blocks -/

theorem cr_wf_ld4 : WF crLd4 := by
  simp +decide only [crLd4, WF, Prim.dst, rQ0, rQ1, rQ2, rQ3, crTA, and_true]

theorem cr_lo_ld4 : Lo crLd4 := by
  simp +decide only [crLd4, Lo, Prim.dst, regs, rQ0, rQ1, rQ2, rQ3, crTA, and_true]

/-- **Four tape words** into `rQ0 … rQ3`. -/
theorem cr_ld4_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : a + 3 < 2 ^ 64)
    (hA : rd s.M crTA = toWord a) :
    [rd (semXIR I crLd4 s).M rQ0, rd (semXIR I crLd4 s).M rQ1, rd (semXIR I crLd4 s).M rQ2,
      rd (semXIR I crLd4 s).M rQ3] =
      [I.getD a 0, I.getD (a + 1) 0, I.getD (a + 2) 0, I.getD (a + 3) 0] := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [crLd4, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rQ0, rQ1, rQ2, rQ3, crTA]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hA, h1, add_one_toWord, add_one_toWord, add_one_toWord, toNat_toWord (by (clear * - ha; omega)),
    toNat_toWord (by (clear * - ha; omega)), toNat_toWord (by (clear * - ha; omega)), toNat_toWord (by omega)]

/-- **The cap node's words**: after `crCapPs ; crLd4`, `rQ0 … rQ3` hold `cap[p / 256]`. -/
theorem cr_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW : ℕ} {cap : List Digest}
    (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 256 < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ3] =
      packBytes (cap[p / 256]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (crCapPs capW)) := by simp +decide only [crCapPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hA : rd (semXIR I (.blk (crCapPs capW)) s).M crTA = toWord (capW + 4 * (p / 256)) := by
    simp only [crCapPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, show (8 : Word) = toWord 8 from rfl, shr_toWord (by (clear * - hp; omega)) (by norm_num),
      show (2 : Word) = toWord 2 from rfl, shl_toWord (by norm_num) (by (clear * - hcw he; omega)), add_toWord]
    congr 1
    (clear * -; omega)
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by (clear * - hcw he; omega)) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

/-- The node test `crChkPs`. -/
theorem cr_chk_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I (.blk crChkPs) s).M crB = bW (decide (rd s.M crQn = toWord 64)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [crChkPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, crK, crB]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [eq_bW]; rfl

/-- **The child's offset**: `crTA := X + 1 + 4 · bit_h(p)` at height `h + 1`. -/
theorem cr_child_sem (I : Array Word) (s : St) (hM : Inv s.M) {x p h : ℕ} (hp : p < 2 ^ 64)
    (hh : h + 1 < 64) (hX : rd s.M crX = toWord x) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) :
    rd (semXIR I (.blk crChildPs) s).M crTA = toWord (x + 1 + 4 * (p / 2 ^ h % 2)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [crChildPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
    [rd_set_self, rd_set_ne]
  have hb : p / 2 ^ h < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hp
  have hbit : p / 2 ^ h % 2 ≤ 1 := by (clear * -; omega)
  rw [hH, h1, hP, hX, show (1 : Word) = toWord 1 from rfl, sub_toWord (by (clear * - hh; omega)) (by (clear * - hh; omega)),
    Nat.add_sub_cancel, shr_toWord hp (by (clear * - hh; omega)), show (toWord 1 : Word) = 1 from rfl,
    and_one_toWord hb, show (2 : Word) = toWord 2 from rfl, shl_toWord (by (clear * -; omega)) (by (clear * - hbit; omega)),
    add_toWord, add_one_toWord]
  congr 1
  (clear * -; omega)

theorem cr_wf_chk : WF (.blk crChkPs) := by
  simp +decide only [crChkPs, WF, Prim.dst, crK, crB, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_wf_child : WF (.blk crChildPs) := by
  simp +decide only [crChildPs, WF, Prim.dst, crK, crB, crTA]

/-! ## The walk's state -/

/-- **The walk's state at height `h`**: either every entry so far was found and `rQ0 … rQ3`
hold a digest `d` whose descent from height `h` is the descent from the cap node `d₀`, or an
entry was missing (or of another length) and the descent from `d₀` is `none`. -/
def crWalk (L : Log) (d0 : Digest) (p h : ℕ) (M : Mem) : Prop :=
  (rd M crOk = 1 ∧ ∃ d : Digest, [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = packBytes d.toList ∧
    xDescend L 8 d0 p = xDescend L h d p) ∨
  (rd M crOk = 0 ∧ xDescend L 8 d0 p = none)

/-! ## The copy's word -/

/-- What the copy stores as word `t`: tape word `x + 1 + t` if `8 t < ql`, else `0`. -/
def crCpW (I : Array Word) (x : Word) (ql t : ℕ) : Word :=
  if 8 * t < ql then I.getD (x + toWord (1 + t)).toNat 0 else 0

theorem crCpW_zero (I : Array Word) (x : Word) (t : ℕ) : crCpW I x 0 t = 0 := by simp [crCpW]

/-- What the copy stores at row cell `i`: `0` in the first `64 − crOcc` cells, then copy word
`i − (64 − crOcc)`. -/
def crCpRow (I : Array Word) (x : Word) (ql i : ℕ) : Word :=
  if i < 64 - crOcc then 0 else crCpW I x ql (i - (64 - crOcc))

/-- **A copy of the leaf's words is a copy of its row** (`crRowW`). -/
theorem crCpRow_of {I : Array Word} {x : Word} {ql : ℕ} {o : Option (List UInt8)}
    (h : ∀ t, crCpW I x ql t = crLeafW o t) (i : ℕ) : crCpRow I x ql i = crRowW o i := by
  rw [crCpRow, crRowW]
  split_ifs
  · rfl
  · exact h _

theorem cr_mask_ltu (v a b : Word) :
    XOp.and.eval v (XOp.sub.eval 0 (XOp.ltu.eval a b)) = if a < b then v else 0 := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    show v &&& (0 - (if a < b then 1 else 0)) = _
    rw [if_pos h, if_pos h, h1, BitVec.and_allOnes]
  · show v &&& (0 - (if a < b then 1 else 0)) = _
    rw [if_neg h, if_neg h, BitVec.sub_self, BitVec.and_zero]
    rfl

section Read

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}

theorem RdDom.small (hD : RdDom pL c π L) : L.length < 2 ^ 62 := by
  have := tape_entries_end4 c π L hD.hs
  have := cr_len_entries L; have := hD.ht
  (clear hD; omega)

theorem RdDom.posE_lt (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) :
    posE4 pL L k + 1 + (L[k].1.size + 7) / 8 + 4 ≤ 2 ^ 64 := by
  have hend := tape_entries_end4 c π L hD.hs
  have hk1 : entryOff L (k + 1) ≤ entryOff L L.length := by
    rcases Nat.lt_or_ge (k + 1) L.length with h | h
    · exact (entryOff_lt L h le_rfl).le
    · rw [show k + 1 = L.length by (clear * - hk h; omega)]
  rw [entryOff_succ L hk] at hk1
  have hqw : qWords L[k] = 5 + (L[k].1.size + 7) / 8 := rfl
  have := hD.ht
  simp only [posE4]; (clear * - hk hend hk1 hqw this; omega)

theorem cr_tp_posL (hD : RdDom pL c π L) : (crTape c π L).getD pL 0 = toWord L.length := by
  rw [crTape, getD_toArray, tape_getD_posL4 c π L hD.hs]

/-- The entry's length word on the tape. -/
theorem cr_tp_len (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) :
    (crTape c π L).getD (posE4 pL L k) 0 = toWord L[k].1.size := by
  rw [crTape, getD_toArray]; exact tape_entry4 c π L hD.hs hk

/-- The entry's query words on the tape. -/
theorem cr_tp_q (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) {j : ℕ}
    (hj : j < (L[k].1.size + 7) / 8) :
    (crTape c π L).getD (posE4 pL L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0 := by
  rw [crTape, getD_toArray]; exact cr_tape_query c π L hD.hs hk hj

/-- **The machine's node test is WP-5's `e.1.size = 64`.** -/
theorem cr_nodeFlag (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) :
    decide ((crTape c π L).getD (posE4 pL L k) 0 = toWord 64) = decide (L[k].1.size = 64) := by
  have hq := hD.hq _ (List.getElem_mem hk)
  rw [cr_tp_len hD hk]
  exact decide_eq_decide.mpr ⟨fun e => by
    have := congrArg BitVec.toNat e
    rwa [toNat_toWord hq, toNat_toWord (by norm_num)] at this, fun e => by rw [e]⟩

/-- **The child's words**: on a 64-byte node query, the tape words at `X + 1 + 4 b` are the
half `b` picks (WP-5's `win e.1 0` or `win e.1 32`). -/
theorem cr_child_words (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length)
    (h64 : L[k].1.size = 64) {b : ℕ} (hb : b ≤ 1) :
    [(crTape c π L).getD (posE4 pL L k + 1 + 4 * b) 0,
      (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + 1) 0,
      (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + 2) 0,
      (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + 3) 0] =
      packBytes (if b = 0 then xWin L[k].1 0 else xWin L[k].1 32).toList := by
  have e : (if b = 0 then xWin L[k].1 0 else xWin L[k].1 32) = xWin L[k].1 (8 * (4 * b)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> rfl
  rw [e, cr_pk_digest_eq4]
  have w : ∀ m < 4, (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + m) 0 =
      (packBytes (xWin L[k].1 (8 * (4 * b))).toList).getD m 0 := fun m hm => by
    rw [cr_win_getD L[k].1 (a := 4 * b) (by (clear * - hk h64 hb; omega)) hm,
      ← cr_tp_q hD hk (j := 4 * b + m) (by (clear * - hk h64 hb hm; omega))]
    congr 1
    (clear * - hk; omega)
  rw [← w 0 (by decide), ← w 1 (by decide), ← w 2 (by decide), ← w 3 (by decide)]
  simp only [Nat.add_zero]

/-- **The copy of a found leaf is its packed words.** -/
theorem cr_cpW_entry (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) (t : ℕ) :
    crCpW (crTape c π L) (toWord (posE4 pL L k)) L[k].1.size t =
      crLeafW (some (xQb L[k].1)) t := by
  have hxl := hD.posE_lt hk
  rw [crCpW, crLeafW, Option.getD_some, xQb]
  by_cases ht : 8 * t < L[k].1.size
  · rw [if_pos ht, toWord_add, toNat_toWord (by (clear * - hk hxl ht; omega)),
      show posE4 pL L k + (1 + t) = posE4 pL L k + 1 + t by (clear * - hk; omega), cr_tp_q hD hk (by (clear * - hk ht; omega))]
  · rw [if_neg ht, cr_pk_getD, if_neg (by rw [cr_size_toList]; omega)]

theorem cr_wf_get : WF (crGet bX) := by
  simp +decide [crGet, WF, Prim.dst, crK, crAd, crX, crQn, and_true]

theorem cr_lo_get : Lo (crGet bX) := by
  simp +decide [crGet, Lo, Prim.dst, regs, crK, crAd, crX, crQn, and_true]

theorem cr_wf_node : WF (crNode bX pL) := by
  have := cr_wf_look bX pL
  simp +decide only [crNode, crGet, crChkPs, crChildPs, crLd4, WF, Prim.dst, crK, crAd, crX, crQn,
    crTA, crB, crOk, rQ0, rQ1, rQ2, rQ3, this, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_loK_node : LoK (crNode bX pL) := by
  have := cr_loK_look bX pL
  simp +decide only [crNode, crGet, crChkPs, crChildPs, crLd4, LoK, Prim.dst, regs, crK, crAd,
    crX, crQn, crTA, crB, crOk, rQ0, rQ1, rQ2, rQ3, this, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

/-- The registers the walk keeps across a node step. -/
theorem cr_node_nw {r : ℕ} (hr : r = crP ∨ r = crWA ∨ r = crHc) : ¬ Writes (crNode bX pL) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r :=
    cr_look_nw bX pL (.inl (by rcases hr with rfl | rfl | rfl <;> decide))
  simp only [crNode, Writes, not_or]
  refine ⟨⟨hl, ?_⟩, ?_⟩ <;>
  rcases hr with rfl | rfl | rfl <;>
  simp +decide only [crGet, crChkPs, crChildPs, crLd4, Writes, Prim.dst, crK, crAd, crX, crQn,
    crTA, crB, crOk, rQ0, rQ1, rQ2, rQ3, crP, crWA, crHc, List.mem_cons, List.mem_nil_iff,
    exists_eq_or_imp, exists_eq_left, or_false, and_true, not_or, exists_false, not_false_eq_true,
    and_self]

theorem cr_wf_leaf : WF (crLeaf bX pL) := by
  have := cr_wf_look bX pL
  simp +decide only [crLeaf, crGet, WF, Prim.dst, crK, crAd, crX, crQn, crQe, this,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_loK_leaf : LoK (crLeaf bX pL) := by
  have := cr_loK_look bX pL
  simp +decide only [crLeaf, crGet, LoK, Prim.dst, regs, crK, crAd, crX, crQn, crQe, this,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_leaf_nw {r : ℕ} (hr : r = crP ∨ r = crWA) : ¬ Writes (crLeaf bX pL) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r :=
    cr_look_nw bX pL (.inl (by rcases hr with rfl | rfl <;> decide))
  simp only [crLeaf, Writes, not_or]
  refine ⟨?_, ⟨hl, ?_⟩, ?_⟩ <;>
  rcases hr with rfl | rfl <;>
  simp +decide only [crGet, Writes, Prim.dst, crK, crAd, crX, crQn, crQe, crP, crWA,
    List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, and_true, not_or,
    exists_false, not_false_eq_true, and_self]

variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **The lookup** on a sorted index `Xi` held in `X[0..|L|)`: the first preimage's slot when
the target is answered, `rFd = 0` otherwise; the heap and the registers from `117` on are kept. -/
theorem cr_look_spec (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) (t : Digest)
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = packBytes t.toList) :
    (∀ k, ansIdx L t = some k → ∃ b < L.length,
      rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M rLo = toWord b ∧
      rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M rFd = 1 ∧ Xi b = toWord (posE4 pL L k)) ∧
    (ansIdx L t = none → rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M rFd = 0) ∧
    (∀ x, regs ≤ x → rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M x = rd s.M x) ∧
    Inv (semXIR (crTape c π L) (lookIR4 bX pL) s).M ∧
    (∀ r, 117 ≤ r → r < regs → rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M r = rd s.M r) := by
  set I := crTape c π L with hI
  obtain ⟨l1, l2, l3⟩ := lookIR4_sem hbX hbX2 hpL I s hM (n := L.length) (X := Xi) (cr_tp_posL hD)
    hD.small hT hXs
  obtain ⟨hmono, hpure⟩ := lookup_pure4 c π L hD.hs hD.hq hD.ht hX t
  obtain ⟨b1, b2, b3⟩ := bsRun_spec (p := ltT I Xi (packBytes t.toList)) (n := L.length)
    (by have := hD.small; (clear * - this; omega)) hmono
  obtain ⟨hsome, hnone⟩ := hpure _ b1 b2 b3
  refine ⟨fun k hk => ?_, fun hk => ?_, l3, inv_sem I (cr_wf_look bX pL) hM,
    fun r hr hr2 => frame I _ s (cr_wf_look bX pL) hM r hr2 (cr_look_nw bX pL (.inl hr))⟩
  · obtain ⟨hb, e⟩ := hsome k hk
    obtain ⟨hkl, hkc⟩ := ansIdx_lt hk
    refine ⟨_, hb, l1, ?_, e⟩
    rw [l2, hXs _ hb, e, ansW_entry4 c π L hD.hs hD.hq hD.ht hkl, hkc]
    simp [hb, bW]
  · rw [l2]
    by_cases hb : (bsRun (ltT I Xi (packBytes t.toList)) 64 (0, L.length)).1 < L.length
    · rw [hXs _ hb]
      have := hnone hk _ hb
      simp [hb, bW]
      exact this
    · simp [hb, bW]

/-- **After a lookup**: the entry's position and its query length. -/
theorem cr_get_sem (I : Array Word) (s : St) (hM : Inv s.M) {b x : ℕ} (hb : b < 2 ^ 62)
    (hx : x < 2 ^ 64) (hL : rd s.M rLo = toWord b) (hX : rd s.M (bX + b) = toWord x) :
    rd (semXIR I (crGet bX) s).M crX = toWord x ∧ rd (semXIR I (crGet bX) s).M crQn = I.getD x 0 := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [crGet, semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, crK, crAd, crX, crQn]; omega))
    only [rd_set_self, rd_set_ne]
  all_goals
    rw [hL, add_toWord, toNat_toWord (by (clear * - hbX2 hb; omega)), rd_set_ne (by simp only [crAd, regs] at hbX ⊢; (clear * - hbX hbX2 hb; omega)),
      rd_set_ne (by simp only [crK, regs] at hbX ⊢; (clear * - hbX hbX2 hb; omega)), show b + bX = bX + b by (clear * -; omega), hX]
  rw [toNat_toWord hx]

/-- **One machine step down the tree is `xStep`**: from `crOk = 1` with the digest `d` in
`rQ0 … rQ3` at height `h + 1`, the step leaves `crOk = 1` and the child's digest, or `crOk = 0`
when the descent stops. -/
theorem cr_node_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {p h : ℕ}
    (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hOk : rd s.M crOk = 1) {d : Digest}
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = packBytes d.toList) :
    (∀ d', xStep L p h d = some d' → rd (semXIR (crTape c π L) (crNode bX pL) s).M crOk = 1 ∧
      [rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ0,
        rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ1,
        rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ2,
        rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ3] = packBytes d'.toList) ∧
    (xStep L p h d = none → rd (semXIR (crTape c π L) (crNode bX pL) s).M crOk = 0) := by
  set I := crTape c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [crNode, semXIR_ite, hOk, if_neg (by decide), semXIR_seq]
  obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := cr_look_spec hbX hbX2 hpL hD hX s hM hXs d hT
  have hP1 := (lk5 crP (by decide) (by decide)).trans hP
  have hH1 := (lk5 crHc (by decide) (by decide)).trans hH
  have hO1 := (lk5 crOk (by decide) (by decide)).trans hOk
  generalize semXIR I (lookIR4 bX pL) s = s1 at lk1 lk2 lk3 lk4 hP1 hH1 hO1
  have hs1 := lk4.1
  simp only [regs] at hs1
  rw [semXIR_ite]
  cases hk : ansIdx L d with
  | none =>
    have hn : xStep L p h d = none := by simp [xStep, xFindA_none hk]
    rw [lk2 hk, if_pos rfl]
    refine ⟨fun d' h' => (by rw [hn] at h'; cases h'), fun _ => ?_⟩
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [crOk]; (clear * - hs1; omega))
  | some k =>
    obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
    obtain ⟨hkL, hpre⟩ := xFindA_some hk
    rw [hfd, if_neg (by decide)]
    have hxl := hD.posE_lt hkL
    have hsm := hD.small
    obtain ⟨g1, g2⟩ := cr_get_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by (clear * - hb hkL hsm; omega))
      (by (clear * - hkL hxl; omega)) hlo (by rw [lk3 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2 hkL; omega)), hXs b hb, hxb])
    have fG : ∀ r, r = crOk ∨ r = crP ∨ r = crHc → rd (semXIR I (crGet bX) s1).M r = rd s1.M r :=
      fun r hr => frame I _ s1 (cr_wf_get (bX := bX)) lk4 r
        (by rcases hr with rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl <;>
          simp +decide [crGet, Writes, Prim.dst, crK, crAd, crX, crQn, crOk, crP, crHc, or_false])
    have hM2 := inv_sem I (cr_wf_get (bX := bX)) lk4
    rw [semXIR_seq]
    generalize semXIR I (crGet bX) s1 = s2 at g1 g2 fG hM2
    have hB := cr_chk_sem I s2 hM2
    rw [g2, cr_nodeFlag hD hkL] at hB
    have fC : ∀ r, r = crOk ∨ r = crP ∨ r = crHc ∨ r = crX →
        rd (semXIR I (.blk crChkPs) s2).M r = rd s2.M r :=
      fun r hr => frame I _ s2 cr_wf_chk hM2 r
        (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl <;>
          simp +decide only [crChkPs, Writes, Prim.dst, crK, crB, crOk, crP, crHc, crX,
            List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
    have hM3 := inv_sem I cr_wf_chk hM2
    rw [semXIR_seq]
    generalize semXIR I (.blk crChkPs) s2 = s3 at hB fC hM3
    have hs3 := hM3.1
    simp only [regs] at hs3
    rw [semXIR_ite, hB]
    by_cases hC : L[k].1.size = 64
    · rw [decide_eq_true hC, if_neg bW_ne_zero]
      have hsome : xStep L p h d =
          some (if p / 2 ^ h % 2 = 0 then xWin L[k].1 0 else xWin L[k].1 32) := by
        simp only [xStep, hpre, Option.bind_some, if_pos hC]
      refine ⟨fun d' h' => ?_, fun h' => by rw [hsome] at h'; cases h'⟩
      rw [hsome] at h'
      cases h'
      rw [semXIR_seq]
      have hA := cr_child_sem I s3 hM3 (x := posE4 pL L k) (p := p) (h := h) (by (clear * - hp hkL; omega)) hh
        (by rw [fC _ (.inr (.inr (.inr rfl))), g1])
        (by rw [fC _ (.inr (.inl rfl)), fG _ (.inr (.inl rfl)), hP1])
        (by rw [fC _ (.inr (.inr (.inl rfl))), fG _ (.inr (.inr rfl)), hH1])
      have hM4 := inv_sem I cr_wf_child hM3
      have hO4 : rd (semXIR I (.blk crChildPs) s3).M crOk = 1 := by
        rw [frame I _ s3 cr_wf_child hM3 crOk (by decide) (by
          simp +decide only [crChildPs, Writes, Prim.dst, crK, crB, crTA, crOk]), fC _ (.inl rfl),
          fG _ (.inl rfl), hO1]
      generalize semXIR I (.blk crChildPs) s3 = s4 at hA hM4 hO4
      have hbt : p / 2 ^ h % 2 ≤ 1 := by (clear * - hkL; omega)
      refine ⟨by
        rw [frame I _ s4 cr_wf_ld4 hM4 crOk (by decide) (by
          simp +decide only [crLd4, Writes, Prim.dst, rQ0, rQ1, rQ2, rQ3, crTA, crOk, or_false])]
        exact hO4, ?_⟩
      rw [cr_ld4_sem I s4 hM4 (by (clear * - hkL hxl hC hbt; omega)) hA]
      exact cr_child_words hD hkL hC hbt
    · rw [decide_eq_false hC, if_pos bW_false]
      have hnone : xStep L p h d = none := by
        simp only [xStep, hpre, Option.bind_some, if_neg hC]
      refine ⟨fun d' h' => (by rw [hnone] at h'; cases h'), fun _ => ?_⟩
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      exact rd_set_self (by simp only [crOk]; (clear * - hkL hs3; omega))

/-- **One node step keeps the walk's state**, one level down. -/
theorem cr_nodeWalk (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {p h : ℕ}
    (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hW : crWalk L d0 p (h + 1) s.M) :
    crWalk L d0 p h (semXIR (crTape c π L) (crNode bX pL) s).M := by
  rcases hW with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · obtain ⟨n1, n2⟩ := cr_node_sem hbX hbX2 hpL hD hX s hM hXs hp hh hP hH hOk hT
    rw [xDescend_succ L h d p] at hc
    cases hn : xStep L p h d with
    | none =>
      rw [hn] at hc
      exact .inr ⟨n2 hn, hc⟩
    | some d' =>
      rw [hn] at hc
      obtain ⟨o1, o2⟩ := n1 d' hn
      exact .inl ⟨o1, d', o2, hc⟩
  · have e : semXIR (crTape c π L) (crNode bX pL) s = s := by
      rw [crNode, semXIR_ite, hOk, if_pos rfl]; rfl
    rw [e]; exact .inr ⟨hOk, hc⟩

/-- **The height loop**: `m` node steps from height `m` reach height `0`; the heap, `crP` and
`crWA` are kept. -/
theorem cr_nodeLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {d0 : Digest} {p : ℕ} (hp : p < 2 ^ 62) :
    ∀ (m : ℕ) (s : St), m < 64 → Inv s.M → (∀ a < L.length, rd s.M (bX + a) = Xi a) →
      rd s.M crP = toWord p → rd s.M crHc = toWord m → crWalk L d0 p m s.M →
      crWalk L d0 p 0 (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      Inv (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      (∀ x, regs ≤ x → rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M x = rd s.M x) ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crP = rd s.M crP ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crWA = rd s.M crWA
  | 0, s, _, hM, _, _, _, hW => ⟨hW, hM, fun _ _ => rfl, rfl, rfl⟩
  | m + 1, s, hm, hM, hXs, hP, hH, hW => by
    set I := crTape c π L
    have h1 := cr_nodeWalk hbX hbX2 hpL hD hX s hM hXs (h := m) hp (by omega) hP hH hW
    have hM1 := inv_sem I (cr_wf_node (bX := bX) (pL := pL)) hM
    have hH1 := hframeK I (crNode bX pL) s cr_loK_node
    have fr : ∀ r, (r = crP ∨ r = crWA ∨ r = crHc) →
        rd (semXIR I (crNode bX pL) s).M r = rd s.M r :=
      fun r hr => frame I _ s (cr_wf_node (bX := bX) (pL := pL)) hM r
        (by rcases hr with rfl | rfl | rfl <;> decide) (cr_node_nw hr)
    have hM' : Inv (decS crHc (semXIR I (crNode bX pL) s)).M := inv_decS hM1 (by decide)
    have hHc : rd (decS crHc (semXIR I (crNode bX pL) s)).M crHc = toWord m :=
      rd_decS_self hM1 (by decide) (by rw [fr _ (.inr (.inr rfl)), hH]) (by omega)
    have dk : ∀ r, r ≠ crHc → rd (decS crHc (semXIR I (crNode bX pL) s)).M r =
        rd (semXIR I (crNode bX pL) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hW' : crWalk L d0 p m (decS crHc (semXIR I (crNode bX pL) s)).M := by
      unfold crWalk at h1 ⊢
      rw [dk crOk (by decide), dk rQ0 (by decide), dk rQ1 (by decide), dk rQ2 (by decide),
        dk rQ3 (by decide)]
      exact h1
    have hHp : ∀ x, regs ≤ x → rd (decS crHc (semXIR I (crNode bX pL) s)).M x = rd s.M x :=
      fun x hx => (dk x (by simp only [crHc, regs] at *; omega)).trans (hH1 x hx)
    obtain ⟨a1, a2, a3, a4, a5⟩ := cr_nodeLoop hD hX hp m _ (by omega) hM'
      (fun a ha => by rw [hHp _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
      (by rw [dk _ (by decide), fr _ (.inl rfl), hP]) hHc hW'
    simp only [iterL]
    refine ⟨a1, a2, fun x hx => (a3 x hx).trans (hHp x hx), ?_, ?_⟩
    · rw [a4, dk _ (by decide), fr _ (.inl rfl)]
    · rw [a5, dk _ (by decide), fr _ (.inr (.inl rfl))]

/-- **The leaf**: after `crLeaf`, `crX` and `crQe` are such that the copy stores the leaf words of
the reading under the cap node `d₀` (`crLeafW`, zeros for an erasure). -/
theorem cr_leaf_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {p : ℕ}
    (hW : crWalk L d0 p 0 s.M) :
    ∃ ql < 2 ^ 64, rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crQe = toWord ql ∧
      ∀ t, crCpW (crTape c π L) (rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crX) ql t =
        crLeafW (crRd L d0 p) t := by
  set I := crTape c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [crLeaf, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const crQe 0]) (by simp +decide only [WF, Prim.dst, crQe]) hM
  have hQ0 : rd (semXIR I (.blk [.const crQe 0]) s).M crQe = toWord 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [crQe]; (clear * - hs; omega))
  have fr0 : ∀ r, r ≠ crQe → rd (semXIR I (.blk [.const crQe 0]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  have hXs0 : ∀ a < L.length, rd (semXIR I (.blk [.const crQe 0]) s).M (bX + a) = Xi a :=
    fun a ha => by rw [fr0 _ (by simp only [crQe, regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a ha]
  have hW0 : crWalk L d0 p 0 (semXIR I (.blk [.const crQe 0]) s).M := by
    unfold crWalk at hW ⊢
    rw [fr0 crOk (by decide), fr0 rQ0 (by decide), fr0 rQ1 (by decide), fr0 rQ2 (by decide),
      fr0 rQ3 (by decide)]
    exact hW
  generalize semXIR I (.blk [.const crQe 0]) s = s0 at hM0 hQ0 hXs0 hW0
  have hs0 := hM0.1
  simp only [regs] at hs0
  rw [semXIR_ite]
  rcases hW0 with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · rw [hOk, if_neg (by decide), semXIR_seq]
    have hrd : crRd L d0 p = (xFindA L d).map fun e => xQb e.1 := by
      rw [crRd, hc]; rfl
    rw [hrd]
    obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := cr_look_spec hbX hbX2 hpL hD hX s0 hM0 hXs0 d hT
    have hQ1 := (lk5 crQe (by decide) (by decide)).trans hQ0
    generalize semXIR I (lookIR4 bX pL) s0 = s1 at lk1 lk2 lk3 lk4 hQ1
    have hs1 := lk4.1
    simp only [regs] at hs1
    rw [semXIR_ite]
    cases hk : ansIdx L d with
    | none =>
      rw [lk2 hk, if_pos rfl, xFindA_none hk]
      refine ⟨0, by norm_num, hQ1, fun t => ?_⟩
      simp [crCpW_zero, crLeafW_none]
    | some k =>
      obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
      obtain ⟨hkL, hpre⟩ := xFindA_some hk
      rw [hfd, if_neg (by decide), hpre, Option.map_some]
      have hxl := hD.posE_lt hkL
      have hsm := hD.small
      have hq := hD.hq _ (List.getElem_mem hkL)
      obtain ⟨g1, g2⟩ := cr_get_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by (clear * - hb hkL hsm; omega))
        (by (clear * - hkL hxl hq; omega)) hlo (by rw [lk3 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2 hkL; omega)), hXs0 b hb, hxb])
      have hM2 := inv_sem I (cr_wf_get (bX := bX)) lk4
      rw [semXIR_seq]
      generalize semXIR I (crGet bX) s1 = s2 at g1 g2 hM2
      have hs2 := hM2.1
      simp only [regs] at hs2
      refine ⟨L[k].1.size, hq, ?_, fun t => ?_⟩
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [crQe]; (clear * - hkL hs2; omega)), g2, cr_tp_len hD hkL, or_self_eval]
      · have e : rd (semXIR I (.blk [.op .or crQe crQn crQn]) s2).M crX =
            toWord (posE4 pL L k) := by
          simp only [semXIR, runPrims, List.foldl, Prim.run]
          rw [rd_set_ne (by decide), g1]
        rw [e, cr_cpW_entry hD hkL t]
  · rw [hOk, if_pos rfl]
    have hrd : crRd L d0 p = none := by rw [crRd, hc]; rfl
    rw [hrd]
    refine ⟨0, by norm_num, by
      show rd (runPrims [] s0.M) crQe = _
      rw [runPrims_nil, hQ0], fun t => ?_⟩
    rw [crCpW_zero, crLeafW_none]

end Read

/-! ## The copy -/

theorem cr_wf_copyBody : WF crCopyBody := by
  simp +decide only [crCopyBody, WF, Prim.dst, crV, crMk, crK, crWA, crTA, cr8, cTmp, and_true]

/-- **One copy step**: cell `a + j` gets `crCpW I x ql j`; the pointers advance. -/
theorem cr_copyBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a j : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a + j) (ha2 : a + j + 1 < 2 ^ 64) (hj : 8 * (j + 1) < 2 ^ 64)
    (has : a + j < s.M.size) (hA : rd s.M crWA = toWord (a + j))
    (hT : rd s.M crTA = x + toWord (1 + j)) (h8 : rd s.M cr8 = toWord (8 * j))
    (hQ : rd s.M crQe = toWord ql) :
    rd (semXIR I crCopyBody s).M (a + j) = crCpW I x ql j ∧
    (∀ y, regs ≤ y → y ≠ a + j → rd (semXIR I crCopyBody s).M y = rd s.M y) ∧
    rd (semXIR I crCopyBody s).M crWA = toWord (a + (j + 1)) ∧
    rd (semXIR I crCopyBody s).M crTA = x + toWord (1 + (j + 1)) ∧
    rd (semXIR I crCopyBody s).M cr8 = toWord (8 * (j + 1)) ∧
    rd (semXIR I crCopyBody s).M crQe = toWord ql ∧
    rd (semXIR I crCopyBody s).M crP = rd s.M crP := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs ha
  -- the masked word
  have wf1 : WF (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
      .op .sub crMk crK crMk, .op .and crV crV crMk])) := by
    simp +decide only [WF, Prim.dst, crV, crMk, crK, and_true]
  have v1 : rd (semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
      .op .sub crMk crK crMk, .op .and crV crV crMk])) s).M crV = crCpW I x ql j := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crV, crMk, crK]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hT, h8, hQ, cr_mask_ltu, crCpW]
    by_cases hc : 8 * j < ql
    · rw [if_pos ((toWord_lt_toWord (by (clear * - hj; omega)) hql).2 hc), if_pos hc]
    · rw [if_neg (fun h => hc ((toWord_lt_toWord (by (clear * - hj; omega)) hql).1 h)), if_neg hc]
  have fr1 : ∀ r, r = crWA ∨ r = crTA ∨ r = cr8 ∨ r = crQe ∨ r = crP ∨ r = cOne →
      rd (semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
        .op .sub crMk crK crMk, .op .and crV crV crMk])) s).M r = rd s.M r := fun r hr =>
    frame I _ s wf1 hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [Writes, Prim.dst, crV, crMk, crK, crWA, crTA, cr8, crQe, crP, cOne,
          or_false])
  have hh1 : ∀ y, regs ≤ y → rd (semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe,
      .const crK 0, .op .sub crMk crK crMk, .op .and crV crV crMk])) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, crV, crMk, crK, and_true])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
      .op .sub crMk crK crMk, .op .and crV crV crMk])) s
  have e : semXIR I crCopyBody s = semXIR I (.seq (.store crWA crV) (.blk [.op .add crWA crWA cOne,
      .op .add crTA crTA cOne, .const crK 8, .op .add cr8 cr8 crK])) (semXIR I (.seq (.input crV crTA)
      (.blk [.op .ltu crMk cr8 crQe, .const crK 0, .op .sub crMk crK crMk, .op .and crV crV crMk]))
      s) := rfl
  rw [e]
  generalize semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
    .op .sub crMk crK crMk, .op .and crV crV crMk])) s = s1 at v1 fr1 hh1 hM1 hsz1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the store
  have hA1 : rd s1.M crWA = toWord (a + j) := (fr1 _ (.inl rfl)).trans hA
  have hsz : a + j < s1.M.size := by (clear * - has hsz1; omega)
  have st : ∀ i, i ≠ cTmp → rd (storeM s1.M crWA crV) i =
      if i = a + j then rd s1.M crV else rd s1.M i := fun i hi =>
    rd_storeM hM1 hA1 (by simp only [regs]; omega) (by (clear * - ha ha2; omega)) hsz (by decide) (by decide) hi
  rw [semXIR_seq]
  have e2 : semXIR I (.store crWA crV) s1 = ⟨storeM s1.M crWA crV, s1.o⟩ := rfl
  rw [e2]
  have hc1 : rd s1.M cOne = 1 := (fr1 _ (.inr (.inr (.inr (.inr (.inr rfl)))))).trans h1
  have hM2 : Inv (storeM s1.M crWA crV) := inv_sem I (P := .store crWA crV)
    (by simp +decide only [WF, crWA, cTmp]) hM1
  have hs2 := hM2.1
  simp only [regs, size_storeM] at hs2
  have reg : ∀ r, r < 256 → r ≠ cTmp → rd (storeM s1.M crWA crV) r = rd s1.M r := fun r hr hrt => by
    rw [st r hrt, if_neg (by (clear * - ha ha2 hr; omega))]
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, fun y hy hne => ?_, ?_⟩
  · rw [rd_set_ne (by simp only [cr8]; (clear * - ha ha2; omega)), rd_set_ne (by simp only [crK]; (clear * - ha ha2; omega)),
      rd_set_ne (by simp only [crTA]; (clear * - ha ha2; omega)), rd_set_ne (by simp only [crWA]; (clear * - ha ha2; omega)),
      st _ (by simp only [cTmp]; (clear * - ha ha2; omega)), if_pos rfl, v1]
  · simp only [regs] at hy
    rw [rd_set_ne (by simp only [cr8]; (clear * - hy; omega)), rd_set_ne (by simp only [crK]; (clear * - hy; omega)),
      rd_set_ne (by simp only [crTA]; (clear * - hy; omega)), rd_set_ne (by simp only [crWA]; (clear * - hy; omega)),
      st _ (by simp only [cTmp]; (clear * - hy; omega)), if_neg hne, hh1 y (by simp only [regs]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, size_storeM, crWA, crTA, crK, cr8]; omega))
    only [rd_set_self, rd_set_ne]
  · rw [reg _ (by decide) (by decide), reg _ (by decide) (by decide), hA1, hc1, add_one_toWord,
      Nat.add_assoc]
  · rw [reg _ (by decide) (by decide), reg _ (by decide) (by decide), fr1 _ (.inr (.inl rfl)), hT,
      hc1]
    show x + toWord (1 + j) + 1 = _
    rw [BitVec.add_assoc, toWord_add_one, Nat.add_assoc]
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inl rfl))), h8,
      show (8 : Word) = toWord 8 from rfl, add_toWord]
    congr 1
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inr (.inl rfl)))), hQ]
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inr (.inr (.inl rfl)))))]

/-- **The copy loop**: `m` steps from word `j` store `crCpW I x ql i` at `a + i`,
`j ≤ i < j + m`. -/
theorem cr_copyLoop (I : Array Word) {x : Word} {ql a nw : ℕ} (hql : ql < 2 ^ 64) (ha : regs ≤ a)
    (ha2 : a + nw + 2 < 2 ^ 64) (hnw : nw < 2 ^ 60) :
    ∀ (m j : ℕ) (s : St), j + m ≤ nw → Inv s.M → a + nw ≤ s.M.size →
      rd s.M crWA = toWord (a + j) → rd s.M crTA = x + toWord (1 + j) →
      rd s.M cr8 = toWord (8 * j) → rd s.M crQe = toWord ql →
      (∀ i, j ≤ i → i < j + m →
        rd (iterL (semXIR I crCopyBody) crCw m s).M (a + i) = crCpW I x ql i) ∧
      (∀ y, regs ≤ y → (y < a + j ∨ a + j + m ≤ y) →
        rd (iterL (semXIR I crCopyBody) crCw m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR I crCopyBody) crCw m s).M ∧
      rd (iterL (semXIR I crCopyBody) crCw m s).M crWA = toWord (a + (j + m)) ∧
      rd (iterL (semXIR I crCopyBody) crCw m s).M crP = rd s.M crP
  | 0, j, s, _, hM, _, hA, _, _, _ =>
    ⟨fun i h1 h2 => by (clear * - h1 h2; omega), fun _ _ _ => rfl, hM, by show rd s.M crWA = _; rw [hA, Nat.add_zero],
      rfl⟩
  | m + 1, j, s, hjm, hM, hsz, hA, hT, h8, hQ => by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := cr_copyBody_sem I s hM hql
      (by simp only [regs] at *; (clear * - ha; omega)) (by (clear * - ha2 hjm; omega)) (by (clear * - hnw hjm; omega)) (by (clear * - hjm hsz; omega)) hA hT h8 hQ
    have hM1 := inv_sem I cr_wf_copyBody hM
    have hM' : Inv (decS crCw (semXIR I crCopyBody s)).M := inv_decS hM1 (by decide)
    have dk : ∀ r, r ≠ crCw → rd (decS crCw (semXIR I crCopyBody s)).M r =
        rd (semXIR I crCopyBody s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hsz' : a + nw ≤ (decS crCw (semXIR I crCopyBody s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    have hy : ∀ y, regs ≤ y → y ≠ crCw := fun y hy => by simp only [crCw, regs] at *; (clear * - hy; omega)
    obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I hql ha ha2 hnw m (j + 1) _ (by (clear * - hjm; omega)) hM' hsz'
      (by rw [dk _ (by decide), c3])
      (by rw [dk _ (by decide), c4]) (by rw [dk _ (by decide), c5]) (by rw [dk _ (by decide), c6])
    simp only [iterL]
    refine ⟨fun i h1 h2 => ?_, fun y hy1 hy2 => ?_, d3,
      by rw [d4, show j + 1 + m = j + (m + 1) by (clear * -; omega)], ?_⟩
    · by_cases hij : i = j
      · subst hij
        rw [d2 _ (by simp only [regs] at *; (clear * - ha; omega)) (.inl (by (clear * -; omega))), dk _ (hy _ (by
          simp only [regs] at *; (clear * - ha; omega))), c1]
      · exact d1 i (by (clear * - h1 hij; omega)) (by (clear * - h2; omega))
    · rw [d2 _ hy1 (by (clear * - hy2; omega)), dk _ (hy _ hy1), c2 _ hy1 (by (clear * - hy2; omega))]
    · rw [d5, dk _ (by decide), c7]

theorem cr_wf_zeroBody : WF crZeroBody := by
  simp +decide only [crZeroBody, WF, Prim.dst, crWA, cTmp, and_true]

theorem cr_wf_zero : WF crZero := by
  simp +decide only [crZero, crZeroBody, WF, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_wf_copy : WF crCopy := by
  simp +decide only [crCopy, crZero, crZeroBody, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK,
    crWA, crTA, cr8, crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true]

/-- The registers the zero prefix keeps. -/
theorem cr_zero_nw {r : ℕ} (hr : r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) :
    ¬ Writes crZero r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [crZero, crZeroBody, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, crX, crQe,
    crP, crTA, cr8, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false,
    not_or, exists_false, not_false_eq_true, and_self]

/-- **The row's zero prefix**: from `crWA = a`, cells `a … a + 63 − crOcc` get `0`; every other
heap cell is kept; `crWA` ends at `a + 64 − crOcc`. -/
theorem cr_zero_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : regs ≤ a)
    (ha2 : a + 64 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size) (hA : rd s.M crWA = toWord a) :
    (∀ i < 64 - crOcc, rd (semXIR I crZero s).M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (64 - crOcc) ≤ y) → rd (semXIR I crZero s).M y = rd s.M y) ∧
    Inv (semXIR I crZero s).M ∧ rd (semXIR I crZero s).M crWA = toWord (a + (64 - crOcc)) := by
  have hs := hM.1
  have hc := crOcc_le
  simp only [regs] at hs ha
  rw [crZero, semXIR_seq]
  have w0 : WF (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) := by
    simp +decide only [WF, Prim.dst, crV, crNw, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
      forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s
  have r0 : rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M crV = 0 ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M crNw =
        toWord (64 - crOcc) ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M crWA =
        toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crV, crNw, crWA]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hA
  have k0 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, crV, crNw, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  generalize semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨v0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M crV = 0 ∧ rd s'.M crWA = toWord (a + j) ∧ (∀ i < j, rd s'.M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + j ≤ y) → rd s'.M y = rd s.M y)
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp →
      rd (entryK crCw crNw (toWord (64 - crOcc)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK crCw crNw (toWord (64 - crOcc)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun i hi => absurd hi (by (clear * - hi; omega)), fun y hy _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), v0]
    · rw [hE _ (by decide) (by decide), a0, Nat.add_zero]
    · simp only [regs] at hy
      rw [hE _ (by simp only [crCw]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega)),
        k0 y (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 64 - crOcc → P j s' →
      P (j + 1) (decS crCw (semXIR I crZeroBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    rw [crZeroBody, semXIR_seq]
    obtain ⟨c1, c2, hM1⟩ := store_sem I s' i1 (p := crWA) (v := crV) (x := a + j) (by decide)
      (by decide) i4 (by simp only [regs]; (clear * - ha ha2; omega)) (by (clear * - ha ha2 hc hj; omega)) (by (clear * - hsz hc z0 h0 hj i2; omega))
    have z1 := size_sem I (.store crWA crV) s'
    generalize semXIR I (.store crWA crV) s' = s1 at c1 c2 hM1 z1
    have hs1 := hM1.1
    simp only [regs] at hs1
    have hdr : ∀ r, r < regs → r ≠ a + j := fun r hr => by simp only [regs] at hr; (clear * - ha ha2 hr; omega)
    have b2 : ∀ r, r ≠ crWA → rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M r = rd s1.M r :=
      fun r hr => by
        simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
    have hM2 := inv_sem I (P := .blk [.op .add crWA crWA cOne])
      (by simp +decide only [WF, Prim.dst, crWA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
        forall_eq, or_false, and_true]) hM1
    have hd : ∀ y, y ≠ crCw → rd (decS crCw (semXIR I (.blk [.op .add crWA crWA cOne]) s1)).M y =
        rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M y := fun y hy => rd_decS (Ne.symm hy) _
    have hx : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ crWA ∧ y ≠ cTmp := fun y hy => by
      simp only [regs, crCw, crWA, cTmp] at *; (clear * - hy; omega)
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, z1, i2], ?_, ?_,
      fun i hi => ?_, fun y hy hy2 => ?_⟩
    · rw [hd _ (by decide), b2 _ (by decide), c2 _ (hdr _ (by decide)) (by decide), i3]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [crWA]; (clear * - hs z0 h0 i2 z1; omega)), c2 _ (hdr _ (by decide)) (by decide), i4,
        c2 _ (hdr _ (by decide)) (by decide), show rd s'.M cOne = 1 from i1.2 0 (by decide),
        add_one_toWord, Nat.add_assoc]
    · obtain ⟨x1, x2, x3⟩ := hx (a + i) (by simp only [regs]; (clear * - ha ha2; omega))
      rw [hd _ x1, b2 _ x2]
      by_cases hij : i = j
      · subst hij; rw [c1, i3]
      · rw [c2 _ (by (clear * - hij; omega)) x3, i5 i (by (clear * - hi hij; omega))]
    · obtain ⟨x1, x2, x3⟩ := hx y hy
      rw [hd _ x1, b2 _ x2, c2 _ (by (clear * - ha ha2 hy2 x1 x2 x3; omega)) x3, i6 y hy (by (clear * - hy2 x1 x2 x3; omega))]
  have hfin := loopK_run I crZeroBody P s0 hM0 (c := crCw) (n := crNw) (K := 64 - crOcc)
    (by decide) (by decide) (by decide) n0 (by (clear * - hc; omega)) h0 hstep
  exact ⟨hfin.2.2.2.2.1, hfin.2.2.2.2.2, hfin.1, hfin.2.2.2.1⟩

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + 63` get
`crCpRow I x ql ·` (`64 − crOcc` zero words, then copy words `0 … crOcc − 1`); every other heap
cell is kept; `crWA` ends at `a + 64`. -/
theorem cr_copy_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a) (ha2 : a + 64 + 2 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < 64, rd (semXIR I crCopy s).M (a + i) = crCpRow I x ql i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 64 ≤ y) → rd (semXIR I crCopy s).M y = rd s.M y) ∧
    Inv (semXIR I crCopy s).M ∧ rd (semXIR I crCopy s).M crWA = toWord (a + 64) ∧
    rd (semXIR I crCopy s).M crP = rd s.M crP := by
  have hc := crOcc_le
  -- the zero prefix
  obtain ⟨z1, z2, hMz, az⟩ := cr_zero_sem I s hM ha (by (clear * - ha2; omega)) hsz hA
  have fz : ∀ r, (r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) →
      rd (semXIR I crZero s).M r = rd s.M r := fun r hr =>
    frame I _ s cr_wf_zero hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (cr_zero_nw hr)
  have hszz := size_sem I crZero s
  rw [crCopy, semXIR_seq]
  generalize semXIR I crZero s = s1 at z1 z2 hMz az fz hszz
  have hX1 : rd s1.M crX = x := (fz _ (.inl rfl)).trans hX
  have hQ1 : rd s1.M crQe = toWord ql := (fz _ (.inr (.inl rfl))).trans hQ
  have hP1 : rd s1.M crP = rd s.M crP := fz _ (.inr (.inr (.inl rfl)))
  -- the copy of `crOcc` words to `a' = a + (64 − crOcc)`
  have hs := hMz.1
  have h1 : rd s1.M cOne = 1 := hMz.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hMz
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)]) s1
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
    s1
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crNw = toWord crOcc ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crWA = toWord (a + (64 - crOcc) + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crP = rd s1.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ1 | exact az | (rw [hX1, h1]; all_goals rfl)
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
    s1 = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord crOcc) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord crOcc) s0.M) crCw = toWord crOcc :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord crOcc) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord crOcc) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw crOcc ⟨entryK crCw crNw (toWord crOcc) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show crOcc < 2 ^ 64 by (clear * - hc; omega))]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; (clear * - hy; omega)
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I (a := a + (64 - crOcc)) (nw := crOcc) hql
    (by (clear * - ha; omega)) (by (clear * - ha2 hc; omega)) (by (clear * - hc; omega)) crOcc 0 ⟨entryK crCw crNw (toWord crOcc) s0.M, s0.o⟩
    (by (clear * -; omega)) hME (by simp only [size_entryK]; (clear * - hsz hc hszz hsz0; omega)) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  have back : ∀ y, regs ≤ y → (y < a + (64 - crOcc) ∨ a + 64 ≤ y) →
      rd (iterL (semXIR I crCopyBody) crCw crOcc ⟨entryK crCw crNw (toWord crOcc) s0.M, s0.o⟩).M y =
        rd s1.M y := fun y hy1 hy2 => by
    rw [d2 y hy1 (by (clear * - hc hy2; omega))]
    show rd (entryK crCw crNw (toWord crOcc) s0.M) y = rd s1.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  refine ⟨fun i hi => ?_, fun y hy1 hy2 => ?_, d3, ?_, ?_⟩
  · rw [crCpRow]
    split_ifs with h
    · rw [back _ (by simp only [regs] at ha ⊢; (clear * - ha ha2 hi; omega)) (.inl (by (clear * - h; omega))), z1 i h]
    · rw [show a + i = a + (64 - crOcc) + (i - (64 - crOcc)) by (clear * - h; omega)]
      exact d1 _ (by (clear * -; omega)) (by (clear * - hc hi h; omega))
  · rw [back y hy1 (by (clear * - hc hy2; omega)), z2 y hy1 (by (clear * - hc hy2; omega))]
  · rw [d4, show a + (64 - crOcc) + (0 + crOcc) = a + 64 by (clear * - hc; omega)]
  · rw [d5]
    show rd (entryK crCw crNw (toWord crOcc) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0, hP1]

end Lvm.X
end
-- ===== end of `LvmXRead` =====

/-!
# The column reads' semantics (`readIR_sem`)

On a domain tape of a SNARK proof, after the log index (`idxIR4 bX pL`, sorted by
`idxIR4_sorted`), with `C_rec`'s cap (128 nodes) on the tape at `capW`, `readIR bX pL capW wB`
leaves in cell `wB + 64 p + t` (`p < 2^15`, `t < 64`) word `t` of the row the log holds under
the cap at position `p`: as a `K` element, `(readRow L cap p).getD t 0` (`64 − crOcc` zero
words, then the leaf's words; zeros for an erasure). It keeps every heap cell outside
`[wB, wB + 2^21)`, in particular the index at `bX`.

* `cr_pos_sem`: one position; `cr_posLoop`: positions `j … j + m − 1`;
* `readIR_sem4`: on any sorted index (`Sorted4`), words as `crRowW`;
* **`readIR_sem`**: after `idxIR4`, words as `K` elements, the frame, the index and `Inv`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

section Read2

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the row words of position `p` at `a … a + 63`; `crP := p + 1`,
`crWA := a + 64`; every other heap cell kept. -/
theorem cr_pos_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < 2 ^ 15) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + 64 + 2 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size) :
    (∀ t < 64, rd (semXIR (crTape c π L) (crPos bX pL capW) s).M (a + t) =
      crRowW (xLeafBytes L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 64 ≤ y) →
      rd (semXIR (crTape c π L) (crPos bX pL capW) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (crPos bX pL capW) s).M ∧
    rd (semXIR (crTape c π L) (crPos bX pL capW) s).M crWA = toWord (a + 64) ∧
    rd (semXIR (crTape c π L) (crPos bX pL capW) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 256 < cap.length := by rw [hcl]; omega
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (crCapPs capW)) crLd4) := ⟨by simp +decide only [crCapPs, WF, Prim.dst,
    crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (crCapPs capW)) crLd4) := ⟨by simp +decide only [crCapPs, Lo, Prim.dst,
    regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], cr_lo_ld4⟩
  have q1 := cr_capLd_sem I s hM (by rw [hcl]; omega) hcap (by omega) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [crCapPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3, crP,
        crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (crCapPs capW)) crLd4) s
  rw [crPos, semXIR_seq]
  generalize semXIR I (.seq (.blk (crCapPs capW)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord 8)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M crNH = toWord 8 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalk L (cap[p / 256]'hpc) p 8 s2.M := by
    refine .inl ⟨o2.1, cap[p / 256]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; omega) (by simp only [crNH, regs] at *; omega),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord 8) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord 8) s2.M) crHc = toWord 8 :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord 8) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord 8) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 8 < 2 ^ 64 by norm_num)]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; omega
  have hWE : crWalk L (cap[p / 256]'hpc) p 8 (entryK crHc crNH (toWord 8) s2.M) := by
    unfold crWalk at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; omega
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord 8) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord 8) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoop hbX hbX2 hpL hD hX (by omega) 8
    ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ (by norm_num) hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord 8) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord 8) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord 8) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord 8) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_sem hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; omega), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := cr_copy_sem I s4 hM4 hql ha ha2 (by omega) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I crCopy s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k1 t ht, crCpRow_of c2,
      xLeafBytes_eq hp hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; omega), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their row words' cells. -/
theorem cr_posLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ 2 ^ 15 → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + 64 * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < 64,
        rd (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M (wB + 64 * q + t) =
          crRowW (xLeafBytes L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + 64 * j ∨ wB + 64 * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : 64 * (j + 1) = 64 * j + 64 := Nat.mul_succ 64 j
    obtain ⟨b1, b2, b3, b4, b5⟩ := cr_pos_sem hbX hbX2 hpL hD hX s hM hXs hcl hcw hcap (p := j)
      (a := wB + 64 * j) (by omega) hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS crCp (semXIR I (crPos bX pL capW) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (crPos bX pL capW) s)).M r =
        rd (semXIR I (crPos bX pL capW) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; omega
    have hsz' : bX ≤ (decS crCp (semXIR I (crPos bX pL capW) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := cr_posLoop hD hX hcl hcw hcap hwB hwB2 m (j + 1) _ (by omega) hM' hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)),
          b2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : 64 * (j + 1 + m) = 64 * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by omega]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by omega) (.inl (by omega)), dk _ (hy _ (by omega)), b1 t ht]
      · exact d1 q (by omega) (by omega) t ht
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), b2 _ hy1 (by omega)]

/-- **The column reads' semantics on a sorted index**: `readIR bX pL capW wB` stores at
`wB + 64 p + t` row word `t` of the reading at position `p < 2^15` (`crRowW`, zeros for an
erasure) and keeps every heap cell outside `[wB, wB + 2^21)`. -/
theorem readIR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < 2 ^ 15, ∀ t < 64,
      rd (semXIR (crTape c π L) (readIR bX pL capW wB) s).M (wB + 64 * p + t) =
        crRowW (xLeafBytes L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 2 ^ 21 ≤ y) →
      rd (semXIR (crTape c π L) (readIR bX pL capW wB) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (readIR bX pL capW wB) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 15))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crWA = toWord (wB + 64 * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crNp = toWord (2 ^ 15) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | (rw [Nat.mul_zero, Nat.add_zero])
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s
  rw [readIR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp → rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crCp = toWord (2 ^ 15) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (2 ^ 15)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (2 ^ 15)) (crPos bX pL capW)) s0 =
      iterL (semXIR I (crPos bX pL capW)) crCp (2 ^ 15)
        ⟨entryK crCp crNp (toWord (2 ^ 15)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 2 ^ 15 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : 64 * (0 + 2 ^ 15) = 2 ^ 21 := by norm_num
  obtain ⟨d1, d2, d3⟩ := cr_posLoop hbX hbX2 hpL hD hX hcl hcw hcap hwB hwB2 (2 ^ 15) 0
    ⟨entryK crCp crNp (toWord (2 ^ 15)) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by omega) (by omega) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) y = _
  rw [hHE y hy1]

end Read2

/-- **`readIR_sem`** (BLUEPRINT §6.2 step 4). On a domain tape of a SNARK proof whose log starts
at tape word `pL`, take a state `s₂` (memory of at least `bX` words) whose `X[0..|L|)` is the
one `idxIR4 bX pL` left from `s`, with `C_rec`'s cap (128 nodes) on the tape at `capW`. After
`readIR bX pL capW wB`, cell `wB + 64 p + t` holds, as a `K` element, word `t` of the row the
log holds under the cap at position `p` (`readRow`, WP-5's first-preimage reading: `64 − crOcc`
zero words, then the leaf's words; zeros for an erasure), for every `p < 2^15`, `t < 64`; every
heap cell outside `[wB, wB + 2^21)` is kept, in particular the index; `Inv` holds. -/
theorem readIR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) :
    (∀ p < 2 ^ 15, ∀ t < 64,
      rdK (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (wB + 64 * p + t) =
        (readRow L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 2 ^ 21 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (bX + a) =
        rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := readIR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; omega)
    (.inr (by omega)), w3⟩
  rw [rdK, w1 p hp t ht', crRowW_readRow L cap p ht']

/-- **The word the decoder consumes** after the read: `readWd L cap p t` at `wB + 64 p + t`. -/
theorem readIR_readWd {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) {p t : ℕ} (hp : p < 2 ^ 15) (ht' : t < 64) :
    rdK (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (wB + 64 * p + t) =
      readWd L cap p t :=
  (readIR_sem hbX hbX2 hpL c π L hs hq ht s hM hsz s₂ hM₂ hsz₂ hX₂ hcl hcw hcap hwB hwB2).1 p hp
    t ht'

end Lvm.X
