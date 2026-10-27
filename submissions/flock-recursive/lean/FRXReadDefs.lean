-- New for `flock-recursive` (BLUEPRINT §6.2 step 3, §6.5 `read_spec`; stage S-H2, track L-ext).
import FRXLookup

/-!
# The ladder read, level 0: the program and the facts about the tape it uses

BLUEPRINT §6.2 step 3. For every position `p < np` of level 0 (`np = 2^logN`), the program walks
from the cap entry `p / 2^sib` down the Merkle tree by first preimages (the lookup `lookIR` of
Part 7/8) and copies the column it finds into the heap: word `w < 128` of position `p` at cell
`colBase + 128 p + w`. A missing entry or a query of the wrong shape gives the column `none`,
stored as zeros: the reading of `FRMerkle.colL (frEnc 0)` and of S-G's `wordOf` (`0` where no
column is read).

* **Pure facts** (`packBytes_getD`, `packBytes_drop8`, `packBytes_take8`, `bytesAt_toList`):
  aligned slices of packed bytes are slices of the packed words.
* **The tape** (`tape_query`): the words of entry `k`'s query sit at `posE L k + 1 + j`;
  (`tape_cap`): cap entry `c` of π's `cap₀` field sits at `capW0 + 4c`.
* **The parsers on words** (`nodeChk_iff`, `colChk_iff`): `parseNode 0`/`parseCol 0` succeed
  iff the length word and the tag word say so (`tagNW`, `tagCW`).
* **First preimages** (`pre_eq_ansIdx`): `FRMerkle.pre` is the entry at `FRLog.ansIdx`.
* **The program** `readIR sib np` and its cost (`cost_readIR`).
-/

namespace FR.X

open RecursionFast FR.Merkle

/-! ## Packed bytes: aligned slices -/

theorem packBytes_getD (l : List UInt8) (j : ℕ) :
    (packBytes l).getD j 0 = if 8 * j < l.length then toWord (ofLE ((l.drop (8 * j)).take 8))
      else 0 := by
  by_cases h : 8 * j < l.length
  · rw [if_pos h, List.getD_eq_getElem _ _ (by rw [packBytes_length]; omega)]
    simp [packBytes]
  · rw [if_neg h, List.getD_eq_default _ _ (by rw [packBytes_length]; omega)]

theorem packBytes_drop8 (l : List UInt8) (a j : ℕ) :
    (packBytes (l.drop (8 * a))).getD j 0 = (packBytes l).getD (a + j) 0 := by
  rw [packBytes_getD, packBytes_getD, List.length_drop, List.drop_drop]
  by_cases h : 8 * (a + j) < l.length
  · rw [if_pos (by omega), if_pos h, show 8 * a + 8 * j = 8 * (a + j) by ring]
  · rw [if_neg (by omega), if_neg h]

theorem packBytes_take8 (l : List UInt8) {n j : ℕ} (hj : j < n) :
    (packBytes (l.take (8 * n))).getD j 0 = (packBytes l).getD j 0 := by
  rw [packBytes_getD, packBytes_getD, List.length_take, List.drop_take, List.take_take]
  by_cases h : 8 * j < l.length
  · rw [if_pos (by omega), if_pos h, Nat.min_eq_left (by omega)]
  · rw [if_neg (by omega), if_neg h]

theorem bytesAt_toList (q : ByteArray) {o n : ℕ} (h : o + n ≤ q.size) :
    (bytesAt q o n).toList = (q.data.toList.drop o).take n := by
  have hl : q.data.toList.length = q.size := Array.length_toList
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  have hk : k < n := by simpa using h1
  rw [Vector.getElem_toList, getElem_bytesAt _ _ _ _ hk, List.getElem_take, List.getElem_drop,
    List.getD_eq_getElem _ _ (by omega)]

/-- **An aligned 32-byte window of a byte string packs to four of its words.** -/
theorem packBytes_bytesAt (q : ByteArray) {a : ℕ} (h : 8 * a + 32 ≤ q.size) {m : ℕ}
    (hm : m < 4) : (packBytes (bytesAt q (8 * a) 32).toList).getD m 0 =
      (packBytes q.data.toList).getD (a + m) 0 := by
  rw [bytesAt_toList q h, show 32 = 8 * 4 from rfl, packBytes_take8 _ hm, packBytes_drop8]

/-- Two byte lists of length at most 8 with the same word are equal (little-endian digits). -/
theorem ofLE_inj {l l' : List UInt8} (hl : l.length = l'.length) (h : ofLE l = ofLE l') :
    l = l' := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have e := congrArg (fun x => x / 256 ^ i % 256) h
  simp only [ofLE_div_mod, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e
  exact UInt8.toNat_inj.mp e

theorem ofLE_lt64 {l : List UInt8} (hl : l.length ≤ 8) : ofLE l < 2 ^ 64 :=
  (ofLE_lt l).trans_le ((Nat.pow_le_pow_right (by norm_num) hl).trans (by norm_num))

/-- The first word of a byte string of at least 8 bytes is the word of its first 8 bytes. -/
theorem packBytes_getD0 (l : List UInt8) (hl : 8 ≤ l.length) :
    (packBytes l).getD 0 0 = toWord (ofLE (l.take 8)) := by
  rw [packBytes_getD, if_pos (by omega)]; rfl

/-- **The tag test on words**: on a string of at least 8 bytes, the first word is the tag's word
iff the first 8 bytes are the tag. -/
theorem tagWord_iff (l t : List UInt8) (hl : 8 ≤ l.length) (ht : t.length = 8) :
    (packBytes l).getD 0 0 = toWord (ofLE t) ↔ l.take 8 = t := by
  rw [packBytes_getD0 l hl]
  have h8 : (l.take 8).length = 8 := by rw [List.length_take]; omega
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [toNat_toWord (ofLE_lt64 h8.le), toNat_toWord (ofLE_lt64 ht.le)] at this
    exact ofLE_inj (h8.trans ht.symm) this
  · intro h; rw [h]

/-! ## The tag words -/

/-- The word of `"FRMNOD" ‖ 0 ‖ 0`. -/
def tagNW : Word := toWord (ofLE (tagNode 0))

/-- The word of `"FRMCOL" ‖ 0 ‖ 0`. -/
def tagCW : Word := toWord (ofLE (tagCol 0))

theorem tagNW_eq : tagNW = 0x0000444F4E4D5246 := by decide

theorem tagCW_eq : tagCW = 0x00004C4F434D5246 := by decide

theorem tagCol_length (i : ℕ) : (tagCol i).length = 8 := rfl

/-! ## The parsers on words -/

section Parse

variable (q : ByteArray)

theorem size_toList : q.data.toList.length = q.size := Array.length_toList

/-- **`parseNode 0` on words**: the length word is `72` and the first word is `tagNW`. -/
theorem nodeChk_iff (hq : q.size < 2 ^ 64) :
    (toWord q.size = toWord 72 ∧ (packBytes q.data.toList).getD 0 0 = tagNW) ↔
      (q.data.toList.take 8 = tagNode 0 ∧ q.size = 72) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hs : q.size = 72 := by
      have := congrArg BitVec.toNat h1; rwa [toNat_toWord hq, toNat_toWord (by norm_num)] at this
    exact ⟨(tagWord_iff _ _ (by rw [size_toList]; omega) (tagNode_length 0)).1 h2, hs⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h2], (tagWord_iff _ _ (by rw [size_toList]; omega) (tagNode_length 0)).2 h1⟩

theorem parseNode_eq_some (h : q.data.toList.take 8 = tagNode 0 ∧ q.size = 72) :
    parseNode 0 q = some (bytesAt q 8 32, bytesAt q 40 32) := by
  simp only [parseNode, h, and_self, ite_true]

theorem parseNode_eq_none (h : ¬ (q.data.toList.take 8 = tagNode 0 ∧ q.size = 72)) :
    parseNode 0 q = none := by
  simp only [parseNode]; rw [if_neg h]

/-- **`parseCol 0` on words**: more than 7 bytes, and the first word is `tagCW`. -/
theorem colChk_iff (hq : q.size < 2 ^ 64) :
    (toWord 7 < toWord q.size ∧ (packBytes q.data.toList).getD 0 0 = tagCW) ↔
      q.data.toList.take 8 = tagCol 0 := by
  rw [toWord_lt_toWord (by norm_num) hq]
  constructor
  · rintro ⟨h1, h2⟩
    exact (tagWord_iff _ _ (by rw [size_toList]; omega) (tagCol_length 0)).1 h2
  · intro h
    have h8 : 8 ≤ q.size := by
      have := congrArg List.length h
      rw [List.length_take, tagCol_length, size_toList] at this; omega
    exact ⟨by omega, (tagWord_iff _ _ (by rw [size_toList]; omega) (tagCol_length 0)).2 h⟩

/-- The column's words are the query's words from word 1 on. -/
theorem packBytes_col (w : ℕ) :
    (packBytes (q.extract 8 q.size).data.toList).getD w 0 =
      (packBytes q.data.toList).getD (1 + w) 0 := by
  rw [FR.toList_extract, show q.size - 8 = q.data.toList.length - 8 by rw [size_toList],
    ← List.length_drop, List.take_length, show 8 = 8 * 1 from rfl, packBytes_drop8]

end Parse

/-! ## First preimages are `ansIdx` -/

theorem pre_eq_ansIdx (L : Log) (d : Digest) :
    pre L d = (FR.Snd.ansIdx L d).bind fun k => L[k]? := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [pre, FR.Snd.ansIdx, List.find?_cons, List.findIdx?_cons] at ih ⊢
    by_cases h : e.2 = d
    · simp [h]
    · simp only [h, decide_false]
      rw [ih]
      cases L.findIdx? (fun e => decide (e.2 = d)) <;> simp

theorem pre_some {L : Log} {d : Digest} {k : ℕ} (h : FR.Snd.ansIdx L d = some k) :
    ∃ hk : k < L.length, pre L d = some L[k] := by
  obtain ⟨hk, -⟩ := FR.Snd.ansIdx_lt h
  exact ⟨hk, by rw [pre_eq_ansIdx, h, Option.bind_some, List.getElem?_eq_getElem hk]⟩

theorem pre_none {L : Log} {d : Digest} (h : FR.Snd.ansIdx L d = none) : pre L d = none := by
  rw [pre_eq_ansIdx, h, Option.bind_none]

/-! ## The tape: query words and cap entries -/

/-- The query words of an entry within the log's words. -/
theorem entries_getD_q : ∀ (L : Log) (k : ℕ) (hk : k < L.length) (j : ℕ),
    j < (L[k].1.size + 7) / 8 →
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD
      (entryOff L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0
  | e :: L, 0, _, j, hj => by
    have hl : (packBytes e.1.data.toList).length = (e.1.size + 7) / 8 := by
      rw [packBytes_length, size_toList]
    simp only [List.getElem_cons_zero] at hj ⊢
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      Nat.zero_add, bytesWords, List.cons_append]
    rw [List.getD_eq_getElem?_getD, Nat.add_comm, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  | e :: L, k + 1, hk, j, hj => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    have ih := entries_getD_q L k (by simp at hk; omega) j hj
    rw [ho, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entry_length]; omega), ← List.getD_eq_getElem?_getD, entry_length]
    simp only [List.getElem_cons_succ]
    rw [← ih]
    congr 1
    omega

/-- **The tape at entry `k`'s query**: word `j < ⌈|q|/8⌉` of `packBytes q`. -/
theorem tape_query (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {k : ℕ}
    (hk : k < L.length) {j : ℕ} (hj : j < (L[k].1.size + 7) / 8) :
    (extractorInput c π L).getD (posE L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0 := by
  have hp : π.size = 755680 := hs.trans piSize_eq
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = posL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      hp, posL, Vector.length_toList, List.length_singleton]
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, posE, show posL + 1 + entryOff L k + 1 + j =
      (posL + 1) + (entryOff L k + 1 + j) by omega, ← hl, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact entries_getD_q L k hk j hj

/-- The byte offset of the caps' field (A.3 row 12, field `fCaps`) in π. -/
def capOff : ℕ := fieldOff fCaps

theorem capOff_eq : capOff = 19168 := by
  rw [capOff, fieldOff, fieldSizes_eq]; decide

/-- **Cap entry `c` of level 0** as π carries it: the 32 bytes at `capOff + 32c` (A.3, A.2). -/
def capPi (π : Proof) (c : ℕ) : Digest := bytesAt π (capOff + 32 * c) 32

/-- The tape word of cap entry `0`'s first word. -/
def capW0 : ℕ := 5 + capOff / 8

theorem capW0_eq : capW0 = 2401 := by rw [capW0, capOff_eq]

/-- **The tape at cap entry `c < 512`**: word `m < 4` of `packBytes (capPi π c)`. -/
theorem tape_cap (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {e : ℕ}
    (he : e < 512) {m : ℕ} (hm : m < 4) :
    (extractorInput c π L).getD (capW0 + 4 * e + m) 0 = (packBytes (capPi π e).toList).getD m 0 := by
  have hp : π.size = 755680 := hs.trans piSize_eq
  have ho := capOff_eq
  rw [capPi, show capOff + 32 * e = 8 * (2396 + 4 * e) by omega,
    packBytes_bytesAt _ (by omega) hm, capW0, show 5 + capOff / 8 + 4 * e + m =
      5 + (2396 + 4 * e + m) by omega, tape_getD_proof c π L (by omega),
    List.getD_eq_getElem _ _]

/-! ## Registers (user registers `117 …`) -/

/-- The position `p`. -/ def rPp : ℕ := 117
/-- `1` while the walk has found every entry. -/ def rOk : ℕ := 118
/-- The height loop's counter (the current height). -/ def rHc : ℕ := 119
/-- The height count `sib`. -/ def rNH : ℕ := 120
/-- The entry's tape position. -/ def rXq : ℕ := 121
/-- The entry's query length. -/ def rQn : ℕ := 122
/-- Scratch (flags, the child's offset). -/ def rB : ℕ := 123
/-- A tape address. -/ def rTA : ℕ := 124
/-- The store address. -/ def rWA : ℕ := 125
/-- `8 (w + 1)` in the copy. -/ def r8 : ℕ := 126
/-- Scratch (flags, the mask). -/ def rMk : ℕ := 127
/-- The copy's counter. -/ def rCw : ℕ := 128
/-- The copy's count (`128`). -/ def rNw : ℕ := 129
/-- The position loop's counter. -/ def rCp : ℕ := 130
/-- The position count `np`. -/ def rNp : ℕ := 131
/-- A tape word. -/ def rV2 : ℕ := 132
/-- Constant scratch. -/ def rK2 : ℕ := 133
/-- The column's query length, `0` if no column was read. -/ def rQe : ℕ := 134
/-- A heap address. -/ def rAd2 : ℕ := 135

/-- The column store: word `w` of position `p` at `colBase + 128 p + w`. -/
def colBase : ℕ := 2 ^ 25

/-! ## The program -/

/-- `rQ0 … rQ3 :=` tape words `rTA … rTA + 3` (`rTA` ends at `+ 3`). -/
def ld4IR : XIR :=
  .seq (.input rQ0 rTA) (.seq (.blk [.op .add rTA rTA cOne]) (.seq (.input rQ1 rTA)
    (.seq (.blk [.op .add rTA rTA cOne]) (.seq (.input rQ2 rTA)
      (.seq (.blk [.op .add rTA rTA cOne]) (.input rQ3 rTA))))))

/-- The cap entry of position `p`: `rTA := capW0 + 4 (p >> sib)`, then its four words. -/
def capPs (sib : ℕ) : List Prim :=
  [.const rK2 (toWord sib), .op .shr rB rPp rK2, .const rK2 2, .op .shl rB rB rK2,
   .const rK2 (toWord capW0), .op .add rTA rB rK2]

/-- After a successful lookup: `rXq := X[lo]` (the entry's position), `rQn := |q|`,
`rV2 :=` the query's first word. -/
def getIR : XIR :=
  .seq (.blk [.const rK2 (toWord memX), .op .add rAd2 rLo rK2]) (.seq (.load rXq rAd2)
    (.seq (.input rQn rXq) (.seq (.blk [.op .add rTA rXq cOne]) (.input rV2 rTA))))

/-- `rB := [|q| = 72 ∧ word₀ = tagNW]` (`parseNode 0`). -/
def nodeChkPs : List Prim :=
  [.const rK2 72, .op .eq rB rQn rK2, .const rK2 tagNW, .op .eq rMk rV2 rK2, .op .and rB rB rMk]

/-- The child at height `h = rHc − 1`: `rTA := X + 2 + 4 · bit_h(p)`. -/
def childPs : List Prim :=
  [.op .sub rB rHc cOne, .op .shr rB rPp rB, .op .and rB rB cOne, .const rK2 2,
   .op .shl rB rB rK2, .op .add rTA rXq rB, .const rK2 2, .op .add rTA rTA rK2]

/-- **One step down the tree**: look up the current digest, parse its node query, load the
child digest picked by bit `h` of `p`; `rOk := 0` on a missing entry or a wrong shape. -/
def nodeBody : XIR :=
  .ite rOk (.seq lookIR (.ite rFd (.seq getIR (.seq (.blk nodeChkPs)
    (.ite rB (.seq (.blk childPs) ld4IR) (.blk [.const rOk 0])))) (.blk [.const rOk 0])))
    (.blk [])

/-- `rB := [7 < |q| ∧ word₀ = tagCW]` (`parseCol 0`). -/
def colChkPs : List Prim :=
  [.const rK2 7, .op .ltu rB rK2 rQn, .const rK2 tagCW, .op .eq rMk rV2 rK2, .op .and rB rB rMk]

/-- **The leaf**: look up the current digest and parse its column query; `rQe := |q|` on
success, else `0`. -/
def colIR : XIR :=
  .seq (.blk [.const rQe 0]) (.ite rOk (.seq lookIR (.ite rFd (.seq getIR (.seq (.blk colChkPs)
    (.ite rB (.blk [.op .or rQe rQn rQn]) (.blk [])))) (.blk []))) (.blk []))

/-- One column word: `M[rWA] := [8 (w + 1) < rQe] · tape[rTA]`; advance. -/
def copyBody : XIR :=
  .seq (.input rV2 rTA) (.seq (.blk [.op .ltu rMk r8 rQe, .const rK2 0, .op .sub rMk rK2 rMk,
    .op .and rV2 rV2 rMk]) (.seq (.store rWA rV2)
      (.blk [.op .add rWA rWA cOne, .op .add rTA rTA cOne, .const rK2 8, .op .add r8 r8 rK2])))

/-- **The copy**: the 128 column words from tape word `X + 2` (`0` past the query). -/
def copyIR : XIR :=
  .seq (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw 128])
    (.loopK rCw rNw 128 copyBody)

/-- **One position**: the cap entry, `sib` steps down, the leaf, the copy, `p += 1`. -/
def posBody (sib : ℕ) : XIR :=
  .seq (.seq (.blk (capPs sib)) ld4IR) (.seq (.blk [.const rOk 1, .const rNH (toWord sib)])
    (.seq (.loopK rHc rNH (toWord sib) nodeBody) (.seq colIR (.seq copyIR
      (.blk [.op .add rPp rPp cOne])))))

/-- **The ladder read of level 0**: positions `0 … np − 1`, `sib` node steps each. -/
def readIR (sib np : ℕ) : XIR :=
  .seq (.blk [.const rPp 0, .const rWA (toWord colBase), .const rNp (toWord np)])
    (.loopK rCp rNp (toWord np) (posBody sib))

/-- The `P30` instance (level 0: `2^18` positions, `9` node steps under a cap of `2^9`). -/
def read0 : XIR := readIR 9 (2 ^ 18)

/-! ## Well formed, cost, size -/

theorem wf_lookIR : WF lookIR := by
  simp [lookIR, bsBody, ansLtIR, cmpTWord, eqTWord, foundIR, aposIR, ceil8Ps, readAt, WF, Writes,
    Prim.dst, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2, rKc, rAd, rX,
    rPa, rKa, rG, rH, rF, cTmp, regs]

/-- `lookIR` writes only registers below `117` (none of this phase's). -/
theorem lookIR_nw {r : ℕ} (h : 117 ≤ r) : ¬ Writes lookIR r := by
  simp [lookIR, bsBody, ansLtIR, cmpTWord, eqTWord, foundIR, aposIR, ceil8Ps, readAt, Writes,
    Prim.dst, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2, rKc, rAd,
    rX, rPa, rKa, rG, rH, rF, cTmp]
  omega

theorem wf_readIR (sib np : ℕ) : WF (readIR sib np) := by
  have h1 := wf_lookIR
  have h2 : ¬ Writes lookIR 130 := lookIR_nw (by omega)
  have h3 : ¬ Writes lookIR 119 := lookIR_nw (by omega)
  simp [readIR, posBody, ld4IR, capPs, getIR, nodeChkPs, childPs, nodeBody, colChkPs, colIR,
    copyBody, copyIR, WF, Writes, Prim.dst, rPp, rOk, rHc, rNH, rXq, rQn, rB, rTA, rWA, r8, rMk,
    rCw, rNw, rCp, rNp, rV2, rK2, rQe, rAd2, rQ0, rQ1, rQ2, rQ3, cTmp, regs, h1, h2, h3]

/-- No tape-length loop: the read's loops are all `loopK`. -/
theorem noLoopT_readIR (sib np : ℕ) : NoLoopT (readIR sib np) := by
  simp [readIR, posBody, ld4IR, getIR, nodeBody, colIR, copyBody, copyIR, lookIR, bsBody, ansLtIR,
    cmpTWord, eqTWord, foundIR, aposIR, readAt, NoLoopT]

theorem outs_readIR (sib np t : ℕ) : outs (readIR sib np) t = 0 := by
  simp [readIR, posBody, ld4IR, getIR, nodeBody, colIR, copyBody, copyIR, lookIR, bsBody, ansLtIR,
    cmpTWord, eqTWord, foundIR, aposIR, readAt, outs]

theorem cost_lookIR (t : ℕ) : cost lookIR t = 6486 := by
  simp only [lookIR, bsBody, ansLtIR, cmpTWord, eqTWord, foundIR, aposIR, ceil8Ps, readAt, cost,
    blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num


/-- **The read's cost** (a constant, `≈ 2^34.07`): `2^18` positions of 10 lookups and a 128-word
copy. -/
theorem cost_read0 (t : ℕ) : cost read0 t = 18001952782 := by
  have a1 : (toWord (2 ^ 18)).toNat = 2 ^ 18 := toNat_toWord (by norm_num)
  have a2 : (toWord 9).toNat = 9 := toNat_toWord (by norm_num)
  have a3 : (128 : Word).toNat = 128 := rfl
  simp only [read0, readIR, posBody, ld4IR, capPs, getIR, nodeChkPs, childPs, nodeBody, colChkPs,
    colIR, copyBody, copyIR, cost, cost_lookIR, blkSteps, List.length_cons, List.length_nil, a1, a2,
    a3]
  norm_num

theorem sizeIR_read0 : sizeIR read0 = 570 := by
  simp only [read0, readIR, posBody, ld4IR, capPs, getIR, nodeChkPs, childPs, nodeBody, colChkPs,
    colIR, copyBody, copyIR, lookIR, bsBody, ansLtIR, cmpTWord, eqTWord, foundIR, aposIR, ceil8Ps,
    readAt, sizeIR, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem sizeIR_logIR_eq : sizeIR logIR = 294 := by
  simp only [logIR, idxIR, walkIR, walkPre, walkBody, sortIR, sortPre, passIR, passPre, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps,
    List.length_cons, List.length_nil, List.length_append]
  norm_num

/-! ## The SNARK branch with the read -/

/-- **The SNARK branch so far**: the log index, then the ladder read of level 0. -/
def decRead : XIR := .seq logIR read0

/-- **The branch meets `DecOk`**: its cost is `2592 + ⌊t/5⌋ · 11871 + 18,001,952,783`. -/
theorem decOk_decRead : DecOk decRead where
  wf := ⟨wf_logIR, wf_readIR 9 (2 ^ 18)⟩
  safe := fun c π L hs _ ht => .seq (safe_logIR (tape_count_le c π L hs ht))
    (safe_of_noLoopT (noLoopT_readIR 9 (2 ^ 18)))
  cost := fun t => by
    simp only [decRead, cost, cost_logIR, cost_read0, decBudget, fuelBase, fuelPerWord]
    have h1 : t / 5 * 11871 ≤ 2380 * t := by omega
    have h2 : (3 * 2 ^ 46 - 2 ^ 27 : ℕ) = 211106098315264 := by norm_num
    have h3 : (2 ^ 12 - 16 : ℕ) = 4080 := by norm_num
    rw [h2, h3]
    omega
  outs := fun t => by simp [decRead, outs, outs_logIR, outs_readIR, read0]
  size := by
    rw [decRead, sizeIR, sizeIR_read0, sizeIR_logIR_eq]; norm_num

end FR.X
