-- New for lvm6 (WP CA, Q_link). Season 1's lane bridge (`LvmQLinkBridge`: `LaneLink`, `linkOk_of_laneLink`)
-- re-targeted from a schedule's `plan p` to any lvm6 plan `P : List PE6`: the `q₀` of lvm6, the seed
-- `a₀ ‖ c ‖ HDR`, positions from the 128-bit draw value `N` of a named draw entry.
import Lvm6QStmt

/-!
# From lanes to the trace (Q_link, the lane bridge)

The stream words `ws` hold `Σ = 0x54 ‖ traceBytes tr`, entry `i ≥ 1` from the word `eLane6 P i`
(its length word; the query from the next word on; the answer after the query).

* **`LaneLink6 P vk c ws`**: `Q_link`'s conditions lane by lane: the stream covers the trace, the two
  constant lanes, every length lane, every chain query's state lanes, the seed's `a₀` and `c`
  lanes, every node query's selected half, every path's cap node.
* **`linkOk6_of_laneLink6`**: with the plan's static stream facts (`streamOkL6`, decided per
  `Shape`), `LaneLink6` makes the decoded trace a trace of the plan (`LinkOk6`).
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay Lvm.QLink

/-! ## Offsets of the plan's entries in the stream -/

/-- The plan's query lengths. -/
def lens6 (P : List PE6) : List ℕ := P.map PE6.len

/-- The byte offset of entry `i` in the stream. -/
def bOff6 (P : List PE6) (i : ℕ) : ℕ := 1 + slenS ((lens6 P).take i)

/-- The word of entry `i`'s length (entries `i ≥ 1` start on a word). -/
def eLane6 (P : List PE6) (i : ℕ) : ℕ := bOff6 P i / 8

/-- The first word of entry `i`'s answer (`q₀`'s answer is words 2–5). -/
def ansLane6 (P : List PE6) (i : ℕ) : ℕ :=
  if i = 0 then 2 else eLane6 P i + 1 + (P.getD i default).len / 8

/-- Bit `n` of the answer words of entry `e`. -/
def ansBit6 (P : List PE6) (ws : List Word) (e n : ℕ) : Bool :=
  (lw ws (ansLane6 P e + n / 64)).testBit (n % 64)

/-- The number of `h` answer bits of entry `e` from bit `s`. -/
def posL6 (P : List PE6) (ws : List Word) (e s h : ℕ) : ℕ :=
  ((List.range h).map fun z => if ansBit6 P ws e (s + z) then 2 ^ z else 0).sum

/-- Word 1 of every stream: the last byte of `enc64 7` (zero) and `q₀`. -/
def lane1C6 : ℕ := ofLE (0 :: q06)

/-- **`Q_link`'s conditions, lane by lane.** -/
structure LaneLink6 (P : List PE6) (c : Digest) (ws : List Word) : Prop where
  size : hashedLen6 P ≤ 8 * ws.length
  c0 : lw ws 0 = lane0C
  c1 : lw ws 1 = lane1C6
  len : ∀ i, 1 ≤ i → i < P.length → lw ws (eLane6 P i) = (P.getD i default).len
  fs : ∀ i < P.length, ∀ st g, (P.getD i default).k = .fs st g →
    ∀ l < 4, lw ws (eLane6 P i + 1 + l) = lw ws (ansLane6 P st + l)
  seed : ∀ i < P.length, (P.getD i default).k = .seed →
    (∀ l < 4, lw ws (eLane6 P i + 1 + l) = lw ws (ansLane6 P 0 + l)) ∧
      wordsBytes ((ws.drop (eLane6 P i + 5)).take 4) = c.toList
  node : ∀ i < P.length, ∀ pd sh h lvl cap, (P.getD i default).k = .node pd sh h lvl cap →
    ∀ l < 4, lw ws ((if ansBit6 P ws pd (sh + lvl) then eLane6 P i + 5 else eLane6 P i + 1) + l) =
      lw ws (eLane6 P i - 4 + l)
  cap : ∀ i < P.length, ∀ pd sh h lvl ce co path,
    (P.getD i default).k = .node pd sh h lvl (some (ce, co, path)) →
    ∀ l < 4, lw ws (eLane6 P i + 9 + l) =
      lw ws (eLane6 P ce + 1 + co / 8 + 4 * posL6 P ws pd (sh + path) (h - path) + l)

/-! ## The plan's static stream facts -/

/-- What the bridge needs of an entry (decided per `Shape`). -/
def entryOk6 (P : List PE6) (e : PE6) (i : ℕ) : Bool :=
  match e.k with
  | .q0 => i == 0 && e.len == 7
  | .seed => i == 1 && decide (64 ≤ e.len)
  | .fs st _ => decide (32 ≤ e.len) && decide (st < i) && decide (1 ≤ i)
  | .leaf => decide (1 ≤ i)
  | .node pd sh h lvl cap =>
    e.len == 64 && decide (2 ≤ i) && decide (lvl < h) && decide (sh + h ≤ 128) && decide (pd < i) &&
      decide (1 ≤ pd) &&
      (match cap with
       | none => true
       | some (ce, co, path) => co % 8 == 0 && decide (path ≤ h) && decide (32 ≤ co) &&
           decide (co + 32 * 2 ^ (h - path) ≤ (P.getD ce default).len) && decide (1 ≤ ce) && decide (ce < i))

/-- Every entry passes `entryOk6`, every length after `q₀` is whole words. -/
def streamOkL6 (P : List PE6) : Bool :=
  (P.tail.all fun e => e.len % 8 == 0) && P.zipIdx.all fun x => entryOk6 P x.1 x.2

section
variable {P : List PE6}

theorem streamOk6_entry (h : streamOkL6 P = true) {i : ℕ} (hi : i < P.length) :
    entryOk6 P (P.getD i default) i = true := by
  simp only [streamOkL6, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 (P[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]))
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem streamOk6_len (h : streamOkL6 P = true) {i : ℕ} (h1 : 1 ≤ i) (hi : i < P.length) :
    (P.getD i default).len % 8 = 0 := by
  simp only [streamOkL6, Bool.and_eq_true, List.all_eq_true] at h
  have hm : P.getD i default ∈ P.tail := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rcases P with _ | ⟨x, P⟩
    · simp at hi
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp
  simpa using h.1 _ hm

theorem lens6_length (P : List PE6) : (lens6 P).length = P.length := by simp [lens6]

theorem lens6_getD (P : List PE6) (i : ℕ) : (lens6 P).getD i 0 = (P.getD i default).len := by
  simp only [lens6, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[i]? <;> rfl

theorem bOff6_succ (P : List PE6) {i : ℕ} (hi : i < P.length) :
    bOff6 P (i + 1) = bOff6 P i + 40 + (P.getD i default).len := by
  simp only [bOff6, slenS]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [lens6_length]; exact hi)]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [← lens6_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lens6_length]; exact hi)]
  simp; omega

theorem hashedLen6_eq (P : List PE6) : hashedLen6 P = 1 + slenS (lens6 P) := by
  simp [hashedLen6, slenS, lens6, Function.comp_def]

theorem bOff6_end (P : List PE6) : bOff6 P P.length = hashedLen6 P := by
  simp only [bOff6, hashedLen6_eq]; rw [← lens6_length, List.take_length]

theorem bOff6_mono (P : List PE6) : ∀ {i j : ℕ}, i ≤ j → j ≤ P.length → bOff6 P i ≤ bOff6 P j
  | i, j, hij, hj => by
    induction j with
    | zero => have : i = 0 := by omega
              subst this; exact le_rfl
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · rw [bOff6_succ P (by omega)]; have := ih (by omega) (by omega); omega
      · have : i = j + 1 := by omega
        subst this; exact le_rfl

theorem entry6_end (P : List PE6) {i : ℕ} (hi : i < P.length) :
    bOff6 P i + 40 + (P.getD i default).len ≤ hashedLen6 P := by
  rw [← bOff6_succ P hi, ← bOff6_end]; exact bOff6_mono P (by omega) le_rfl

theorem plan0 (h : streamOkL6 P = true) (hP : 0 < P.length) : (P.getD 0 default).len = 7 ∧
    (P.getD 0 default).k = .q0 := by
  have := streamOk6_entry h hP
  rcases he : P.getD 0 default with ⟨k, len⟩
  rw [he] at this
  cases k <;> simp_all [entryOk6]

theorem bOff6_one (h : streamOkL6 P = true) (hP : 0 < P.length) : bOff6 P 1 = 48 := by
  rw [show 1 = 0 + 1 from rfl, bOff6_succ P hP, (plan0 h hP).1]; rfl

theorem bOff6_mod (h : streamOkL6 P = true) : ∀ i, 1 ≤ i → i ≤ P.length → bOff6 P i % 8 = 0
  | 0, h1, _ => absurd h1 (by omega)
  | 1, _, hi => by rw [bOff6_one h (by omega)]
  | i + 2, _, hi => by
    rw [bOff6_succ P (by omega)]
    have := bOff6_mod h (i + 1) (by omega) (by omega)
    have := streamOk6_len h (i := i + 1) (by omega) (by omega)
    omega

theorem bOff6_eq (h : streamOkL6 P = true) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ P.length) :
    bOff6 P i = 8 * eLane6 P i := by
  have := bOff6_mod h i h1 hi; simp only [eLane6]; omega

theorem eLane6_succ (h : streamOkL6 P = true) {i : ℕ} (h1 : 1 ≤ i) (hi : i < P.length) :
    eLane6 P (i + 1) = eLane6 P i + 5 + (P.getD i default).len / 8 := by
  have h8 := streamOk6_len h h1 hi
  have e1 := bOff6_eq h (i := i + 1) (by omega) (by omega)
  have e2 := bOff6_eq h h1 (by omega)
  rw [bOff6_succ P hi] at e1
  omega

theorem ansLane6_pred (h : streamOkL6 P = true) {i : ℕ} (h2 : 2 ≤ i) (hi : i < P.length) :
    ansLane6 P (i - 1) = eLane6 P i - 4 := by
  have := eLane6_succ h (i := i - 1) (by omega) (by omega)
  rw [show i - 1 + 1 = i by omega] at this
  simp only [ansLane6, show i - 1 ≠ 0 by omega, ite_false]
  omega

theorem hashedLen6_mod (h : streamOkL6 P = true) (hP : 0 < P.length) : hashedLen6 P % 8 = 0 := by
  have := bOff6_mod h P.length (by omega) le_rfl
  rwa [bOff6_end] at this

theorem hashedLen6_ge (h : streamOkL6 P = true) (hP : 0 < P.length) : 48 ≤ hashedLen6 P := by
  have := bOff6_mono P (i := 1) (j := P.length) (by omega) le_rfl
  rw [bOff6_one h hP, bOff6_end] at this; exact this

end

/-! ## The decoded entries -/

section
variable {P : List PE6} {ws : List Word}

theorem decode6_getD (P : List PE6) (ws : List Word) {i : ℕ} (hi : i < P.length) :
    (decode6 P ws).getD i dflt = entryAt (wordsBytes ws) (bOff6 P i) (P.getD i default).len := by
  rw [decode6, show P.map PE6.len = lens6 P from rfl, readEntries_getD _ _ _ _ (by rw [lens6_length]; exact hi),
    lens6_getD]; rfl

theorem decode6_length (P : List PE6) (ws : List Word) : (decode6 P ws).length = P.length := by
  rw [decode6, readEntries_length, List.length_map]

theorem bl_qOf6 (P : List PE6) (ws : List Word) {i : ℕ} (hi : i < P.length) :
    bl (qOf (decode6 P ws) i) = ((wordsBytes ws).drop (bOff6 P i + 8)).take (P.getD i default).len := by
  simp only [qOf, decode6_getD P ws hi, entryAt]; rfl

theorem aOf_toList6 (P : List PE6) (ws : List Word) {i : ℕ} (hi : i < P.length)
    (hB : bOff6 P i + 40 + (P.getD i default).len ≤ (wordsBytes ws).length) :
    (aOf (decode6 P ws) i).toList = ((wordsBytes ws).drop (bOff6 P i + 8 + (P.getD i default).len)).take 32 := by
  simp only [aOf, decode6_getD P ws hi, entryAt, Vector.toList_ofFn]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take, List.length_drop]; omega)
    fun x h1 h2 => ?_
  simp only [List.length_ofFn] at h1
  rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem qOf_size6 (P : List PE6) (ws : List Word) {i : ℕ} (hi : i < P.length)
    (hB : bOff6 P i + 40 + (P.getD i default).len ≤ (wordsBytes ws).length) :
    (qOf (decode6 P ws) i).size = (P.getD i default).len := by
  rw [size_bl, bl_qOf6 P ws hi, List.length_take, List.length_drop]; omega

theorem hB6 (hw : hashedLen6 P ≤ 8 * ws.length) {i : ℕ} (hi : i < P.length) :
    bOff6 P i + 40 + (P.getD i default).len ≤ (wordsBytes ws).length := by
  rw [wordsBytes_length]; have := entry6_end P hi; omega

/-- The answer of entry `i` is the four words at `ansLane6`. -/
theorem aOf_lanes6 (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length) {i : ℕ}
    (hi : i < P.length) :
    (aOf (decode6 P ws) i).toList = wordsBytes ((ws.drop (ansLane6 P i)).take 4) := by
  rw [aOf_toList6 P ws hi (hB6 hw hi), ← wordsBytes_slice]
  congr 2
  by_cases h0 : i = 0
  · subst h0
    simp only [ansLane6, ite_true, bOff6, List.take_zero, slenS, List.map_nil, List.sum_nil,
      (plan0 hS hi).1]
    rfl
  · have := bOff6_eq hS (i := i) (by omega) (by omega)
    have h8 := streamOk6_len hS (i := i) (by omega) hi
    simp only [ansLane6, h0, ite_false]
    omega

theorem qOf_take6 (hS : streamOkL6 P = true) {i : ℕ} (h1 : 1 ≤ i) (hi : i < P.length) {n : ℕ}
    (hn : 8 * n ≤ (P.getD i default).len) :
    (bl (qOf (decode6 P ws) i)).take (8 * n) = wordsBytes ((ws.drop (eLane6 P i + 1)).take n) := by
  rw [bl_qOf6 P ws hi, List.take_take, Nat.min_eq_left hn, ← wordsBytes_slice, bOff6_eq hS h1 (by omega)]
  congr 2

theorem qOf_drop32_6 (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length) {i : ℕ} (h1 : 1 ≤ i)
    (hi : i < P.length) (h64 : (P.getD i default).len = 64) :
    (bl (qOf (decode6 P ws) i)).drop 32 = wordsBytes ((ws.drop (eLane6 P i + 5)).take 4) := by
  rw [bl_qOf6 P ws hi, h64, List.drop_take, ← wordsBytes_slice, List.drop_drop, bOff6_eq hS h1 (by omega)]
  congr 2 <;> omega

theorem qOf_get6 (hS : streamOkL6 P = true) {i : ℕ} (h1 : 1 ≤ i)
    (hi : i < P.length) {x : ℕ} (hx : x < (P.getD i default).len) :
    (qOf (decode6 P ws) i).get! x = (wordsBytes ws).getD (8 * eLane6 P i + 8 + x) 0 := by
  rw [get!_bl, bl_qOf6 P ws hi, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hx,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD, bOff6_eq hS h1 (by omega), Nat.add_assoc]

theorem ansLane6_bound (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length) {e : ℕ}
    (he : e < P.length) : ansLane6 P e + 4 ≤ ws.length := by
  by_cases h0 : e = 0
  · subst h0
    have := entry6_end P (i := 0) he
    simp only [ansLane6, ite_true]
    have : bOff6 P 0 = 1 := rfl
    rw [(plan0 hS he).1] at *; omega
  · have h8 := streamOk6_len hS (i := e) (by omega) he
    have hb := bOff6_eq hS (i := e + 1) (by omega) (by omega)
    have := entry6_end P he
    rw [← bOff6_succ P he] at this
    have := eLane6_succ hS (i := e) (by omega) he
    simp only [ansLane6, h0, ite_false]
    omega

theorem eLane6_bound (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length) {i : ℕ} (h1 : 1 ≤ i)
    (hi : i < P.length) : 8 * eLane6 P i + 40 + (P.getD i default).len ≤ 8 * ws.length := by
  have := entry6_end P hi; rw [bOff6_eq hS h1 (by omega)] at this; omega

end

/-! ## Positions -/

theorem testBit_two (u0 u1 : ℕ) (h0 : u0 < 2 ^ 64) (n : ℕ) :
    (u0 + 2 ^ 64 * u1).testBit n = (if n < 64 then u0.testBit n else u1.testBit (n - 64)) := by
  rw [show u0 + 2 ^ 64 * u1 = 2 ^ 64 * u1 + u0 by ring, Nat.testBit_two_pow_mul_add _ h0]

theorem posOf_bit (tr : Trace) (pd sh h lvl : ℕ) (hl : lvl < h) :
    (posOf tr pd sh h >>> lvl) % 2 = 0 ↔ (drawN (aOf tr pd)).testBit (sh + lvl) = false := by
  have e := Nat.toNat_testBit (posOf tr pd sh h) lvl
  rw [← Nat.shiftRight_eq_div_pow] at e
  rw [← e]
  simp only [posOf, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hl, decide_true, Bool.true_and]
  cases (drawN (aOf tr pd)).testBit (sh + lvl) <;> simp

theorem posOf_shift (tr : Trace) (pd sh h path : ℕ) (hp : path ≤ h) :
    posOf tr pd sh h >>> path = (drawN (aOf tr pd) >>> (sh + path)) % 2 ^ (h - path) := by
  apply Nat.eq_of_testBit_eq; intro t
  simp only [posOf, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.add_assoc]
  congr 1
  simp only [decide_eq_decide]; omega

theorem posOf_lt (tr : Trace) (pd sh h : ℕ) : posOf tr pd sh h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos h)

theorem posL6_eq (P : List PE6) (ws : List Word) (A e s : ℕ) :
    ∀ k, (∀ n, s ≤ n → n < s + k → ansBit6 P ws e n = A.testBit n) → posL6 P ws e s k = (A >>> s) % 2 ^ k
  | 0, _ => by simp [posL6, Nat.mod_one]
  | k + 1, hb => by
    have ih := posL6_eq P ws A e s k (fun n h1 h2 => hb n h1 (by omega))
    simp only [posL6, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero] at ih ⊢
    rw [ih, Nat.mod_pow_succ, hb (s + k) (by omega) (by omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.toNat_testBit]
    cases A.testBit (s + k) <;> simp

theorem posL6_lt (P : List PE6) (ws : List Word) (e s : ℕ) : ∀ h, posL6 P ws e s h < 2 ^ h
  | 0 => by simp [posL6]
  | h + 1 => by
    have : posL6 P ws e s (h + 1) = posL6 P ws e s h + (if ansBit6 P ws e (s + h) then 2 ^ h else 0) := by
      simp [posL6, List.range_succ]
    rw [this, Nat.pow_succ]; have := posL6_lt P ws e s h
    split <;> omega

section
variable {P : List PE6} {ws : List Word}

/-- **A decoded answer's draw value is its first two words.** -/
theorem drawN_lanes (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length) {e : ℕ}
    (he : e < P.length) :
    drawN (aOf (decode6 P ws) e) = lw ws (ansLane6 P e) + 2 ^ 64 * lw ws (ansLane6 P e + 1) := by
  have hb := ansLane6_bound hS hw he
  have hlen : ((ws.drop (ansLane6 P e)).take 4).length = 4 := by simp; omega
  have ha := aOf_lanes6 hS hw he
  have u := fun k hk => u64At_digest hlen ha (k := k) hk
  simp only [drawN]
  rw [show (0 : ℕ) = 8 * 0 from rfl, u 0 (by omega), show (8 : ℕ) = 8 * 1 from rfl, u 1 (by omega)]
  simp only [lw, lw_of_slice (by omega : 0 < 4) (by omega), lw_of_slice (by omega : 1 < 4) (by omega),
    Nat.add_zero]

theorem testBit_drawN (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length) {e : ℕ}
    (he : e < P.length) {n : ℕ} (hn : n < 128) :
    (drawN (aOf (decode6 P ws) e)).testBit n = ansBit6 P ws e n := by
  rw [drawN_lanes hS hw he, testBit_two _ _ (lw_lt _ _), ansBit6]
  split_ifs with h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.add_zero]
  · rw [show n / 64 = 1 by omega, show n % 64 = n - 64 by omega]

end

/-! ## The bridge -/

theorem first16_6 : enc64 lane0C ++ enc64 lane1C6 =
    [0x54, 7, 0, 0, 0, 0, 0, 0, 0, 0x6C, 0x76, 0x6D, 0x36, 0x2F, 0x31, 0] := by decide

theorem wordsBytes_split (ws : List Word) (a : ℕ) :
    wordsBytes ((ws.drop a).take 8) = wordsBytes ((ws.drop a).take 4) ++ wordsBytes ((ws.drop (a + 4)).take 4) := by
  rw [show 8 = 4 + 4 from rfl, List.take_add, List.drop_drop]
  simp only [wordsBytes, List.flatMap_append, Nat.add_comm a 4]

section
variable {P : List PE6} {c : Digest} {ws : List Word}

theorem take16_6 (hS : streamOkL6 P = true) (hP : 0 < P.length) (hL : LaneLink6 P c ws) :
    (wordsBytes ws).take 16 = enc64 lane0C ++ enc64 lane1C6 := by
  have h2 : 2 ≤ ws.length := by have := hL.size; have := hashedLen6_ge hS hP; omega
  have e : ws.take 2 = [ws.getD 0 0, ws.getD 1 0] := by
    rcases ws with _ | ⟨a, _ | ⟨b, ws⟩⟩ <;> simp_all
  rw [show (16 : ℕ) = 8 * 2 from rfl, wordsBytes_take, e, ← hL.c0, ← hL.c1]
  rfl

theorem byte0_6 (hS : streamOkL6 P = true) (hP : 0 < P.length) (hL : LaneLink6 P c ws) :
    (wordsBytes ws).head? = some tagTrace := by
  have h := congrArg List.head? (take16_6 hS hP hL)
  rw [first16_6, List.head?_take] at h
  simpa [tagTrace] using h

/-- **The stream is the trace it encodes**: its first `hashedLen6 P` bytes are `tagTrace ::
traceBytes (decode6 P ws)`. -/
theorem stream_of_laneLink6 (hS : streamOkL6 P = true) (hP : 0 < P.length) (hL : LaneLink6 P c ws) :
    (wordsBytes ws).take (hashedLen6 P) = tagTrace :: traceBytes (decode6 P ws) := by
  have hlen : hashedLen6 P ≤ (wordsBytes ws).length := by rw [wordsBytes_length]; exact hL.size
  have hw : WfAt (wordsBytes ws) 1 (lens6 P) := by
    refine wfAt_of _ _ _ fun i hi => ?_
    rw [lens6_length] at hi
    rw [lens6_getD]
    by_cases h0 : i = 0
    · subst h0
      rw [(plan0 hS hP).1]
      simp only [slenS, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]
      rw [drop_take_of_take (m := 16) (by omega), take16_6 hS hP hL, first16_6]; decide
    · have e := bOff6_eq hS (i := i) (by omega) (by omega)
      simp only [bOff6] at e
      rw [e, show (8 : ℕ) = 8 * 1 from rfl, wordsBytes_slice]
      have hb := hL.len i (by omega) hi
      have hle : eLane6 P i < ws.length := by
        have := eLane6_bound hS hL.size (i := i) (by omega) hi; omega
      rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hle, Option.toList_some]
      show wordBytes _ ++ [] = _
      rw [List.append_nil, wordBytes, ← hb, lw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle,
        Option.getD_some]
  have ht := take_readEntries (wordsBytes ws) (lens6 P) 1 hw (by rw [← hashedLen6_eq]; exact hlen)
  rw [hashedLen6_eq, List.take_add, List.take_one, byte0_6 hS hP hL, Option.toList_some, ht]
  rfl

/-- **`Q_link`'s lane conditions make the decoded trace a trace of the plan.** -/
theorem linkOk6_of_laneLink6 (hS : streamOkL6 P = true) (hL : LaneLink6 P c ws) :
    LinkOk6 P c (decode6 P ws) := by
  refine ⟨decode6_length P ws, fun i hi => ?_⟩
  rw [decode6_length] at hi
  have hw := hL.size
  have hE := streamOk6_entry hS hi
  have hP : 0 < P.length := by omega
  refine ⟨qOf_size6 P ws hi (hB6 hw hi), ?_⟩
  rcases he : P.getD i default with ⟨k, len⟩
  rw [he] at hE
  cases k with
  | q0 =>
    simp only [entryOk6, Bool.and_eq_true, beq_iff_eq] at hE
    obtain ⟨rfl, rfl⟩ := hE
    show bl (qOf (decode6 P ws) 0) = q06
    rw [bl_qOf6 P ws hi, he]
    show ((wordsBytes ws).drop 9).take 7 = q06
    rw [drop_take_of_take (m := 16) (by omega), take16_6 hS hP hL, first16_6]; decide
  | seed =>
    simp only [entryOk6, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE
    obtain ⟨rfl, h64⟩ := hE
    show (bl (qOf (decode6 P ws) 1)).take 64 = (aOf (decode6 P ws) 0).toList ++ c.toList
    obtain ⟨ha, hc⟩ := hL.seed 1 hi (by rw [he])
    rw [aOf_lanes6 hS hw hP, show (64 : ℕ) = 8 * 8 from rfl, qOf_take6 hS (by omega) hi (by rw [he]; exact h64),
      wordsBytes_split, Nat.add_assoc, show 1 + 4 = 5 from rfl, hc]
    have := eLane6_bound hS hw (i := 1) le_rfl hi; rw [he] at this
    rw [slice_eq (by simp only at this; omega) (ansLane6_bound hS hw hP) ha]
  | fs st g =>
    simp only [entryOk6, Bool.and_eq_true, decide_eq_true_eq] at hE
    obtain ⟨⟨h32, hst⟩, h1⟩ := hE
    show (bl (qOf (decode6 P ws) i)).take 32 = (aOf (decode6 P ws) st).toList
    rw [aOf_lanes6 hS hw (by omega), show (32 : ℕ) = 8 * 4 from rfl, qOf_take6 hS h1 hi (by rw [he]; exact h32)]
    congr 1
    have := eLane6_bound hS hw h1 hi; rw [he] at this
    exact slice_eq (by simp only at this; omega) (ansLane6_bound hS hw (by omega)) (hL.fs i hi st g (by rw [he]))
  | leaf => trivial
  | node pd sh h lvl cap =>
    simp only [entryOk6, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE
    obtain ⟨⟨⟨⟨⟨⟨h64, h2⟩, hlvl⟩, h128⟩, hpd⟩, hpd1⟩, hcap⟩ := hE
    subst h64
    have hb8 := eLane6_bound hS hw (i := i) (by omega) hi; rw [he] at hb8; simp only at hb8
    have hprev := ansLane6_pred hS h2 hi
    have hpb := ansLane6_bound hS hw (e := i - 1) (by omega)
    refine ⟨?_, ?_⟩
    · show (if (posOf (decode6 P ws) pd sh h >>> lvl) % 2 = 0 then (bl (qOf (decode6 P ws) i)).take 32
        else (bl (qOf (decode6 P ws) i)).drop 32) = (aOf (decode6 P ws) (i - 1)).toList
      have hbit := posOf_bit (decode6 P ws) pd sh h lvl hlvl
      rw [testBit_drawN hS hw (by omega) (by omega)] at hbit
      have hn := hL.node i hi pd sh h lvl cap (by rw [he])
      rw [aOf_lanes6 hS hw (by omega), hprev]
      by_cases hab : ansBit6 P ws pd (sh + lvl)
      · rw [if_neg (by rw [hbit, hab]; decide), qOf_drop32_6 hS hw (by omega) hi (by rw [he])]
        congr 1
        simp only [hab, ite_true] at hn
        exact slice_eq (by omega) (by omega) hn
      · rw [if_pos (by rw [hbit]; simpa using hab), show (32 : ℕ) = 8 * 4 from rfl,
          qOf_take6 hS (by omega) hi (by rw [he]; show 8 * 4 ≤ 64; omega)]
        congr 1
        simp only [hab, Bool.false_eq_true, ite_false] at hn
        exact slice_eq (by omega) (by omega) hn
    · rcases cap with _ | ⟨ce, co, path⟩
      · trivial
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcap
        obtain ⟨⟨⟨⟨⟨hco8, hph⟩, hco32⟩, hcob⟩, hce1⟩, hcei⟩ := hcap
        show aOf (decode6 P ws) i = digestAt (qOf (decode6 P ws) ce) (co + 32 * (posOf (decode6 P ws) pd sh h >>> path))
        have hidx : posOf (decode6 P ws) pd sh h >>> path = posL6 P ws pd (sh + path) (h - path) := by
          rw [posOf_shift _ _ _ _ _ hph]
          symm
          apply posL6_eq
          intro n h1 h2
          exact (testBit_drawN hS hw (e := pd) (by omega) (by omega)).symm
        have hidxlt : posL6 P ws pd (sh + path) (h - path) < 2 ^ (h - path) := posL6_lt _ _ _ _ _
        have hcb := eLane6_bound hS hw (i := ce) hce1 (by omega)
        have hlt : 32 * posL6 P ws pd (sh + path) (h - path) + 32 ≤ 32 * 2 ^ (h - path) := by
          have := Nat.mul_le_mul_left 32 (show posL6 P ws pd (sh + path) (h - path) + 1 ≤ 2 ^ (h - path) by omega)
          omega
        apply digest_ext
        rw [aOf_lanes6 hS hw hi, digestAt, Vector.toList_ofFn, hidx]
        have hq : (List.ofFn fun x : Fin 32 => (qOf (decode6 P ws) ce).get!
            (co + 32 * posL6 P ws pd (sh + path) (h - path) + x.val)) =
            wordsBytes ((ws.drop (eLane6 P ce + 1 + co / 8 + 4 * posL6 P ws pd (sh + path) (h - path))).take 4) := by
          rw [← wordsBytes_slice]
          refine List.ext_getElem (by simp [wordsBytes_length]; omega) fun x h1 h2 => ?_
          simp only [List.length_ofFn] at h1
          have hxb : co + 32 * posL6 P ws pd (sh + path) (h - path) + x < (P.getD ce default).len := by omega
          rw [List.getElem_ofFn, qOf_get6 hS hce1 (by omega) hxb, List.getElem_take, List.getElem_drop,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [wordsBytes_length]; omega),
            Option.getD_some]
          congr 1; omega
        rw [hq]
        congr 1
        refine slice_eq (by have := ansLane6_bound hS hw (e := i) hi; omega) (by omega) ?_
        intro l hl
        have := hL.cap i hi pd sh h lvl ce co path (by rw [he]) l hl
        simp only [ansLane6, show i ≠ 0 by omega, ite_false, he]
        exact this

end

end Lvm6.Q
