-- lvm6 X2 (BLUEPRINT v3 §3 step 1; FORMAT6 v2 §5): the v6 extractor's Merkle inversion, the five trees of the
-- opening read off the log from their caps with season 1's generic first-preimage reader (`readGIR`,
-- `Lvm6XReadG`), at the geometry of FORMAT6 §5; the caps read from `π` at a byte offset.
import Lvm6XReadG

/-!
# The v6 Merkle inversion (replay, part 1)

FORMAT6 §5 (v2.6, `P17`; PORT17 X1) fixes five trees: level `i` has `2^ht` positions, its cap at height `ht − lv` (`2^lv` nodes, sent in
`π` and absorbed, never hashed: there is no root), and leaves of `occ` words (level 0: 46 `K` words, 368 bytes;
levels 1–4: 16 `E` values = 32 `K` words, 256 bytes).

| level `i` | `ht6 i` | `lv6 i` | steps `ht − lv` | `occ6 i` |
|---|---|---|---|---|
| 0 | 20 | 7 | 13 | 46 |
| 1 | 19 | 6 | 13 | 32 |
| 2 | 18 | 5 | 13 | 32 |
| 3 | 17 | 5 | 12 | 32 |
| 4 | 16 | 5 | 11 | 32 |

* **`rows6 i L cap p`**: the row the log holds at position `p` of level `i`: from cap node `p >> (ht − lv)`,
  `ht − lv` first-preimage steps down through 64-byte queries (the length classifier of a node: `xDescend`
  takes a step only through a query of exactly 64 bytes), then the first entry answering the leaf digest; its
  first `occ` little-endian words, missing bytes zero; a missing entry anywhere is an erasure (the zero row).
  Row word `t` is the leaf's word `t` in hashed order: at level 0 that is **slot `45 − t`** (`slot6`), at
  levels `≥ 1` word `2u + c` is coordinate `c` of lane `u`.
* **`capOf6 π off lv`**: the cap as `π` carries it, `2^lv` digests from byte `off` (FORMAT6 §5: node 0 first);
  `capOf6_tape`: on the tape, entry `e`'s words are tape words `5 + off/8 + 4e + m` (`off ≡ 0 mod 8`).
* **`read6IR i bX pL capW wB`**: the program, `readGIR` at the level's geometry (rows of `occ6 i` words at
  `wB + occ6 i · p`, no zero prefix); **`read6IR_sem`**: it stores `rows6`, keeps the index and every heap cell
  outside the rows; **`cost_read6IR`**: exactly `14 + 2^ht · (6572 + 6532 (ht − lv) + 25 occ)` steps on every
  tape; the five levels together `cost6_reads` (≈ `2^37.44` at `P17`).
-/

namespace Lvm6.X

open RecursionFast Lvm.X

/-! ## The geometry of FORMAT6 §5 -/

/-- Level `i`'s tree height: `2^ht` positions. -/
def ht6 : ℕ → ℕ
  | 0 => 20
  | 1 => 19
  | 2 => 18
  | 3 => 17
  | _ => 16

/-- Level `i`'s cap level: `2^lv` cap nodes. -/
def lv6 : ℕ → ℕ
  | 0 => 7
  | 1 => 6
  | _ => 5

/-- Level `i`'s leaf words: 46 at level 0 (368 bytes), 32 at levels 1–4 (256 bytes). -/
def occ6 : ℕ → ℕ
  | 0 => 46
  | _ => 32

/-! ## The pure reading -/

/-- **The row the log holds at position `p` of level `i`** under the cap `cap` (`occ6 i` words, hashed order;
the zero row for an erasure). -/
def rows6 (i : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : List BF64 :=
  readRowG (ht6 i) (lv6 i) 0 (occ6 i) L cap p

/-- **The symbol of slot `s < 46`** in a level-0 row (FORMAT6 §5: word `j` of the leaf is slot `45 − j`). -/
def slot6 (row : List BF64) (s : ℕ) : BF64 := row.getD (45 - s) 0

/-- **The cap carried by `π`** at byte offset `off`: `2^lv` digests, node 0 first. -/
def capOf6 (π : Proof) (off lv : ℕ) : List Digest :=
  (List.range (2 ^ lv)).map fun e => xWin π (off + 32 * e)

@[simp] theorem capOf6_length (π : Proof) (off lv : ℕ) : (capOf6 π off lv).length = 2 ^ lv := by
  simp [capOf6]

/-! ## The program -/

/-- **The reads of level `i`**: row word `t` of position `p` at `wB + occ6 i · p + t`. -/
def read6IR (i bX pL capW wB : ℕ) : XIR :=
  readGIR bX pL capW wB (2 ^ ht6 i) (ht6 i - lv6 i) 0 (occ6 i)

theorem wf_read6IR (i bX pL capW wB : ℕ) : WF (read6IR i bX pL capW wB) :=
  wf_readGIR ..

theorem noLoopT_read6IR (i bX pL capW wB : ℕ) : NoLoopT (read6IR i bX pL capW wB) :=
  noLoopT_readGIR ..

theorem outs_read6IR (i bX pL capW wB t : ℕ) : outs (read6IR i bX pL capW wB) t = 0 :=
  outs_readGIR ..

theorem sizeIR_read6IR (i bX pL capW wB : ℕ) : sizeIR (read6IR i bX pL capW wB) = 563 :=
  sizeIR_readGIR ..

theorem ht6_le (i : ℕ) : ht6 i ≤ 21 := by
  unfold ht6; split <;> omega

theorem lv6_le_ht6 (i : ℕ) : lv6 i ≤ ht6 i := by
  unfold lv6 ht6; split <;> split <;> omega

theorem occ6_le (i : ℕ) : occ6 i ≤ 46 := by
  unfold occ6; split <;> omega

/-- **The exact cost of level `i`'s reads**, on every tape. -/
theorem cost_read6IR (i bX pL capW wB t : ℕ) :
    cost (read6IR i bX pL capW wB) t =
      14 + 2 ^ ht6 i * (6572 + 6532 * (ht6 i - lv6 i) + 25 * occ6 i) := by
  have h1 : 2 ^ ht6 i ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) (ht6_le i)
  have h2 := ht6_le i
  have h3 := occ6_le i
  rw [read6IR, cost_readGIR _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  simp

/-- The five levels' reads together at `P17`: `186,148,454,470` steps (≈ `2^37.44`), on every tape. -/
theorem cost6_reads (bX pL : ℕ) (capW wB : ℕ → ℕ) (t : ℕ) :
    (List.range 5).foldr (fun i a => cost (read6IR i bX pL (capW i) (wB i)) t + a) 0 = 186148454470 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.foldr_cons,
    List.foldr_nil, cost_read6IR]
  norm_num [ht6, lv6, occ6]

/-! ## The caps on the tape -/

/-- **The cap's words on the tape**: entry `e`'s packed word `m` is tape word `5 + a + 4e + m`, for a cap at byte
`8a` of `π` that `π` holds whole. -/
theorem capOf6_tape (c : Digest) (π : Proof) (L : Log) {a lv : ℕ} (hπ : 8 * a + 32 * 2 ^ lv ≤ π.size)
    (e : ℕ) (he : e < (capOf6 π (8 * a) lv).length) (m : ℕ) (hm : m < 4) :
    (extractorInput c π L).toArray.getD (5 + a + 4 * e + m) 0 =
      (packBytes (capOf6 π (8 * a) lv)[e].toList).getD m 0 := by
  rw [capOf6_length] at he
  have hw : 8 * (a + 4 * e) + 32 ≤ π.size := by
    have : 32 * (e + 1) ≤ 32 * 2 ^ lv := Nat.mul_le_mul_left _ he
    omega
  have hj : a + 4 * e + m < (π.size + 7) / 8 := by omega
  simp only [capOf6, List.getElem_map, List.getElem_range]
  rw [show 8 * a + 32 * e = 8 * (a + 4 * e) by ring, cr_win_getD π hw hm, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, ← List.getD_eq_getElem?_getD, show 5 + a + 4 * e + m = 5 + (a + 4 * e + m) by ring,
    tape_getD_proof c π L hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

/-! ## The semantics -/

/-- **The reads of level `i` compute `rows6`**: after the index (`idxIR4`), `read6IR i` stores row word `t` of
position `p` as `rows6 i L cap p`'s word `t` at `wB + occ6 i · p + t`, for the cap `cap` at tape word `capW`; the
index and every heap cell outside the rows are kept. -/
theorem read6IR_sem {i bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 2 ^ lv6 i)
    (hcw : capW + 4 * 2 ^ lv6 i < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + occ6 i * 2 ^ ht6 i ≤ bX) :
    (∀ p < 2 ^ ht6 i, ∀ t < occ6 i,
      rdK (semXIR (extractorInput c π L).toArray (read6IR i bX pL capW wB) s₂).M (wB + occ6 i * p + t) =
        (rows6 i L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + occ6 i * 2 ^ ht6 i ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (read6IR i bX pL capW wB) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (read6IR i bX pL capW wB) s₂).M (bX + a) = rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (read6IR i bX pL capW wB) s₂).M := by
  have hlh := lv6_le_ht6 i
  have hh := ht6_le i
  have hh2 : 2 ^ ht6 i ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) hh
  have hcl' : ∀ q < 2 ^ ht6 i, q / 2 ^ (ht6 i - lv6 i) < cap.length := fun q hq => by
    rw [hcl, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_sub_cancel' hlh]
    exact hq
  have r := readGIR_sem hbX hbX2 hpL c π L hs hq ht s hM hsz s₂ hM₂ hsz₂ hX₂ (ht' := ht6 i) (lv := lv6 i) (z := 0)
    (occ := occ6 i) (capW := capW) (wB := wB) hcl' (by rw [hcl]; exact hcw) (by omega) (by omega)
    (by have := occ6_le i; omega) hcap hwB (by simpa using hwB2)
  simp only [Nat.zero_add] at r
  exact r

end Lvm6.X
