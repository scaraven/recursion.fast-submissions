-- New for `flock-recursive` (PACK-4.4.1 §4.3, A.5; IMP-RESULT §5.2; SRA-RESULT §6.3; track ASK-P):
-- `reassemble4`'s positional spec, field by field and phase by phase.
import FRNodeRows4AskPos
import FRXOut4

/-!
# Which trace bytes a proof field's bytes are (`reassemble4`'s positional spec)

The generators read phase `n`'s bytes of field `f` at the absolute offset
`fieldOffOf S f + phaseOffOf S n f` (`FRVIR4.genPhase4`'s `o f`). `reassemble4 S tr` lays the fields
out in order, each field phase by phase (`ctbs4`), so:

* **`reassemble4_byte`**: byte `fieldOffOf S f + phaseOffOf S n f + j` of the proof is byte `j` of
  phase `n`'s contribution `ctb4 … (phIx S n) (phAns …) sh f`, `phIx S n` the phase's first item.
* **Per shape** (`ctb4_seed`, `ctb4_absorb`, `ctb4_uni`, `ctb4_rounds`, `ctb4_cols`, `ctb4_sibs`): the
  contribution's byte is a query byte of an item of the phase (`hdr` from the seed's byte 71, a
  message from byte 40 of its absorb, a column from byte 8 of its column query), or a sibling half.
* **`itemsOf_phIx`**: item `phIx S n + q` of `itemsOf S` is the phase's item `q`.
* **The slot's proof** (`slotπ_byte`): at slot `v`, `rd4 pf4`'s proof is `pf4` of the slot's trace.
  **`slot_pfAbsorb`**: at an active slot, an absorb phase's message byte `j` is byte
  `(o + 48 + j) mod 16` of the H cell of element `⌊(o + 48 + j)/16⌋` of the slot's segment
  (`o = 1 + itOff (phIx seq4 n)`), outside the last block.
-/

namespace FR
namespace X
open RecursionFast FR.Snd FR.Rev4

/-! ## Lists of blocks -/

theorem getD_flatMap_const {α : Type} (g : α → List UInt8) (c : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, (g x).length = c) → ∀ {p t : ℕ} (hp : p < l.length), t < c →
      (l.flatMap g).getD (p * c + t) 0 = (g l[p]).getD t 0
  | [], _, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | x :: l, h, p, t, hp, ht => by
    rw [List.flatMap_cons]
    rcases p with _ | p
    · rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by rw [h x List.mem_cons_self]; exact ht)]; rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [h x List.mem_cons_self]; nlinarith), h x List.mem_cons_self,
        show (p + 1) * c + t - c = p * c + t by rw [Nat.add_one_mul]; omega,
        getD_flatMap_const g c l (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by simpa using hp) ht]
      rfl

theorem getD_flatMap_range (g : ℕ → List UInt8) : ∀ (N f o : ℕ), f < N → o < (g f).length →
    ((List.range N).flatMap g).getD (((List.range f).map fun i => (g i).length).sum + o) 0 = (g f).getD o 0
  | 0, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | N + 1, f, o, hf, ho => by
    rw [List.range_succ, List.flatMap_append]
    have hl : ((List.range N).flatMap g).length = ((List.range N).map fun i => (g i).length).sum := by
      simp [List.length_flatMap]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | rfl
    · have hle : ((List.range f).map fun i => (g i).length).sum + o < ((List.range N).flatMap g).length := by
        rw [hl]
        obtain ⟨d, rfl⟩ : ∃ d, N = f + 1 + d := ⟨N - f - 1, by omega⟩
        rw [List.range_add, List.map_append, List.sum_append, List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
      rw [List.getD_append _ _ _ _ hle, getD_flatMap_range g N f o hf ho]
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
      simp

/-! ## The phases -/

/-- The position answers after `n` phases (`ctbs4`'s threading of `ansOf4`). -/
def ansN (S : Seq) (a : Array (ByteArray × Digest)) : ℕ → List Digest → List Sh → ℕ → List Digest
  | _, ans, _, 0 => ans
  | _, ans, [], _ + 1 => ans
  | ix, ans, sh :: shs, n + 1 => ansN S a (ix + (sh.itemsL S.lv).length) (ansOf4 a ix ans sh) shs n

/-- **Phase `n`'s contribution in `ctbs4`**: byte `Σ_{q<n} |sh_q|_f + j` is its byte `j`. -/
theorem ctbs4_getD (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (f : ℕ) :
    ∀ (shs : List Sh) (ix : ℕ) (ans : List Digest) (n j : ℕ) (hn : n < shs.length),
      j < shs[n].bytesToL S.lv f →
      (ctbs4 S m a ix ans shs f).getD (((shs.take n).map fun sh => sh.bytesToL S.lv f).sum + j) 0 =
        (ctb4 S m a (ix + ((shs.take n).map fun sh => (sh.itemsL S.lv).length).sum) (ansN S a ix ans shs n)
          shs[n] f).getD j 0
  | [], _, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | sh :: shs, ix, ans, 0, j, _, hj => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero, ansN, ctbs4,
      List.getElem_cons_zero]
    rw [List.getD_append _ _ _ _ (by rw [ctb4_length]; exact hj)]
  | sh :: shs, ix, ans, n + 1, j, hn, hj => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, ansN, ctbs4, List.getElem_cons_succ] at hj ⊢
    rw [List.getD_append_right _ _ _ _ (by rw [ctb4_length]; omega), ctb4_length,
      show sh.bytesToL S.lv f + ((shs.take n).map fun sh => sh.bytesToL S.lv f).sum + j -
        sh.bytesToL S.lv f = ((shs.take n).map fun sh => sh.bytesToL S.lv f).sum + j by omega,
      ctbs4_getD S m a f shs _ _ n j (by simpa using hn) hj, Nat.add_assoc]

/-- **Phase `n`'s first item** (index in `itemsOf S`). -/
def phIx (S : Seq) (n : ℕ) : ℕ := (((phasesOf S).take n).map fun p => (p.2.itemsL S.lv).length).sum

/-- The position answers phase `n` reads (the trace `a`'s). -/
def phAns (S : Seq) (a : Array (ByteArray × Digest)) (n : ℕ) : List Digest :=
  ansN S a 0 [] ((phasesOf S).map Prod.snd) n

theorem fieldSize_ctbs4 (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (f : ℕ) :
    (ctbs4 S m a 0 [] ((phasesOf S).map Prod.snd) f).length = fieldSizeOf S f := by
  rw [ctbs4_length, List.map_map]; rfl

theorem take_sum_le {α : Type} (F : α → ℕ) : ∀ (l : List α) (n : ℕ) (hn : n < l.length),
    ((l.take n).map F).sum + F l[n] ≤ (l.map F).sum
  | [], _, hn => absurd hn (Nat.not_lt_zero _)
  | x :: l, 0, _ => by simp
  | x :: l, n + 1, hn => by
    have := take_sum_le F l n (by simpa using hn)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-- **`reassemble4`'s positional spec**: byte `j` of phase `n`'s part of field `f` (the generators'
absolute offset `fieldOffOf S f + phaseOffOf S n f + j`) is byte `j` of the phase's contribution. -/
theorem reassemble4_byte (S : Seq) (tr : Trace) {f n j : ℕ} (hf : f < nFields4) (hn : n < (phasesOf S).length)
    (hj : j < ((phasesOf S)[n]).2.bytesToL S.lv f) :
    byteAt (reassemble4 S tr) (fieldOffOf S f + phaseOffOf S n f + j) =
      (ctb4 S (trM4 tr.toArray) tr.toArray (phIx S n) (phAns S tr.toArray n) ((phasesOf S)[n]).2 f).getD j 0 := by
  have hn' : n < ((phasesOf S).map Prod.snd).length := by simpa using hn
  have hm : ((phasesOf S).map Prod.snd)[n] = ((phasesOf S)[n]).2 := by simp
  have hpo : phaseOffOf S n f = ((((phasesOf S).map Prod.snd).take n).map fun sh => sh.bytesToL S.lv f).sum := by
    rw [phaseOffOf, ← List.map_take, List.map_map]; rfl
  have hpi : phIx S n = 0 + ((((phasesOf S).map Prod.snd).take n).map fun sh => (sh.itemsL S.lv).length).sum := by
    rw [phIx, ← List.map_take, List.map_map, Nat.zero_add]; rfl
  have hfo : fieldOffOf S f = ((List.range f).map fun i =>
      (ctbs4 S (trM4 tr.toArray) tr.toArray 0 [] ((phasesOf S).map Prod.snd) i).length).sum := by
    rw [fieldOffOf]
    exact congrArg List.sum (List.map_congr_left fun i _ => (fieldSize_ctbs4 S _ _ i).symm)
  have hlt : phaseOffOf S n f + j <
      (ctbs4 S (trM4 tr.toArray) tr.toArray 0 [] ((phasesOf S).map Prod.snd) f).length := by
    rw [ctbs4_length, hpo]
    have := take_sum_le (fun sh : Sh => sh.bytesToL S.lv f) _ n hn'
    rw [hm] at this; omega
  rw [reassemble4, N4s.byteAt_mk, hfo, Nat.add_assoc,
    getD_flatMap_range (fun i => ctbs4 S (trM4 tr.toArray) tr.toArray 0 [] ((phasesOf S).map Prod.snd) i)
      nFields4 f _ hf hlt,
    hpo, ctbs4_getD S _ _ f _ 0 [] n j hn' (by rw [hm]; exact hj), hm, ← hpi]
  rfl

/-! ## Each shape's contribution -/

section Shapes
variable (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest)

theorem qB4_getD {j o n t : ℕ} (ht : t < n) : (qB4 a j o n).getD t 0 = byteAt (a.getD j (ByteArray.empty, 0)).1 (o + t) := by
  rw [qB4, qBytes]; exact fitL_extract_getDj _ _ _ ht

/-- `hdr`: the seed query's bytes from 71. -/
theorem ctb4_seed {j : ℕ} (hj : j < 48) :
    (ctb4 S m a ix ans .seed fHdr).getD j 0 = byteAt (a.getD ix (ByteArray.empty, 0)).1 (71 + j) := by
  rw [ctb4, if_pos rfl, qB4_getD _ hj]

/-- An absorb phase: its message, the query's bytes from 40 (`tag ‖ st ‖ msg`). -/
theorem ctb4_absorb {g len j : ℕ} (hj : j < len) :
    (ctb4 S m a ix ans (.absorb g len) g).getD j 0 = byteAt (a.getD ix (ByteArray.empty, 0)).1 (40 + j) := by
  rw [ctb4, if_pos rfl, qB4_getD _ hj]

/-- A univariate phase: its absorb's message. -/
theorem ctb4_uni {g j : ℕ} (hj : j < uniBytes) :
    (ctb4 S m a ix ans (.uni g) g).getD j 0 = byteAt (a.getD ix (ByteArray.empty, 0)).1 (40 + j) := by
  rw [ctb4, if_pos rfl, qB4_getD _ hj]

/-- A rounds phase: round `p`'s message, its absorb (item `2p`) from byte 40. -/
theorem ctb4_rounds {g n d : ℕ} {inK : Bool} {p t : ℕ} (hp : p < n) (ht : t < roundBytes inK) :
    (ctb4 S m a ix ans (.rounds g n d inK) g).getD (p * roundBytes inK + t) 0 =
      byteAt (a.getD (ix + 2 * p) (ByteArray.empty, 0)).1 (40 + t) := by
  rw [ctb4, if_pos rfl, getD_flatMap_const (fun j => qB4 a (ix + 2 * j) 40 (roundBytes inK)) _ _
    (fun _ _ => N4s.fitL_length _ _) (by simpa using hp) ht, List.getElem_range, qB4_getD _ ht]

/-- A queries phase, field `fCols`: position `p`'s column, its column query (item `(1 + sib)·p`) from
byte 8. -/
theorem ctb4_cols {i p t : ℕ} (hp : p < (S.lv i).t) (ht : t < colBytes i) :
    (ctb4 S m a ix ans (.queries i) fCols).getD (p * colBytes i + t) 0 =
      byteAt (a.getD (ix + (1 + (S.lv i).sib) * p) (ByteArray.empty, 0)).1 (8 + t) := by
  rw [ctb4, if_pos rfl, getD_flatMap_const (fun p => qB4 a (ix + (1 + (S.lv i).sib) * p) 8 (colBytes i)) _ _
    (fun _ _ => N4s.fitL_length _ _) (by simpa using hp) ht, List.getElem_range, qB4_getD _ ht]

/-- A queries phase, field `fSibs`: position `p`'s sibling `h`, the half of its node query (item
`(1 + sib)·p + 1 + h`) not at the position's bit `h` (`sib4`). -/
theorem ctb4_sibs {i p h t : ℕ} (hp : p < (S.lv i).t) (hh : h < (S.lv i).sib) (ht : t < 32) :
    (ctb4 S m a ix ans (.queries i) fSibs).getD ((p * (S.lv i).sib + h) * 32 + t) 0 =
      (sib4 S m i h (posOf4 S m i ans p) (a.getD (ix + (1 + (S.lv i).sib) * p + 1 + h) (ByteArray.empty, 0)).1).getD t 0 := by
  have hne : fSibs ≠ fCols := by decide
  rw [ctb4, if_neg hne, if_pos rfl, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
    getD_flatMap_const _ _ _ (fun _ _ => by
      rw [flatMap_const_length _ _ 32 fun _ _ => sib4_length .., List.length_range]) (by simpa using hp)
      (by nlinarith),
    List.getElem_range, getD_flatMap_const _ _ _ (fun _ _ => sib4_length ..) (by simpa using hh) ht,
    List.getElem_range]

end Shapes

/-! ## The items of a phase -/

theorem getElem?_flatMap_take {β γ : Type} (g : β → List γ) : ∀ (l : List β) (n q : ℕ) (hn : n < l.length),
    q < (g l[n]).length → (l.flatMap g)[((l.take n).map fun x => (g x).length).sum + q]? = (g l[n])[q]?
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | x :: l, 0, q, _, hq => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
      List.getElem_cons_zero] at hq ⊢
    rw [List.getElem?_append_left hq]
  | x :: l, n + 1, q, h, hq => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.getElem_cons_succ] at hq ⊢
    rw [List.getElem?_append_right (by omega), show (g x).length + ((l.take n).map fun x => (g x).length).sum + q -
      (g x).length = ((l.take n).map fun x => (g x).length).sum + q by omega,
      getElem?_flatMap_take g l n q (by simpa using h) hq]

/-- **Item `phIx S n + q` of `itemsOf S` is phase `n`'s item `q`.** -/
theorem itemsOf_phIx (S : Seq) {n q : ℕ} (hn : n < (phasesOf S).length)
    (hq : q < (((phasesOf S)[n]).2.itemsL S.lv).length) :
    (itemsOf S)[phIx S n + q]? = (((phasesOf S)[n]).2.itemsL S.lv)[q]? := by
  rw [itemsOf, phIx]
  exact getElem?_flatMap_take (fun p : String × Sh => p.2.itemsL S.lv) _ n q hn hq

/-! ## At a slot: the proof the reader reads -/

/-- **The slot's proof is `pf4` of its trace** (`fitL` keeps `reassemble4`'s exact size). -/
theorem slotπ_byte (κ : NodeKind) (v : ℕ) (w : Circ.Asg) (i : ℕ) :
    byteAt ((N4s.rd4 pf4).slotπ κ v w) i = byteAt (pf4 (N4s.slotTr4 κ v w)) i := by
  have hp : pf4 = reassemble4 seq4 := rfl
  have hl : (pf4 (N4s.slotTr4 κ v w)).data.toList.length = piSizeOf seq4 := by
    rw [Array.length_toList, hp]; exact reassemble4_size seq4 (N4s.slotTr4 κ v w)
  have hf : N4s.fitL (piSizeOf seq4) (pf4 (N4s.slotTr4 κ v w)).data.toList = (pf4 (N4s.slotTr4 κ v w)).data.toList := by
    generalize piSizeOf seq4 = P at hl ⊢
    rw [N4s.fitL, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hr : (N4s.rd4 pf4).slotπ κ v w = ⟨(N4s.slotPf pf4 κ v w).toArray⟩ := rfl
  rw [hr, N4s.slotPf, hf, Array.toArray_toList]

/-- The trace as an array: entry `k` (`k < 8,783`) is item `k` read off the slot's stream. -/
theorem slotTr_getD (κ : NodeKind) (v : ℕ) (w : Circ.Asg) {k : ℕ} (hk : k < (itemsOf seq4).length) :
    (N4s.slotTr4 κ v w).toArray.getD k (ByteArray.empty, 0) =
      Read.entryAt (N4s.slotStr κ v w) (1 + segIx κ v * N4c.strideB + N4s.itOff k) (N4s.itAt k) := by
  have h := N4s.slotTr4_getElem? κ v w k
  rw [N4s.itAt_eq hk, Option.map_some] at h
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, h, Option.getD_some]

/-- **An absorb phase's message at an active slot** (not the last block's item): proof byte
`fieldOffOf seq4 g + phaseOffOf seq4 n g + j` is byte `(o + 48 + j) mod 16` of the H cell of element
`⌊(o + 48 + j)/16⌋`, `o = 1 + itOff (phIx seq4 n)` (the absorb's query: `tag ‖ st ‖ msg`). -/
theorem slot_pfAbsorb {pf : Trace → Proof} {κ : NodeKind} {w : Circ.Asg} {v : ℕ}
    (hv : N4c.Active4 (N4s.rd4 pf) κ w v) {n g len j : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : ((phasesOf seq4)[n]).2 = .absorb g len) (hg : g < nFields4) (hj : j < len)
    (hb : 1 + N4s.itOff (phIx seq4 n) + (N4s.itAt (phIx seq4 n)).slen + 64 ≤ N4c.segB) :
    byteAt ((N4s.rd4 pf4).slotπ κ v w) (fieldOffOf seq4 g + phaseOffOf seq4 n g + j) =
      (F.toBytes (w (sCell (slotB0 κ v) ((1 + N4s.itOff (phIx seq4 n) + 8 + (40 + j)) / 16))))[
        (1 + N4s.itOff (phIx seq4 n) + 8 + (40 + j)) % 16]'(Nat.mod_lt _ (by norm_num)) := by
  have hq0 : 0 < (((phasesOf seq4)[n]).2.itemsL seq4.lv).length := by rw [hsh]; simp [Sh.itemsL]
  have hit := itemsOf_phIx seq4 hn hq0
  rw [hsh, Nat.add_zero] at hit
  simp only [Sh.itemsL, List.getElem?_cons_zero] at hit
  have hk : phIx seq4 n < (itemsOf seq4).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hit; exact absurd hit (by simp)
  have hia : N4s.itAt (phIx seq4 n) = .absorb len := by
    rw [N4s.itAt, List.getD_eq_getElem?_getD, hit]; rfl
  rw [slotπ_byte, pf4, reassemble4_byte seq4 _ hg hn (by rw [hsh]; simpa [Sh.bytesToL] using hj), hsh,
    ctb4_absorb _ _ _ _ _ hj, slotTr_getD κ v w hk]
  have he : (N4s.slotTr4 κ v w)[phIx seq4 n]? = some (Read.entryAt (N4s.slotStr κ v w)
      (1 + segIx κ v * N4c.strideB + N4s.itOff (phIx seq4 n)) (N4s.itAt (phIx seq4 n))) := by
    rw [N4s.slotTr4_getElem?, N4s.itAt_eq hk]; rfl
  exact N4s.slot_qbyte hv hk he hb (by rw [hia]; simp [Item.qlen]; omega)

/-! ## Controls -/

/-- (+) Blocks of constant length: byte `1·3 + 2` of `[a, b]` in blocks of 3 is block `b`'s byte 2;
(−) not block `a`'s. -/
theorem getD_flatMap_ctl :
    ([[1, 2, 3], [4, 5, 6]].flatMap id : List UInt8).getD (1 * 3 + 2) 0 = 6 ∧
      ([[1, 2, 3], [4, 5, 6]].flatMap id : List UInt8).getD (1 * 3 + 2) 0 ≠ 3 := by decide

end X
end FR
