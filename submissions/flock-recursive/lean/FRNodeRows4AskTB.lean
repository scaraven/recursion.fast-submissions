-- New for `flock-recursive` (PACK-4.4.1 §4.2–§4.3; track ASK-T): what the ask generator's soundness
-- reads: its tables, the byte sources against `reassemble4`, every stream byte an H cell, the pinned tags.
import FRNodeRows4AskPosR
import FRNodeRows4AskT

/-!
# The ask generator's facts

* **The tables** (`itemsT_get`, `offT_get`, `srcT_get`): the closed constants are `itemsOf seq4`,
  `itOff` and `srcOf seq4`, read positionally.
* **The byte sources** (`src_spec`): where `srcOf seq4` names `(A, len)` for item `k`, bytes
  `A … A + len` of `reassemble4 seq4 tr` are item `k`'s query bytes from `qoffOf` (the seed's `hdr`
  from 71, a message from 40, a column from 8), which end the query; `A + len ≤ piSizeOf seq4`.
* **Every byte of an active slot's segment is an H cell** (`slot_byte'`): `slot_byte` without its
  last-block exclusion. The last block is the main chain's, or, for an aggregate with `k < maxK`, its
  candidate final block, whose message `aggPad` (`AggPad4`, a theorem of the statement's rows) makes
  the main chain's. So the last item (the cap check's last squeeze) is read like any other.
* **The tags** (`tag_byte`): an entry's query tag is its item's (`itemTag`), from the pack rows' pins
  (`wfSeg`; the seed's from `HeadOk`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The tables -/

theorem itemsT_get (k : ℕ) : itemsT[k]? = (itemsOf seq4)[k]? := by simp [itemsT]

theorem srcT_get (k : ℕ) : srcT[k]? = (srcOf seq4)[k]? := by simp [srcT]

theorem scanl_get (f : Item → ℕ) : ∀ (l : List Item) (o k : ℕ), k ≤ l.length →
    (l.scanl (fun a it => a + f it) o)[k]? = some (o + ((l.take k).map f).sum)
  | [], o, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | it :: l, o, 0, _ => by simp
  | it :: l, o, k + 1, h => by
    rw [List.scanl_cons, List.getElem?_cons_succ, scanl_get f l _ k (by simpa using h)]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, Option.some.injEq]
    omega

theorem offT_get {k : ℕ} (hk : k ≤ (itemsOf seq4).length) : offT.getD k 0 = itOff k := by
  unfold offT itOff
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, scanl_get _ _ 0 k hk, Option.getD_some,
    Nat.zero_add]

/-! ## Lists of blocks -/

theorem flatMap_inv {α β : Type} (g : α → List β) : ∀ (l : List α) (k : ℕ) (x : β), (l.flatMap g)[k]? = some x →
    ∃ n, ∃ hn : n < l.length, ∃ q, k = ((l.take n).map fun a => (g a).length).sum + q ∧ (g l[n])[q]? = some x
  | [], k, x, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.flatMap_cons] at h
    by_cases hk : k < (g a).length
    · rw [List.getElem?_append_left hk] at h
      exact ⟨0, by simp, k, by simp, by simpa using h⟩
    · rw [List.getElem?_append_right (by omega)] at h
      obtain ⟨n, hn, q, hq, hx⟩ := flatMap_inv g l _ x h
      refine ⟨n + 1, by simpa using hn, q, ?_, by simpa using hx⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega

theorem flatMap_range_len {β : Type} (g : ℕ → List β) (c : ℕ) (hc : ∀ p, (g p).length = c) :
    ∀ N, ((List.range N).flatMap g).length = N * c
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_len g c hc N]
    simp [hc, Nat.succ_mul]

theorem flatMap_range_get {β : Type} (g : ℕ → List β) (c : ℕ) (hc : ∀ p, (g p).length = c) :
    ∀ (N p r : ℕ), p < N → r < c → ((List.range N).flatMap g)[c * p + r]? = (g p)[r]?
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | N + 1, p, r, hp, hr => by
    rw [List.range_succ, List.flatMap_append]
    have hl := flatMap_range_len g c hc N
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · have : c * p + r < N * c := by nlinarith
      rw [List.getElem?_append_left (by omega), flatMap_range_get g c hc N p r hp hr]
    · rw [List.getElem?_append_right (by rw [hl, Nat.mul_comm]; omega), hl,
        show c * p + r - p * c = r by rw [Nat.mul_comm]; omega]
      simp

theorem flatMap_range_inv {β : Type} (g : ℕ → List β) {c : ℕ} (hc : ∀ p, (g p).length = c) (hc0 : 0 < c)
    {N k : ℕ} {x : β} (h : ((List.range N).flatMap g)[k]? = some x) : k / c < N ∧ (g (k / c))[k % c]? = some x := by
  have hk : k < N * c := by
    rw [← flatMap_range_len g c hc N]
    exact (List.getElem?_eq_some_iff.1 h).1
  have hN : k / c < N := (Nat.div_lt_iff_lt_mul hc0).2 hk
  refine ⟨hN, ?_⟩
  rw [← flatMap_range_get g c hc N _ _ hN (Nat.mod_lt _ hc0), Nat.div_add_mod]; exact h

theorem replicate_flatten_get {β : Type} (l : List β) : ∀ (N p r : ℕ), p < N → r < l.length →
    ((List.replicate N l).flatten)[l.length * p + r]? = l[r]?
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | N + 1, 0, r, _, hr => by
    rw [List.replicate_succ, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_append_left hr]
  | N + 1, p + 1, r, hp, hr => by
    rw [List.replicate_succ, List.flatten_cons, List.getElem?_append_right (by nlinarith),
      show l.length * (p + 1) + r - l.length = l.length * p + r by rw [Nat.mul_succ]; omega]
    exact replicate_flatten_get l N p r (by omega) hr

/-! ## The byte sources against `reassemble4` -/

/-- Where the proof bytes an item gives start in its query. -/
def qoffOf : Item → ℕ
  | .seed => 71
  | .absorb _ => 40
  | .col _ => 8
  | _ => 0

theorem srcL_length (S : Seq) (n : ℕ) (sh : Sh) : (sh.srcL S n).length = (sh.itemsL S.lv).length := by
  cases sh with
  | rounds g k d inK =>
    simp only [Sh.srcL, Sh.itemsL]
    rw [flatMap_range_len _ 2 (fun _ => rfl)]
    simp [List.length_flatten, List.sum_replicate, Nat.mul_comm]
  | queries i =>
    simp only [Sh.srcL, Sh.itemsL]
    rw [flatMap_range_len _ (1 + (S.lv i).sib) (fun _ => by simp; omega)]
    simp [List.length_flatten, List.sum_replicate, posItemsL, Nat.mul_comm, Nat.add_comm]
  | _ => simp [Sh.srcL, Sh.itemsL]

theorem srcOf_sum (S : Seq) (n : ℕ) :
    (((phasesOf S).zipIdx.take n).map fun p => (p.1.2.srcL S p.2).length).sum = X.phIx S n := by
  have hf : (fun p : (String × Sh) × ℕ => (p.1.2.srcL S p.2).length) =
      (fun a : String × Sh => (a.2.itemsL S.lv).length) ∘ Prod.fst := by
    funext p; simp [srcL_length]
  rw [hf, ← List.map_map, List.map_take, List.zipIdx_map_fst, X.phIx]

theorem fieldOff_succ (S : Seq) (b : ℕ) : fieldOffOf S (b + 1) = fieldOffOf S b + fieldSizeOf S b := by
  simp [fieldOffOf, List.range_succ]

theorem fieldOff_mono (S : Seq) (a : ℕ) : ∀ d, fieldOffOf S a ≤ fieldOffOf S (a + d)
  | 0 => le_rfl
  | d + 1 => by rw [← Nat.add_assoc, fieldOff_succ]; have := fieldOff_mono S a d; omega

/-- **A field's phase part ends inside the proof.** -/
theorem src_le (S : Seq) {f n j : ℕ} (hf : f < nFields4) (hn : n < (phasesOf S).length)
    (hj : j ≤ ((phasesOf S)[n]).2.bytesToL S.lv f) : fieldOffOf S f + phaseOffOf S n f + j ≤ piSizeOf S := by
  have h1 := X.take_sum_le (fun p : String × Sh => p.2.bytesToL S.lv f) (phasesOf S) n hn
  have h2 : phaseOffOf S n f + ((phasesOf S)[n]).2.bytesToL S.lv f ≤ fieldSizeOf S f := h1
  have e := fieldOff_succ S f
  have h3 := fieldOff_mono S (f + 1) (nFields4 - (f + 1))
  rw [Nat.add_sub_cancel' hf] at h3
  have h4 : fieldOffOf S nFields4 = piSizeOf S := rfl
  omega

theorem itAt_of {k : ℕ} {it : Item} (h : (itemsOf seq4)[k]? = some it) : k < (itemsOf seq4).length ∧ itAt k = it := by
  have hk : k < (itemsOf seq4).length := (List.getElem?_eq_some_iff.1 h).1
  exact ⟨hk, by rw [itAt, List.getD_eq_getElem?_getD, h, Option.getD_some]⟩

/-- **The byte sources are `reassemble4`'s**: where `srcOf seq4` names `(A, len)` for item `k`, proof
bytes `A + j` are item `k`'s query bytes `qoffOf + j`, the query's last `len` bytes. -/
theorem src_spec {k A len : ℕ} (h : (srcOf seq4)[k]? = some (some (A, len))) :
    k < (itemsOf seq4).length ∧ qoffOf (itAt k) + len = (itAt k).qlen ∧ A + len ≤ piSizeOf seq4 ∧
      ∀ (tr : Trace) (j : ℕ), j < len → byteAt (X.reassemble4 seq4 tr) (A + j) =
        byteAt (tr.toArray.getD k (ByteArray.empty, 0)).1 (qoffOf (itAt k) + j) := by
  obtain ⟨n, hn, q, rfl, hq⟩ := flatMap_inv _ _ k _ h
  rw [srcOf_sum] at *
  simp only [List.length_zipIdx] at hn
  rw [List.getElem_zipIdx, Nat.zero_add] at hq
  have hqi : q < (((phasesOf seq4)[n]).2.itemsL seq4.lv).length := by
    rw [← srcL_length seq4 n]; exact (List.getElem?_eq_some_iff.1 hq).1
  have hit := X.itemsOf_phIx seq4 hn hqi
  have hrb := fun (tr : Trace) {f j : ℕ} (hf : f < nFields4)
    (hj : j < ((phasesOf seq4)[n]).2.bytesToL seq4.lv f) => X.reassemble4_byte seq4 tr hf hn hj
  have hle := fun {f j : ℕ} (hf : f < nFields4) (hj : j ≤ ((phasesOf seq4)[n]).2.bytesToL seq4.lv f) =>
    src_le seq4 hf hn hj
  generalize hsh : ((phasesOf seq4)[n]).2 = sh at hq hit hrb hle
  cases sh with
  | seed =>
    simp only [Sh.srcL] at hq
    obtain rfl : q = 0 := by rcases q with _ | q; rfl; simp at hq
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨hk, hia⟩ := itAt_of (by rw [hit]; rfl)
    refine ⟨hk, by rw [hia]; rfl, hle (by decide) (by simp [Sh.bytesToL, fHdr]), fun tr j hj => ?_⟩
    rw [hrb tr (f := fHdr) (by decide) (by simpa [Sh.bytesToL, fHdr] using hj), X.ctb4_seed _ _ _ _ _ hj, hia, Nat.add_zero]
    rfl
  | absorb g len' =>
    simp only [Sh.srcL] at hq
    obtain rfl : q = 0 := by rcases q with _ | q; rfl; simp at hq
    split_ifs at hq with hg
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨hk, hia⟩ := itAt_of (by rw [hit]; rfl)
      refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega, hle hg (by simp [Sh.bytesToL]), fun tr j hj => ?_⟩
      rw [hrb tr hg (by simpa [Sh.bytesToL] using hj), X.ctb4_absorb _ _ _ _ _ hj, hia, Nat.add_zero]
      rfl
    · simp at hq
  | squeezes k' ch =>
    rw [Sh.srcL, List.getElem?_replicate] at hq
    split_ifs at hq <;> simp at hq
  | uni g =>
    simp only [Sh.srcL] at hq
    rcases q with _ | _ | q
    · split_ifs at hq with hg
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨hk, hia⟩ := itAt_of (by rw [hit]; rfl)
        refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega, hle hg (by simp [Sh.bytesToL]),
          fun tr j hj => ?_⟩
        rw [hrb tr hg (by simpa [Sh.bytesToL] using hj), X.ctb4_uni _ _ _ _ _ hj, hia, Nat.add_zero]
        rfl
      · simp at hq
    · simp at hq
    · simp at hq
  | rounds g k' d inK =>
    simp only [Sh.srcL] at hq
    obtain ⟨hp, hq'⟩ := flatMap_range_inv _ (c := 2) (fun _ => rfl) (by norm_num) hq
    have hr : q % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
      · exact h0
      · rw [h1] at hq'; simp at hq'
    rw [hr] at hq'
    split_ifs at hq' with hg
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨rfl, rfl⟩ := hq'
      have e2 := replicate_flatten_get [Item.absorb (roundBytes inK), .squeeze] k' (q / 2) 0 hp (by simp)
      have hq2 : [Item.absorb (roundBytes inK), Item.squeeze].length * (q / 2) + 0 = q := by simp; omega
      rw [hq2] at e2
      obtain ⟨hk, hia⟩ := itAt_of (by rw [hit, Sh.itemsL, e2]; rfl)
      have hb : (q / 2) * roundBytes inK + roundBytes inK ≤ k' * roundBytes inK := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
      refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega,
        by have := hle (j := q / 2 * roundBytes inK + roundBytes inK) hg (by simp [Sh.bytesToL]; omega); omega,
        fun tr j hj => ?_⟩
      have e := hrb tr (j := q / 2 * roundBytes inK + j) hg (by simp [Sh.bytesToL]; omega)
      rw [X.ctb4_rounds _ _ _ _ _ hp hj, show 2 * (q / 2) = q by omega] at e
      rw [Nat.add_assoc, e, hia]; rfl
    · simp at hq'
  | queries i =>
    simp only [Sh.srcL] at hq
    have hc : ∀ p, ((fun p => some (fieldOffOf seq4 fCols + phaseOffOf seq4 n fCols + p * colBytes i, colBytes i) ::
        List.replicate (seq4.lv i).sib (none : Option (ℕ × ℕ))) p).length = 1 + (seq4.lv i).sib := fun p => by
      simp only [List.length_cons, List.length_replicate]; omega
    obtain ⟨hp, hq'⟩ := flatMap_range_inv _ hc (by omega) hq
    have hr : q % (1 + (seq4.lv i).sib) = 0 := by
      by_contra h0
      obtain ⟨r, hr⟩ : ∃ r, q % (1 + (seq4.lv i).sib) = r + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
      rw [hr] at hq'; simp only [List.getElem?_cons_succ, List.getElem?_replicate] at hq'
      split_ifs at hq' <;> simp at hq'
    rw [hr] at hq'
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    have hpl : (posItemsL seq4.lv i).length = 1 + (seq4.lv i).sib := by simp [posItemsL]; omega
    have hq2 : (1 + (seq4.lv i).sib) * (q / (1 + (seq4.lv i).sib)) = q := by
      have := Nat.div_add_mod q (1 + (seq4.lv i).sib); omega
    have e2 := replicate_flatten_get (posItemsL seq4.lv i) _ _ 0 hp (by simp [posItemsL])
    rw [hpl, Nat.add_zero, hq2] at e2
    obtain ⟨hk, hia⟩ := itAt_of (by rw [hit, Sh.itemsL, e2]; rfl)
    set p := q / (1 + (seq4.lv i).sib)
    have hb : p * colBytes i + colBytes i ≤ (seq4.lv i).t * colBytes i := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
    have hfc : fCols < nFields4 := by decide
    refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega,
      by have := hle (j := p * colBytes i + colBytes i) hfc (by simp [Sh.bytesToL]; omega); omega,
      fun tr j hj => ?_⟩
    have e := hrb tr (j := p * colBytes i + j) hfc (by simp [Sh.bytesToL]; omega)
    rw [X.ctb4_cols _ _ _ _ _ hp hj, hq2] at e
    rw [Nat.add_assoc, e, hia]; rfl

end N4s
end FR
