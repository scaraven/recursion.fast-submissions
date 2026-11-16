-- New for lvm2 E2-FT (E2F-QH6): the stream positions of the schedule's items (`LvmE2QPlan.itemLanes`) as the
-- verifier's cursor positions: one generic step lemma (`posOf_succ`), one lane-alignment decision per stage
-- (`alignB`), and the root pin's positions at S2GF (the start of the typed phases).
import LvmE2QAsm
import LvmE2VPub
import LvmQAsmHarRun
import LvmReplay
import LvmE2QKGkr
import LvmE2QAsmFront

-- (GOLF2: 13 declarations that `certified` does not use moved verbatim to `LvmE2QHarPosOff`, outside its import closure.)

/-!
# The items' positions

`itemLanes` walks the schedule with a cursor `(entry byte, pending bytes)` (`stepSt`); an item other than an opening
gets the lane `(entry + 40 + pending) / 8` (`laneSt`). V's cursor position before the item is `entry + pending`.

* **`posOf p k`** `:= 8 · laneOf p k − 40`; **`alignB p`**: the start byte and every item's width are whole lanes
  (one decision per stage: `alignF` at `P20F`).
* **`lane_pos`**: `8 · laneOf p k = posOf p k + 40`; **`posOf_succ`**: `posOf p (k+1) = posOf p k + itemW p (item k)`
  between two items that are not openings (`itemW`: `read m` 24m, `readW m w` w·m, `cap c` 32·2^c, `sample` 72,
  `positions r` 72·nPosQ). So a helper's start `P` is `posOf` of its first item, its end `posOf` of the next phase's
  first item, and an answer lane `q` after a nonce read at `P` has `8q = P + 48` (`lane_pos`, `posOf_succ`).
* At a stage with the root pin (`StE2`: S2GF or S2GT, `phasesE2`; the commit phase is `cap, ν samples, read 1`):
  `posOf_one`, **`pos_startH`**; at `P20F`: **`hbF`** (`core_of_phasesF`'s `hb`: `Pb = posOf P20F 1`), **`pinHPF`**,
  **`pinQaF`** (QH5's `pin_phase` hypotheses), **`pinEndF`** (`Pb + 72ν + 24 = typedPosF P20F`); at `P20T`: in
  `LvmS2GTFront`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm

/-! ## The cursor along the schedule -/

/-- The cursor `(entry byte, pending bytes)` after an item (`itemLanesAux`'s step). -/
def stepSt (p : Params) (st : Nat × Nat) : Item → Nat × Nat
  | .read m => (st.1, st.2 + eBytes * m)
  | .cap c _ => (st.1, st.2 + nodeBytes * 2 ^ c)
  | .sample => (st.1 + 72 + st.2, 0)
  | .positions ref => (st.1 + 72 + st.2 + ((p.level ref).nPosQ - 1) * 72, 0)
  | .opening ref =>
    (st.1 + (p.level ref).t * (40 + (p.level ref).row) + (p.level ref).t * (p.level ref).path * 104, st.2)
  | .readW m w => (st.1, st.2 + w * m)

/-- An item's lane at a cursor. -/
def laneSt (st : Nat × Nat) : Item → Nat
  | .opening _ => st.1 / 8
  | .read _ => (st.1 + 40 + st.2) / 8
  | .cap _ _ => (st.1 + 40 + st.2) / 8
  | .sample => (st.1 + 40 + st.2) / 8
  | .positions _ => (st.1 + 40 + st.2) / 8
  | .readW _ _ => (st.1 + 40 + st.2) / 8

theorem itemLanesAux_cons (p : Params) (b pend : Nat) (it : Item) (r : List Item) :
    itemLanesAux p b pend (it :: r) =
      laneSt (b, pend) it :: itemLanesAux p (stepSt p (b, pend) it).1 (stepSt p (b, pend) it).2 r := by
  cases it <;> rfl

/-- The cursor before item `k`. -/
def stAt (p : Params) (st : Nat × Nat) (items : List Item) (k : Nat) : Nat × Nat :=
  (items.take k).foldl (stepSt p) st

theorem stAt_cons_succ (p : Params) (st : Nat × Nat) (it : Item) (r : List Item) (k : Nat) :
    stAt p st (it :: r) (k + 1) = stAt p (stepSt p st it) r k := rfl

theorem stAt_succ (p : Params) : ∀ (items : List Item) (st : Nat × Nat) (k : Nat), k < items.length →
    stAt p st items (k + 1) = stepSt p (stAt p st items k) (items.getD k default)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | it :: r, st, k + 1, h => by
    rw [stAt_cons_succ, stAt_cons_succ, stAt_succ p r _ k (Nat.lt_of_succ_lt_succ h)]
    rfl

theorem itemLanesAux_getD (p : Params) : ∀ (items : List Item) (st : Nat × Nat) (k : Nat), k < items.length →
    (itemLanesAux p st.1 st.2 items).getD k 0 = laneSt (stAt p st items k) (items.getD k default)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | it :: r, st, 0, _ => by rw [itemLanesAux_cons]; rfl
  | it :: r, st, k + 1, h => by
    rw [itemLanesAux_cons, List.getD_cons_succ,
      itemLanesAux_getD p r (stepSt p (st.1, st.2) it) k (Nat.lt_of_succ_lt_succ h)]
    rfl

/-- **The lane of item `k`** is its lane at the cursor before it. -/
theorem laneOf_eq (p : Params) {k : Nat} (hk : k < (schedule p).length) :
    laneOf p k = laneSt (stAt p (startByte p, 0) (schedule p) k) ((schedule p).getD k default) :=
  itemLanesAux_getD p (schedule p) (startByte p, 0) k hk

/-! ## Whole lanes -/

/-- An item keeps the cursor on lane boundaries. -/
def itemAlB (p : Params) : Item → Bool
  | .readW _ w => w % 8 == 0
  | .opening ref =>
    ((p.level ref).t * (40 + (p.level ref).row) + (p.level ref).t * (p.level ref).path * 104) % 8 == 0
  | _ => true

theorem stepSt_al (p : Params) {st : Nat × Nat} (h : (st.1 + st.2) % 8 = 0) (it : Item) (hit : itemAlB p it = true) :
    ((stepSt p st it).1 + (stepSt p st it).2) % 8 = 0 := by
  cases it with
  | read m => show (st.1 + (st.2 + 24 * m)) % 8 = 0; omega
  | cap c r => show (st.1 + (st.2 + 32 * 2 ^ c)) % 8 = 0; omega
  | sample => show (st.1 + 72 + st.2 + 0) % 8 = 0; omega
  | positions r => show (st.1 + 72 + st.2 + ((p.level r).nPosQ - 1) * 72 + 0) % 8 = 0; omega
  | opening r =>
    have hx : ((p.level r).t * (40 + (p.level r).row) + (p.level r).t * (p.level r).path * 104) % 8 = 0 := by
      simpa [itemAlB] using hit
    show (st.1 + (p.level r).t * (40 + (p.level r).row) + (p.level r).t * (p.level r).path * 104 + st.2) % 8 = 0
    generalize (p.level r).t * (40 + (p.level r).row) = a at hx ⊢
    generalize (p.level r).t * (p.level r).path * 104 = b at hx ⊢
    omega
  | readW m w =>
    have hw : w % 8 = 0 := by simpa [itemAlB] using hit
    obtain ⟨c, rfl⟩ : 8 ∣ w := Nat.dvd_of_mod_eq_zero hw
    show (st.1 + (st.2 + 8 * c * m)) % 8 = 0
    rw [Nat.mul_assoc]
    generalize c * m = d
    omega

theorem stAt_al (p : Params) : ∀ (items : List Item) (st : Nat × Nat) (k : Nat), (st.1 + st.2) % 8 = 0 →
    (∀ it ∈ items, itemAlB p it = true) → ((stAt p st items k).1 + (stAt p st items k).2) % 8 = 0
  | [], st, k, h, _ => by cases k <;> exact h
  | _ :: _, _, 0, h, _ => h
  | it :: r, st, k + 1, h, ha => by
    rw [stAt_cons_succ]
    exact stAt_al p r _ k (stepSt_al p h it (ha it (List.mem_cons.mpr (Or.inl rfl))))
      fun i hi ↦ ha i (List.mem_cons.mpr (Or.inr hi))

/-- **The schedule keeps the cursor on lane boundaries** (one decision per stage). -/
def alignB (p : Params) : Bool := startByte p % 8 == 0 && (schedule p).all (itemAlB p)

theorem stAt_alS {p : Params} (hA : alignB p = true) (k : Nat) :
    ((stAt p (startByte p, 0) (schedule p) k).1 + (stAt p (startByte p, 0) (schedule p) k).2) % 8 = 0 := by
  simp only [alignB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hA
  exact stAt_al p _ _ k (by simpa using hA.1) hA.2

/-! ## Positions -/

/-- **The cursor position of item `k`** (`8 · lane − 40`: V's `ent + msg` before the item). -/
def posOf (p : Params) (k : Nat) : Nat := 8 * laneOf p k - 40

/-- An item's stream width (an opening: none). -/
def itemW (p : Params) : Item → Nat
  | .read m => eBytes * m
  | .cap c _ => nodeBytes * 2 ^ c
  | .sample => 72
  | .positions ref => 72 + ((p.level ref).nPosQ - 1) * 72
  | .opening _ => 0
  | .readW m w => w * m

/-- Not an opening. -/
def notOpen : Item → Bool
  | .opening _ => false
  | _ => true

theorem lane_st {p : Params} (hA : alignB p = true) {k : Nat} (hk : k < (schedule p).length)
    (ho : notOpen ((schedule p).getD k default) = true) :
    8 * laneOf p k = (stAt p (startByte p, 0) (schedule p) k).1 + (stAt p (startByte p, 0) (schedule p) k).2 + 40 := by
  have hal := stAt_alS hA k
  rw [laneOf_eq p hk]
  generalize stAt p (startByte p, 0) (schedule p) k = st at hal ⊢
  generalize (schedule p).getD k default = it at ho ⊢
  cases it <;> first
    | (show 8 * ((st.1 + 40 + st.2) / 8) = st.1 + st.2 + 40; omega)
    | (simp [notOpen] at ho)

theorem posOf_st {p : Params} (hA : alignB p = true) {k : Nat} (hk : k < (schedule p).length)
    (ho : notOpen ((schedule p).getD k default) = true) :
    posOf p k = (stAt p (startByte p, 0) (schedule p) k).1 + (stAt p (startByte p, 0) (schedule p) k).2 := by
  unfold posOf
  rw [lane_st hA hk ho]
  omega

/-- **An item's lane and position**: `8 · lane = pos + 40`. -/
theorem lane_pos {p : Params} (hA : alignB p = true) {k : Nat} (hk : k < (schedule p).length)
    (ho : notOpen ((schedule p).getD k default) = true) : 8 * laneOf p k = posOf p k + 40 := by
  rw [lane_st hA hk ho, posOf_st hA hk ho]

/-- **The step**: between two items that are not openings, the position advances by the first one's width. -/
theorem posOf_succ {p : Params} (hA : alignB p = true) {k : Nat} (hk : k + 1 < (schedule p).length)
    (h0 : notOpen ((schedule p).getD k default) = true) (h1 : notOpen ((schedule p).getD (k + 1) default) = true) :
    posOf p (k + 1) = posOf p k + itemW p ((schedule p).getD k default) := by
  rw [posOf_st hA hk h1, posOf_st hA (by omega) h0, stAt_succ p _ _ k (by omega)]
  generalize stAt p (startByte p, 0) (schedule p) k = st
  generalize (schedule p).getD k default = it at h0 ⊢
  cases it <;> simp only [stepSt, itemW, notOpen, eBytes, nodeBytes, Bool.false_eq_true] at h0 ⊢ <;> omega

/-- **A run of items**: if items `k …` of the schedule are `xs` (no opening in `xs`, nor the item after it), the
position advances over `xs` by its widths. -/
theorem posOf_items {p : Params} (hA : alignB p = true) : ∀ (xs : List Item) (k : Nat),
    k + xs.length < (schedule p).length →
    (∀ i < xs.length, (schedule p).getD (k + i) default = xs.getD i default) → (∀ it ∈ xs, notOpen it = true) →
    notOpen ((schedule p).getD (k + xs.length) default) = true →
    posOf p (k + xs.length) = posOf p k + (xs.map (itemW p)).sum
  | [], k, _, _, _, _ => by simp
  | it :: r, k, hk, hits, ho, hend => by
    simp only [List.length_cons] at hk hend
    have e0 : (schedule p).getD k default = it := by
      have := hits 0 (by simp)
      rw [Nat.add_zero, List.getD_cons_zero] at this
      exact this
    have h0 : notOpen ((schedule p).getD k default) = true := by
      rw [e0]; exact ho it (List.mem_cons.mpr (Or.inl rfl))
    have h1 : notOpen ((schedule p).getD (k + 1) default) = true := by
      rcases r with _ | ⟨it', r'⟩
      · simpa using hend
      · rw [hits 1 (by simp)]
        exact ho it' (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have ih := posOf_items hA r (k + 1) (by omega)
      (fun i hi ↦ by
        rw [show k + 1 + i = k + (i + 1) by omega, hits (i + 1) (by simp only [List.length_cons]; omega),
          List.getD_cons_succ])
      (fun x hx ↦ ho x (List.mem_cons.mpr (Or.inr hx)))
      (by rw [show k + 1 + r.length = k + (r.length + 1) by omega]; exact hend)
    have hs := posOf_succ hA (k := k) (by omega) h0 h1
    rw [e0] at hs
    rw [List.length_cons, show k + (r.length + 1) = k + 1 + r.length by omega, ih, hs]
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## The builders' widths -/

/-- The widths of a list of items. -/
def wsum (p : Params) (xs : List Item) : Nat := (xs.map (itemW p)).sum

/-- No opening among the items. -/
def NoOpen (xs : List Item) : Prop := ∀ it ∈ xs, notOpen it = true

theorem wsum_append (p : Params) (a b : List Item) : wsum p (a ++ b) = wsum p a + wsum p b := by
  simp only [wsum, List.map_append, List.sum_append]

theorem noOpen_append {a b : List Item} (ha : NoOpen a) (hb : NoOpen b) : NoOpen (a ++ b) := fun it hit ↦ by
  rcases List.mem_append.mp hit with h | h
  · exact ha it h
  · exact hb it h

theorem wsum_rep (p : Params) (xs : List Item) : ∀ n, wsum p (List.replicate n xs).flatten = n * wsum p xs
  | 0 => by simp [wsum]
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, wsum_append, wsum_rep p xs n]
    ring

theorem noOpen_rep {xs : List Item} (h : NoOpen xs) (n : Nat) : NoOpen (List.replicate n xs).flatten := by
  intro it hit
  obtain ⟨l, hl, hit⟩ := List.mem_flatten.mp hit
  rw [(List.eq_of_mem_replicate hl)] at hit
  exact h it hit

theorem wsum_gsmpN (p : Params) (n : Nat) : wsum p (gsmpN n) = 80 * n := by
  rw [gsmpN, wsum_rep, show wsum p gsmp = 80 from rfl, Nat.mul_comm]

theorem noOpen_gsmp : NoOpen gsmp := fun it hit ↦ by
  simp only [gsmp, List.mem_cons, List.mem_nil_iff, or_false] at hit
  rcases hit with rfl | rfl <;> rfl

theorem noOpen_gsmpN (n : Nat) : NoOpen (gsmpN n) := noOpen_rep noOpen_gsmp n

theorem length_gsmpN (n : Nat) : (gsmpN n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gsmpN, List.replicate_succ, List.flatten_cons, List.length_append, ← gsmpN, ih]
    show 2 + 2 * n = 2 * (n + 1)
    omega

theorem noOpen_smp (n : Nat) : NoOpen (smp n) := fun it hit ↦ by
  unfold smp at hit; rw [List.eq_of_mem_replicate hit]; rfl

theorem wsum_rdE2 (p : Params) (m : Nat) : wsum p (rdE2 m) = 16 * m := by
  unfold rdE2; split
  · subst_vars; rfl
  · simp [wsum, itemW, e2Bytes, Nat.mul_comm]

theorem noOpen_rdE2 (m : Nat) : NoOpen (rdE2 m) := by
  unfold rdE2; split
  · intro it hit; exact absurd hit List.not_mem_nil
  · intro it hit; rw [List.mem_singleton.mp hit]; rfl

theorem wsum_sumcheckE2I (p : Params) (r d : Nat) : wsum p (sumcheckE2I r d) = r * (16 * d + 80) := by
  rw [sumcheckE2I, wsum_rep, wsum_append, wsum_rdE2]; rfl

theorem length_sumcheckE2I (r d : Nat) (hd : d ≠ 0) : (sumcheckE2I r d).length = 3 * r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [sumcheckE2I, List.replicate_succ, List.flatten_cons, List.length_append, ← sumcheckE2I, ih,
      List.length_append, show (rdE2 d).length = 1 by simp [rdE2, hd]]
    show 1 + 2 + 3 * r = 3 * (r + 1)
    omega

theorem noOpen_sumcheckE2I (r d : Nat) : NoOpen (sumcheckE2I r d) :=
  noOpen_rep (noOpen_append (noOpen_rdE2 d) noOpen_gsmp) r

/-- A Keccak layer's widths at `E2`: `3368 + 112 · point` (U of 105 scalars). -/
theorem wsum_keccakLayerE2I (p : Params) (k : Nat) : wsum p (keccakLayerE2I k) = 3368 + 112 * k := by
  simp only [keccakLayerE2I, List.flatten_cons, List.flatten_nil, List.append_nil, wsum_append, wsum_rdE2,
    wsum_sumcheckE2I, productBits, localBits]
  have hs : wsum p sepI = 72 := rfl
  have hg : wsum p gsmp = 80 := rfl
  rw [hs, hg]
  ring

theorem noOpen_keccakLayerE2I (k : Nat) : NoOpen (keccakLayerE2I k) := by
  simp only [keccakLayerE2I, List.flatten_cons, List.flatten_nil, List.append_nil]
  refine noOpen_append (noOpen_rdE2 _) (noOpen_append ?_ (noOpen_append noOpen_gsmp
    (noOpen_append (noOpen_sumcheckE2I _ _) (noOpen_append (noOpen_sumcheckE2I _ _)
      (noOpen_append (noOpen_rdE2 _) noOpen_gsmp)))))
  intro it hit; simp only [sepI, List.mem_singleton] at hit; subst hit; rfl

/-- The tape GKR's widths at `E2`: five lane challenges, 24 layers. -/
theorem wsum_tapeLayersE2I (p : Params) (L : Nat) :
    wsum p (tapeLayersE2I L) = 400 + 24 * (3368 + 112 * (L - 5)) := by
  rw [tapeLayersE2I, wsum_append, wsum_gsmpN, wsum_rep, wsum_keccakLayerE2I]; rfl

theorem noOpen_tapeLayersE2I (L : Nat) : NoOpen (tapeLayersE2I L) :=
  noOpen_append (noOpen_gsmpN _) (noOpen_rep (noOpen_keccakLayerE2I _) _)

/-- The `KS` GKR's widths at `E2` (`verify_keccak`, 12 layers, the tails): `3440 + 12 · (3368 + 112 · point)`. -/
theorem wsum_keccakE2I (p : Params) (k : Nat) :
    wsum p (keccakE2I k) = 3440 + 12 * (3368 + 112 * (k - 5 + 1)) := by
  simp only [keccakE2I, List.flatten_cons, List.flatten_nil, List.append_nil, wsum_append, wsum_gsmpN, wsum_rdE2,
    wsum_rep, wsum_keccakLayerE2I, wsum_sumcheckE2I, segmentBits, laneBits, gkrDepth, packBits, slotLog, kBits]
  omega

theorem noOpen_keccakE2I (k : Nat) : NoOpen (keccakE2I k) := by
  simp only [keccakE2I, List.flatten_cons, List.flatten_nil, List.append_nil]
  exact noOpen_append (noOpen_gsmpN _) (noOpen_append (noOpen_rdE2 _) (noOpen_append
    (noOpen_rep (noOpen_keccakLayerE2I _) _) (noOpen_append (noOpen_sumcheckE2I _ _) (noOpen_append (noOpen_rdE2 _)
      (noOpen_append (noOpen_sumcheckE2I _ _) (noOpen_append (noOpen_sumcheckE2I _ _) (noOpen_rdE2 _)))))))

theorem keccakE2I_head (k : Nat) : (keccakE2I k).getD 0 default = .readW 1 nonceBytes := rfl

theorem keccakE2I_len (k : Nat) : 2 ≤ (keccakE2I k).length := by
  simp only [keccakE2I, List.flatten_cons, List.length_append, length_gsmpN, segmentBits, laneBits]
  omega

/-! ## A phase's items -/

/-- **Item `j` of a phase** is item `phaseItem0 + j` of the flattened phase list (distinct phase keys). -/
theorem getD_phase : ∀ (L : List (Phase × List Item)) {ph : Phase} {its : List Item}, (ph, its) ∈ L →
    (L.map (·.1)).Nodup → ∀ {j : Nat}, j < its.length →
    (L.flatMap (·.2)).getD (((L.takeWhile (·.1 != ph)).map (·.2.length)).sum + j) default = its.getD j default
  | [], _, _, hm, _, _, _ => absurd hm List.not_mem_nil
  | (ph', its') :: L, ph, its, hm, hnd, j, hj => by
    simp only [List.map_cons, List.nodup_cons, List.flatMap_cons] at hnd ⊢
    by_cases he : ph' = ph
    · subst he
      have hits : its = its' := by
        rcases List.mem_cons.mp hm with e | e
        · exact (Prod.mk.inj e).2
        · exact (hnd.1 (List.mem_map.mpr ⟨_, e, rfl⟩)).elim
      subst hits
      simp only [List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.map_nil,
        List.sum_nil, Nat.zero_add]
      exact List.getD_append _ _ _ _ hj
    · have hm' : (ph, its) ∈ L := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd (Prod.mk.inj e).1.symm he
        · exact e
      have hb : (ph' != ph) = true := bne_iff_ne.mpr he
      simp only [List.takeWhile_cons, hb, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [Nat.add_assoc, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact getD_phase L hm' hnd.2 hj

/-- A phase's items end within the flattened list. -/
theorem len_phase : ∀ (L : List (Phase × List Item)) {ph : Phase} {its : List Item}, (ph, its) ∈ L →
    (L.map (·.1)).Nodup →
    ((L.takeWhile (·.1 != ph)).map (·.2.length)).sum + its.length ≤ (L.flatMap (·.2)).length
  | [], _, _, hm, _ => absurd hm List.not_mem_nil
  | (ph', its') :: L, ph, its, hm, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.flatMap_cons, List.length_append] at hnd ⊢
    by_cases he : ph' = ph
    · subst he
      have hits : its = its' := by
        rcases List.mem_cons.mp hm with e | e
        · exact (Prod.mk.inj e).2
        · exact (hnd.1 (List.mem_map.mpr ⟨_, e, rfl⟩)).elim
      subst hits
      simp only [List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.map_nil,
        List.sum_nil]
      omega
    · have hm' : (ph, its) ∈ L := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd (Prod.mk.inj e).1.symm he
        · exact e
      have hb : (ph' != ph) = true := bne_iff_ne.mpr he
      simp only [List.takeWhile_cons, hb, ↓reduceIte, List.map_cons, List.sum_cons]
      have := len_phase L hm' hnd.2
      omega

/-- **The phases at a stage with the root pin and the `E2` front**: S2GF's, or at stage 2 S2GT's (`phasesS2GT`: only
the phase `bus` differs). -/
def phasesE2 (p : Params) : List (Phase × List Item) := if p.stage = 2 then phasesS2GT p else phasesS2GF p

/-- A stage with the root pin and the `E2` front: S2GF (`stage = 1`) or S2GT (`stage = 2`). -/
def StE2 (p : Params) : Prop := p.stage = 1 ∨ p.stage = 2

theorem phases_E2 {p : Params} (h : StE2 p) : phases p = phasesE2 p := by
  rcases h with h | h <;> simp [phases, phasesE2, h]

theorem nodup_e2 (p : Params) : ((phasesE2 p).map (·.1)).Nodup := by
  unfold phasesE2; split <;> simp [phasesS2GT, phasesS2GF]

/-! ## The root pin at a stage with it (`StE2`: S2GF or S2GT) -/

section Pin

variable {p : Params} (h : StE2 p)
include h

theorem sched_s2gf : schedule p = .cap (p.level ⟨.main, 0⟩).cap ⟨.main, 0⟩ ::
    (smp p.nuMain ++ rd 1 ++ ((phasesE2 p).drop 1).flatMap (·.2)) := by
  rw [schedule, phases_E2 h, phasesE2]
  split <;> rfl

/-- **Item `j` of phase `ph`** at S2GF is item `j` of its builder list in `phasesS2GF`. -/
theorem sched_phase {ph : Phase} {its : List Item} (hm : (ph, its) ∈ phasesE2 p) {j : Nat} (hj : j < its.length) :
    (schedule p).getD (phaseItem0 p ph + j) default = its.getD j default := by
  rw [schedule, phaseItem0, phases_E2 h]
  exact getD_phase _ hm (nodup_e2 p) hj

theorem phase_lt {ph : Phase} {its : List Item} (hm : (ph, its) ∈ phasesE2 p) {j : Nat} (hj : j < its.length) :
    phaseItem0 p ph + j < (schedule p).length := by
  have := len_phase _ hm (nodup_e2 p)
  rw [schedule, phaseItem0, phases_E2 h]
  omega

theorem notOpen_in {ph : Phase} {its : List Item} (hm : (ph, its) ∈ phasesE2 p) (ho : NoOpen its) {j : Nat}
    (hj : j < its.length) : notOpen ((schedule p).getD (phaseItem0 p ph + j) default) = true := by
  rw [sched_phase h hm hj, List.getD_eq_getElem _ _ hj]
  exact ho _ (List.getElem_mem hj)

theorem sched_zero : (schedule p).getD 0 default = .cap (p.level ⟨.main, 0⟩).cap ⟨.main, 0⟩ := by
  rw [sched_s2gf h]; rfl

theorem sched_pin {i : Nat} (hi : i < p.nuMain) : (schedule p).getD (i + 1) default = .sample := by
  rw [sched_s2gf h, List.getD_cons_succ, List.append_assoc, List.getD_append _ _ _ _ (by simpa [smp] using hi)]
  simp [smp, List.getD_eq_getElem?_getD, hi]

theorem sched_read : (schedule p).getD (p.nuMain + 1) default = .read 1 := by
  rw [sched_s2gf h, List.getD_cons_succ, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp [smp])]
  simp [smp, rd]

/-- The typed phases' first item is a sample (`τ₀`). -/
theorem sched_bus : (schedule p).getD (p.nuMain + 2) default = .sample := by
  rw [sched_s2gf h, List.getD_cons_succ, List.append_assoc, List.getD_append_right _ _ _ _ (by simp [smp]),
    show p.nuMain + 1 - (smp p.nuMain).length = 1 by simp [smp]]
  unfold phasesE2; split <;> rfl

theorem sched_len : p.nuMain + 2 < (schedule p).length := by
  by_contra hc
  have e := sched_bus h
  rw [List.getD_eq_default _ _ (by omega)] at e
  exact absurd e (by decide)

theorem phaseItem0_commit : phaseItem0 p .commit = 0 := by
  rcases h with h | h <;> simp [phaseItem0, phases, h, phasesS2GT, phasesS2GF]

theorem phaseItem0_bus : phaseItem0 p .bus = p.nuMain + 2 := by
  rcases h with h | h <;> simp [phaseItem0, phases, h, phasesS2GT, phasesS2GF, smp, rd] <;> omega

theorem notOpen_pin {j : Nat} (hj : j ≤ p.nuMain + 1) : notOpen ((schedule p).getD j default) = true := by
  rcases j with _ | j
  · rw [sched_zero h]; rfl
  · rcases Nat.lt_or_ge j p.nuMain with hj' | hj'
    · rw [sched_pin h hj']; rfl
    · rw [show j = p.nuMain by omega, sched_read h]; rfl

variable (hA : alignB p = true)
include hA

/-- **A run inside a phase**: if phase `ph`'s items are `pre ++ xs ++ post` (`|pre| = a`, `|xs| = b`, no opening in
`xs` nor at the item after it), the position advances over `xs` by its widths. -/
theorem posOf_run {ph : Phase} {its pre xs post : List Item} {a b : Nat} (hm : (ph, its) ∈ phasesE2 p)
    (hs : its = pre ++ xs ++ post) (ha : pre.length = a) (hb : xs.length = b) (ho : NoOpen xs)
    (hk : phaseItem0 p ph + (a + b) < (schedule p).length)
    (hend : notOpen ((schedule p).getD (phaseItem0 p ph + (a + b)) default) = true) :
    posOf p (phaseItem0 p ph + a + b) = posOf p (phaseItem0 p ph + a) + wsum p xs := by
  subst ha hb
  have e := posOf_items hA xs (phaseItem0 p ph + pre.length) (by rw [Nat.add_assoc]; exact hk)
    (fun i hi ↦ by
      have hj : pre.length + i < its.length := by rw [hs]; simp only [List.length_append]; omega
      rw [Nat.add_assoc, sched_phase h hm hj, hs, List.append_assoc,
        List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getD_append _ _ _ _ hi])
    ho (by rw [Nat.add_assoc]; exact hend)
  exact e

theorem posOf_zero : posOf p 0 = startByte p := by
  rw [posOf_st hA (by have := sched_len h; omega) (notOpen_pin h (by omega))]
  rfl

theorem posOf_one : posOf p 1 = startByte p + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap := by
  have e := posOf_succ hA (k := 0) (by have := sched_len h; omega) (notOpen_pin h (by omega))
    (notOpen_pin h (by omega))
  rw [sched_zero h, posOf_zero h hA] at e
  exact e

/-- The pin's samples: `posOf (1 + i) = posOf 1 + 72 i` (`i ≤ ν`). -/
theorem posOf_pin : ∀ i ≤ p.nuMain, posOf p (i + 1) = posOf p 1 + 72 * i
  | 0, _ => rfl
  | i + 1, hi => by
    have e := posOf_succ hA (k := i + 1) (by have := sched_len h; omega) (notOpen_pin h (by omega))
      (notOpen_pin h (by omega))
    rw [sched_pin h (by omega), posOf_pin i (by omega)] at e
    rw [e]
    show posOf p 1 + 72 * i + 72 = posOf p 1 + 72 * (i + 1)
    omega

/-- **`pin_phase`'s `hP`** (QH5): the first pin answer's lane. -/
theorem pin_hP : posOf p 1 + 40 = 8 * phaseLane p .commit 1 := by
  rw [phaseLane, phaseItem0_commit h, lane_pos hA (by have := sched_len h; omega) (notOpen_pin h (by omega))]

/-- **`pin_phase`'s `hqa`** (QH5): the pin's value read `ν` samples later. -/
theorem pin_hqa : phaseLane p .commit (p.nuMain + 1) = phaseLane p .commit 1 + 9 * p.nuMain := by
  have h1 := pin_hP h hA
  have h2 := lane_pos hA (k := p.nuMain + 1) (by have := sched_len h; omega) (notOpen_pin h le_rfl)
  rw [posOf_pin h hA p.nuMain le_rfl] at h2
  rw [phaseLane, phaseLane, phaseItem0_commit h, Nat.zero_add, Nat.zero_add]
  rw [phaseLane, phaseItem0_commit h, Nat.zero_add] at h1
  omega

/-- **The pin's end is the typed phases' start**: `posOf 1 + 72 ν + 24 = typedPosF p`. -/
theorem pin_end : posOf p 1 + 72 * p.nuMain + 24 = typedPosF p := by
  have e := posOf_succ hA (k := p.nuMain + 1) (sched_len h) (notOpen_pin h le_rfl)
    (by rw [show p.nuMain + 1 + 1 = p.nuMain + 2 by omega, sched_bus h]; rfl)
  rw [sched_read h, posOf_pin h hA p.nuMain le_rfl] at e
  rw [show typedPosF p = posOf p (phaseItem0 p .bus) from rfl, phaseItem0_bus h,
    show p.nuMain + 2 = p.nuMain + 1 + 1 by omega, e]
  rfl

end Pin

/-! ## The tape phase (`StE2`) -/

/-- The tape phase's items at S2GF: the separator, `logN` ground challenges, the 25 outputs, the GKR. -/
abbrev tapeIts (p : Params) : List Item := List.flatten [sepI, gsmpN p.logN, rdE2 lanes, tapeLayersE2I p.logN]

theorem mem_tape (p : Params) : (Phase.tape, tapeIts p) ∈ phasesE2 p := by
  unfold phasesE2; split <;> simp [phasesS2GT, phasesS2GF]

theorem noOpen_sepI : NoOpen sepI := fun it hit ↦ by
  simp only [sepI, List.mem_singleton] at hit; subst hit; rfl

theorem noOpen_tape (p : Params) : NoOpen (tapeIts p) := by
  simp only [tapeIts, List.flatten_cons, List.flatten_nil, List.append_nil]
  exact noOpen_append noOpen_sepI (noOpen_append (noOpen_gsmpN _) (noOpen_append (noOpen_rdE2 _)
    (noOpen_tapeLayersE2I _)))

theorem length_tape (p : Params) : (tapeIts p).length = 2 * p.logN + 2 + (tapeLayersE2I p.logN).length := by
  simp only [tapeIts, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append, length_gsmpN]
  have h1 : sepI.length = 1 := rfl
  have h2 : (rdE2 lanes).length = 1 := rfl
  rw [h1, h2]
  omega

/-- The wire phase's items at S2GF. -/
abbrev wireIts (p : Params) : List Item :=
  List.flatten [sumcheckE2I p.logN 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages]

theorem mem_wire (p : Params) : (Phase.wire, wireIts p) ∈ phasesE2 p := by
  unfold phasesE2; split <;> simp [phasesS2GT, phasesS2GF]

theorem noOpen_wire (p : Params) : NoOpen (wireIts p) := by
  simp only [wireIts, List.flatten_cons, List.flatten_nil, List.append_nil]
  exact noOpen_append (noOpen_sumcheckE2I _ _) (noOpen_append (noOpen_rdE2 _) (noOpen_append
    (noOpen_sumcheckE2I _ _) (noOpen_append (noOpen_rdE2 _) (noOpen_smp _))))

theorem wire_pos (p : Params) : 0 < (wireIts p).length := by
  simp only [wireIts, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
  have : (rdE2 1).length = 1 := rfl
  omega

/-- The wire phase starts after the tape's items. -/
theorem phaseItem0_wire {p : Params} (h : StE2 p) :
    phaseItem0 p .wire = phaseItem0 p .tape + (tapeIts p).length := by
  rcases h with h | h <;> simp [phaseItem0, phases, h, phasesS2GT, phasesS2GF] <;> omega

/-- The `KS` phase's items at S2GF. -/
abbrev ksIts (p : Params) : List Item :=
  List.flatten [gsmpN p.ksLog, rdE2 lanes, keccakE2I p.ksLog, smp rowSwitchStages]

theorem mem_ks (p : Params) : (Phase.ks, ksIts p) ∈ phasesE2 p := by
  unfold phasesE2; split <;> simp [phasesS2GT, phasesS2GF]

theorem ks_split (p : Params) :
    ksIts p = gsmpN p.ksLog ++ rdE2 lanes ++ keccakE2I p.ksLog ++ smp rowSwitchStages := by
  simp [ksIts, List.append_assoc]

theorem noOpen_ks (p : Params) : NoOpen (ksIts p) := by
  rw [ks_split]
  exact noOpen_append (noOpen_append (noOpen_append (noOpen_gsmpN _) (noOpen_rdE2 _)) (noOpen_keccakE2I _))
    (noOpen_smp _)

theorem length_ks (p : Params) :
    (ksIts p).length = 2 * p.ksLog + 1 + (keccakE2I p.ksLog).length + rowSwitchStages := by
  have h1 : (rdE2 lanes).length = 1 := rfl
  rw [ks_split]
  simp only [List.length_append, length_gsmpN, h1, smp, List.length_replicate]

theorem ks_pos (p : Params) : 0 < (ksIts p).length := by
  simp only [ksIts, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
  have : (rdE2 lanes).length = 1 := rfl
  omega

/-- The `KS` phase starts after the wire's items. -/
theorem phaseItem0_ks {p : Params} (h : StE2 p) :
    phaseItem0 p .ks = phaseItem0 p .wire + (wireIts p).length := by
  rcases h with h | h <;> simp [phaseItem0, phases, h, phasesS2GT, phasesS2GF] <;> omega

theorem wsum_smp (p : Params) (n : Nat) : wsum p (smp n) = 72 * n := by
  simp [wsum, smp, itemW, Nat.mul_comm]

/-- The wire phase's items before its row switch. -/
abbrev wireBody (p : Params) : List Item := sumcheckE2I p.logN 2 ++ rdE2 1 ++ sumcheckE2I 2 2 ++ rdE2 kBits

theorem wire_split (p : Params) : wireIts p = wireBody p ++ smp rowSwitchStages := by
  simp [wireIts, wireBody, List.append_assoc]

theorem noOpen_wireBody (p : Params) : NoOpen (wireBody p) :=
  noOpen_append (noOpen_append (noOpen_append (noOpen_sumcheckE2I _ _) (noOpen_rdE2 _)) (noOpen_sumcheckE2I _ _))
    (noOpen_rdE2 _)

theorem length_wireBody (p : Params) : (wireBody p).length = 3 * p.logN + 8 := by
  have h1 : (rdE2 1).length = 1 := rfl
  have h2 : (rdE2 kBits).length = 1 := rfl
  simp only [wireBody, List.length_append, length_sumcheckE2I _ 2 (by decide), h1, h2]

theorem wsum_wireBody (p : Params) : wsum p (wireBody p) = 112 * p.logN + 1264 := by
  simp only [wireBody, wsum_append, wsum_sumcheckE2I, wsum_rdE2, kBits]
  omega

theorem length_wire (p : Params) : (wireIts p).length = 3 * p.logN + 8 + rowSwitchStages := by
  simp only [wireIts, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
    length_sumcheckE2I _ 2 (by decide)]
  have h1 : (rdE2 1).length = 1 := rfl
  have h2 : (rdE2 kBits).length = 1 := rfl
  have h3 : (smp rowSwitchStages).length = rowSwitchStages := List.length_replicate
  rw [h1, h2, h3]
  omega

/-- The `KS` link phase's items at S2GF. -/
abbrev linkIts (p : Params) : List Item :=
  List.flatten [gsmpN (p.ksLog + laneBits), sumcheckE2I p.ksLog 2, rdE2 4]

theorem mem_link (p : Params) : (Phase.ksLink, linkIts p) ∈ phasesE2 p := by
  unfold phasesE2; split <;> simp [phasesS2GT, phasesS2GF]

theorem link_split (p : Params) : linkIts p = gsmpN (p.ksLog + laneBits) ++ sumcheckE2I p.ksLog 2 ++ rdE2 4 := by
  simp [linkIts, List.append_assoc]

theorem noOpen_link (p : Params) : NoOpen (linkIts p) := by
  rw [link_split]
  exact noOpen_append (noOpen_append (noOpen_gsmpN _) (noOpen_sumcheckE2I _ _)) (noOpen_rdE2 _)

theorem length_link (p : Params) : (linkIts p).length = 2 * (p.ksLog + laneBits) + 3 * p.ksLog + 1 := by
  have h1 : (rdE2 4).length = 1 := rfl
  rw [link_split]
  simp only [List.length_append, length_gsmpN, length_sumcheckE2I _ 2 (by decide), h1]

theorem wsum_link (p : Params) : wsum p (linkIts p) = 80 * (p.ksLog + laneBits) + 112 * p.ksLog + 64 := by
  rw [link_split]
  simp only [wsum_append, wsum_gsmpN, wsum_sumcheckE2I, wsum_rdE2]
  omega

/-- The opening phase's first item (the separating sample). -/
theorem open_head (p : Params) (h : StE2 p) :
    (schedule p).getD (phaseItem0 p .openMain) default = .sample ∧ phaseItem0 p .openMain < (schedule p).length := by
  have hm : (Phase.openMain, smp 1 ++ (if p.mainOod then whirIJ else whirI) .main p.mainLevels p.mainFinalLog p.grind)
      ∈ phasesE2 p := by
    unfold phasesE2; split <;> simp [phasesS2GT, phasesS2GF]
  have e := sched_phase h hm (j := 0) (by simp [smp])
  have l := phase_lt h hm (j := 0) (by simp [smp])
  rw [Nat.add_zero] at e l
  exact ⟨e.trans rfl, l⟩

/-- The `KS` link phase starts after `KS`'s items; the opening after the link's. -/
theorem phaseItem0_link {p : Params} (h : StE2 p) :
    phaseItem0 p .ksLink = phaseItem0 p .ks + (ksIts p).length := by
  rcases h with h | h <;> simp [phaseItem0, phases, h, phasesS2GT, phasesS2GF] <;> omega

theorem phaseItem0_open {p : Params} (h : StE2 p) :
    phaseItem0 p .openMain = phaseItem0 p .ksLink + (linkIts p).length := by
  rcases h with h | h <;> simp [phaseItem0, phases, h, phasesS2GT, phasesS2GF] <;> omega

section Tape

variable {p : Params} (h : StE2 p) (hA : alignB p = true)
include h hA

/-- **The separator**: from the tape's start, 72 bytes (QH5's `sepE2_phase`). -/
theorem tape_sep : posOf p (phaseItem0 p .tape + 1) = posOf p (phaseItem0 p .tape) + 72 := by
  have hl := length_tape p
  have e := posOf_run h hA (a := 0) (b := 1) (mem_tape p) (pre := []) (xs := sepI)
    (post := List.flatten [gsmpN p.logN, rdE2 lanes, tapeLayersE2I p.logN]) rfl rfl rfl noOpen_sepI
    (phase_lt h (mem_tape p) (by omega)) (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  exact e

/-- **The `logN` ground challenges `r_i`** (QH5's `samplesG_phase`): 80 bytes each. -/
theorem tape_rs : posOf p (phaseItem0 p .tape + 1 + 2 * p.logN) = posOf p (phaseItem0 p .tape + 1) + 80 * p.logN := by
  have hl := length_tape p
  have e := posOf_run h hA (a := 1) (b := 2 * p.logN) (mem_tape p) (pre := sepI) (xs := gsmpN p.logN)
    (post := List.flatten [rdE2 lanes, tapeLayersE2I p.logN]) rfl rfl (length_gsmpN _) (noOpen_gsmpN _)
    (phase_lt h (mem_tape p) (by omega)) (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  rw [wsum_gsmpN] at e
  exact e

/-- **The 25 outputs** (QH5's `readE2s_phase`): their first lane (`8 · lane = P + 40`) and 400 bytes. -/
theorem tape_out : 8 * phaseLane p .tape (2 * p.logN + 1) = posOf p (phaseItem0 p .tape + 1 + 2 * p.logN) + 40 ∧
    posOf p (phaseItem0 p .tape + 1 + 2 * p.logN + 1) = posOf p (phaseItem0 p .tape + 1 + 2 * p.logN) + 400 := by
  have hl := length_tape p
  have hT : 10 ≤ (tapeLayersE2I p.logN).length := by
    rw [tapeLayersE2I, List.length_append, length_gsmpN]; show 10 ≤ 2 * 5 + _; omega
  refine ⟨?_, ?_⟩
  · rw [phaseLane, show phaseItem0 p .tape + (2 * p.logN + 1) = phaseItem0 p .tape + 1 + 2 * p.logN by omega]
    exact lane_pos hA (by have := phase_lt h (mem_tape p) (j := 2 * p.logN + 1) (by omega); omega)
      (by rw [Nat.add_assoc]; exact notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  · have e := posOf_run h hA (a := 1 + 2 * p.logN) (b := 1) (mem_tape p) (pre := sepI ++ gsmpN p.logN)
      (xs := rdE2 lanes) (post := tapeLayersE2I p.logN) (by simp [tapeIts, List.append_assoc])
      (by rw [List.length_append, length_gsmpN]; rfl) rfl (noOpen_rdE2 _)
      (phase_lt h (mem_tape p) (by omega)) (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
    rw [wsum_rdE2, ← Nat.add_assoc] at e
    exact e

/-- **The tape GKR's start** (QH4's `tape_phase2`: `8 qs − 48`, `qs` the first lane challenge's answer, after its
nonce at item `2 logN + 2`). -/
theorem tape_qsA : 8 * phaseLane p .tape (2 * p.logN + 3) = posOf p (phaseItem0 p .tape + (2 * p.logN + 2)) + 48 := by
  have hl := length_tape p
  have hT : 10 ≤ (tapeLayersE2I p.logN).length := by
    rw [tapeLayersE2I, List.length_append, length_gsmpN]; show 10 ≤ 2 * 5 + _; omega
  have hn : (schedule p).getD (phaseItem0 p .tape + (2 * p.logN + 2)) default = .readW 1 nonceBytes := by
    rw [sched_phase h (mem_tape p) (by omega)]
    have e1 : sepI.length = 1 := rfl
    have e2 : (rdE2 lanes).length = 1 := rfl
    have hs : tapeIts p = (sepI ++ gsmpN p.logN ++ rdE2 lanes) ++ tapeLayersE2I p.logN := by
      simp [tapeIts, List.append_assoc]
    rw [hs, List.getD_append_right _ _ _ _ (by simp only [List.length_append, length_gsmpN, e1, e2]; omega),
      show 2 * p.logN + 2 - (sepI ++ gsmpN p.logN ++ rdE2 lanes).length = 0 by
        simp only [List.length_append, length_gsmpN, e1, e2]; omega]
    rfl
  have e := posOf_succ hA (k := phaseItem0 p .tape + (2 * p.logN + 2))
    (by have := phase_lt h (mem_tape p) (j := 2 * p.logN + 3) (by omega); omega)
    (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
    (by rw [Nat.add_assoc]; exact notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  rw [hn] at e
  have l3 := lane_pos hA (k := phaseItem0 p .tape + (2 * p.logN + 3)) (phase_lt h (mem_tape p) (by omega))
    (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  rw [phaseLane, l3, show phaseItem0 p .tape + (2 * p.logN + 3) = phaseItem0 p .tape + (2 * p.logN + 2) + 1 by omega,
    e]
  simp only [itemW, nonceBytes]

/-- **The tape GKR's end is the wire's start** (QH4's `tape_phase2` end `8 · tapeEnd2 P qs − 40`, `P = logN − 6`). -/
theorem tape_end (hlog : 6 ≤ p.logN) :
    8 * Lvm.Q1.tapeEnd2 (p.logN - 6) (phaseLane p .tape (2 * p.logN + 3)) - 40 = posOf p (phaseItem0 p .wire) := by
  have hl := length_tape p
  have hw := phaseItem0_wire h
  have hwl := phase_lt h (mem_wire p) (j := 0) (wire_pos p)
  have e := posOf_run h hA (a := 2 * p.logN + 2) (b := (tapeLayersE2I p.logN).length) (mem_tape p)
    (pre := sepI ++ gsmpN p.logN ++ rdE2 lanes) (xs := tapeLayersE2I p.logN) (post := [])
    (by simp [tapeIts, List.append_assoc])
    (by simp only [List.length_append, length_gsmpN]; show 1 + 2 * p.logN + 1 = _; omega) rfl
    (noOpen_tapeLayersE2I _) (by omega)
    (by rw [show phaseItem0 p .tape + (2 * p.logN + 2 + (tapeLayersE2I p.logN).length) = phaseItem0 p .wire + 0 by
          omega]
        exact notOpen_in h (mem_wire p) (noOpen_wire p) (wire_pos p))
  have hq := tape_qsA h hA
  rw [show phaseItem0 p .wire = phaseItem0 p .tape + (2 * p.logN + 2) + (tapeLayersE2I p.logN).length by omega, e,
    wsum_tapeLayersE2I]
  simp only [Lvm.Q1.tapeEnd2, Lvm.Q1.tapeQ2, tapeDepth, Lvm.Q1.lay02, Lvm.Q1.LCfg.str2]
  omega

/-! ## The wire phase -/

/-- **The wiring's first message lane** (QH2's `wireG2` `qw`: `8 · qw = P + 40`, `P` the wire's start). -/
theorem wire_qw : 8 * phaseLane p .wire 0 = posOf p (phaseItem0 p .wire) + 40 :=
  lane_pos hA (phase_lt h (mem_wire p) (wire_pos p)) (notOpen_in h (mem_wire p) (noOpen_wire p) (wire_pos p))

/-- **The wiring's rounds and values** (before the row switch): `112 logN + 1264` bytes. -/
theorem wire_body : posOf p (phaseItem0 p .wire + (3 * p.logN + 8)) =
    posOf p (phaseItem0 p .wire) + (112 * p.logN + 1264) := by
  have hl := length_wire p
  have hr : rowSwitchStages = 7 := rfl
  have e := posOf_run h hA (a := 0) (b := 3 * p.logN + 8) (mem_wire p) (pre := []) (xs := wireBody p)
    (post := smp rowSwitchStages) (by rw [wire_split]; rfl) rfl (length_wireBody p) (noOpen_wireBody p)
    (phase_lt h (mem_wire p) (by omega)) (notOpen_in h (mem_wire p) (noOpen_wire p) (by omega))
  rw [wsum_wireBody, Nat.add_zero] at e
  exact e

/-- **The wire's row switch** (QH2's `rowG` at `ringLane p .wire`): its first answer lane (`8 · lane = P + 40`) and its
seven samples end where `KS` starts. -/
theorem wire_ring : 8 * ringLane p .wire = posOf p (phaseItem0 p .wire + (3 * p.logN + 8)) + 40 ∧
    posOf p (phaseItem0 p .ks) = posOf p (phaseItem0 p .wire + (3 * p.logN + 8)) + 72 * rowSwitchStages := by
  have hl := length_wire p
  have hk := phaseItem0_ks h
  have hkl := phase_lt h (mem_ks p) (j := 0) (ks_pos p)
  have hr : rowSwitchStages = 7 := rfl
  refine ⟨?_, ?_⟩
  · show 8 * laneOf p (phaseItem0 p .ks - 7) = _
    rw [show phaseItem0 p .ks - 7 = phaseItem0 p .wire + (3 * p.logN + 8) by omega]
    exact lane_pos hA (by omega) (notOpen_in h (mem_wire p) (noOpen_wire p) (by omega))
  · have e := posOf_run h hA (a := 3 * p.logN + 8) (b := rowSwitchStages) (mem_wire p) (pre := wireBody p)
      (xs := smp rowSwitchStages) (post := []) (by rw [wire_split, List.append_nil]) (length_wireBody p)
      (by simp [smp]) (noOpen_smp _) (by omega)
      (by rw [show phaseItem0 p .wire + (3 * p.logN + 8 + rowSwitchStages) = phaseItem0 p .ks + 0 by omega]
          exact notOpen_in h (mem_ks p) (noOpen_ks p) (ks_pos p))
    rw [show phaseItem0 p .ks = phaseItem0 p .wire + (3 * p.logN + 8) + rowSwitchStages by omega, e, wsum_smp]

/-! ## The `KS` phase -/

/-- **The `ksLog` instance challenges**: 80 bytes each. -/
theorem ks_rs : posOf p (phaseItem0 p .ks + 2 * p.ksLog) = posOf p (phaseItem0 p .ks) + 80 * p.ksLog := by
  have hl := length_ks p
  have h2 := keccakE2I_len p.ksLog
  have e := posOf_run h hA (a := 0) (b := 2 * p.ksLog) (mem_ks p) (pre := []) (xs := gsmpN p.ksLog)
    (post := rdE2 lanes ++ keccakE2I p.ksLog ++ smp rowSwitchStages) (by rw [ks_split]; simp [List.append_assoc])
    rfl (length_gsmpN _) (noOpen_gsmpN _) (phase_lt h (mem_ks p) (by omega))
    (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  rw [wsum_gsmpN, Nat.add_zero] at e
  exact e

/-- **`KS`'s 25 outputs**: their first lane (`8 · lane = P + 40`) and 400 bytes. -/
theorem ks_out : 8 * phaseLane p .ks (2 * p.ksLog) = posOf p (phaseItem0 p .ks + 2 * p.ksLog) + 40 ∧
    posOf p (phaseItem0 p .ks + 2 * p.ksLog + 1) = posOf p (phaseItem0 p .ks + 2 * p.ksLog) + 400 := by
  have hl := length_ks p
  have h2 := keccakE2I_len p.ksLog
  refine ⟨?_, ?_⟩
  · rw [phaseLane]
    exact lane_pos hA (phase_lt h (mem_ks p) (by omega)) (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  · have e := posOf_run h hA (a := 2 * p.ksLog) (b := 1) (mem_ks p) (pre := gsmpN p.ksLog) (xs := rdE2 lanes)
      (post := keccakE2I p.ksLog ++ smp rowSwitchStages) (by rw [ks_split]; simp [List.append_assoc])
      (length_gsmpN _) rfl (noOpen_rdE2 _) (phase_lt h (mem_ks p) (by omega))
      (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
    rw [wsum_rdE2] at e
    exact e

/-- **`KS`'s GKR start** (QH4's `gkr_phase2`: `8 qs − 48 = P`, `qs` the segment challenge's answer). -/
theorem ks_qsA : 8 * phaseLane p .ks (2 * p.ksLog + 2) = posOf p (phaseItem0 p .ks + (2 * p.ksLog + 1)) + 48 := by
  have hl := length_ks p
  have h2 := keccakE2I_len p.ksLog
  have h1 : (rdE2 lanes).length = 1 := rfl
  have hn : (schedule p).getD (phaseItem0 p .ks + (2 * p.ksLog + 1)) default = .readW 1 nonceBytes := by
    rw [sched_phase h (mem_ks p) (by omega), ks_split,
      List.getD_append _ _ _ _ (by simp only [List.length_append, length_gsmpN, h1]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_append, length_gsmpN, h1]; omega),
      show 2 * p.ksLog + 1 - (gsmpN p.ksLog ++ rdE2 lanes).length = 0 by
        simp only [List.length_append, length_gsmpN, h1]; omega, keccakE2I_head]
  have e := posOf_succ hA (k := phaseItem0 p .ks + (2 * p.ksLog + 1))
    (by have := phase_lt h (mem_ks p) (j := 2 * p.ksLog + 2) (by omega); omega)
    (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
    (by rw [Nat.add_assoc]; exact notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  rw [hn] at e
  have l3 := lane_pos hA (k := phaseItem0 p .ks + (2 * p.ksLog + 2)) (phase_lt h (mem_ks p) (by omega))
    (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  rw [phaseLane, l3, show phaseItem0 p .ks + (2 * p.ksLog + 2) = phaseItem0 p .ks + (2 * p.ksLog + 1) + 1 by omega, e]
  simp only [itemW, nonceBytes]

/-- **`KS`'s GKR end is its row switch's start** (QH4's `gkr_phase2` end `8 · gkrEnd2 P qs − 40`, `P = ksLog − 5`). -/
theorem ks_end (hk : 5 ≤ p.ksLog) :
    8 * Lvm.Q1.gkrEnd2 (p.ksLog - 5) (phaseLane p .ks (2 * p.ksLog + 2)) - 40 =
      posOf p (phaseItem0 p .ks + (2 * p.ksLog + 1) + (keccakE2I p.ksLog).length) := by
  have hl := length_ks p
  have hr : rowSwitchStages = 7 := rfl
  have h1 : (rdE2 lanes).length = 1 := rfl
  have e := posOf_run h hA (a := 2 * p.ksLog + 1) (b := (keccakE2I p.ksLog).length) (mem_ks p)
    (pre := gsmpN p.ksLog ++ rdE2 lanes) (xs := keccakE2I p.ksLog) (post := smp rowSwitchStages)
    (by rw [ks_split]) (by simp only [List.length_append, length_gsmpN, h1]) rfl (noOpen_keccakE2I _)
    (phase_lt h (mem_ks p) (by omega)) (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  have hq := ks_qsA h hA
  rw [e, wsum_keccakE2I]
  simp only [Lvm.Q1.gkrEnd2, Lvm.Q1.gkrQO2, Lvm.Q1.lay02, Lvm.Q1.LCfg.str2]
  omega

/-- **`KS`'s row switch** (QH2's `rowG` at `ringLane p .ks`): its first answer lane and its seven samples end where the
`KS` link starts. -/
theorem ks_ring : 8 * ringLane p .ks = posOf p (phaseItem0 p .ks + (2 * p.ksLog + 1) + (keccakE2I p.ksLog).length) + 40 ∧
    posOf p (phaseItem0 p .ksLink) =
      posOf p (phaseItem0 p .ks + (2 * p.ksLog + 1) + (keccakE2I p.ksLog).length) + 72 * rowSwitchStages := by
  have hl := length_ks p
  have hk := phaseItem0_link h
  have hll : 0 < (linkIts p).length := by rw [length_link]; omega
  have hkl := phase_lt h (mem_link p) (j := 0) hll
  have hr : rowSwitchStages = 7 := rfl
  have h1 : (rdE2 lanes).length = 1 := rfl
  refine ⟨?_, ?_⟩
  · show 8 * laneOf p (phaseItem0 p .ksLink - 7) = _
    rw [show phaseItem0 p .ksLink - 7 = phaseItem0 p .ks + (2 * p.ksLog + 1) + (keccakE2I p.ksLog).length by omega]
    exact lane_pos hA (by omega) (by rw [Nat.add_assoc]; exact notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  · have e := posOf_run h hA (a := 2 * p.ksLog + 1 + (keccakE2I p.ksLog).length) (b := rowSwitchStages) (mem_ks p)
      (pre := gsmpN p.ksLog ++ rdE2 lanes ++ keccakE2I p.ksLog) (xs := smp rowSwitchStages) (post := [])
      (by rw [ks_split, List.append_nil]) (by simp only [List.length_append, length_gsmpN, h1]) (by simp [smp])
      (noOpen_smp _) (by omega)
      (by rw [show phaseItem0 p .ks + (2 * p.ksLog + 1 + (keccakE2I p.ksLog).length + rowSwitchStages) =
            phaseItem0 p .ksLink + 0 by omega]
          exact notOpen_in h (mem_link p) (noOpen_link p) hll)
    rw [show phaseItem0 p .ksLink = phaseItem0 p .ks + (2 * p.ksLog + 1 + (keccakE2I p.ksLog).length) +
      rowSwitchStages by omega, e, wsum_smp, show phaseItem0 p .ks + (2 * p.ksLog + 1 + (keccakE2I p.ksLog).length) =
      phaseItem0 p .ks + (2 * p.ksLog + 1) + (keccakE2I p.ksLog).length by omega]

/-! ## The `KS` link phase -/

theorem link_item0 : (schedule p).getD (phaseItem0 p .ksLink) default = .readW 1 nonceBytes := by
  have e := sched_phase h (mem_link p) (j := 0) (by rw [length_link]; omega)
  rw [Nat.add_zero] at e
  rw [e, link_split]
  rfl

/-- **The link's first challenge's answer lane** (QH2's `ksLinkG2` `qa`: `8 · qa = P + 48`, `P` the link's start). -/
theorem link_qa : 8 * phaseLane p .ksLink 1 = posOf p (phaseItem0 p .ksLink) + 48 := by
  have hl := length_link p
  unfold laneBits at hl
  have hkl := phase_lt h (mem_link p) (j := 1) (by omega)
  have e := posOf_succ hA (k := phaseItem0 p .ksLink) hkl
    (by have := notOpen_in h (mem_link p) (noOpen_link p) (j := 0) (by omega); rwa [Nat.add_zero] at this)
    (notOpen_in h (mem_link p) (noOpen_link p) (by omega))
  rw [link_item0 h hA] at e
  have l1 := lane_pos hA hkl (notOpen_in h (mem_link p) (noOpen_link p) (by omega))
  rw [phaseLane, l1, e]
  simp only [itemW, nonceBytes]

/-- **The link's end is the opening's start**: `80 (ksLog + 5) + 112 ksLog + 64` bytes. -/
theorem link_end : posOf p (phaseItem0 p .openMain) =
    posOf p (phaseItem0 p .ksLink) + (80 * (p.ksLog + laneBits) + 112 * p.ksLog + 64) := by
  have ho := phaseItem0_open h
  have hoh := open_head p h
  have e := posOf_run h hA (a := 0) (b := (linkIts p).length) (mem_link p) (pre := []) (xs := linkIts p)
    (post := []) (by simp) rfl rfl (noOpen_link p) (by rw [Nat.zero_add, ← ho]; exact hoh.2)
    (by rw [Nat.zero_add, ← ho, hoh.1]; rfl)
  rw [Nat.add_zero, wsum_link] at e
  rw [ho]
  exact e

end Tape

/-- `V`'s cursor after the header (`RS.startH`) is at the schedule's first entry. -/
theorem pos_startH (p : Params) : Lvm.Har.pos (RS.startH (headerBytesP p)) = startByte p := by
  simp only [Lvm.Har.pos, RS.startH, startByte, seedLenP]
  omega

/-! ## At `P20F` -/

end Lvm.E2Q
