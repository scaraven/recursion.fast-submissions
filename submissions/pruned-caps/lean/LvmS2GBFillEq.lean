-- New for lvm2 MP-B cap pruning (CAP-X2, 2026-11-17): the expanded proof `fillB` keeps π's static bytes in place
-- between the openings (proof-help of `ext_eqB_gen`: E reads π, the scheme reads `fillB P20B π w`).
import LvmS2GBFill

/-!
# `fillB` copies π's static bytes

* `fillStat p it`, `fillExp p it`: an item's static bytes in π and the upper-sibling bytes the expansion adds;
* **`fillItems_append`**: the expansion of `xs ++ ys` is `xs`'s, then `ys`'s from the advanced cursors;
* **`fillItems_noOpen`**: without openings the expansion is π's bytes verbatim;
* **`length_fillItems_le`**, **`length_fillItems`**: the expansion's length (at most the static bytes and `w`'s;
  exactly static plus expansion when π and `w` are long enough).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- An item's static bytes in π (`fillItems`' cursor advance). -/
def fillStat (p : Params) : Item → Nat
  | .read m => eBytes * m
  | .readW m wd => wd * m
  | .cap c r => nodeBytes * 2 ^ p.capSendBits r.lv c
  | .sample => 0
  | .positions _ => 0
  | .opening r => (p.level r).t * ((p.level r).row + nodeBytes * (p.level r).path)

/-- The upper-sibling bytes an item's expansion takes from `w`. -/
def fillExp (p : Params) : Item → Nat
  | .opening r => (p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap))
  | _ => 0

/-- An opening item. -/
def isOpenI : Item → Bool
  | .opening _ => true
  | _ => false

theorem fillItems_append (p : Params) (b : List UInt8) : ∀ (xs ys : List Item) (o : Nat) (w : List UInt8),
    fillItems p b (xs ++ ys) o w = fillItems p b xs o w ++
      fillItems p b ys (o + (xs.map (fillStat p)).sum) (w.drop (xs.map (fillExp p)).sum)
  | [], ys, o, w => by simp [fillItems]
  | it :: xs, ys, o, w => by
    cases it with
    | read m =>
      simp only [List.cons_append, fillItems, fillItems_append p b xs ys, List.append_assoc, List.map_cons,
        List.sum_cons, fillStat, fillExp, Nat.zero_add, Nat.add_assoc]
    | readW m wd =>
      simp only [List.cons_append, fillItems, fillItems_append p b xs ys, List.append_assoc, List.map_cons,
        List.sum_cons, fillStat, fillExp, Nat.zero_add, Nat.add_assoc]
    | cap c r =>
      simp only [List.cons_append, fillItems, fillItems_append p b xs ys, List.append_assoc, List.map_cons,
        List.sum_cons, fillStat, fillExp, Nat.zero_add, Nat.add_assoc]
    | sample =>
      simp only [List.cons_append, fillItems, fillItems_append p b xs ys, List.map_cons,
        List.sum_cons, fillStat, fillExp, Nat.zero_add]
    | positions r =>
      simp only [List.cons_append, fillItems, fillItems_append p b xs ys, List.map_cons,
        List.sum_cons, fillStat, fillExp, Nat.zero_add]
    | opening r =>
      simp only [List.cons_append, fillItems, fillItems_append p b xs ys, List.append_assoc, List.map_cons,
        List.sum_cons, fillStat, fillExp, Nat.add_assoc, List.drop_drop]

theorem take_take_add (l : List UInt8) (o a c : Nat) :
    (l.drop o).take a ++ (l.drop (o + a)).take c = (l.drop o).take (a + c) := by
  rw [List.take_add, List.drop_drop]

theorem fillItems_noOpen (p : Params) (b : List UInt8) : ∀ (xs : List Item) (o : Nat) (w : List UInt8),
    (xs.all fun it => !isOpenI it) = true → fillItems p b xs o w = (b.drop o).take (xs.map (fillStat p)).sum
  | [], o, w, _ => by simp [fillItems]
  | it :: xs, o, w, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases it with
    | read m =>
      simp only [fillItems, fillItems_noOpen p b xs _ w h.2, List.map_cons, List.sum_cons, fillStat, take_take_add]
    | readW m wd =>
      simp only [fillItems, fillItems_noOpen p b xs _ w h.2, List.map_cons, List.sum_cons, fillStat, take_take_add]
    | cap c r =>
      simp only [fillItems, fillItems_noOpen p b xs _ w h.2, List.map_cons, List.sum_cons, fillStat, take_take_add]
    | sample =>
      simp only [fillItems, fillItems_noOpen p b xs _ w h.2, List.map_cons, List.sum_cons, fillStat, Nat.zero_add]
    | positions r =>
      simp only [fillItems, fillItems_noOpen p b xs _ w h.2, List.map_cons, List.sum_cons, fillStat, Nat.zero_add]
    | opening r => simp [isOpenI] at h

theorem length_fillPaths_le (b : List UInt8) (n u : Nat) : ∀ (k o : Nat) (w : List UInt8),
    (fillPaths b n u k o w).length ≤ k * n + min (k * u) w.length
  | 0, _, _ => by simp [fillPaths]
  | k + 1, o, w => by
    have ih := length_fillPaths_le b n u k (o + n) (w.drop u)
    simp only [fillPaths, List.length_append, List.length_take, List.length_drop] at ih ⊢
    have h1 : min n (b.length - o) ≤ n := Nat.min_le_left _ _
    rw [Nat.succ_mul, Nat.succ_mul]
    omega

theorem length_fillPaths (b : List UInt8) (n u : Nat) : ∀ (k o : Nat) (w : List UInt8),
    o + k * n ≤ b.length → k * u ≤ w.length → (fillPaths b n u k o w).length = k * n + k * u
  | 0, _, _, _, _ => by simp [fillPaths]
  | k + 1, o, w, hb, hw => by
    rw [Nat.succ_mul] at hb hw
    have ih := length_fillPaths b n u k (o + n) (w.drop u) (by omega) (by rw [List.length_drop]; omega)
    simp only [fillPaths, List.length_append, List.length_take, List.length_drop, ih]
    rw [Nat.succ_mul, Nat.succ_mul]
    omega

theorem length_fillItems_le (p : Params) (b : List UInt8) : ∀ (xs : List Item) (o : Nat) (w : List UInt8),
    (fillItems p b xs o w).length ≤ (xs.map (fillStat p)).sum + min (xs.map (fillExp p)).sum w.length
  | [], _, _ => by simp [fillItems]
  | it :: xs, o, w => by
    cases it with
    | read m =>
      have ih := length_fillItems_le p b xs (o + eBytes * m) w
      simp only [fillItems, List.length_append, List.length_take, List.map_cons, List.sum_cons, fillStat,
        fillExp, Nat.zero_add] at ih ⊢
      omega
    | readW m wd =>
      have ih := length_fillItems_le p b xs (o + wd * m) w
      simp only [fillItems, List.length_append, List.length_take, List.map_cons, List.sum_cons, fillStat,
        fillExp, Nat.zero_add] at ih ⊢
      omega
    | cap c r =>
      have ih := length_fillItems_le p b xs (o + nodeBytes * 2 ^ p.capSendBits r.lv c) w
      simp only [fillItems, List.length_append, List.length_take, List.map_cons, List.sum_cons, fillStat,
        fillExp, Nat.zero_add] at ih ⊢
      omega
    | sample =>
      have ih := length_fillItems_le p b xs o w
      simp only [fillItems, List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at ih ⊢
      exact ih
    | positions r =>
      have ih := length_fillItems_le p b xs o w
      simp only [fillItems, List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at ih ⊢
      exact ih
    | opening r =>
      have ih := length_fillItems_le p b xs (o + (p.level r).t * ((p.level r).row + nodeBytes * (p.level r).path))
        (w.drop ((p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap))))
      have hp := length_fillPaths_le b ((p.level r).row + nodeBytes * (p.level r).path)
        (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap)) (p.level r).t o w
      simp only [fillItems, List.length_append, List.length_drop, List.map_cons, List.sum_cons, fillStat,
        fillExp] at ih hp ⊢
      omega

theorem length_fillItems (p : Params) (b : List UInt8) : ∀ (xs : List Item) (o : Nat) (w : List UInt8),
    o + (xs.map (fillStat p)).sum ≤ b.length → (xs.map (fillExp p)).sum ≤ w.length →
    (fillItems p b xs o w).length = (xs.map (fillStat p)).sum + (xs.map (fillExp p)).sum
  | [], _, _, _, _ => by simp [fillItems]
  | it :: xs, o, w, hb, hw => by
    cases it with
    | read m =>
      simp only [List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at hb hw
      have ih := length_fillItems p b xs (o + eBytes * m) w (by omega) hw
      simp only [fillItems, List.length_append, List.length_take, List.length_drop, List.map_cons, List.sum_cons,
        fillStat, fillExp, Nat.zero_add, ih]
      omega
    | readW m wd =>
      simp only [List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at hb hw
      have ih := length_fillItems p b xs (o + wd * m) w (by omega) hw
      simp only [fillItems, List.length_append, List.length_take, List.length_drop, List.map_cons, List.sum_cons,
        fillStat, fillExp, Nat.zero_add, ih]
      omega
    | cap c r =>
      simp only [List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at hb hw
      have ih := length_fillItems p b xs (o + nodeBytes * 2 ^ p.capSendBits r.lv c) w (by omega) hw
      simp only [fillItems, List.length_append, List.length_take, List.length_drop, List.map_cons, List.sum_cons,
        fillStat, fillExp, Nat.zero_add, ih]
      omega
    | sample =>
      simp only [List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at hb hw
      simp only [fillItems, List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add]
      exact length_fillItems p b xs o w hb hw
    | positions r =>
      simp only [List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add] at hb hw
      simp only [fillItems, List.map_cons, List.sum_cons, fillStat, fillExp, Nat.zero_add]
      exact length_fillItems p b xs o w hb hw
    | opening r =>
      simp only [List.map_cons, List.sum_cons, fillStat, fillExp] at hb hw
      have ih := length_fillItems p b xs (o + (p.level r).t * ((p.level r).row + nodeBytes * (p.level r).path))
        (w.drop ((p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap))))
        (by omega) (by rw [List.length_drop]; omega)
      have hp := length_fillPaths b ((p.level r).row + nodeBytes * (p.level r).path)
        (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap)) (p.level r).t o w (by omega)
        (by omega)
      simp only [fillItems, List.length_append, List.map_cons, List.sum_cons, fillStat, fillExp, ih, hp]
      omega

/-- Dropping past a prefix. -/
theorem drop_len_add : ∀ (l₁ l₂ : List UInt8) (i : Nat), (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i
  | [], _, i => by simp
  | a :: l, l₂, i => by
    rw [show (a :: l).length + i = (l.length + i) + 1 by simp only [List.length_cons]; omega]
    exact drop_len_add l l₂ i

/-- **The expansion's bytes of a whole proof** (`fillB` unfolded on lists). -/
theorem fillB_toList (p : Params) (π : ByteArray) (w : List UInt8) :
    (fillB p π w).data.toList = π.data.toList.take (headerBytesP p) ++
      fillItems p π.data.toList (schedule p) (headerBytesP p) w := by
  simp [fillB]

/-- **A static stretch is copied with its shift**: in the schedule `xs ++ ys ++ zs` with `ys` free of openings, π's
bytes `[hb + stat xs + j, … + n)` (`j + n ≤ stat ys`) sit in the expansion `exp xs` bytes later. -/
theorem fillB_sl (p : Params) (π : ByteArray) (w : List UInt8) (xs ys zs : List Item)
    (hs : schedule p = xs ++ ys ++ zs) (hy : (ys.all fun it => !isOpenI it) = true)
    (hπ : headerBytesP p + (xs.map (fillStat p)).sum + (ys.map (fillStat p)).sum ≤ π.size)
    (hw : (xs.map (fillExp p)).sum ≤ w.length) {j n : Nat} (hj : j + n ≤ (ys.map (fillStat p)).sum) :
    ((fillB p π w).data.toList.drop
        (headerBytesP p + (xs.map (fillStat p)).sum + (xs.map (fillExp p)).sum + j)).take n =
      (π.data.toList.drop (headerBytesP p + (xs.map (fillStat p)).sum + j)).take n := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  rw [fillB_toList, hs, fillItems_append, fillItems_append, fillItems_noOpen p _ ys _ _ hy]
  have hh : (π.data.toList.take (headerBytesP p)).length = headerBytesP p := by
    rw [List.length_take]; omega
  have hx := length_fillItems p π.data.toList xs (headerBytesP p) w (by omega) hw
  rw [show headerBytesP p + (xs.map (fillStat p)).sum + (xs.map (fillExp p)).sum + j =
      ((π.data.toList.take (headerBytesP p)).length + (fillItems p π.data.toList xs (headerBytesP p) w).length) + j by
    rw [hh, hx]; omega, ← List.length_append,
    List.append_assoc (fillItems p π.data.toList xs (headerBytesP p) w),
    ← List.append_assoc (π.data.toList.take (headerBytesP p)) (fillItems p π.data.toList xs (headerBytesP p) w),
    drop_len_add]
  have hS : ((π.data.toList.drop (headerBytesP p + (xs.map (fillStat p)).sum)).take
      (ys.map (fillStat p)).sum).length = (ys.map (fillStat p)).sum := by
    rw [List.length_take, List.length_drop]; omega
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by rw [List.length_drop]; omega),
    List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

/-- **An expansion of full size took all its upper siblings**: if `fillB p π w` has the header, the static bytes and
the expansion bytes of the whole schedule, then `w` had them. -/
theorem fillB_w_long (p : Params) (π : ByteArray) (w : List UInt8)
    (hz : (fillB p π w).size = headerBytesP p + ((schedule p).map (fillStat p)).sum +
      ((schedule p).map (fillExp p)).sum) : ((schedule p).map (fillExp p)).sum ≤ w.length := by
  have h1 := length_fillItems_le p π.data.toList (schedule p) (headerBytesP p) w
  have h2 : (fillB p π w).size = (fillB p π w).data.toList.length := (Array.length_toList).symm
  rw [h2, fillB_toList, List.length_append, List.length_take] at hz
  have h3 : min (headerBytesP p) π.data.toList.length ≤ headerBytesP p := Nat.min_le_left _ _
  have h4 : min ((schedule p).map (fillExp p)).sum w.length ≤ w.length := Nat.min_le_right _ _
  omega

/-- **`fillB` keeps the header**: π's first `headerBytesP p` bytes. -/
theorem fillB_take_hdr (p : Params) (π : ByteArray) (w : List UInt8) (hπ : headerBytesP p ≤ π.size) :
    (fillB p π w).data.toList.take (headerBytesP p) = π.data.toList.take (headerBytesP p) := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  rw [fillB_toList, List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take,
    Nat.min_self]

end Lvm
