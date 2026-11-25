-- New for lvm6 (ST-4, STARTUP2 route (b)): `cancelChk`, a cancellation check of entry lists, and its soundness.
import Lvm6VPhiRows

/-!
# The cancellation check

`cancelChk ka ix pe` decides that the entries `pe` (coefficient, index) sum like the keyed array `ka`, at every weight:
* `D := ka`'s coefficients. Each entry `(c, k)` of `pe` is looked up through the **untrusted** slot index `ix`; a
  candidate position counts only if its key is `k` (`findK`). Found: `D[i] := D[i] - c`. Not found: the entry goes to a
  side list (the exporter's exception pairs, which cancel among themselves).
* `zpass`: each non-zero `D[i]` moves to a position of the same key (`findK`); then `D` must be all zero. The side
  list is made a keyed array and treated the same way.
* One invariant, `T ka D f = Σ_i D[i]·f(key i)`: a found entry lowers it by `c·f(k)`, a move keeps it.
  **`cancelChk_sound`**: on `true`, `Σ_{pe} c·f(k) = Σ_{ka} c·f(k)` for every `f`. A wrong index can only make the check false.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Specification -/

/-- The weighted sum of a list of (coefficient, index) entries. -/
def sumL (l : List (FE2 × ℕ)) (f : ℕ → FE2) : FE2 := (l.map fun p => p.1 * f p.2).sum

/-- An index's slot (`idxOf`'s slot bits). -/
@[inline] def slotOf (k : ℕ) : ℕ := k / 4 % 2 ^ 20

/-- **An untrusted slot index**: offsets by slot and positions grouped by slot. -/
structure SlotIx where
  off : Array ℕ
  pos : Array ℕ

/-- The candidate positions of index `k`. -/
def SlotIx.cands (ix : SlotIx) (k : ℕ) : List ℕ :=
  let s := slotOf k
  (List.range' (ix.off.getD s 0) (ix.off.getD (s + 1) 0 - ix.off.getD s 0)).map fun p => ix.pos.getD p 0

/-- A position of key `k` in `ka` among the candidates (checked). -/
def findK (ka : Array (FE2 × ℕ)) (ix : SlotIx) (k : ℕ) : Option ℕ :=
  (ix.cands k).find? fun i => decide (i < ka.size) && (ka.getD i (0, 0)).2 == k

/-- One entry of `pe`: cancelled at its position, or onto the side list. -/
def cancelStep (ka : Array (FE2 × ℕ)) (ix : SlotIx) (st : Array FE2 × List (FE2 × ℕ)) (p : FE2 × ℕ) :
    Array FE2 × List (FE2 × ℕ) :=
  match findK ka ix p.2 with
  | some i => (st.1.modify i (· - p.1), st.2)
  | none => (st.1, p :: st.2)

/-- Position `i`'s coefficient moved to a position of the same key. -/
def zstep (ka : Array (FE2 × ℕ)) (ix : SlotIx) (D : Array FE2) (i : ℕ) : Array FE2 :=
  let d := D.getD i 0
  if d == 0 then D else
    match findK ka ix (ka.getD i (0, 0)).2 with
    | some j => if j == i then D else (D.modify j (· + d)).modify i (fun _ => 0)
    | none => D

/-- Every non-zero coefficient moved to a position of the same key. -/
def zpass (ka : Array (FE2 × ℕ)) (ix : SlotIx) (D : Array FE2) : Array FE2 :=
  (List.range ka.size).foldl (zstep ka ix) D

/-- The slot index of a keyed array (counting pass; untrusted). -/
def mkIx (ka : Array (FE2 × ℕ)) : SlotIx := Id.run do
  let n := 2 ^ 20
  let mut cnt : Array ℕ := Array.replicate (n + 1) 0
  for p in ka do
    cnt := cnt.modify (slotOf p.2 + 1) (· + 1)
  for s in [0:n] do
    cnt := cnt.set! (s + 1) (cnt[s + 1]! + cnt[s]!)
  let mut fill := cnt
  let mut pos : Array ℕ := Array.replicate ka.size 0
  for i in [0:ka.size] do
    let s := slotOf (ka[i]!).2
    pos := pos.set! (fill[s]!) i
    fill := fill.modify s (· + 1)
  return ⟨cnt, pos⟩

/-- **The cancellation check** of `pe` against `ka` with the index `ix`. -/
def cancelChk (ka : Array (FE2 × ℕ)) (ix : SlotIx) (pe : List (FE2 × ℕ)) : Bool :=
  let st := pe.foldl (cancelStep ka ix) (ka.map (·.1), [])
  let sa := st.2.toArray
  (zpass ka ix st.1).all (· == 0) && (zpass sa (mkIx sa) (sa.map (·.1))).all (· == 0)

/-! ## The invariant -/

/-- `Σ_i D[i]·f(key i)`. -/
def tsum (ka : Array (FE2 × ℕ)) (D : Array FE2) (f : ℕ → FE2) : FE2 :=
  ((List.range ka.size).map fun i => D.getD i 0 * f (ka.getD i (0, 0)).2).sum

theorem findK_some {ka : Array (FE2 × ℕ)} {ix : SlotIx} {k i : ℕ} (h : findK ka ix k = some i) :
    i < ka.size ∧ (ka.getD i (0, 0)).2 = k := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this

theorem getD_modify' (D : Array FE2) (i j : ℕ) (g : FE2 → FE2) (hi : i < D.size) :
    (D.modify i g).getD j 0 = if j = i then g (D.getD i 0) else D.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [Ne.symm h, h]

theorem sum_range_update (a : ℕ → FE2) (b : FE2) (i : ℕ) : ∀ n, i < n →
    ((List.range n).map fun j => if j = i then b else a j).sum = ((List.range n).map a).sum + (b - a i)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    by_cases hi : i < n
    · rw [sum_range_update a b i n hi]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg (show n ≠ i by omega)]
      ring
    · have hin : i = n := by omega
      subst hin
      have e : ((List.range i).map fun j => if j = i then b else a j) = (List.range i).map a :=
        List.map_congr_left fun j hj => if_neg (by have := List.mem_range.1 hj; omega)
      rw [e]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ↓reduceIte]
      ring

theorem tsum_modify (ka : Array (FE2 × ℕ)) (D : Array FE2) (f : ℕ → FE2) (i : ℕ) (g : FE2 → FE2)
    (hD : D.size = ka.size) (hi : i < ka.size) :
    tsum ka (D.modify i g) f = tsum ka D f + (g (D.getD i 0) - D.getD i 0) * f (ka.getD i (0, 0)).2 := by
  unfold tsum
  have e : ((List.range ka.size).map fun j => (D.modify i g).getD j 0 * f (ka.getD j (0, 0)).2) =
      (List.range ka.size).map fun j => if j = i then g (D.getD i 0) * f (ka.getD i (0, 0)).2
        else D.getD j 0 * f (ka.getD j (0, 0)).2 := by
    refine List.map_congr_left fun j _ => ?_
    rw [getD_modify' D i j g (by omega)]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e, sum_range_update _ _ i _ hi]
  ring

theorem tsum_init (ka : Array (FE2 × ℕ)) (f : ℕ → FE2) : tsum ka (ka.map (·.1)) f = sumL ka.toList f := by
  unfold tsum sumL
  have h := sum_getD ka.toList fun p => p.1 * f p.2
  simp only [Array.length_toList] at h
  rw [← h]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : j < ka.size := List.mem_range.1 hj
  have e1 : (ka.map (·.1)).getD j 0 = ka[j].1 := by simp [Array.getD, hj']
  have e2 : ka.getD j (0, 0) = ka[j] := by simp [Array.getD, hj']
  have e3 : ka.toList.getD j default = ka[j] := by simp [List.getD_eq_getElem?_getD, hj']
  rw [e1, e2, e3]

theorem tsum_zero (ka : Array (FE2 × ℕ)) (D : Array FE2) (f : ℕ → FE2) (hD : D.size = ka.size)
    (h : D.all (· == 0) = true) : tsum ka D f = 0 := by
  unfold tsum
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj' : j < D.size := by rw [hD]; exact List.mem_range.1 hj
  have hz := (Array.all_eq_true.1 h) j hj'
  simp only [beq_iff_eq] at hz
  simp [Array.getD, hj', hz]

/-! ## The passes -/

theorem cancel_inv (ka : Array (FE2 × ℕ)) (ix : SlotIx) (f : ℕ → FE2) : ∀ (ps : List (FE2 × ℕ))
    (st : Array FE2 × List (FE2 × ℕ)), st.1.size = ka.size →
    (ps.foldl (cancelStep ka ix) st).1.size = ka.size ∧
      tsum ka (ps.foldl (cancelStep ka ix) st).1 f - sumL (ps.foldl (cancelStep ka ix) st).2 f + sumL ps f =
        tsum ka st.1 f - sumL st.2 f
  | [], st, h => by simp [sumL, h]
  | p :: ps, st, h => by
    rw [List.foldl_cons]
    have hs : (cancelStep ka ix st p).1.size = ka.size := by
      unfold cancelStep; split <;> simp [h]
    obtain ⟨h1, h2⟩ := cancel_inv ka ix f ps _ hs
    refine ⟨h1, ?_⟩
    have hp : sumL (p :: ps) f = p.1 * f p.2 + sumL ps f := by simp [sumL]
    rw [hp]
    have e : tsum ka (cancelStep ka ix st p).1 f - sumL (cancelStep ka ix st p).2 f =
        tsum ka st.1 f - sumL st.2 f - p.1 * f p.2 := by
      unfold cancelStep
      split
      · rename_i i hk
        obtain ⟨hi, hkey⟩ := findK_some hk
        simp only
        rw [tsum_modify ka st.1 f i _ h hi, hkey]
        ring
      · simp only [sumL, List.map_cons, List.sum_cons]
        ring
    calc _ = (tsum ka (List.foldl (cancelStep ka ix) (cancelStep ka ix st p) ps).1 f -
          sumL (List.foldl (cancelStep ka ix) (cancelStep ka ix st p) ps).2 f + sumL ps f) + p.1 * f p.2 := by ring
      _ = _ := by rw [h2, e]; ring

theorem zstep_inv (ka : Array (FE2 × ℕ)) (ix : SlotIx) (f : ℕ → FE2) (D : Array FE2) (i : ℕ)
    (h : D.size = ka.size) : (zstep ka ix D i).size = ka.size ∧ tsum ka (zstep ka ix D i) f = tsum ka D f := by
  unfold zstep
  simp only
  split
  · exact ⟨h, rfl⟩
  · rename_i hd
    split
    · rename_i j hk
      split
      · exact ⟨h, rfl⟩
      · rename_i hji
        have hne : j ≠ i := by simpa using hji
        obtain ⟨hj, hkey⟩ := findK_some hk
        have hi : i < ka.size := by
          by_contra hi
          apply hd
          simp [Array.getD, show ¬ i < D.size by omega]
        have hs1 : (D.modify j (· + D.getD i 0)).size = ka.size := by simp [h]
        refine ⟨by simp [h], ?_⟩
        rw [tsum_modify ka _ f i _ hs1 hi, tsum_modify ka D f j _ h hj, getD_modify' D j i _ (by omega),
          if_neg (Ne.symm hne), hkey]
        ring
    · exact ⟨h, rfl⟩

theorem zpass_inv (ka : Array (FE2 × ℕ)) (ix : SlotIx) (f : ℕ → FE2) : ∀ (l : List ℕ) (D : Array FE2),
    D.size = ka.size → (l.foldl (zstep ka ix) D).size = ka.size ∧ tsum ka (l.foldl (zstep ka ix) D) f = tsum ka D f
  | [], D, h => ⟨h, rfl⟩
  | i :: l, D, h => by
    rw [List.foldl_cons]
    obtain ⟨hs, ht⟩ := zstep_inv ka ix f D i h
    obtain ⟨h1, h2⟩ := zpass_inv ka ix f l _ hs
    exact ⟨h1, h2.trans ht⟩

theorem zpass_tsum (ka : Array (FE2 × ℕ)) (ix : SlotIx) (f : ℕ → FE2) (D : Array FE2) (h : D.size = ka.size) :
    (zpass ka ix D).size = ka.size ∧ tsum ka (zpass ka ix D) f = tsum ka D f :=
  zpass_inv ka ix f (List.range ka.size) D h

/-! ## Soundness -/

/-- **The cancellation check is sound**: on `true`, `pe` and `ka` have equal sums at every weight (any index `ix`). -/
theorem cancelChk_sound {ka : Array (FE2 × ℕ)} {ix : SlotIx} {pe : List (FE2 × ℕ)} (h : cancelChk ka ix pe = true)
    (f : ℕ → FE2) : sumL pe f = sumL ka.toList f := by
  simp only [cancelChk, Bool.and_eq_true] at h
  obtain ⟨hq, hs⟩ := h
  set st := pe.foldl (cancelStep ka ix) (ka.map (·.1), []) with hst
  obtain ⟨h1, h2⟩ := cancel_inv ka ix f pe (ka.map (·.1), []) (by simp)
  rw [← hst] at h1 h2
  obtain ⟨hz1, hz2⟩ := zpass_tsum ka ix f st.1 h1
  have hT : tsum ka st.1 f = 0 := hz2.symm.trans (tsum_zero ka _ f hz1 hq)
  set sa := st.2.toArray with hsa
  obtain ⟨hs1, hs2⟩ := zpass_tsum sa (mkIx sa) f (sa.map (·.1)) (by simp)
  have hS : sumL st.2 f = 0 := by
    have e := tsum_init sa f
    rw [hsa, List.toList_toArray] at e
    rw [← e, ← hs2]
    exact tsum_zero _ _ f hs1 hs
  rw [hT, hS, tsum_init] at h2
  simp only [sumL, List.map_nil, List.sum_nil, sub_zero, zero_sub] at h2
  have : sumL pe f = sumL ka.toList f := by
    unfold sumL; linear_combination h2
  exact this

end Lvm6.V
