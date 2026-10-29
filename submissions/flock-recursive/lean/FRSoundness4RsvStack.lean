-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form; track RSV-S2a): the
-- algebra of `finE` (iv″)'s one stacked `evalM`: the coefficients `s^P` split into the own kind's
-- `f̂·κ_E^m` and the child's `w·s`, the mixed point is `x̂ = r_E2 ‖ p_x[e2R, 23)`.
import FRSoundness4P4bE
import FRSoundness4RsvRun

/-!
# The stacked call of `finE` (iv″) in the log's terms

`V(P)`'s row point is `r_E2[<22] ‖ x̂₂₂ ‖ s^P` (32 entries) and its column point `r′[<24] ‖ ŷ₂₄`;
`s^P_i = [i/3 = κ_P.ix]·f̂·κ_E^{i%3} + w·s_i`. **`mStack_sP`**: the stacked extension at those
entries is `f̂·(M̃_A + κ_E M̃_B + κ_E² M̃_C)_{κ_P}(r_E2, r′) + w·Σ_i s_i M̃_i(x̂, ŷ)`, the form of
`P4b.RejFinE4`.
-/

namespace FR.Snd.P4b
open RecursionFast Rev4

theorem arr_getD {α : Type} (l : List α) (j : ℕ) (d : α) : l.toArray.getD j d = l.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem e2R_ge (ν : NodeKind) : 22 ≤ e2R ν ∧ e2R ν ≤ 23 ∧ 24 ≤ ncR ν ∧ ncR ν ≤ 25 := by
  cases ν <;> decide

/-- `mStack` reads `s` below 9, `p` below 23 and `q` below 25. -/
theorem mStack_congr' (srcE : NodeKind → ESrc) {s s' p p' q q' : ℕ → F}
    (hs : ∀ i < 9, s i = s' i) (hp : ∀ j < 23, p j = p' j) (hq : ∀ j < 25, q j = q' j) :
    mStack srcE s p q = mStack srcE s' p' q' := by
  have hlp : ∀ κ : NodeKind, Rsv.lowA (e2R κ) p = Rsv.lowA (e2R κ) p' :=
    fun κ => funext fun j => hp j (lt_of_lt_of_le j.isLt (dims_le' κ).2.1)
  have hlq : ∀ κ : NodeKind, Rsv.lowA (ncR κ) q = Rsv.lowA (ncR κ) q' :=
    fun κ => funext fun j => hq j (lt_of_lt_of_le j.isLt (dims_le' κ).2.2.1)
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hlp, hlq, NodeKind.ix]
  rw [hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), hs 3 (by norm_num), hs 4 (by norm_num),
    hs 5 (by norm_num), hs 6 (by norm_num), hs 7 (by norm_num), hs 8 (by norm_num)]

/-- `mStack` is linear in its coefficients. -/
theorem mStack_lin (srcE : NodeKind → ESrc) (a b : ℕ → F) (w : F) (p q : ℕ → F) :
    mStack srcE (fun i => a i + w * b i) p q = mStack srcE a p q + w * mStack srcE b p q := by
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- The own kind's coefficients `[i/3 = ν.ix]·f̂·κ_E^{i%3}` select `ν`'s three matrices. -/
theorem mStack_own (srcE : NodeKind → ESrc) (ν : NodeKind) (fz kE : F) (p q : ℕ → F) :
    mStack srcE (fun i => (if ν.ix = i / 3 then 1 else 0) * [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0) p q =
      fz * (Eval.matMLE (srcE ν).ea (Rsv.lowA (e2R ν) p) (Rsv.lowA (ncR ν) q) +
        kE * Eval.matMLE (srcE ν).eb (Rsv.lowA (e2R ν) p) (Rsv.lowA (ncR ν) q) +
        kE ^ 2 * Eval.matMLE (srcE ν).ec (Rsv.lowA (e2R ν) p) (Rsv.lowA (ncR ν) q)) := by
  cases ν <;>
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, NodeKind.ix,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, List.getD_cons_zero, List.getD_cons_succ,
    ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, zero_mul, one_mul, add_zero, zero_add] <;> ring

/-- A mixed entry: below `e` the list `r` (of length `e`), at and above it `hi`. -/
theorem mixed_entry {r : List F} {e : ℕ} (hr : r.length = e) (hi : ℕ → F) {n j : ℕ} (hj : j < n)
    (hen : e ≤ n) (d : F) :
    (r ++ ((List.range n).map hi).drop e).getD j d = Rsv.hiPt (ptOf e r) hi j := by
  by_cases h : j < e
  · rw [Rsv.hiPt_lt _ _ h, List.getD_append _ _ _ _ (by omega)]
    simp only [ptOf]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [Rsv.hiPt_ge _ _ h, List.getD_append_right _ _ _ _ (by omega), hr, List.getD_eq_getElem?_getD,
      List.getElem?_drop, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]; congr 1; omega

/-- **The stacked call of `finE` (iv″)** at `V`'s entries (RSV2 §2.2). -/
theorem mStack_sP (srcE : NodeKind → ESrc) (ν : NodeKind) (r2 r4 : List F) (h2 : r2.length = e2R ν)
    (h4 : r4.length = ncR ν) (px py s : ℕ → F) (fz kE w d1 d2 : F) :
    mStack srcE
      (fun i => ((r2.take 22 ++ [(r2 ++ ((List.range 23).map px).drop (e2R ν)).getD 22 d1] ++
        (List.range 9).map fun i => (if ν.ix = i / 3 then 1 else 0) *
          [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 + w * s i).toArray).getD (23 + i) 0)
      (fun j => ((r2.take 22 ++ [(r2 ++ ((List.range 23).map px).drop (e2R ν)).getD 22 d1] ++
        (List.range 9).map fun i => (if ν.ix = i / 3 then 1 else 0) *
          [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 + w * s i).toArray).getD j 0)
      (fun j => ((r4.take 24 ++ [(r4 ++ ((List.range 25).map py).drop (ncR ν)).getD 24 d2]).toArray).getD j 0) =
    fz * (Eval.matMLE (srcE ν).ea (ptOf (e2R ν) r2) (ptOf (ncR ν) r4) +
        kE * Eval.matMLE (srcE ν).eb (ptOf (e2R ν) r2) (ptOf (ncR ν) r4) +
        kE ^ 2 * Eval.matMLE (srcE ν).ec (ptOf (e2R ν) r2) (ptOf (ncR ν) r4)) +
      w * mStack srcE s (Rsv.hiPt (ptOf (e2R ν) r2) px) (Rsv.hiPt (ptOf (ncR ν) r4) py) := by
  obtain ⟨g2, l2, g4, l4⟩ := e2R_ge ν
  have hl22 : (r2.take 22 ++ [(r2 ++ ((List.range 23).map px).drop (e2R ν)).getD 22 d1]).length = 23 := by
    simp [h2]; omega
  rw [mStack_congr' srcE (s' := fun i => (if ν.ix = i / 3 then 1 else 0) *
      [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 + w * s i)
    (p' := Rsv.hiPt (ptOf (e2R ν) r2) px) (q' := Rsv.hiPt (ptOf (ncR ν) r4) py)]
  · rw [mStack_lin, mStack_own]
    have e1 : Rsv.lowA (e2R ν) (Rsv.hiPt (ptOf (e2R ν) r2) px) = ptOf (e2R ν) r2 :=
      funext fun j => Rsv.hiPt_lt _ _ j.isLt
    have e2 : Rsv.lowA (ncR ν) (Rsv.hiPt (ptOf (ncR ν) r4) py) = ptOf (ncR ν) r4 :=
      funext fun j => Rsv.hiPt_lt _ _ j.isLt
    rw [e1, e2]
  · intro i hi
    rw [arr_getD, List.getD_append_right _ _ _ _ (by omega), hl22, Nat.add_sub_cancel_left,
      R4.getD_mapRange _ _ hi]
  · intro j hj
    rw [arr_getD, List.getD_append _ _ _ _ (by omega)]
    by_cases hj22 : j < 22
    · rw [List.getD_append _ _ _ _ (by simp; omega), R4.getD_take' _ _ hj22]
      rw [← mixed_entry h2 px hj l2 0, List.getD_append _ _ _ _ (by omega)]
    · obtain rfl : j = 22 := by omega
      rw [List.getD_append_right _ _ _ _ (by simp <;> omega)]
      simp only [List.length_take, h2, Nat.min_eq_left g2, Nat.sub_self, List.getD_cons_zero]
      exact mixed_entry h2 px (by norm_num) l2 d1
  · intro j hj
    rw [arr_getD]
    by_cases hj24 : j < 24
    · rw [List.getD_append _ _ _ _ (by simp; omega), R4.getD_take' _ _ hj24]
      rw [← mixed_entry h4 py hj l4 0, List.getD_append _ _ _ _ (by omega)]
    · obtain rfl : j = 24 := by omega
      rw [List.getD_append_right _ _ _ _ (by simp <;> omega)]
      simp only [List.length_take, h4, Nat.min_eq_left g4, Nat.sub_self, List.getD_cons_zero]
      exact mixed_entry h4 py (by norm_num) l4 d2

end FR.Snd.P4b
