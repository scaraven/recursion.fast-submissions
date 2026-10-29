-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessFrWalk` (20). Content: the front walk's bridge
-- lemmas (`walk_bridge`, `lc_bridge`, `free_term`, …). The 3.x modules import this one.
import FRSoundnessCoreAcc
import FRSoundnessCoreFront

/-! ## From `FRSoundnessFrWalk` (20 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl

theorem sum_map_filter_ite {α : Type*} (l : List α) (p : α → Bool) (f : α → F) :
    ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [h, ih]

/-- **`maskOf` as a sum over the nine kinds**: kind `j`'s weight counts at row `k` unless kind
`j` pins `k`. -/
theorem maskOf_eq (w : Array F) (k : ℕ) :
    maskOf w k = ∑ j : Fin 9, if isZeroRow (bkOf j) k then 0 else w.getD j 0 := by
  have hb : ∀ (b : Bool) (x : F), (if b = false then x else 0) = if b = true then 0 else x := by
    intro b x; cases b <;> rfl
  rw [maskOf, sum_map_filter_ite]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, blockKinds, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Bool.not_eq_true', hb]
  rfl

/-- `bkOf j` is `free` only at `j = 8`. -/
theorem bkOf_free_iff (j : Fin 9) : bkOf j = .free ↔ j = 8 := bkOf_eq_iff j .free

/-- `kMat` off `free`: the circuit's row where the kind pins nothing, `0` on a pinned row. -/
theorem kMat_of_ne (C : Block.Pos → Block.Pos → Bool) {j : Fin 9} (hf : bkOf j ≠ .free) (p k : Fin (2 ^ 14)) :
    kMat C j p k = if isZeroRow (bkOf j) p.val then 0 else ProductCircuit.ofBool F (C p k) := by
  unfold kMat; rw [if_neg hf]

/-- `mulVec` at a Boolean matrix as a sum of `ofBool` weights. -/
theorem mulVec_ofBool (M : Fin (2 ^ 14) → Fin (2 ^ 14) → Bool) (z : Fin (2 ^ 14) → F) (k : Fin (2 ^ 14)) :
    BlockR1CS.mulVec M z k = ∑ q, ProductCircuit.ofBool F (M k q) * z q := by
  unfold BlockR1CS.mulVec ProductCircuit.ofBool
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

theorem maskRows_getD (w r : Array F) {k : ℕ} (hk : k < r.size) :
    (maskRows w r).getD k 0 = r.getD k 0 * maskOf w k := by
  rw [maskRows_eq, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
    Option.getD_some]

theorem rowWS_getD (l : F) (rhi : Array F) (k : Fin (2 ^ 14)) :
    (rowWS l rhi).getD k.val 0 = rowW (p := 8) l (ptA 8 rhi) k := by
  unfold rowWS
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [k.isLt, dif_pos, Option.getD_some]

section Alg

variable {N : ℕ} {ι : Type*} [Fintype ι] (A B : Fin N → Fin N → Bool) (rw e : Fin N → F) (α : F)
  (zr : ι → Fin N → Bool) (w : ι → F)

/-- The A and B rows of `k` against the column weights: `Σ_q (A_{kq} + α B_{kq}) e_q`. -/
noncomputable def rowAB (k : Fin N) : F :=
  ∑ q, ProductCircuit.ofBool F (A k q) * e q + α * ∑ q, ProductCircuit.ofBool F (B k q) * e q

/-- One kind's column form, summed over the rows first. -/
theorem colK_eq (zj : Fin N → Bool) :
    ∑ q, e q * ∑ k, rw k * (if zj k then 0 else
        ProductCircuit.ofBool F (A k q) + α * ProductCircuit.ofBool F (B k q)) =
      ∑ k, rw k * (if zj k then 0 else rowAB A B e α k) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · simp
  · simp only [rowAB, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring

/-- **The walk's algebra**: the masked walk is the kinds' weighted column forms. -/
theorem walk_alg :
    ∑ k, (rw k * ∑ j, (if zr j k then 0 else w j)) * ∑ q, ProductCircuit.ofBool F (A k q) * e q +
        α * ∑ k, (rw k * ∑ j, (if zr j k then 0 else w j)) * ∑ q, ProductCircuit.ofBool F (B k q) * e q =
      ∑ j, w j * ∑ q, e q * ∑ k, rw k * (if zr j k then 0 else
        ProductCircuit.ofBool F (A k q) + α * ProductCircuit.ofBool F (B k q)) := by
  simp only [colK_eq]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have h1 : ∀ k, (rw k * ∑ j, (if zr j k then 0 else w j)) * ∑ q, ProductCircuit.ofBool F (A k q) * e q +
      α * ((rw k * ∑ j, (if zr j k then 0 else w j)) * ∑ q, ProductCircuit.ofBool F (B k q) * e q) =
      ∑ j, w j * (rw k * (if zr j k then 0 else rowAB A B e α k)) := by
    intro k
    rw [rowAB, ← mul_assoc α, mul_comm α, mul_assoc _ α, ← mul_add, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

end Alg

/-- **The walk bridge at the specification** (A.8, A.9 `finLc` (ii)): with `free`'s weight `0`,
`Â(rowW′, eq(r_k,·)) + α B̂(rowW′, eq(r_k,·))` at `rowW′ = maskRows w rowW` is
`Σ_j w_j · M̃_j(r_k)`, `M_j = linM (zlmFR.Ak j) (zlmFR.Bk j) rowW α`. -/
theorem walk_bridge (w : Fin 9 → F) (hw : w 8 = 0) (l α : F) (rhi rk : Array F) (hrk : rk.size = 14) :
    Eval.walkSpecA (maskRows (Array.ofFn w) (rowWS l rhi)) (eqTab rk) +
        α * Eval.walkSpecB (maskRows (Array.ofFn w) (rowWS l rhi)) (eqTab rk) =
      ∑ j, w j * mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rowW (p := 8) l (ptA 8 rhi)) α)
        (fun v : Fin 14 => rk.getD v 0) := by
  have hrow : ∀ k : Fin (2 ^ 14), Eval.onPos (maskRows (Array.ofFn w) (rowWS l rhi)) k =
      rowW (p := 8) l (ptA 8 rhi) k * ∑ j : Fin 9, if isZeroRow (bkOf j) k.val then 0 else w j := by
    intro k
    have hs : k.val < (rowWS l rhi).size := by rw [rowWS, Array.size_ofFn]; exact k.isLt
    rw [Eval.onPos, maskRows_getD _ _ hs, rowWS_getD, maskOf_eq]
    refine congrArg (_ * ·) (Finset.sum_congr rfl fun j _ => ?_)
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
      simp only [j.isLt, dif_pos, Option.getD_some]
  have hcol : ∀ q : Fin (2 ^ 14), Eval.onPos (eqTab rk) q = eq (fun v : Fin 14 => rk.getD v 0) (cube q) := by
    intro q
    rw [Eval.onPos, eqTab_getD rk (by rw [hrk]; exact q.isLt), hrk, eqBits_eq_eq]
  have hR : ∀ j, w j * mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rowW (p := 8) l (ptA 8 rhi)) α)
      (fun v : Fin 14 => rk.getD v 0) =
      w j * ∑ q, eq (fun v : Fin 14 => rk.getD v 0) (cube q) * ∑ k, rowW (p := 8) l (ptA 8 rhi) k *
        (if isZeroRow (bkOf j) k.val then 0 else ProductCircuit.ofBool F (Block.circuitR1CS.A k q) +
          α * ProductCircuit.ofBool F (Block.circuitR1CS.B k q)) := by
    intro j
    by_cases hj : j = 8
    · subst hj; rw [hw, zero_mul, zero_mul]
    have hf : bkOf j ≠ .free := fun h => hj ((bkOf_free_iff j).1 h)
    refine congrArg (w j * ·) (Finset.sum_congr rfl fun q _ => congrArg (_ * ·)
      (Finset.sum_congr rfl fun k _ => ?_))
    show _ * (kMat Block.circuitR1CS.A j k q + α * kMat Block.circuitR1CS.B j k q) = _
    rw [kMat_of_ne _ hf, kMat_of_ne _ hf]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => hR j, ← walk_alg Block.circuitR1CS.A Block.circuitR1CS.B
    (rowW (p := 8) l (ptA 8 rhi)) (fun q => eq (fun v : Fin 14 => rk.getD v 0) (cube q)) α
    (fun j k => isZeroRow (bkOf j) k.val) w]
  simp only [Eval.walkSpecA, Eval.walkSpecB, hrow, mulVec_ofBool, hcol]
  rfl

/-- `zlmFR`'s `free` matrices are the identity (`free` pins no row). -/
theorem zlmFR_free (C : Block.Pos → Block.Pos → Bool) :
    kMat C 8 = fun p k => if p = k then 1 else 0 := by
  funext p k
  have h : isZeroRow (bkOf 8) p.val = false := by simp [bkOf, blockKinds, isZeroRow, zeroRows]
  simp only [kMat, h, Bool.false_eq_true, if_false]
  rfl

/-- `L_s(λ)`: `eqZS λ 0` on the first 64 entries (bit 6 of `s` is `0`). -/
theorem eqZS_lo (l : F) {s : ℕ} (hs : s < 64) :
    (eqZS l 0).getD s 0 = lagrangeWeight sNodeF l ⟨s, hs⟩ := by
  have h6 : s.testBit 6 = false := Nat.testBit_lt_two_pow (by simpa using hs)
  rw [eqZS, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show s < 128 by omega, dif_pos, Option.getD_some, h6, Bool.false_eq_true, if_false,
    sub_zero, mul_one, Nat.mod_eq_of_lt hs]

/-- **The `free` term's closed form** (A.9 `finLc` (ii), revision 3.16, R-V-M2): with `y =
v_free · (Σ_{s<64} L_s(λ) eq(r_k[0..5], s)) · eq(r′_hi, r_k[6..13])` as the verifier computes it
(`dotAcc`, `eqTab`, `eqPoint`), `y + α y` is `v_free · M̃_free(r_k)`. -/
theorem free_term (l α vf : F) (rhi : Array F) (hrhi : rhi.size = 8) (rk : List F) (hrk : rk.length = 14) :
    let y := vf * (dotAcc 0 (eqZS l 0) (eqTab (rk.take 6).toArray) 64 *
      eqPoint rhi (rk.drop 6).toArray)
    y + α * y = vf * mle (linM (zlmFR.Ak 8) (zlmFR.Bk 8) (rowW (p := 8) l (ptA 8 rhi)) α)
      (fun v : Fin 14 => rk.getD v 0) := by
  intro y
  have hpt : (fun v : Fin 14 => rk.getD v 0) =
      Fin.append (fun i : Fin 6 => rk.getD i 0) (fun i : Fin 8 => rk.getD (6 + i) 0) := by
    funext v
    refine Fin.addCases (m := 6) (n := 8) (fun i => ?_) (fun i => ?_) v
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  have hA : zlmFR.Ak 8 = fun p k => if p = k then 1 else 0 := zlmFR_free Block.circuitR1CS.A
  have hB : zlmFR.Bk 8 = fun p k => if p = k then 1 else 0 := zlmFR_free Block.circuitR1CS.B
  have hL := linM_free_mle (p := 8) l α (ptA 8 rhi) (fun i : Fin 6 => rk.getD i 0)
    (fun i : Fin 8 => rk.getD (6 + i) 0)
  rw [hA, hB, hpt]
  erw [hL]
  have hdot : dotAcc 0 (eqZS l 0) (eqTab (rk.take 6).toArray) 64 =
      ∑ s : Fin (2 ^ 6), lagrangeWeight (fun b : Fin 64 ↦ skipNode (Fin.castLE (by norm_num) b)) l s *
        eq (fun i : Fin 6 => rk.getD i 0) (cube s) := by
    have h6 : (rk.take 6).toArray.size = 6 := by simp [hrk]
    rw [dotAcc_eq, zero_add, ← Fin.sum_univ_eq_sum_range]
    refine Fintype.sum_equiv (finCongr (by norm_num)) _ _ fun s => ?_
    rw [eqZS_lo l s.isLt, eqTab_getD _ (by rw [h6]; exact s.isLt), h6, eqBits_eq_eq]
    refine congrArg₂ (· * ·) rfl (congrArg₂ eq (funext fun i => ?_) rfl)
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      show (i : ℕ) < 6 from i.isLt]
  have hpt2 : eqPoint rhi (rk.drop 6).toArray = eq (ptA 8 rhi) (fun i : Fin 8 => rk.getD (6 + i) 0) := by
    rw [eqPoint_eq, hrhi]
    refine congrArg (eq _) (funext fun i => ?_)
    simp [ptA, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_drop]
  simp only [y, hdot, hpt2]
  ring

theorem toArray_ofFn9 (l : List F) (hl : l.length = 9) :
    l.toArray = Array.ofFn fun j : Fin 9 => l.getD j 0 := by
  apply Array.ext
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_toArray, Array.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, Option.getD_some]

/-- The verifier's packed weights `w` (`finLc`'s `packFK`): a node's `nodeKindW v`, a leaf's
`v₀ :: 0⁸`. -/
def lcWts (κ : Kind) (v : List F) : List F :=
  if κ.isNode then nodeKindW v else v.headD 0 :: List.replicate 8 0

theorem lcWts_length (κ : Kind) {v : List F} (hv : v.length = 8) : (lcWts κ v).length = 9 := by
  unfold lcWts nodeKindW; split <;> simp [hv]

theorem lcWts_free (κ : Kind) {v : List F} (hv : v.length = 8) : (lcWts κ v).getD 8 0 = 0 := by
  unfold lcWts nodeKindW
  split
  · rw [List.getD_cons_succ, List.getD_append_right _ _ _ _ (by simp [hv])]; simp [hv]
  · simp

/-- **The kinds' weights in `finLc` (ii)**: `w` off `free`, `v_free` at `free`, are `vM`'s shape:
a node's `0 :: v`, a leaf's `v₀ :: 0⁸`. -/
theorem lcWts_vM (κ : Kind) {v : List F} (hv : v.length = 8) (vf : F)
    (hvf : vf = if κ.isNode then v.getD 7 0 else 0) (j : Fin 9) :
    (if j = 8 then vf else (lcWts κ v).getD j 0) =
      if κ.isNode then (if j.val = 0 then 0 else v.getD (j.val - 1) 0)
      else (if j.val = 0 then v.getD 0 0 else 0) := by
  subst hvf
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, rfl⟩ : ∃ v0 v1 v2 v3 v4 v5 v6 v7 : F,
      v = [v0, v1, v2, v3, v4, v5, v6, v7] := by
    match v, hv with
    | [v0, v1, v2, v3, v4, v5, v6, v7], _ => exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, rfl⟩
  cases hk : κ.isNode <;> fin_cases j <;> simp [lcWts, nodeKindW, hk]

/-- **`finLc` (ii)'s right side is the lincheck's per-kind sum** (the walk bridge at the verifier,
revision 3.16, R-V-M2): for ops meeting their specifications (`walkAB`, `rowW`, `eqZ`), the walk at
`maskRows (lcWts κ v) (rowW λ r′_hi)` and `eq(r_k, ·)`, plus `(1 + α)·y` with `y` the verifier's
`free` term, is `Σ_j v′_j · M̃_j(r_k)`, `v′` the kind-masked weights with `v_free` at `free`. -/
theorem lc_bridge {impl : OpImpl}
    (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    (κ : Kind) {v : List F} (hv : v.length = 8) (vf l α : F) (rhi : Array F) (hrhi : rhi.size = 8)
    (rk : List F) (hrk : rk.length = 14) :
    let rw := maskRows (lcWts κ v).toArray (impl.rowW l rhi)
    let cw := eqTab rk.toArray
    let y := vf * (dotAcc 0 (impl.eqZ l 0) (eqTab (rk.take 6).toArray) 64 *
      eqPoint rhi (rk.drop 6).toArray)
    (impl.walkAB rw cw).1 + α * (impl.walkAB rw cw).2 + (y + α * y) =
      ∑ j : Fin 9, (if j = 8 then vf else (lcWts κ v).getD j 0) *
        mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rowW (p := 8) l (ptA 8 rhi)) α)
          (fun u : Fin 14 => rk.getD u 0) := by
  intro rw cw y
  have hsz : rw.size = 2 ^ 14 := by
    simp only [rw, maskRows, Array.size_mapIdx, hR, rowWS, Array.size_ofFn]
  have hcz : cw.size = 2 ^ 14 := by simp only [cw, eqTab_size', List.size_toArray, hrk]
  have hw := walk_bridge (fun j : Fin 9 => (lcWts κ v).getD j 0) (lcWts_free κ hv) l α rhi rk.toArray
    (by simp [hrk])
  rw [← toArray_ofFn9 _ (lcWts_length κ hv)] at hw
  have hf := free_term l α vf rhi hrhi rk hrk
  simp only at hf
  rw [hW rw cw hsz hcz]
  simp only [rw, cw, y, hR, hZ, hw, hf, Fin.sum_univ_castSucc (n := 8)]
  have hpt : (fun u : Fin 14 => rk.toArray.getD u 0) = fun u : Fin 14 => rk.getD u 0 := by
    funext u; simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hw8 : (lcWts κ v).getD (Fin.last 8 : Fin 9).val 0 = 0 := lcWts_free κ hv
  rw [hpt, if_pos (show (Fin.last 8 : Fin 9) = 8 from rfl), hw8, zero_mul, add_zero]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_) rfl
  have hj : (Fin.castSucc j : Fin 9) ≠ 8 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [if_neg hj]

end FR.Snd

end
