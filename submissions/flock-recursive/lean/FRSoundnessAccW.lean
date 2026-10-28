-- New for `flock-recursive` (BLUEPRINT §3, A.9 `finPf`, A.10; stage S-G4, `hFin` step 6).
import FRSoundnessAccCol

/-!
# `hFin`, step 6: `finPf`'s level steps are `wHatL`'s

* **`tail_vals`**: the tail registers `tailRegs fi κ.m k` (`Pₖ[1..]`, `k = 1 … 4`) hold
  `ptL es k (v + 1)`, `v < mLog κ (k − 1)` (`tailList` is their value list; `tailList_eq` is the
  recursion of `ptL`: `sₖ[1..]`, then level `k + 1`'s point from its coordinate 1, then Pf's).
* **`lvStepV_eq`**: with `tensorW` at the spec, `lvStepV … k W` is `wHatL`'s step:
  `û(Pₖ[0])·(W + Σ_q eq(κ_c, bits₉ q)·tensorTwin(Pₖ[1..])(p_q))`.
* **`wV_eq`**: `wV = wHatL W₀ L es 4` once `w0V = wHatL W₀ L es 0` (the front's).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## The tail points as value lists -/

/-- `Pₖ[1..]`'s values: `sⱼ[1..]` for `j = k … 4`, then Pf's first `m − 25` challenges. -/
def tailList (es : Log) (m k : ℕ) : List K :=
  (List.range' k (5 - k)).flatMap (fun j => (List.range (hEll j - 1)).map fun t => sAt es j (t + 1)) ++
    (List.range (m - 25)).map (pfP es)

/-- Control (positive): at level 4 the tail is `s₄[1..3]` then Pf's challenges. -/
theorem tailList_four (es : Log) (m : ℕ) :
    tailList es m 4 = (List.range 3).map (fun t => sAt es 4 (t + 1)) ++
      (List.range (m - 25)).map (pfP es) := by
  simp [tailList, hEll, lvlStar, lvl, ladder, ladder32]

/-- Control (negative): the tail of level 1 does not start with level 1's first challenge (it is
`P₁[1..]`): its head is `s₁[1]`. -/
theorem tailList_one_head (es : Log) (m : ℕ) : (tailList es m 1).head? = some (sAt es 1 1) := by
  simp [tailList, hEll, lvlStar, lvl, ladder, ladder32, List.range'_succ, List.range_succ_eq_map]

/-- Controls on the tail's length: level 1's tail has `mLog L32 0 = 19` values at `m = 32` and a
different number (17) at `m = 30`. -/
theorem tailList_len (es : Log) : (tailList es 32 1).length = 19 ∧
    (tailList es 30 1).length ≠ (tailList es 32 1).length := by
  simp [tailList, hEll, lvlStar, lvl, ladder, ladder32, List.range'_succ]

theorem map_range_append {α : Type} (a b : ℕ) (f g : ℕ → α) :
    (List.range a).map f ++ (List.range b).map g =
      (List.range (a + b)).map (fun v => if v < a then f v else g (v - a)) := by
  refine List.ext_getElem (by simp) fun v h1 h2 => ?_
  simp only [List.length_append, List.length_map, List.length_range] at h1
  by_cases hv : v < a
  · rw [List.getElem_append_left (by simpa using hv)]; simp [hv]
  · rw [List.getElem_append_right (by simpa using hv)]; simp [hv]

/-- The tail's length sum from level `k`. -/
def tLen (m k : ℕ) : ℕ := ((List.range' k (5 - k)).map fun j => hEll j - 1).sum + (m - 25)

theorem tailList_four_eq (es : Log) (m : ℕ) :
    tailList es m 4 = (List.range (tLen m 4)).map (fun v => ptL es 4 (v + 1)) := by
  rw [tailList_four]
  have h3 : tLen m 4 = 3 + (m - 25) := by simp [tLen, hEll, lvlStar, lvl, ladder, ladder32]
  rw [h3, map_range_append]
  refine List.map_congr_left fun v _ => ?_
  have h4 : hEll 4 = 4 := by simp [hEll, lvlStar, lvl, ladder, ladder32]
  unfold ptL ptD
  simp only [show 4 - 4 = 0 from rfl, h4]
  split_ifs with h1 h2 h2 <;> first | omega | exact congrArg _ (by omega)

theorem tailList_step (es : Log) (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 4)
    (ih : tailList es m (k + 1) = (List.range (tLen m (k + 1))).map (fun v => ptL es (k + 1) (v + 1))) :
    tailList es m k = (List.range (tLen m k)).map (fun v => ptL es k (v + 1)) := by
  have hr : List.range' k (5 - k) = k :: List.range' (k + 1) (5 - (k + 1)) := by
    rw [show 5 - k = (5 - (k + 1)) + 1 by omega, List.range'_succ]
  have hl : tailList es m k = (List.range (hEll k - 1)).map (fun t => sAt es k (t + 1)) ++
      tailList es m (k + 1) := by
    rw [tailList, tailList, hr, List.flatMap_cons, List.append_assoc]
  have hlen : tLen m k = (hEll k - 1) + tLen m (k + 1) := by
    simp only [tLen, hr, List.map_cons, List.sum_cons]; omega
  rw [hl, ih, map_range_append, hlen]
  refine List.map_congr_left fun v _ => ?_
  have he := hEll_pos (i := k) (by omega)
  rw [ptL_lt (k := k) hk]
  beta_reduce
  by_cases h1 : v < hEll k - 1
  · simp only [h1, show v + 1 < hEll k by omega, ite_true]
  · rw [show v - (hEll k - 1) + 1 = v + 1 - hEll k + 1 by omega]
    simp only [h1, show ¬ v + 1 < hEll k by omega, ite_false]

theorem tailList_eq (es : Log) (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    tailList es m k = (List.range (tLen m k)).map (fun v => ptL es k (v + 1)) := by
  have h4 := tailList_four_eq es m
  have h3 := tailList_step es m (k := 3) (by norm_num) (by norm_num) h4
  have h2 := tailList_step es m (k := 2) (by norm_num) (by norm_num) h3
  have h1 := tailList_step es m (k := 1) (by norm_num) (by norm_num) h2
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  exacts [h1, h2, h3, h4]

/-- Control (negative): the two ladders' tails differ at level 1. -/
theorem tLen_ne : tLen 32 1 ≠ tLen 30 1 := by decide

/-- The tails' lengths are the levels' `mLog` (both ladders). -/
theorem tail_len (κ : Kind) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    tLen κ.m k = mLog κ (k - 1) := by
  cases κ <;> interval_cases k <;> decide

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem drop_one_map_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).drop 1 = (List.range (n - 1)).map fun t => g (t + 1) := by
  rcases n with _ | n
  · rfl
  · rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

/-- **The tail registers hold `ptL`** (`k = 1 … 4`, any registers extending the skeleton's). -/
theorem tail_vals (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
    {r' : Array Val} (hE : ExtA (#[] ++ y.1.toArray) r') {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (tailRegs fi κ.m k).map (fun x => (rd r' x).toK) =
        (List.range (mLog κ (k - 1))).map (fun v => ptL (fsOf tr items) k (v + 1)) ∧
      ∀ x ∈ tailRegs fi κ.m k, x < (#[] ++ y.1.toArray).size := by
  obtain ⟨hpv, hpl, -, -, hpo, -⟩ := pf_facts h hfi
  have hm : κ.m - 25 ≤ 7 := by cases κ <;> decide
  have hS : ∀ j < 5, ((sRegs fi j).drop 1).map (fun x => (rd r' x).toK) =
      (List.range (hEll j - 1)).map (fun t => sAt (fsOf tr items) j (t + 1)) ∧
      ∀ x ∈ (sRegs fi j).drop 1, x < (#[] ++ y.1.toArray).size := fun j hj => by
    obtain ⟨b, hs, -, hsv, -, -, hb, -⟩ := p1_facts h hfi hj
    have hlt : ∀ x ∈ sRegs fi j, x < (#[] ++ y.1.toArray).size := fun x hx =>
      hb x (by rw [sRegs] at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx))
    refine ⟨?_, fun x hx => hlt x (List.mem_of_mem_drop hx)⟩
    rw [hs, drop_one_map_range, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have ht' := List.mem_range.1 ht
    simp only [Function.comp_apply]
    rw [hE.rd (hlt _ (by rw [hs]; exact List.mem_map.2 ⟨t + 1, List.mem_range.2 (by omega), rfl⟩)),
      hsv _ (by omega)]
    rfl
  have hP : ((chals fi "Pf" 7).take (κ.m - 25)).map (fun x => (rd r' x).toK) =
      (List.range (κ.m - 25)).map (pfP (fsOf tr items)) := by
    refine List.ext_getElem (by simp [hpl]; omega) fun v h1 h2 => ?_
    simp only [List.length_map, List.length_take, hpl] at h1
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hv : v < 7 := by omega
    have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
      unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
    have hmem : (chals fi "Pf" 7)[v] ∈ outsOf fi "Pf" := hch _ (List.getElem_mem _)
    rw [hE.rd (hpo _ hmem), ← List.getD_eq_getElem _ 0, hpv v hv]; rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [tailRegs, List.map_append, List.map_flatMap, hP, ← tail_len κ hk1 hk4,
      ← tailList_eq _ _ hk1 hk4, tailList,
      List.flatMap_congr fun j hj => (hS j (by have := List.mem_range'.1 hj; omega)).1]
  · rw [tailRegs, List.mem_append, List.mem_flatMap] at hx
    rcases hx with ⟨j, hj, hx⟩ | hx
    · exact (hS j (by have := List.mem_range'.1 hj; omega)).2 x hx
    · refine hpo x ?_
      have hx' := List.mem_of_mem_take hx
      unfold chals at hx'; exact List.mem_of_mem_drop (List.mem_of_mem_take hx')

theorem ptL_zero {es : Log} {k : ℕ} (hk : k ≤ 4) : ptL es k 0 = sAt es k 0 := by
  rcases Nat.lt_or_ge k 4 with h | h
  · rw [ptL_lt h]; simp [hEll_pos (i := k) (by omega)]
  · obtain rfl : k = 4 := by omega
    exact ptL_four_lt es (hEll_pos (by norm_num))

/-- **One level step of `finPf` at the spec** (`k + 1 = 1 … 4`): `lvStepV` is `wHatL`'s step. -/
theorem lvStepV_eq (h : SkRun impl κ inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hπ : inp.π.size = piSize) {fi : FinIn}
    (hfi : fi.outs = skeleton.2.outs) {r' : Array Val} (hE : ExtA (#[] ++ y.1.toArray) r')
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {k : ℕ} (hk : k < 4) (W : K) :
    lvStepV impl fi (rd r') (tailV κ fi r') (k + 1) W =
      uHat (ptL (fsOf tr items) (k + 1) 0) * (W + ∑ q ∈ range (lvl κ k).t,
        algebraMap F K (eqBits (kcAt (fsOf tr items) k) 9 q) *
          tensorTwin D logNMax (mLog κ k)
            (fun v => if v < mLog κ k then ptL (fsOf tr items) (k + 1) (v + 1) else 0)
            (qPos κ (fsOf tr items) k q)) := by
  obtain ⟨b, hs, -, hsv, -, -, hb, -⟩ := p1_facts h hfi (i := k + 1) (by omega)
  obtain ⟨hkc, hkcl⟩ := kc_facts h hfi (i := k) (by omega)
  obtain ⟨hyl, hylt, hyv⟩ := ys_facts h hL hin hπ hfi (i := k) (by omega)
  obtain ⟨htv, htl⟩ := tail_vals h hfi hE (k := k + 1) (by omega) (by omega)
  have h9 := (lvl_facts κ (i := k) (by omega)).2.2.2.2.2.2.2.1
  rw [Nat.add_sub_cancel] at htv
  unfold lvStepV
  simp only [Nat.add_sub_cancel]
  have hE0 := hEll_pos (i := k + 1) (by omega)
  -- `Pₖ[0]`
  have hsub : ∀ x ∈ sRegs fi (k + 1), x ∈ lvOuts fi (k + 1) 0 := fun x hx => by
    unfold sRegs at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  have hhead : (sRegs fi (k + 1)).headD 0 = b + 13 * 0 + 6 := by
    rw [hs]; obtain ⟨e, he⟩ : ∃ e, hEll (k + 1) = e + 1 := ⟨hEll (k + 1) - 1, by omega⟩
    rw [he, List.range_succ_eq_map]; rfl
  have hmem0 : b + 13 * 0 + 6 ∈ sRegs fi (k + 1) := by
    rw [hs]; exact List.mem_map.2 ⟨0, List.mem_range.2 hE0, rfl⟩
  rw [hhead, hE.rd (hb _ (hsub _ hmem0)), hsv 0 hE0, Val.toK, ptL_zero (by omega)]
  congr 1
  -- `eq(κ_c, ·)` and the folds
  have hkc' : (kcOf fi k).map (fun x => (rd r' x).toF) = (List.range 9).map (kcAt (fsOf tr items) k) := by
    rw [← hkc]; exact List.map_congr_left fun x hx => by rw [hE.rd (hkcl x hx)]
  rw [hkc', accVal_eq, List.length_map, List.length_range, hyl,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_range.1 hq
  have hqa : (List.range 9).length = 9 := List.length_range
  rw [Nat.zero_add, eqTab_getD _ (by simp; omega), K.smulF_eq_mul, ← K.algebraMap_eq_ofF]
  simp only [List.size_toArray, List.length_map, List.length_range]
  rw [eqBits_congr (r' := kcAt (fsOf tr items) k) (fun v hv => by
    simp [Array.getD_eq_getD_getElem?, hv])]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
  obtain ⟨hidx, -⟩ := hyv q hq'
  have hlt : (ysOf fi k).getD q 0 - 3 < (#[] ++ y.1.toArray).size := by
    have hm : (ysOf fi k).getD q 0 ∈ ysOf fi k := by
      rw [List.getD_eq_getElem _ _ (by rw [hyl]; exact hq')]; exact List.getElem_mem _
    exact lt_of_le_of_lt (α := ℕ) (Nat.sub_le _ _) (hylt _ hm)
  rw [hE.rd hlt, hidx, Val.toN, ht, Impl.tensorWS, tensorTwin, tensorTwin]
  have hsz : (tailV κ fi r' (k + 1)).size = mLog κ k := by
    rw [tailV, List.size_toArray, htv]; simp
  rw [hsz]
  refine prod_congr rfl fun v hv => ?_
  have hv' := mem_range.1 hv
  have hg : (tailV κ fi r' (k + 1)).getD v 0 = ptL (fsOf tr items) (k + 1) (v + 1) := by
    rw [tailV, Array.getD_eq_getD_getElem?, List.getElem?_toArray, htv]; simp [hv']
  rw [hg, if_pos hv']

theorem lvsV_snoc (impl : OpImpl) (fi : FinIn) (rv : ℕ → Val) (tl : ℕ → Array K) (x : ℕ) :
    ∀ (l : List ℕ) (W : K), lvsV impl fi rv tl (l ++ [x]) W = lvStepV impl fi rv tl x (lvsV impl fi rv tl l W)
  | [], _ => rfl
  | k :: l, W => by simp only [List.cons_append, lvsV]; exact lvsV_snoc impl fi rv tl x l _

/-- **`finPf`'s `Ŵ₄(P₄)` at the spec is `wHatL … 4`**, from `Ŵ₀(P₀)` (the front's). -/
theorem wV_eq (h : SkRun impl κ inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hπ : inp.π.size = piSize) {fi : FinIn}
    (hfi : fi.outs = skeleton.2.outs) {r' : Array Val} (hE : ExtA (#[] ++ y.1.toArray) r')
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) (W₀ : Log → Log → ℕ → K)
    (hk : kindOf (fsOf tr items) = κ)
    (hw0 : w0V impl κ fi r' = wHatL W₀ L (fsOf tr items) 0) :
    wV impl κ fi r' = wHatL W₀ L (fsOf tr items) 4 := by
  have key : ∀ k ≤ 4, lvsV impl fi (rd r') (tailV κ fi r') ((List.range k).map (· + 1))
      (w0V impl κ fi r') = wHatL W₀ L (fsOf tr items) k := by
    intro k hk4
    induction k with
    | zero => exact hw0
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, lvsV_snoc, ih (by omega),
        lvStepV_eq h hL hin hπ hfi hE ht (by omega), wHatL, hk]
  exact key 4 le_rfl

end FR.Snd
