-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stage S-E4, track
-- L-circ). The node section (`Plan`, `planOf`, `nodeIRows`, `evalMT`, `evalMKT`) moved here from
-- `FRVIRTplEval` (S-E3); `evalMT` is now the flat evaluation.
import FRVIRTplPlan

/-!
# The flat evaluation of the node's M matrices (`evalM`)

BLUEPRINT §10 changes 17 (e), revision 3.12 item 3. `FRVIRTplEval.slotVal` evaluates a slot's
rows through lists of boxed terms, one `eq(σ, cell)` product per entry and one lookup in the
layout per template instance (S-E3: 1.13 s per `evalM`). Here the same value is computed from data
prepared **once per node** (`Plan.fs`, at `planOf`):

* every linear form is **grouped by the high part of its cells** (`grp`: consecutive terms with the
  same `cell / 2^12`), so a term costs a table lookup (and a product only when its coefficient is
  not `1`), and a group one product with `eq(σ_hi, ·)`;
* the skeleton's rows are **grouped by the high part of their index** (`grows`), so a row costs
  one product with `eq(τ_lo, ·)` per non-empty form;
* each template instance's alignment test, bases and grouped input forms are precomputed
  (`GInst`); its two high `eq` factors are computed once per evaluation and shared by the three
  matrices; each key's input terms are **compacted per input** (`compactIT`: one coefficient per
  input instead of one per occurrence);
* the `eq` tables of `τ` and `σ` and the keys' local parts are shared by the two slots.

**`evalMT_eq`** (the statement of S-E3, unchanged): `evalMT pl τ σ = evalMS pl τ σ`, the MLEs of
the node's indexed M rows. The proof goes through `slotVal_eq`: `fslotVal_eq` shows that the flat
value of a slot is `slotVal`'s.
-/

namespace FR
namespace TEval
open Circ Tpl

/-! ## Products without a unit coefficient -/

/-- `c · x`, with no product when `c = 1`. -/
@[inline] def cmulF (c x : F) : F := if c == 1 then x else c * x

theorem cmulF_eq (c x : F) : cmulF c x = c * x := by
  unfold cmulF; split_ifs with h
  · rw [beq_iff_eq.1 h, one_mul]
  · rfl

/-! ## Forms grouped by high cell index -/

/-- A linear form in groups `(hi, [(lo, coefficient)])` of consecutive terms with the same high
index. -/
abbrev GForm := List (ℕ × List (ℕ × F))

/-- Put one term in front of a grouped form. -/
def grpStep (p : ℕ) (t : ℕ × F) : GForm → GForm
  | g :: gs => if g.1 = t.1 / p then (g.1, (t.1 % p, t.2) :: g.2) :: gs
    else (t.1 / p, [(t.1 % p, t.2)]) :: g :: gs
  | [] => [(t.1 / p, [(t.1 % p, t.2)])]

/-- **The grouped form** (`p` = the size of the low table). -/
def grp (p : ℕ) (l : Lin) : GForm := l.foldr (grpStep p) []

/-- A group's inner sum `Σ c · lo[j]`. -/
@[inline] def gInner (lo : Array F) (es : List (ℕ × F)) : F := sumL (fun e => cmulF e.2 (lo.getD e.1 0)) es

/-- **The value of a grouped form**: `Σ_groups hi[h] · Σ c · lo[j]`. -/
def glVal (lo hi : Array F) (g : GForm) : F := sumL (fun h => hi.getD h.1 0 * gInner lo h.2) g

theorem glVal_cons (lo hi : Array F) (h : ℕ × List (ℕ × F)) (g : GForm) :
    glVal lo hi (h :: g) = hi.getD h.1 0 * gInner lo h.2 + glVal lo hi g := by
  simp only [glVal, sumL_eq, List.map_cons, List.sum_cons]

theorem gInner_cons (lo : Array F) (e : ℕ × F) (es : List (ℕ × F)) :
    gInner lo (e :: es) = e.2 * lo.getD e.1 0 + gInner lo es := by
  simp only [gInner, sumL_eq, List.map_cons, List.sum_cons, cmulF_eq]

theorem glVal_grpStep (lo hi : Array F) (p : ℕ) (t : ℕ × F) (G : GForm) :
    glVal lo hi (grpStep p t G) =
      t.2 * (lo.getD (t.1 % p) 0 * hi.getD (t.1 / p) 0) + glVal lo hi G := by
  cases G with
  | nil =>
    simp only [grpStep, glVal_cons, gInner_cons]
    simp [glVal, gInner, sumL_eq]; ring
  | cons g gs =>
    simp only [grpStep]
    split_ifs with h
    · simp only [glVal_cons, gInner_cons, h]; ring
    · simp only [glVal_cons, gInner_cons]
      simp [gInner, sumL_eq]; ring

/-- **The grouped form has the form's value** (with `eq(σ, ·)` split at `p`). -/
theorem glVal_grp (lo hi : Array F) (p : ℕ) (l : Lin) :
    glVal lo hi (grp p l) = linEI (RingHom.id F) (splitAt lo hi p) l := by
  unfold grp
  induction l with
  | nil => simp [glVal, linEI, sumL_eq]
  | cons t l ih =>
    rw [List.foldr_cons, glVal_grpStep, ih]
    simp only [linEI, sumL_eq, List.map_cons, List.sum_cons, cmul_eq, splitAt, RingHom.id_apply]

theorem glVal_nil (lo hi : Array F) : glVal lo hi [] = 0 := rfl

/-! ## Rows grouped by high row index -/

/-- A grouped row: the low part of its index and its three grouped forms. -/
structure GRow where
  lo : ℕ
  a : GForm
  b : GForm
  c : GForm

/-- Matrix `s`'s form of a grouped row. -/
def GRow.m : Mat → GRow → GForm
  | .a, r => r.a | .b, r => r.b | .c, r => r.c

/-- Rows in groups `(hi, rows)` of consecutive rows with the same high index. -/
abbrev GRows := List (ℕ × List GRow)

/-- A row grouped at low row table size `pr` and low cell table size `pc`. -/
def growOf (pr pc : ℕ) (r : ℕ × Row) : GRow := ⟨r.1 % pr, grp pc r.2.a, grp pc r.2.b, grp pc r.2.c⟩

/-- Put one row in front of grouped rows. -/
def growsStep (pr pc : ℕ) (r : ℕ × Row) : GRows → GRows
  | g :: gs => if g.1 = r.1 / pr then (g.1, growOf pr pc r :: g.2) :: gs
    else (r.1 / pr, [growOf pr pc r]) :: g :: gs
  | [] => [(r.1 / pr, [growOf pr pc r])]

/-- **The grouped rows.** -/
def grows (pr pc : ℕ) (rows : List (ℕ × Row)) : GRows := rows.foldr (growsStep pr pc) []

/-- `w · v(g)`, no product for an empty form. -/
@[inline] def rowMul (lo hi : Array F) (w : F) (g : GForm) : F :=
  match g with
  | [] => 0
  | _ => w * glVal lo hi g

theorem rowMul_eq (lo hi : Array F) (w : F) (g : GForm) : rowMul lo hi w g = w * glVal lo hi g := by
  cases g with
  | nil => simp [rowMul, glVal_nil]
  | cons _ _ => rfl

/-- A row group's inner sum. -/
@[inline] def rInner (s : Mat) (tlo slo shi : Array F) (rs : List GRow) : F :=
  sumL (fun r => rowMul slo shi (tlo.getD r.lo 0) (r.m s)) rs

/-- **The value of grouped rows** for matrix `s`. -/
def growsVal (s : Mat) (tlo thi slo shi : Array F) (G : GRows) : F :=
  sumL (fun h => thi.getD h.1 0 * rInner s tlo slo shi h.2) G

theorem growsVal_cons (s : Mat) (tlo thi slo shi : Array F) (h : ℕ × List GRow) (G : GRows) :
    growsVal s tlo thi slo shi (h :: G) =
      thi.getD h.1 0 * rInner s tlo slo shi h.2 + growsVal s tlo thi slo shi G := by
  simp only [growsVal, sumL_eq, List.map_cons, List.sum_cons]

theorem rInner_cons (s : Mat) (tlo slo shi : Array F) (r : GRow) (rs : List GRow) :
    rInner s tlo slo shi (r :: rs) =
      tlo.getD r.lo 0 * glVal slo shi (r.m s) + rInner s tlo slo shi rs := by
  simp only [rInner, sumL_eq, List.map_cons, List.sum_cons, rowMul_eq]

theorem growOf_m (s : Mat) (pr pc : ℕ) (r : ℕ × Row) :
    (growOf pr pc r).m s = grp pc (s.r r.2) := by cases s <;> rfl

theorem growsVal_step (s : Mat) (tlo thi slo shi : Array F) (pr pc : ℕ) (r : ℕ × Row) (G : GRows) :
    growsVal s tlo thi slo shi (growsStep pr pc r G) =
      (tlo.getD (r.1 % pr) 0 * thi.getD (r.1 / pr) 0) *
        linEI (RingHom.id F) (splitAt slo shi pc) (s.r r.2) + growsVal s tlo thi slo shi G := by
  have hv : glVal slo shi ((growOf pr pc r).m s) = linEI (RingHom.id F) (splitAt slo shi pc) (s.r r.2) := by
    rw [growOf_m, glVal_grp]
  cases G with
  | nil =>
    simp only [growsStep, growsVal_cons, rInner_cons, hv]
    simp only [growOf, rInner, sumL_eq, List.map_nil, List.sum_nil, growsVal]; ring
  | cons g gs =>
    simp only [growsStep]
    split_ifs with h
    · simp only [growsVal_cons, rInner_cons, hv, h]
      simp only [growOf]; ring
    · simp only [growsVal_cons, rInner_cons, hv]
      simp only [growOf, rInner, sumL_eq, List.map_nil, List.sum_nil]; ring

/-- **The grouped rows have the rows' sparse value** (`eq(τ, ·)` split at `pr`, `eq(σ, ·)` at
`pc`). -/
theorem growsVal_grows (s : Mat) (tlo thi slo shi : Array F) (pr pc : ℕ) (rows : List (ℕ × Row)) :
    growsVal s tlo thi slo shi (grows pr pc rows) =
      rowsValI (RingHom.id F) s (splitAt tlo thi pr) (splitAt slo shi pc) rows := by
  unfold grows
  induction rows with
  | nil => simp [growsVal, rowsValI, sumL_eq]
  | cons r rows ih =>
    rw [List.foldr_cons, growsVal_step, ih]
    simp only [rowsValI, sumL_eq, List.map_cons, List.sum_cons, splitAt]

/-! ## Input terms compacted per input -/

/-- **One coefficient per input**: the terms `(i, u)` summed per `i` (zero sums dropped). -/
def compactIT (it : List (ℕ × F)) : List (ℕ × F) :=
  let N := it.foldl (fun m q => max m (q.1 + 1)) 0
  let U := it.foldl (fun U q => U.modify q.1 (· + q.2)) (Array.replicate N (0 : F))
  (List.range N).filterMap fun i => let u := U.getD i 0; if u == 0 then none else some (i, u)

theorem foldl_max_ge (it : List (ℕ × F)) (a : ℕ) : a ≤ it.foldl (fun m q => max m (q.1 + 1)) a := by
  induction it generalizing a with
  | nil => exact le_rfl
  | cons q it ih => exact le_trans (le_max_left _ _) (ih _)

theorem foldl_max_lt (it : List (ℕ × F)) (a : ℕ) : ∀ q ∈ it, q.1 < it.foldl (fun m q => max m (q.1 + 1)) a := by
  induction it generalizing a with
  | nil => simp
  | cons q it ih =>
    intro q' hq'
    rcases List.mem_cons.1 hq' with rfl | h
    · exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) (foldl_max_ge _ _)
    · exact ih _ q' h

theorem modify_getD (U : Array F) (j : ℕ) (c : F) (i : ℕ) :
    (U.modify j (· + c)).getD i 0 = U.getD i 0 + (if i = j ∧ j < U.size then c else 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : j = i
  · subst hij
    by_cases hs : j < U.size
    · simp [Array.getElem?_eq_getElem hs, hs]
    · simp [Array.getElem?_eq_none (by omega : U.size ≤ j), hs]
  · simp [hij, Ne.symm hij]

theorem sum_range_ite (N j : ℕ) (a : F) :
    ((List.range N).map fun i => if i = j then a else 0).sum = if j < N then a else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h : j < N
    · simp [h, show j < N + 1 by omega, show N ≠ j by omega]
    · by_cases h' : j = N
      · subst h'; simp
      · simp [h, h', show ¬ j < N + 1 by omega, Ne.symm h']

theorem sum_range_modify (N : ℕ) (U : Array F) (hU : U.size = N) (j : ℕ) (hj : j < N) (c : F)
    (f : ℕ → F) :
    ((List.range N).map fun i => (U.modify j (· + c)).getD i 0 * f i).sum =
      ((List.range N).map fun i => U.getD i 0 * f i).sum + c * f j := by
  have : ∀ i, (U.modify j (· + c)).getD i 0 * f i =
      U.getD i 0 * f i + (if i = j then c * f j else 0) := fun i => by
    rw [modify_getD]; by_cases h : i = j
    · subst h; simp [hU, hj]; ring
    · simp [h]
  simp only [this, List.sum_map_add, sum_range_ite, hj, if_true]

theorem foldl_modify (N : ℕ) (f : ℕ → F) :
    ∀ (it : List (ℕ × F)) (U : Array F), U.size = N → (∀ q ∈ it, q.1 < N) →
      ((List.range N).map fun i => (it.foldl (fun U q => U.modify q.1 (· + q.2)) U).getD i 0 * f i).sum =
        ((List.range N).map fun i => U.getD i 0 * f i).sum + (it.map fun q => q.2 * f q.1).sum
  | [], U, _, _ => by simp
  | q :: it, U, hU, hq => by
    rw [List.foldl_cons, foldl_modify N f it _ (by rw [Array.size_modify, hU])
      (fun q' h => hq q' (List.mem_cons_of_mem _ h)),
      sum_range_modify N U hU q.1 (hq q (List.mem_cons_self ..)) q.2 f, List.map_cons, List.sum_cons]
    ring

theorem sum_filterMap_nz (L : List ℕ) (u : ℕ → F) (f : ℕ → F) :
    ((L.filterMap fun i => if u i == 0 then none else some (i, u i)).map fun q => q.2 * f q.1).sum =
      (L.map fun i => u i * f i).sum := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [beq_iff_eq] at ih ⊢
    by_cases h : u i = 0
    · simp [List.filterMap_cons, h, ih]
    · simp [List.filterMap_cons, h, ih]

/-- **Compaction keeps the input sum.** -/
theorem compactIT_sum (it : List (ℕ × F)) (f : ℕ → F) :
    ((compactIT it).map fun q => q.2 * f q.1).sum = (it.map fun q => q.2 * f q.1).sum := by
  unfold compactIT
  simp only []
  rw [sum_filterMap_nz, foldl_modify _ f it _ (Array.size_replicate ..) (foldl_max_lt it 0)]
  have h0 : ∀ N i, (Array.replicate N (0 : F)).getD i 0 = 0 := fun N i => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl
  simp only [h0, zero_mul]
  simp

/-! ## A raw template instance in closed form (`tplR_mle`) -/

section Raw
variable {R : Type*} [CommRing R] (ι : F →+* R)

/-- A raw template's terms with the row factor: `(wire, eq(τ_lo, j) · ι c)`. -/
def ttR (s : Mat) (T : List RowT) (eτ : ℕ → R) : List (Wire × R) :=
  T.zipIdx.flatMap fun p => (s.t p.1).map fun t => (t.1, eτ p.2 * ι t.2)

/-- **`tplR_mle`** (`tpl_mle` for raw template rows): an instance at row base `2^A · Xh` and cell
base `2^B · Ch` is `Hτ · (Hσ · LOC + ONE · E(one) + Σ_IT u · E(ins_i))`, when the rows fit `2^A`
and the locals `2^B`. -/
theorem tplR_mle (s : Mat) {n m A B : ℕ} (τ σ : ℕ → R) (T : List RowT) (one : Lin)
    (ins : List Lin) (Xh Ch : ℕ) (hA : A ≤ n) (hB : B ≤ m) (hT : T.length ≤ 2 ^ A)
    (hL : ∀ r ∈ T, ∀ k c, (Wire.loc k, c) ∈ s.t r → k < 2 ^ B) (eτ eσ : ℕ → R)
    (heτ : ∀ j < T.length, eτ j = eqN A τ j) (heσ : ∀ k < 2 ^ B, eσ k = eqN B σ k) :
    rowsVal ι s n m τ σ (instIR T one ins (2 ^ A * Xh) (2 ^ B * Ch)) =
      instClosed ι m σ one ins (gN (n - A) (fun l => τ (A + l)) Xh)
        (gN (m - B) (fun l => σ (B + l)) Ch) (locSum eσ (ttR ι s T eτ))
        (oneSum (ttR ι s T eτ)) (inpList (ttR ι s T eτ)) := by
  set Hτ := gN (n - A) (fun l => τ (A + l)) Xh
  set Hσ := gN (m - B) (fun l => σ (B + l)) Ch
  set cb := 2 ^ B * Ch
  have hloc : ∀ p ∈ ttR ι s T eτ, ∀ k, p.1 = .loc k → gN m σ (cb + k) = eσ k * Hσ := by
    intro p hp k hk
    simp only [ttR, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, ⟨w, c⟩, hwc, rfl⟩ := hp
    simp only at hk; subst hk
    have hk' := hL _ (zipIdx_mem hq).1 _ _ hwc
    rw [gN_split hB _ _ hk', heσ k hk']
  have hrow : ∀ p ∈ T.zipIdx,
      gN n τ (2 ^ A * Xh + p.2) * linE ι m σ (s.r (instRow one ins cb p.1)) =
      Hτ * ((s.t p.1).map fun t => eτ p.2 * ι t.2 * wireE ι m σ one ins cb t.1).sum := by
    intro p hp
    have hj := (zipIdx_mem hp).2
    rw [gN_split hA _ _ (lt_of_lt_of_le hj hT), Mat.r_inst, linE_instLin, ← heτ _ hj,
      mul_comm (eτ _), mul_assoc, ← List.sum_map_mul_left]
    simp only [mul_assoc]; rfl
  unfold instClosed
  rw [← partition ι m σ one ins cb eσ Hσ _ hloc, rowsVal, instIR, List.map_map, ttR,
    sum_flatMap_map]
  simp only [Function.comp_def]
  rw [List.map_congr_left hrow, List.sum_map_mul_left]
  simp only [List.map_map, Function.comp_def]

end Raw

/-! ## Input coefficients as a dense array -/

/-- **One coefficient per input index** (`U[i] = Σ_{(i, u) ∈ IT} u`). -/
def denseIT (it : List (ℕ × F)) : Array F :=
  it.foldl (fun U q => U.modify q.1 (· + q.2))
    (Array.replicate (it.foldl (fun m q => max m (q.1 + 1)) 0) 0)

theorem foldl_modify_size (it : List (ℕ × F)) : ∀ U : Array F,
    (it.foldl (fun U q => U.modify q.1 (· + q.2)) U).size = U.size := by
  induction it with
  | nil => intro U; rfl
  | cons q it ih => intro U; rw [List.foldl_cons, ih, Array.size_modify]

theorem sum_range_ext (g : ℕ → F) (L : ℕ) (h : ∀ i, L ≤ i → g i = 0) :
    ∀ k, ((List.range (L + k)).map g).sum = ((List.range L).map g).sum := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, ih]; simp [h (L + k) (by omega)]

theorem sum_range_ext' (g : ℕ → F) {L M : ℕ} (hLM : L ≤ M) (h : ∀ i, L ≤ i → g i = 0) :
    ((List.range M).map g).sum = ((List.range L).map g).sum := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLM; exact sum_range_ext g L h k

/-- **The dense coefficients give the input sum**, over any range covering the inputs read. -/
theorem denseIT_sum (it : List (ℕ × F)) (f : ℕ → F) (M : ℕ) (hM : ∀ i, M ≤ i → f i = 0) :
    (it.map fun q => q.2 * f q.1).sum = ((List.range M).map fun i => (denseIT it).getD i 0 * f i).sum := by
  set N := it.foldl (fun m q => max m (q.1 + 1)) 0
  have h0 : ∀ i, (Array.replicate N (0 : F)).getD i 0 = 0 := fun i => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl
  have hf := foldl_modify N f it (Array.replicate N 0) (Array.size_replicate ..) (foldl_max_lt it 0)
  simp only [h0, zero_mul, List.map_const', List.sum_replicate, smul_zero, zero_add] at hf
  rw [← hf]
  change ((List.range N).map fun i => (denseIT it).getD i 0 * f i).sum = _
  have hs : (denseIT it).size = N := by rw [denseIT, foldl_modify_size, Array.size_replicate]
  have hU : ∀ i, N ≤ i → (denseIT it).getD i 0 * f i = 0 := fun i hi => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; simp
  have hV : ∀ i, M ≤ i → (denseIT it).getD i 0 * f i = 0 := fun i hi => by simp [hM i hi]
  rw [← sum_range_ext' _ (le_max_left N M) hU, sum_range_ext' _ (le_max_right N M) hV]

/-- **The input sum split into shared and own inputs.** -/
theorem sum_split (U : Array F) (E : Lin → F) (hE : E [] = 0) (sh own : List Lin) :
    ((List.range (sh.length + own.length)).map fun i => U.getD i 0 * E ((sh ++ own).getD i [])).sum =
      ((List.range sh.length).map fun i => U.getD i 0 * E (sh.getD i [])).sum +
        ((List.range own.length).map fun j => U.getD (sh.length + j) 0 * E (own.getD j [])).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    rw [List.getD_append _ _ _ _ (List.mem_range.1 hi)]
  · refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-! ## The high `eq` factors by tables -/

/-- `eq(t_[A, S), ·)` for every `A ≤ S` that a key needs (`need[A]`; the others are left empty). -/
def hiTabs (t : ℕ → F) (S : ℕ) (need : Array Bool) : Array (Array F) :=
  (Array.range (S + 1)).map fun A => if need.getD A false then loTab (S - A) (fun l => t (A + l)) else #[]

/-- **`eq(t_[A, n), x)`**: a lookup in `hiTabs`' row `A` times one in the table of `t_[S, n)` (one
product), `gNL` when `A > S` or the row was not built. -/
def hfac (tabs : Array (Array F)) (need : Array Bool) (hi : Array F) (S n : ℕ) (t : ℕ → F) (A x : ℕ) :
    F :=
  if A ≤ S ∧ need.getD A false = true then
    (tabs.getD A #[]).getD (x % 2 ^ (S - A)) 0 * hi.getD (x / 2 ^ (S - A)) 0
  else gNL (n - A) (fun l => t (A + l)) x

theorem hfac_eq (t : ℕ → F) {S n : ℕ} (hS : S ≤ n) (need : Array Bool) (A x : ℕ) :
    hfac (hiTabs t S need) need (loTab (n - S) fun l => t (S + l)) S n t A x =
      gN (n - A) (fun l => t (A + l)) x := by
  unfold hfac
  split_ifs with h
  · have ht : (hiTabs t S need).getD A #[] = loTab (S - A) fun l => t (A + l) := by
      have h2 := h.2
      simp only [hiTabs, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
        show A < S + 1 by omega, if_true, Option.map_some, Option.getD_some] at h2 ⊢
      rw [if_pos h2]
    rw [ht, ← splitE_eq (m := n - A) (s := S - A) (by omega)]
    simp only [splitE, splitAt]
    have e1 : n - A - (S - A) = n - S := by omega
    have e2 : (fun l => t (A + (S - A + l))) = fun l => t (S + l) := funext fun l => by
      congr 1; omega
    rw [e1, e2]
  · rw [gNL_eq]

/-! ## Prepared pieces and their values -/

/-- A key's prepared values for matrix `s` (once per evaluation, shared by the two slots). -/
structure KP where
  loc : F
  one : F
  u : Array F

/-- A key's preparation from its row and cell tables. -/
def kprepT (s : Mat) (eτ eσ : ℕ → F) (K : Key) : KP :=
  let tt := ttR (RingHom.id F) s K.rows eτ
  ⟨locSum eσ tt, oneSum tt, denseIT (inpList tt)⟩

/-- **A key's preparation**: its local part, `one` part and dense input coefficients. -/
def kprep (s : Mat) (t u : ℕ → F) (K : Key) : KP :=
  kprepT s (getD0 (loTab K.A t)) (getD0 (loTab K.B u)) K

/-- A prepared piece: grouped sparse rows, or an instance with grouped own forms. -/
inductive PPc where
  | sp (g : GRows)
  | ins (k xh ch : ℕ) (own : List GForm)

/-- A row with some entry (the alignment's padding rows have none). -/
def nonEmpty (p : ℕ × Row) : Bool := !(p.2.a.isEmpty && p.2.b.isEmpty && p.2.c.isEmpty)

def prepPiece : Piece → PPc
  | .sp rs => .sp (grows 2048 4096 (rs.filter nonEmpty))
  | .ins k xh ch own => .ins k xh ch (own.map (grp 4096))

/-- `Σ_j U[j0 + j] · E(g_j)`. -/
def ownSum (U : Array F) (slo shi : Array F) : ℕ → List GForm → F
  | _, [] => 0
  | j, g :: gs => U.getD j 0 * glVal slo shi g + ownSum U slo shi (j + 1) gs

/-- **The tables of an evaluation point** (computed once, shared by the matrices and slots): `eq(τ,
·)` over `n` coordinates and `eq(σ, ·)` over 23, split at `2^11` and `2^12`, the per-key low tables,
and `E(one)`. -/
structure Tb where
  tlo : Array F
  thi : Array F
  slo : Array F
  shi : Array F
  nt : Array Bool
  ns : Array Bool
  ttab : Array (Array F)
  stab : Array (Array F)
  e1 : F

/-- The tables (`nt`, `ns`: the row and cell bits some key has). -/
def tbOf (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns : Array Bool) : Tb :=
  let slo := loTab 12 u; let shi := loTab 11 fun l => u (12 + l)
  ⟨loTab 11 t, loTab (n - 11) fun l => t (11 + l), slo, shi, nt, ns, hiTabs t 11 nt, hiTabs u 12 ns,
    glVal slo shi (grp 4096 one)⟩

/-- The bits `< m` that some key has as `A` (resp. `B`). -/
def needA (keys : Array Key) (m : ℕ) : Array Bool := (Array.range m).map fun A => keys.any (·.A == A)
def needB (keys : Array Key) (m : ℕ) : Array Bool := (Array.range m).map fun B => keys.any (·.B == B)

/-- **The evaluation context** of a slot and a matrix (`n`: the row coordinates). -/
structure ECtx where
  n : ℕ
  tb : Tb
  t : ℕ → F
  u : ℕ → F
  keys : Array Key
  kp : Array KP
  dkp : KP
  /-- Each key's shared value in the slot. -/
  sv : Array F
  /-- Each key's number of shared inputs in the slot. -/
  nsh : Array ℕ

/-- **A prepared piece's value** for matrix `s` (the specification of `ppv3`). -/
def ppv (s : Mat) (c : ECtx) : PPc → F
  | .sp g => growsVal s c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t (c.keys.getD k dkey).A xh *
      (hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u (c.keys.getD k dkey).B ch * (c.kp.getD k c.dkp).loc +
        (c.kp.getD k c.dkp).one * c.tb.e1 + c.sv.getD k 0 +
        ownSum (c.kp.getD k c.dkp).u c.tb.slo c.tb.shi (c.nsh.getD k 0) own)

/-- **A slot's context** (`gsh`: its shared forms, grouped). -/
def ectx (s : Mat) (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP)
    (gsh : Array (List GForm)) : ECtx :=
  let dkp := kprep s t u dkey
  ⟨n, tb, t, u, keys, kp, dkp,
    (Array.range gsh.size).map (fun k => ownSum (kp.getD k dkp).u tb.slo tb.shi 0 (gsh.getD k [])),
    gsh.map List.length⟩

/-- A slot's value: the sum of its pieces'. -/
def slotV (s : Mat) (c : ECtx) (pps : List PPc) : F := sumL (ppv s c) pps

/-! ## Correctness of the pieces' values -/

/-- **Empty rows add nothing.** -/
theorem rowsValI_filter (s : Mat) (gt gs : ℕ → F) (rs : List (ℕ × Row)) :
    rowsValI (RingHom.id F) s gt gs (rs.filter nonEmpty) = rowsValI (RingHom.id F) s gt gs rs := by
  simp only [rowsValI, sumL_eq]
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rw [List.filter_cons]
    split_ifs with h
    · simp [ih]
    · have h' : p.2.a.isEmpty = true ∧ p.2.b.isEmpty = true ∧ p.2.c.isEmpty = true := by
        simpa [nonEmpty, and_assoc] using h
      have hm : s.r p.2 = [] := by
        cases s <;> simp only [Mat.r] <;> simp only [List.isEmpty_iff] at h' <;> simp [h']
      rw [List.map_cons, List.sum_cons, ← ih, hm]
      simp [linEI, sumL_eq]

theorem getD_map' {α β : Type*} (a : Array α) (f : α → β) (k : ℕ) (d : α) :
    (a.map f).getD k (f d) = f (a.getD k d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]; cases a[k]? <;> rfl

theorem ownSum_eq (U slo shi : Array F) (E : Lin → F) (hE : ∀ l, glVal slo shi (grp 4096 l) = E l) :
    ∀ (own : List Lin) (j0 : ℕ), ownSum U slo shi j0 (own.map (grp 4096)) =
      ((List.range own.length).map fun j => U.getD (j0 + j) 0 * E (own.getD j [])).sum
  | [], _ => rfl
  | a :: own, j0 => by
    rw [List.map_cons, ownSum, ownSum_eq U slo shi E hE own (j0 + 1), List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, hE]
    simp only [Nat.add_zero, List.getD_cons_zero, Function.comp_def, List.getD_cons_succ,
      Nat.add_assoc, Nat.add_comm 1]

theorem linE_glVal (u : ℕ → F) (l : Lin) :
    glVal (loTab 12 u) (loTab 11 fun l => u (12 + l)) (grp 4096 l) = linE (RingHom.id F) 23 u l := by
  rw [glVal_grp, ← linEI_eq]; congr 1; exact splitE_eq (m := 23) (s := 12) (by norm_num) u

theorem key_ok {n : ℕ} {keys : Array Key} (hk : keys.all (Key.ok n) = true) (k : ℕ) :
    (keys.getD k dkey).ok n = true := by
  rw [Array.getD_eq_getD_getElem?]
  rcases h : keys[k]? with _ | K
  · simp [Key.ok, dkey]
  · obtain ⟨hk', hK⟩ := Array.getElem?_eq_some_iff.1 h
    exact hK ▸ (Array.all_eq_true.1 hk) k hk'

theorem locOk_mem {B : ℕ} {l : LinT} (h : locOk B l = true) {k : ℕ} {c : F}
    (hm : (Wire.loc k, c) ∈ l) : k < 2 ^ B := by
  have := List.all_eq_true.1 h _ hm
  simpa using this

theorem Key.ok_spec {n : ℕ} {K : Key} (h : K.ok n = true) :
    K.A ≤ n ∧ K.B ≤ 23 ∧ K.rows.length ≤ 2 ^ K.A ∧
      ∀ s : Mat, ∀ r ∈ K.rows, ∀ k c, (Wire.loc k, c) ∈ s.t r → k < 2 ^ K.B := by
  simp only [Key.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun s r hr k c hm => ?_⟩
  obtain ⟨⟨ha, hb⟩, hc⟩ := h4 r hr
  cases s
  · exact locOk_mem ha hm
  · exact locOk_mem hb hm
  · exact locOk_mem hc hm

/-- **A piece's value is its rows' sparse value** (`tplR_mle` for an instance). -/
theorem ppv_eq (s : Mat) {n : ℕ} (hn : 11 ≤ n) (t u : ℕ → F) (one : Lin) (nt ns : Array Bool)
    (keys : Array Key) (sh : Array (List Lin)) (hk : keys.all (Key.ok n) = true) (p : Piece) :
    ppv s (ectx s n (tbOf n t u one nt ns) t u keys (keys.map (kprep s t u)) (sh.map (·.map (grp 4096))))
        (prepPiece p) = rowsVal (RingHom.id F) s n 23 t u (p.rows keys sh one) := by
  have hE : ∀ l, glVal (loTab 12 u) (loTab 11 fun l => u (12 + l)) (grp 4096 l) =
      linE (RingHom.id F) 23 u l := linE_glVal u
  cases p with
  | sp rs =>
    simp only [prepPiece, ppv, ectx, tbOf, Piece.rows]
    have h1 : splitAt (loTab 11 t) (loTab (n - 11) fun l => t (11 + l)) 2048 = gN n t :=
      splitE_eq (m := n) (s := 11) hn t
    have h2 : splitAt (loTab 12 u) (loTab 11 fun l => u (12 + l)) 4096 = gN 23 u :=
      splitE_eq (m := 23) (s := 12) (by norm_num) u
    rw [growsVal_grows, h1, h2, rowsValI_filter, rowsValI_eq]
  | ins k xh ch own =>
    obtain ⟨hA, hB, hT, hL⟩ := Key.ok_spec (key_ok hk k)
    set K := keys.getD k dkey with hK
    simp only [prepPiece, ppv, ectx, tbOf, Piece.rows]
    rw [← hK, tplR_mle (RingHom.id F) s t u K.rows one _ xh ch hA hB hT (hL s)
      (getD0 (loTab K.A t)) (getD0 (loTab K.B u))
      (fun j hj => loTab_getD _ _ (lt_of_lt_of_le hj hT)) (fun j hj => loTab_getD _ _ hj)]
    have hP : (keys.map (kprep s t u)).getD k (kprep s t u dkey) = kprep s t u K := getD_map' ..
    rw [hP, hfac_eq t (S := 11) (n := n) hn, hfac_eq u (S := 12) (n := 23) (by norm_num)]
    have hsh : (sh.map (·.map (grp 4096))).getD k [] = (sh.getD k []).map (grp 4096) :=
      getD_map' sh (·.map (grp 4096)) k []
    have hn' : ((sh.map (·.map (grp 4096))).map List.length).getD k 0 = (sh.getD k []).length := by
      rw [show (0 : ℕ) = List.length ([] : List GForm) from rfl, getD_map', hsh, List.length_map]
    have hsv : ((Array.range (sh.map (·.map (grp 4096))).size).map fun k' =>
        ownSum ((keys.map (kprep s t u)).getD k' (kprep s t u dkey)).u (loTab 12 u)
          (loTab 11 fun l => u (12 + l)) 0 ((sh.map (·.map (grp 4096))).getD k' [])).getD k 0 =
        ((List.range (sh.getD k []).length).map fun i =>
          (kprep s t u K).u.getD i 0 * linE (RingHom.id F) 23 u ((sh.getD k []).getD i [])).sum := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      split_ifs with hks
      · simp only [Option.map_some, Option.getD_some]
        rw [hP, hsh, ownSum_eq _ _ _ _ hE]; simp
      · have : sh.getD k [] = [] := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hks)]; rfl
        simp [this]
    rw [hn', hsv, ownSum_eq _ _ _ _ hE, hE]
    unfold instClosed
    simp only [kprep, kprepT]
    rw [denseIT_sum _ (fun i => linE (RingHom.id F) 23 u ((sh.getD k [] ++ own).getD i []))
      ((sh.getD k []).length + own.length) (fun i hi => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]; rfl),
      sum_split _ _ rfl]
    ring

/-- **A slot's value is its pieces' rows' sparse value.** -/
theorem slotV_eq (s : Mat) {n : ℕ} (hn : 11 ≤ n) (t u : ℕ → F) (one : Lin) (nt ns : Array Bool)
    (keys : Array Key) (sh : Array (List Lin)) (hk : keys.all (Key.ok n) = true) (pcs : List Piece) :
    slotV s (ectx s n (tbOf n t u one nt ns) t u keys (keys.map (kprep s t u)) (sh.map (·.map (grp 4096))))
        (pcs.map prepPiece) = rowsVal (RingHom.id F) s n 23 t u (pcs.flatMap (Piece.rows keys sh one)) := by
  rw [slotV, sumL_eq, rowsVal_flatMap, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun p _ => ppv_eq s hn t u one nt ns keys sh hk p)

/-! ## The three matrices in one pass

`ppv3` computes a piece's `A`, `B` and `C` values together: the high `eq` factors, the own and
shared inputs' `E` values and the sparse rows' row factors are computed once for the three. -/

/-- A triple of values. -/
abbrev F3 := F × F × F

@[inline] def add3 (x y : F3) : F3 := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

/-- `Σ_{x ∈ l} f x` over triples. -/
def sum3 {α : Type*} (f : α → F3) (l : List α) : F3 := l.foldl (fun a x => add3 a (f x)) (0, 0, 0)

theorem sum3_eq {α : Type*} (f : α → F3) (l : List α) :
    sum3 f l = (sumL (fun x => (f x).1) l, sumL (fun x => (f x).2.1) l, sumL (fun x => (f x).2.2) l) := by
  suffices ∀ a : F3, l.foldl (fun a x => add3 a (f x)) a =
      (a.1 + sumL (fun x => (f x).1) l, a.2.1 + sumL (fun x => (f x).2.1) l,
        a.2.2 + sumL (fun x => (f x).2.2) l) by
    simpa [sum3] using this (0, 0, 0)
  induction l with
  | nil => intro a; simp [sumL]
  | cons x l ih => intro a; rw [List.foldl_cons, ih]; simp only [add3, sumL_eq, List.map_cons,
      List.sum_cons]; simp only [add_assoc]

/-- The three matrices' values of grouped rows. -/
def growsVal3 (tlo thi slo shi : Array F) (G : GRows) : F3 :=
  sum3 (fun h =>
    let x := sum3 (fun r => let w := tlo.getD r.lo 0
      (rowMul slo shi w r.a, rowMul slo shi w r.b, rowMul slo shi w r.c)) h.2
    let y := thi.getD h.1 0
    (y * x.1, y * x.2.1, y * x.2.2)) G

theorem growsVal3_eq (tlo thi slo shi : Array F) (G : GRows) :
    growsVal3 tlo thi slo shi G = (growsVal .a tlo thi slo shi G, growsVal .b tlo thi slo shi G,
      growsVal .c tlo thi slo shi G) := by
  simp only [growsVal3, sum3_eq, growsVal, rInner, GRow.m]

/-- The own inputs of the three matrices: `E(g_j)` once. -/
def ownSum3 (Ua Ub Uc : Array F) (slo shi : Array F) : ℕ → List GForm → F3
  | _, [] => (0, 0, 0)
  | j, g :: gs =>
    let e := glVal slo shi g
    add3 (Ua.getD j 0 * e, Ub.getD j 0 * e, Uc.getD j 0 * e) (ownSum3 Ua Ub Uc slo shi (j + 1) gs)

theorem ownSum3_eq (Ua Ub Uc slo shi : Array F) : ∀ (j : ℕ) (g : List GForm),
    ownSum3 Ua Ub Uc slo shi j g = (ownSum Ua slo shi j g, ownSum Ub slo shi j g, ownSum Uc slo shi j g)
  | _, [] => rfl
  | j, g :: gs => by rw [ownSum3, ownSum3_eq Ua Ub Uc slo shi (j + 1) gs]; rfl

/-- The three preparations of a key. -/
abbrev KP3 := KP × KP × KP

/-- The three preparations, the key's two tables built once. -/
def kprep3 (t u : ℕ → F) (K : Key) : KP3 :=
  let eτ := getD0 (loTab K.A t); let eσ := getD0 (loTab K.B u)
  (kprepT .a eτ eσ K, kprepT .b eτ eσ K, kprepT .c eτ eσ K)

/-- **A slot's context for the three matrices.** -/
structure ECtx3 where
  n : ℕ
  tb : Tb
  t : ℕ → F
  u : ℕ → F
  keys : Array Key
  kp : Array KP3
  dkp : KP3
  sv : Array F3
  nsh : Array ℕ

def ectx3 (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP3)
    (gsh : Array (List GForm)) : ECtx3 :=
  let dkp := kprep3 t u dkey
  ⟨n, tb, t, u, keys, kp, dkp,
    (Array.range gsh.size).map (fun k => let P := kp.getD k dkp
      ownSum3 P.1.u P.2.1.u P.2.2.u tb.slo tb.shi 0 (gsh.getD k [])),
    gsh.map List.length⟩

/-- **A prepared piece's three values.** -/
def ppv3 (c : ECtx3) : PPc → F3
  | .sp g => growsVal3 c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    let K := c.keys.getD k dkey; let P := c.kp.getD k c.dkp
    let h1 := hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t K.A xh
    let h2 := hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u K.B ch
    let sv := c.sv.getD k (0, 0, 0)
    let o := ownSum3 P.1.u P.2.1.u P.2.2.u c.tb.slo c.tb.shi (c.nsh.getD k 0) own
    (h1 * (h2 * P.1.loc + P.1.one * c.tb.e1 + sv.1 + o.1),
     h1 * (h2 * P.2.1.loc + P.2.1.one * c.tb.e1 + sv.2.1 + o.2.1),
     h1 * (h2 * P.2.2.loc + P.2.2.one * c.tb.e1 + sv.2.2 + o.2.2))

def slotV3 (c : ECtx3) (pps : List PPc) : F3 := sum3 (ppv3 c) pps

theorem kp3_getD (t u : ℕ → F) (keys : Array Key) (k : ℕ) :
    (keys.map (kprep3 t u)).getD k (kprep3 t u dkey) =
      ((keys.map (kprep .a t u)).getD k (kprep .a t u dkey),
       (keys.map (kprep .b t u)).getD k (kprep .b t u dkey),
       (keys.map (kprep .c t u)).getD k (kprep .c t u dkey)) := by
  rw [getD_map' keys (kprep3 t u), getD_map', getD_map', getD_map']; rfl

theorem getD_range3 (f g h : ℕ → F) (n k : ℕ) :
    ((Array.range n).map fun k => (f k, g k, h k)).getD k (0, 0, 0) =
      (((Array.range n).map f).getD k 0, ((Array.range n).map g).getD k 0,
        ((Array.range n).map h).getD k 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

/-- **The one-pass value is the three values.** -/
theorem slotV3_eq (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (g : Array (List GForm))
    (pps : List PPc) :
    slotV3 (ectx3 n tb t u keys (keys.map (kprep3 t u)) g) pps =
      (slotV .a (ectx .a n tb t u keys (keys.map (kprep .a t u)) g) pps,
       slotV .b (ectx .b n tb t u keys (keys.map (kprep .b t u)) g) pps,
       slotV .c (ectx .c n tb t u keys (keys.map (kprep .c t u)) g) pps) := by
  simp only [slotV3, slotV, sum3_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;>
    refine congrArg (sumL · pps) (funext fun p => ?_) <;>
    cases p <;> simp only [ppv3, ppv, ectx3, ectx, growsVal3_eq, kp3_getD, ownSum3_eq, getD_range3]

/-! ## The node -/

/-- Slot `σ`'s selector forms. -/
def slotP (σ : ℕ) : Params := muxP Layout.oneCell (Layout.selCells σ)

/-- Slot `σ`'s layout (the two-pass compile's first pass). -/
def slotLay (fin : Finals) (σ : ℕ) : TLay := layOf (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- **Slot `σ`'s compiled program with the templates** (`compileT (gen fin .mux)`). -/
def slotCST (fin : Finals) (σ : ℕ) : CS :=
  compileT (slotLay fin σ) (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- M's `one` form. -/
abbrev oneL : Lin := Lin.cell Layout.oneCell

/-- **The node's plan** (computed once per node): both slots' layouts and compiled programs, the
keys, each slot's shared forms and pieces — whose rows are the slot's indexed rows (`ok`) — and
their prepared forms. -/
structure Plan where
  lay : ℕ → TLay
  cs : ℕ → CS
  keys : Array Key
  sh0 : Array (List Lin)
  sh1 : Array (List Lin)
  pc0 : List Piece
  pc1 : List Piece
  ok : keys.all (Key.ok 21) = true ∧
    pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows (lay 0) oneL 0 (cs 0) ∧
    pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows (lay 1) oneL Layout.slotM (cs 1)
  g0 : Array (List GForm)
  g1 : Array (List GForm)
  p0 : List PPc
  p1 : List PPc
  hg0 : g0 = sh0.map (·.map (grp 4096))
  hg1 : g1 = sh1.map (·.map (grp 4096))
  hp0 : p0 = pc0.map prepPiece
  hp1 : p1 = pc1.map prepPiece

/-- A plan from its parts. -/
def mkPlanOf (l0 l1 : TLay) (c0 c1 : CS) (keys : Array Key) (sh0 sh1 : Array (List Lin))
    (pc0 pc1 : List Piece) (ok : keys.all (Key.ok 21) = true ∧
      pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows l0 oneL 0 c0 ∧
      pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows l1 oneL Layout.slotM c1) : Plan where
  lay σ := if σ = 0 then l0 else l1
  cs σ := if σ = 0 then c0 else c1
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := by simpa using ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  p0 := pc0.map prepPiece
  p1 := pc1.map prepPiece
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl

/-- **The plan of two laid-out, compiled slots** from the search's data: kept if the keys are well
formed and the pieces' rows are the slots' rows (checked here, once), else one sparse piece per
slot. -/
def mkPlan (l0 l1 : TLay) (c0 c1 : CS)
    (d : Array Key × Array (List Lin) × Array (List Lin) × List Piece × List Piece) : Plan :=
  if h : (d.1.all (Key.ok 21) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL))
      (slotIRows l0 oneL 0 c0) &&
      eqL (d.2.2.2.2.flatMap (Piece.rows d.1 d.2.2.1 oneL)) (slotIRows l1 oneL Layout.slotM c1)) = true
  then
    mkPlanOf l0 l1 c0 c1 d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 (by
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1.1, eqL_eq h.1.2, eqL_eq h.2⟩)
  else
    mkPlanOf l0 l1 c0 c1 #[] #[] #[] [.sp (slotIRows l0 oneL 0 c0)]
      [.sp (slotIRows l1 oneL Layout.slotM c1)] (by simp [Piece.rows])

/-- **The node's plan** (once per node). -/
def planOf (fin : Finals) : Plan :=
  let ops := (gen fin .mux).ops
  let l0 := slotLay fin 0; let l1 := slotLay fin 1
  let c0 := compileT l0 (slotP 0) (Layout.slotBase 0) ops
  let c1 := compileT l1 (slotP 1) (Layout.slotBase 1) ops
  mkPlan l0 l1 c0 c1 (groupPPs
    (slotPPs (tplExt l0.ctx) (slotP 0) (Layout.slotBase 0) ops l0 oneL 0 c0)
    (slotPPs (tplExt l1.ctx) (slotP 1) (Layout.slotBase 1) ops l1 oneL Layout.slotM c1))

/-- **The node's indexed M rows**: slot `σ`'s at offset `σ · 2^20`. -/
def nodeIRows (pl : Plan) : List (ℕ × Row) :=
  slotIRows (pl.lay 0) oneL 0 (pl.cs 0) ++ slotIRows (pl.lay 1) oneL Layout.slotM (pl.cs 1)

/-- The node's value of matrix `s`, given the tables (the specification of `nodeV3`). -/
def nodeV (pl : Plan) (s : Mat) (t u : ℕ → F) (tb : Tb) : F :=
  let kp := pl.keys.map (kprep s t u)
  slotV s (ectx s 21 tb t u pl.keys kp pl.g0) pl.p0 + slotV s (ectx s 21 tb t u pl.keys kp pl.g1) pl.p1

theorem nodeV_eq (pl : Plan) (s : Mat) (t u : ℕ → F) (nt ns : Array Bool) :
    nodeV pl s t u (tbOf 21 t u oneL nt ns) = rowsVal (RingHom.id F) s 21 23 t u (nodeIRows pl) := by
  simp only [nodeV, nodeIRows]
  rw [pl.hg0, pl.hg1, pl.hp0, pl.hp1, slotV_eq _ (by norm_num) _ _ _ _ _ _ _ pl.ok.1,
    slotV_eq _ (by norm_num) _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.1, pl.ok.2.2, rowsVal_append]

/-- The node's three matrices in one pass per slot. -/
def nodeV3 (pl : Plan) (t u : ℕ → F) (tb : Tb) : F3 :=
  let kp := pl.keys.map (kprep3 t u)
  add3 (slotV3 (ectx3 21 tb t u pl.keys kp pl.g0) pl.p0) (slotV3 (ectx3 21 tb t u pl.keys kp pl.g1) pl.p1)

theorem nodeV3_eq (pl : Plan) (t u : ℕ → F) (tb : Tb) :
    nodeV3 pl t u tb = (nodeV pl .a t u tb, nodeV pl .b t u tb, nodeV pl .c t u tb) := by
  simp only [nodeV3, nodeV, slotV3_eq, add3]

/-- **`evalM`** (revision 3.12; S-E5): the node's three M matrices at `(τ, σ)`, the pieces of both
slots in closed form or sparse, the three matrices in one pass; the tables are computed once. -/
def evalMT (pl : Plan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  nodeV3 pl t u (tbOf 21 t u oneL (needA pl.keys 12) (needB pl.keys 13))

/-- **`evalM`'s specification**: the MLEs of the node's M matrices (`FRVIREval.matMLE`). -/
noncomputable def evalMS (pl : Plan) (τ σ : Array F) : F × F × F :=
  (Eval.matMLE (entriesI .a (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .b (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .c (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ))

/-- **`evalM_eq`** (A.11: the instances' `tplR_mle` and the sparse pieces' `sparse_eq`). -/
theorem evalMT_eq (pl : Plan) (τ σ : Array F) : evalMT pl τ σ = evalMS pl τ σ := by
  simp only [evalMT, evalMS, nodeV3_eq, nodeV_eq, rowsVal_F, Eval.sparse_eq]

/-! ## `evalL`: L's rows (revision 3.13: at the full 23-coordinate point) -/

/-- **L's plan**: L's rows (indexed by position, 15 row coordinates) in aligned blocks of `2^6`. -/
structure LPlan where
  rows : List Row
  keys : Array Key
  sh : Array (List Lin)
  pc : List Piece
  ok : keys.all (Key.ok 15) = true ∧
    pc.flatMap (Piece.rows keys sh oneL) = rows.zipIdx.map fun p => (p.2, p.1)
  g : Array (List GForm)
  p : List PPc
  hg : g = sh.map (·.map (grp 4096))
  hp : p = pc.map prepPiece

def mkLPlanOf (rows : List Row) (keys : Array Key) (sh : Array (List Lin)) (pc : List Piece)
    (ok : keys.all (Key.ok 15) = true ∧
      pc.flatMap (Piece.rows keys sh oneL) = rows.zipIdx.map fun p => (p.2, p.1)) : LPlan :=
  ⟨rows, keys, sh, pc, ok, sh.map (·.map (grp 4096)), pc.map prepPiece, rfl, rfl⟩

/-- **L's plan** from its rows (checked as the node's). -/
def planL (rows : List Row) : LPlan :=
  let d := groupPPs (listPPs 6 rows) #[]
  let tgt := rows.zipIdx.map fun p => (p.2, p.1)
  if h : (d.1.all (Key.ok 15) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL)) tgt) = true then
    mkLPlanOf rows d.1 d.2.1 d.2.2.2.1 (by
      simp only [Bool.and_eq_true] at h; exact ⟨h.1, eqL_eq h.2⟩)
  else mkLPlanOf rows #[] #[] [.sp tgt] (by simp [Piece.rows, tgt])

/-- **`evalL`, templated**: L's three matrices at `(τ, σ)` (15 and 23 coordinates). -/
def evalLT (pl : LPlan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  slotV3 (ectx3 15 (tbOf 15 t u oneL (needA pl.keys 12) (needB pl.keys 13)) t u pl.keys (pl.keys.map (kprep3 t u)) pl.g) pl.p

theorem entriesOf_eq (sel : Mat) (rows : List Row) :
    Eval.entriesOf sel.r rows = entriesI sel (rows.zipIdx.map fun p => (p.2, p.1)) := by
  simp only [Eval.entriesOf, entriesI, List.flatMap_map]

/-- **`evalL_eq`**: the templated `evalL` is the MLE of L's rows (`FRVIREval.evalRowsSpec`). -/
theorem evalLT_eq (pl : LPlan) (τ σ : Array F) : evalLT pl τ σ = Eval.evalRowsSpec 15 23 pl.rows τ σ := by
  simp only [evalLT, slotV3_eq, Eval.evalRowsSpec]
  rw [pl.hg, pl.hp]
  simp only [slotV_eq _ (by norm_num : 11 ≤ 15) _ _ _ _ _ _ _ pl.ok.1, pl.ok.2, rowsVal_F,
    Eval.sparse_eq]
  simp only [← entriesOf_eq]
  rfl

end TEval
end FR
