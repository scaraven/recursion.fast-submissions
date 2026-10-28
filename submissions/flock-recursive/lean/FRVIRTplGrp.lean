-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stages S-E4/S-E5, track
-- L-circ). Split out of `FRVIRTplFast` in S-E11 (unchanged): grouped forms, the raw template's closed
-- form, dense input coefficients, the high `eq` factors, a key's preparation.
import FRVIRTplPlan

/-!
# The flat evaluation of the node's M matrices (`evalM`): grouped forms, closed forms, key preparation

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


/-! ## Triples -/

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

/-! ## Own inputs -/

/-- `Σ_j U[j0 + j] · E(g_j)`. -/
def ownSum (U : Array F) (slo shi : Array F) : ℕ → List GForm → F
  | _, [] => 0
  | j, g :: gs => U.getD j 0 * glVal slo shi g + ownSum U slo shi (j + 1) gs

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

end TEval
end FR
