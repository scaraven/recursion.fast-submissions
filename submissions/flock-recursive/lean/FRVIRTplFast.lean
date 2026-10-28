-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stage S-E4, track
-- L-circ). The node section (`Plan`, `planOf`, `nodeIRows`, `evalMT`, `evalMKT`) moved here from
-- `FRVIRTplEval` (S-E3); `evalMT` is now the flat evaluation.
import FRVIRTplEval

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

/-! ## Template instances -/

/-- A key's prepared values with its input terms compacted. -/
def cprep (p : Prep F) : Prep F := { p with it := compactIT p.it }

/-- The keys' prepared values for matrix `s` from their cached templates (once per evaluation,
shared by the two slots). -/
def pcache (s : Mat) (τ σ : ℕ → F) (tp : List (TKey × Tpl)) : List (TKey × Prep F) :=
  tp.map fun p => (p.1, cprep (prepT (RingHom.id F) s τ σ p.2))

/-- A key's prepared values from the cache. -/
def pfind (s : Mat) (τ σ : ℕ → F) (c : List (TKey × Prep F)) (k : TKey) : Prep F :=
  match c.find? (·.1 == k) with
  | some p => p.2
  | none => cprep (prepOf (RingHom.id F) s τ σ k)

theorem pfind_eq (s : Mat) (τ σ : ℕ → F) (tp : List (TKey × Tpl)) (htp : ∀ p ∈ tp, p.2 = tplOf p.1)
    (k : TKey) : pfind s τ σ (pcache s τ σ tp) k = cprep (prepOf (RingHom.id F) s τ σ k) := by
  unfold pfind
  split
  · rename_i p hp
    have h1 := List.find?_some hp
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hp)
    simp only [beq_iff_eq] at h1
    simp only [prepOf, htp k' hk', h1]
  · rfl

/-- The cached templates of a list of keys. -/
def tplCache (ks : List TKey) : List (TKey × Tpl) := ks.map fun k => (k, tplOf k)

theorem tplCache_ok (ks : List TKey) : ∀ p ∈ tplCache ks, p.2 = tplOf p.1 := by
  intro p hp; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp; rfl

/-- **An instance, prepared once per node**: its key, the row and cell bits of its template, the
alignment test of `instVal`, the high parts of its bases, its grouped input forms, and its grouped
rows when it is not aligned. -/
structure GInst where
  key : TKey
  a : ℕ
  b : ℕ
  al : Bool
  xh : ℕ
  ch : ℕ
  ins : Array GForm
  rows : GRows

/-- The prepared instance `t` of a slot at row offset `off`. -/
def ginstOf (L : TLay) (one : Lin) (off : ℕ) (t : TKey × ℕ × List Lin) : GInst :=
  let T := tplOf t.1
  let X := off + L.rb t.1 + t.2.1 * 2 ^ T.rbits
  let cb := L.cb t.1 t.2.1
  let al := decide (T.rbits ≤ 21 ∧ T.cbits ≤ 23 ∧ X % 2 ^ T.rbits = 0 ∧ cb % 2 ^ T.cbits = 0)
  ⟨t.1, T.rbits, T.cbits, al, X / 2 ^ T.rbits, cb / 2 ^ T.cbits, (t.2.2.map (grp 4096)).toArray,
    if al then [] else grows 2048 4096 (tinIRows L one off t)⟩

/-- The instance's two high `eq` factors (shared by the three matrices). -/
def ghv (τ σ : ℕ → F) (g : GInst) : F × F :=
  (gNL (21 - g.a) (fun l => τ (g.a + l)) g.xh, gNL (23 - g.b) (fun l => σ (g.b + l)) g.ch)

/-- **An instance's value** for matrix `s` (`instVal`'s closed form, or its grouped rows). -/
def ginstVal (s : Mat) (tlo thi slo shi : Array F) (p : Prep F) (e1 : F) (hv : F × F) (g : GInst) :
    F :=
  if g.al then
    hv.1 * (hv.2 * p.loc + p.one * e1 + sumL (fun q => q.2 * glVal slo shi (g.ins.getD q.1 [])) p.it)
  else growsVal s tlo thi slo shi g.rows

theorem ginstVal_eq (s : Mat) (tlo thi slo shi : Array F) (τ σ : ℕ → F) (L : TLay) (one : Lin)
    (off : ℕ) (t : TKey × ℕ × List Lin) :
    ginstVal s tlo thi slo shi (cprep (prepOf (RingHom.id F) s τ σ t.1))
        (glVal slo shi (grp 4096 one)) (ghv τ σ (ginstOf L one off t)) (ginstOf L one off t) =
      instVal (RingHom.id F) s 21 23 τ σ (splitAt tlo thi 2048) (splitAt slo shi 4096) L one off
        (prepOf (RingHom.id F) s τ σ t.1) t := by
  have hins : ∀ i, ((t.2.2.map (grp 4096)).toArray).getD i [] = grp 4096 (t.2.2.getD i []) := by
    intro i
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases t.2.2[i]? <;> rfl
  unfold ginstVal instVal ginstOf ghv
  simp only [prepOf, prepT, cprep]
  split_ifs with h1 h2 h2
  · simp only [ite_eq_left h2, glVal_grp, hins, sumL_eq]
    rw [compactIT_sum _ (fun i => linEI (RingHom.id F) (splitAt slo shi 4096) (t.2.2.getD i []))]
  · exact absurd (by simpa using h1) h2
  · exact absurd (by simpa using h2) h1
  · simp only [h2, ↓reduceIte]; rw [growsVal_grows]

/-! ## A slot -/

/-- **A slot, prepared once per node**: the grouped skeleton rows, the prepared instances, the
grouped `one` form. -/
structure FSlot where
  sk : GRows
  insts : List GInst
  one : GForm

/-- The prepared slot (row offset `off`). -/
def fslotOf (L : TLay) (one : Lin) (off : ℕ) (cs : CS) : FSlot :=
  ⟨grows 2048 4096 (cs.rowList.zipIdx.map fun p => (off + p.2, p.1)), cs.tins.map (ginstOf L one off),
    grp 4096 one⟩

/-- **The flat value of a slot** for matrix `s` (`hvs`: the instances' high factors). -/
def fslotVal (s : Mat) (tlo thi slo shi : Array F) (τ σ : ℕ → F) (c : List (TKey × Prep F))
    (fs : FSlot) (hvs : List (F × F)) : F :=
  let e1 := glVal slo shi fs.one
  growsVal s tlo thi slo shi fs.sk +
    sumL (fun gh => ginstVal s tlo thi slo shi (pfind s τ σ c gh.1.key) e1 gh.2 gh.1) (fs.insts.zip hvs)

theorem map_zip_map {α β γ δ : Type*} (l : List α) (g : α → β) (h : β → γ) (f : β × γ → δ) :
    ((l.map g).zip (l.map fun x => h (g x))).map f = l.map fun x => f (g x, h (g x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- **`fslotVal_eq`**: the flat value of the prepared slot is `slotVal`'s. -/
theorem fslotVal_eq (s : Mat) (tlo thi slo shi : Array F) (τ σ : ℕ → F) (tp : List (TKey × Tpl))
    (htp : ∀ p ∈ tp, p.2 = tplOf p.1) (L : TLay) (one : Lin) (off : ℕ) (cs : CS) :
    fslotVal s tlo thi slo shi τ σ (pcache s τ σ tp) (fslotOf L one off cs)
        ((fslotOf L one off cs).insts.map (ghv τ σ)) =
      slotVal (RingHom.id F) s 21 23 τ σ (splitAt tlo thi 2048) (splitAt slo shi 4096) L one off cs := by
  unfold fslotVal slotVal fslotOf
  simp only []
  rw [growsVal_grows]
  congr 1
  simp only [sumL_eq, List.map_map, Function.comp_def]
  rw [map_zip_map]
  simp only [pfind_eq s τ σ tp htp, prepFind_eq]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  exact ginstVal_eq s tlo thi slo shi τ σ L one off t

/-! ## The node -/

/-- Slot `σ`'s selector forms. -/
def slotP (σ : ℕ) : Params := muxP Layout.oneCell (Layout.selCells σ)

/-- Slot `σ`'s layout (the two-pass compile's first pass). -/
def slotLay (fin : Finals) (σ : ℕ) : TLay := layOf (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- **Slot `σ`'s compiled program with the templates** (`compileT (gen fin .mux)`). -/
def slotCST (fin : Finals) (σ : ℕ) : CS :=
  compileT (slotLay fin σ) (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- The node's plan: both slots' layouts and compiled programs, and their prepared forms (computed
once per node). -/
structure Plan where
  lay : ℕ → TLay
  cs : ℕ → CS
  fs0 : FSlot
  fs1 : FSlot
  h0 : fs0 = fslotOf (lay 0) (Lin.cell Layout.oneCell) 0 (cs 0)
  h1 : fs1 = fslotOf (lay 1) (Lin.cell Layout.oneCell) Layout.slotM (cs 1)
  /-- The templates of the keys present (a missing key is prepared on demand). -/
  tp : List (TKey × Tpl)
  htp : ∀ p ∈ tp, p.2 = tplOf p.1

/-- The plan of two laid-out, compiled slots. -/
def mkPlan (l0 l1 : TLay) (c0 c1 : CS) : Plan where
  lay σ := if σ = 0 then l0 else l1
  cs σ := if σ = 0 then c0 else c1
  fs0 := fslotOf l0 (Lin.cell Layout.oneCell) 0 c0
  fs1 := fslotOf l1 (Lin.cell Layout.oneCell) Layout.slotM c1
  h0 := by simp
  h1 := by simp
  tp := tplCache ((keyCounts c0.tins).map (·.1))
  htp := tplCache_ok _

/-- **The node's plan** (once per node). -/
def planOf (fin : Finals) : Plan :=
  let l0 := slotLay fin 0; let l1 := slotLay fin 1
  mkPlan l0 l1 (compileT l0 (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops)
    (compileT l1 (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops)

/-- **The node's indexed M rows**: slot `σ`'s at offset `σ · 2^20`. -/
def nodeIRows (pl : Plan) : List (ℕ × Row) :=
  slotIRows (pl.lay 0) (Lin.cell Layout.oneCell) 0 (pl.cs 0) ++
    slotIRows (pl.lay 1) (Lin.cell Layout.oneCell) Layout.slotM (pl.cs 1)

/-- The node's value of matrix `s` (templated, generic: `evalMKT`), over `R`. -/
@[specialize]
def nodeVal {R : Type*} [CommRing R] (ι : F →+* R) (s : Mat) (τ σ : ℕ → R) (pl : Plan) : R :=
  let gt := splitAt (loTab 11 τ) (loTab 10 fun l => τ (11 + l)) 2048
  let gs := splitAt (loTab 12 σ) (loTab 11 fun l => σ (12 + l)) 4096
  slotVal ι s 21 23 τ σ gt gs (pl.lay 0) (Lin.cell Layout.oneCell) 0 (pl.cs 0) +
    slotVal ι s 21 23 τ σ gt gs (pl.lay 1) (Lin.cell Layout.oneCell) Layout.slotM (pl.cs 1)

theorem nodeVal_eq {R : Type*} [CommRing R] (ι : F →+* R) (s : Mat) (τ σ : ℕ → R) (pl : Plan) :
    nodeVal ι s τ σ pl = rowsVal ι s 21 23 τ σ (nodeIRows pl) := by
  have h1 : splitAt (loTab 11 τ) (loTab 10 fun l => τ (11 + l)) 2048 = gN 21 τ :=
    splitE_eq (m := 21) (s := 11) (by norm_num) τ
  have h2 : splitAt (loTab 12 σ) (loTab 11 fun l => σ (12 + l)) 4096 = gN 23 σ :=
    splitE_eq (m := 23) (s := 12) (by norm_num) σ
  simp only [nodeVal, h1, h2, slotVal_eq, nodeIRows, rowsVal_append]

/-- **The flat value of the node's matrix `s`** at `(τ, σ)`, given the shared tables and the
instances' high factors. -/
def nodeFlat (pl : Plan) (s : Mat) (t u : ℕ → F) (tlo thi slo shi : Array F) (hv0 hv1 : List (F × F)) :
    F :=
  let c := pcache s t u pl.tp
  fslotVal s tlo thi slo shi t u c pl.fs0 hv0 + fslotVal s tlo thi slo shi t u c pl.fs1 hv1

theorem nodeFlat_eq (pl : Plan) (s : Mat) (t u : ℕ → F) :
    nodeFlat pl s t u (loTab 11 t) (loTab 10 fun l => t (11 + l)) (loTab 12 u)
        (loTab 11 fun l => u (12 + l)) (pl.fs0.insts.map (ghv t u)) (pl.fs1.insts.map (ghv t u)) =
      nodeVal (RingHom.id F) s t u pl := by
  unfold nodeFlat nodeVal
  simp only []
  rw [pl.h0, pl.h1, fslotVal_eq _ _ _ _ _ _ _ _ pl.htp, fslotVal_eq _ _ _ _ _ _ _ _ pl.htp]

/-- **`evalM`** (flat, A.11 / revision 3.12): the node's three M matrices at `(τ, σ)`; the tables,
the keys' local parts and the instances' high factors are computed once and shared. -/
def evalMT (pl : Plan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  let tlo := loTab 11 t; let thi := loTab 10 fun l => t (11 + l)
  let slo := loTab 12 u; let shi := loTab 11 fun l => u (12 + l)
  let hv0 := pl.fs0.insts.map (ghv t u); let hv1 := pl.fs1.insts.map (ghv t u)
  (nodeFlat pl .a t u tlo thi slo shi hv0 hv1, nodeFlat pl .b t u tlo thi slo shi hv0 hv1,
    nodeFlat pl .c t u tlo thi slo shi hv0 hv1)

/-- **`evalM`'s specification**: the MLEs of the node's M matrices (`FRVIREval.matMLE`). -/
noncomputable def evalMS (pl : Plan) (τ σ : Array F) : F × F × F :=
  (Eval.matMLE (entriesI .a (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .b (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .c (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ))

/-- **`evalM_eq`** (A.11: the sum of the templates' `tpl_mle` and the skeleton's `sparse_eq`). -/
theorem evalMT_eq (pl : Plan) (τ σ : Array F) : evalMT pl τ σ = evalMS pl τ σ := by
  simp only [evalMT, evalMS, nodeFlat_eq, nodeVal_eq, rowsVal_F, Eval.sparse_eq]

/-- **`evalMK`, templated**: the M matrices at an F row point and a K column point. -/
def evalMKT (pl : Plan) (τ : Array F) (σ : Array K) : K × K × K :=
  let t := fun l => K.ofF (τ.getD l 0); let u := fun l => σ.getD l 0
  (nodeVal K.ofFRingHom .a t u pl, nodeVal K.ofFRingHom .b t u pl, nodeVal K.ofFRingHom .c t u pl)

/-- `evalMKT` is the sparse sum over `K` (`FRVerifierImpl.sparseEvalK`'s body). -/
theorem evalMKT_eq (pl : Plan) (τ : Array F) (σ : Array K) :
    evalMKT pl τ σ = (((entriesI .a (nodeIRows pl)).map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          Impl.eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum,
      ((entriesI .b (nodeIRows pl)).map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          Impl.eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum,
      ((entriesI .c (nodeIRows pl)).map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          Impl.eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum) := by
  simp only [evalMKT, nodeVal_eq, rowsVal_K]

end TEval
end FR
