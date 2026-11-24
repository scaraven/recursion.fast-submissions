-- New for lvm6 (WP-TWT): the fast `Φ_Q` at 43 variables (A23's accumulator check, Y1's `PhiQFE`). The entries are
-- grouped once into runs of equal low index (`o + 4x`); per evaluation the equality weights come off split tables,
-- the high part (`y`) once per distinct word, the low part once per run.
import Lvm6TyProg
import Lvm6VTwA

/-!
# The fast `Φ_Q`

`Φ_Q(pt) = Σ_e c_e·eq(pt, idx_e)` with `idx_e = o + 4·(x + 2^20·y)` (Y1's `PhiQFE`, 43 variables). Split the point
at 22 coordinates: `eq(pt, idx) = eq(pt_{<22}, lo)·eq(pt_{≥22}, hi)` with `lo = idx mod 2^22`, `hi = idx / 2^22`.

* `SEq`, `mkSEq`, `SEq.at`: `eq(ρ, i)` from the tables of the low 11 and the high coordinates (`mkSEq_at`).
* `PhiTab`: the entries as runs of equal `lo` (`mkRuns`, kept in order: `flat_mkRuns`), each item with its `hi` and
  the rank of `hi` among the distinct words (`ys`); the rank is checked when it is read, so it needs no proof.
* `phiEval tab a b`: `Σ_runs eq(a, lo)·Σ_items c·eq(b, hi)`, `eq(b, ·)` once per distinct word (`phiEval_eq`).
* **`phiFast tab pt`**, **`phiFast_eq`**: `phiFast (mkPhiTab (entsE Q lay)) pt = PhiQFE Q lay pt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Split equality tables -/

section Gen

variable {F : Type} [Field F] [Algebra K F]

/-- The split tables of a point: whether it has 11 coordinates, `2^|ρ|`, the low and the high table. -/
structure SEq (F : Type) where
  ok : Bool
  bound : ℕ
  lo : Array F
  hi : Array F

/-- The split tables of `ρ`. -/
def mkSEq (ρ : List F) : SEq F :=
  ⟨decide (11 ≤ ρ.length), 2 ^ ρ.length, eqKernelAF (ρ.take 11), eqKernelAF (ρ.drop 11)⟩

/-- `eq(ρ, i)` off the tables (`eqAtF` past them). -/
@[inline] def SEq.at (s : SEq F) (ρ : List F) (i : ℕ) : F :=
  if s.ok && decide (i < s.bound) then s.lo.getD (i % 2048) 0 * s.hi.getD (i / 2048) 0 else eqAtF ρ i

theorem mkSEq_at (ρ : List F) (i : ℕ) : (mkSEq ρ).at ρ i = eqAtF ρ i := by
  unfold SEq.at mkSEq
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h11, hi⟩ := h
    have ht : (ρ.take 11).length = 11 := by simp [h11]
    have hd : (ρ.drop 11).length = ρ.length - 11 := by simp
    have hp : 2 ^ ρ.length = 2048 * 2 ^ (ρ.length - 11) := by
      rw [show (2048 : ℕ) = 2 ^ 11 from rfl, ← pow_add]; congr 1; omega
    rw [eqKernelAF_getD, eqKernelAF_getD, ht, hd, if_pos (by rw [show (2:ℕ) ^ 11 = 2048 from rfl]; omega),
      if_pos (by rw [hp] at hi; exact Nat.div_lt_of_lt_mul hi)]
    conv_rhs => rw [← List.take_append_drop 11 ρ]
    rw [eqAtF_append, ht, show (2:ℕ) ^ 11 = 2048 from rfl, eqAtF_mod (ρ.take 11) i, ht,
      show (2:ℕ) ^ 11 = 2048 from rfl]
  · rfl

end Gen

/-! ## Sums -/

section Sums

variable {α : Type}

theorem foldl_add_eq {F : Type} [AddCommMonoid F] (g : α → F) :
    ∀ (l : List α) (acc : F), l.foldl (fun s x => s + g x) acc = acc + (l.map g).sum
  | [], acc => by simp
  | x :: l, acc => by rw [List.foldl_cons, foldl_add_eq g l, List.map_cons, List.sum_cons, add_assoc]

theorem foldr_add_eq {F : Type} [AddCommMonoid F] (g : α → F) :
    ∀ l : List α, l.foldr (fun x s => g x + s) 0 = (l.map g).sum
  | [] => rfl
  | x :: l => by rw [List.foldr_cons, foldr_add_eq g l, List.map_cons, List.sum_cons]

end Sums

/-! ## The table -/

/-- An item of a run: the coefficient, the high index, its rank among the distinct high indices. -/
structure PItem where
  c : FE2
  hi : ℕ
  k : ℕ

/-- A run of entries with the same low index. -/
structure PRun where
  lo : ℕ
  items : Array PItem

/-- **The table of `Φ_Q`**: the entries (for the short-point fallback), the distinct high indices, the runs. -/
structure PhiTab where
  es : List EntT
  ys : Array ℕ
  runs : Array PRun

/-- The table's entries as `(c, lo, hi)`. -/
def PhiTab.ents (tab : PhiTab) : List (FE2 × ℕ × ℕ) :=
  tab.runs.toList.flatMap fun r => r.items.toList.map fun it => (it.c, r.lo, it.hi)

/-- An entry's key: `(c, idx mod 2^22, idx / 2^22)`. -/
def keyOf (e : EntT) : FE2 × ℕ × ℕ := (e.c, Lvm6.Ty.EntT.idxE e % 2 ^ 22, Lvm6.Ty.EntT.idxE e / 2 ^ 22)

/-- Consecutive keys with the same `lo` as one run (the order kept). -/
def mkRuns : List (FE2 × ℕ × ℕ) → List (ℕ × List (FE2 × ℕ))
  | [] => []
  | (c, lo, hi) :: rest =>
    match mkRuns rest with
    | (lo', items) :: rs => if lo' = lo then (lo, (c, hi) :: items) :: rs else (lo, [(c, hi)]) :: (lo', items) :: rs
    | [] => [(lo, [(c, hi)])]

/-- The runs read back as keys. -/
def flatRuns (rs : List (ℕ × List (FE2 × ℕ))) : List (FE2 × ℕ × ℕ) :=
  rs.flatMap fun r => r.2.map fun ch => (ch.1, r.1, ch.2)

theorem flat_mkRuns : ∀ l : List (FE2 × ℕ × ℕ), flatRuns (mkRuns l) = l
  | [] => rfl
  | (c, lo, hi) :: rest => by
    have ih := flat_mkRuns rest
    unfold mkRuns
    split
    · rename_i lo' items rs h
      rw [h] at ih
      split
      · rename_i he
        subst he
        simp only [flatRuns, List.flatMap_cons, List.map_cons, List.cons_append] at ih ⊢
        rw [ih]
      · simp only [flatRuns, List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append] at ih ⊢
        rw [ih]
    · rename_i h
      rw [h] at ih
      simp only [flatRuns, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.append_nil] at ih ⊢
      rw [← ih]

/-- The distinct high indices in order of appearance, with their ranks. -/
def rankYs (ks : List (FE2 × ℕ × ℕ)) : Array ℕ × Std.HashMap ℕ ℕ :=
  ks.foldl (fun st k => if st.2.contains k.2.2 then st else (st.1.push k.2.2, st.2.insert k.2.2 st.1.size))
    (#[], {})

/-- **The table of a list of entries.** -/
def mkPhiTab (es : List EntT) : PhiTab :=
  let ks := es.map keyOf
  let yr := rankYs ks
  ⟨es, yr.1, ((mkRuns ks).map fun r =>
    (⟨r.1, (r.2.map fun ch => (⟨ch.1, ch.2, yr.2.getD ch.2 0⟩ : PItem)).toArray⟩ : PRun)).toArray⟩

theorem ents_mkPhiTab (es : List EntT) : (mkPhiTab es).ents = es.map keyOf := by
  rw [← flat_mkRuns (es.map keyOf)]
  simp only [mkPhiTab, PhiTab.ents, flatRuns, List.toList_toArray, List.flatMap_map, List.map_map]
  try rfl

/-! ## The evaluation -/

/-- `c·v`, with `1·v = v` read off. -/
@[inline] def cmul (c v : FE2) : FE2 := if c = 1 then v else c * v

theorem cmul_eq (c v : FE2) : cmul c v = c * v := by
  unfold cmul; split
  · rename_i h; rw [h, one_mul]
  · rfl

/-- `eq(b, hi)` of an item: the precomputed value when the rank is right. -/
@[inline] def yAt (ys : Array ℕ) (yv : Array FE2) (sb : SEq FE2) (b : List FE2) (it : PItem) : FE2 :=
  match ys[it.k]?, yv[it.k]? with
  | some y, some v => if y = it.hi then v else sb.at b it.hi
  | _, _ => sb.at b it.hi

theorem yAt_eq (ys : Array ℕ) (b : List FE2) (it : PItem) :
    yAt ys (ys.map fun y => (mkSEq b).at b y) (mkSEq b) b it = eqAtF b it.hi := by
  unfold yAt
  rw [Array.getElem?_map]
  cases h : ys[it.k]? with
  | none => simp only [Option.map_none]; exact mkSEq_at b it.hi
  | some y =>
    simp only [Option.map_some]
    split_ifs with hy
    · rw [hy, mkSEq_at]
    · exact mkSEq_at b it.hi

/-- **`Σ_runs eq(a, lo)·Σ_items c·eq(b, hi)`** off the split tables. -/
def phiEval (tab : PhiTab) (a b : List FE2) : FE2 :=
  let sa := mkSEq a
  let sb := mkSEq b
  let yv := tab.ys.map fun y => sb.at b y
  tab.runs.foldl (fun acc r =>
    acc + sa.at a r.lo * r.items.foldl (fun s it => s + cmul it.c (yAt tab.ys yv sb b it)) 0) 0

theorem phiEval_eq (tab : PhiTab) (a b : List FE2) :
    phiEval tab a b = (tab.ents.map fun x => x.1 * (eqAtF a x.2.1 * eqAtF b x.2.2)).sum := by
  unfold phiEval PhiTab.ents
  simp only [yAt_eq]
  simp only [mkSEq_at, ← Array.foldl_toList, foldl_add_eq, zero_add, cmul_eq]
  generalize tab.runs.toList = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      ← List.sum_map_mul_left]
    congr 2
    refine List.map_congr_left fun it _ => ?_
    simp only [Function.comp_apply]
    ring

/-- `eqWT` is `eqAtF` at `FE2`. -/
theorem eqWT_eq : ∀ (pt : List FE2) (w : ℕ), eqWT pt w = eqAtF pt w
  | [], _ => rfl
  | r :: rs, w => by rw [eqWT, Lvm.E2V.eqAtF, eqWT_eq rs]

/-- **The fast `Φ_Q`**: split at 22 coordinates; a shorter point by the entries. -/
def phiFast (tab : PhiTab) (pt : List FE2) : FE2 :=
  if 22 ≤ pt.length then phiEval tab (pt.take 22) (pt.drop 22)
  else tab.es.foldr (fun e acc => e.c * eqWT pt (Lvm6.Ty.EntT.idxE e) + acc) 0

theorem phiFast_ents (es : List EntT) (pt : List FE2) :
    phiFast (mkPhiTab es) pt = es.foldr (fun e acc => e.c * eqWT pt (Lvm6.Ty.EntT.idxE e) + acc) 0 := by
  unfold phiFast
  split
  · rename_i h
    rw [phiEval_eq, ents_mkPhiTab, foldr_add_eq, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    have ht : (pt.take 22).length = 22 := by simp [h]
    simp only [Function.comp_apply, keyOf, eqWT_eq]
    conv_rhs => rw [← List.take_append_drop 22 pt]
    rw [eqAtF_append, ht, eqAtF_mod (pt.take 22) (Lvm6.Ty.EntT.idxE e), ht]
  · simp only [mkPhiTab]

/-- **`Φ_Q` off its table.** -/
theorem phiFast_eq (Q : Program) (lay : Lay) (pt : List FE2) :
    phiFast (mkPhiTab (Lvm6.Ty.entsE Q lay)) pt = Lvm6.Ty.PhiQFE Q lay pt :=
  phiFast_ents _ pt

end Lvm6.V
