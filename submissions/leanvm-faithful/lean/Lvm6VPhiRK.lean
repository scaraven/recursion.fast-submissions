-- New for lvm6 (ST-4): the row kind `RK`, entries grouped by slot and matrix, E2 cell pairs as one line; a proved builder.
import Lvm6VPhiR3

/-!
# The row kind

A cover for any entry list given row by row (`ptOfRowsG`'s rest: rows under no class, class differences):
* `RK`: runs `(x, o, lines)` of equal slot and matrix; a line is one entry `(c, y)` or the cell pair
  `(c, 2y), (c·X, 2y + 1)` (`RL.ents`). **`RK.valW`**: per run `fa(o)·fs(x)·Σ lines`, a pair's weight
  `T·fcv(y)` (one product for two entries, `T` the twin factor); **`RK.valW_eq`**.
* **`rkOf`**: runs of consecutive equal `(o, x)`, pairs of consecutive `(c, 2y), (c·X, 2y + 1)`, both by `foldr`;
  **`rkOf_ents`**: `(rkOf l).ents = l`.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Specification -/

/-- A line: one entry `(c, y)` (`p = false`) or the cell pair `(c, 2y), (c·X, 2y+1)` (`p = true`). -/
structure RL where
  c : FE2
  y : ℕ
  p : Bool
  deriving Inhabited

/-- A line's entries at matrix `o`, slot `x`. -/
def RL.ents (o x : ℕ) (l : RL) : List Q4 :=
  if l.p then [(l.c, o, x, 2 * l.y), (l.c * xF, o, x, 2 * l.y + 1)] else [(l.c, o, x, l.y)]

/-- **The row kind**: runs `(x, o, lines)`. -/
structure RK where
  runs : Array (ℕ × ℕ × Array RL)
  deriving Inhabited

/-- **Its entries.** -/
def RK.ents (k : RK) : List Q4 := k.runs.toList.flatMap fun r => r.2.2.toList.flatMap (RL.ents r.2.1 r.1)

/-- A line's weight (`fw` words, `fcv` cells, `T` the twin factor). -/
@[inline] def RL.val (fw fcv : ℕ → FE2) (T : FE2) (l : RL) : FE2 :=
  let w := if l.p then mulE T (fcv l.y) else fw l.y
  if l.c = 1 then w else mulE l.c w

/-- **Its value**: per run `fa(o)·fs(x)·Σ lines`. -/
@[specialize] def RK.valW (k : RK) (fa fs fw fcv : ℕ → FE2) (T : FE2) : FE2 :=
  k.runs.foldl (fun s r => s + mulE (mulE (fa r.2.1) (fs r.1)) (r.2.2.foldl (fun s l => s + l.val fw fcv T) 0)) 0

/-! ## Value -/

private theorem foldl_sum {α : Type} (f : α → FE2) : ∀ (l : List α) (a : FE2),
    l.foldl (fun s x => s + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_sum f l, List.map_cons, List.sum_cons, add_assoc]

theorem RL.val_eq (fw fcv : ℕ → FE2) (T : FE2) (hT : ∀ c, fw (2 * c) + xF * fw (2 * c + 1) = T * fcv c)
    (fa fs : ℕ → FE2) (o x : ℕ) (l : RL) :
    ((l.ents o x).map (qv fa fs fw)).sum = fa o * fs x * l.val fw fcv T := by
  have hv : l.val fw fcv T = l.c * (if l.p then T * fcv l.y else fw l.y) := by
    unfold RL.val
    by_cases hc : l.c = 1 <;> by_cases hp : l.p = true <;> simp [hc, hp, mulE_eq]
  rw [hv]
  unfold RL.ents
  split
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qv]
    rw [← hT]; ring
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qv]; ring

/-- **The kind's value is the sum over its entries.** -/
theorem RK.valW_eq (k : RK) (fa fs fw fcv : ℕ → FE2) (T : FE2)
    (hT : ∀ c, fw (2 * c) + xF * fw (2 * c + 1) = T * fcv c) :
    k.valW fa fs fw fcv T = (k.ents.map (qv fa fs fw)).sum := by
  unfold RK.valW RK.ents
  rw [← Array.foldl_toList, foldl_sum, zero_add, sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  rw [mulE_eq, mulE_eq, ← Array.foldl_toList, foldl_sum, zero_add, sum_map_flatMap, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
  rw [RL.val_eq fw fcv T hT]

/-! ## The builder -/

/-- One step of the pairing (right to left): `q` joins a following single `(c·X, 2y+1)` into a pair. -/
def rkLineStep (q : Q4) : List RL → List RL
  | l :: ls =>
    if !l.p && q.2.2.2 % 2 == 0 && l.y == q.2.2.2 + 1 && l.c == q.1 * xF then ⟨q.1, q.2.2.2 / 2, true⟩ :: ls
    else ⟨q.1, q.2.2.2, false⟩ :: l :: ls
  | [] => [⟨q.1, q.2.2.2, false⟩]

/-- The lines of a run (`foldr`: compiled without deep recursion). -/
def rkLines (qs : List Q4) : List RL := qs.foldr rkLineStep []

/-- One step of the runs (right to left): `q` joins the following run of equal `(o, x)`. -/
def rkRunStep (q : Q4) : List (ℕ × ℕ × List Q4) → List (ℕ × ℕ × List Q4)
  | r :: rs => if q.2.2.1 == r.1 && q.2.1 == r.2.1 then (r.1, r.2.1, q :: r.2.2) :: rs else (q.2.2.1, q.2.1, [q]) :: r :: rs
  | [] => [(q.2.2.1, q.2.1, [q])]

/-- The runs of equal `(x, o)`. -/
def rkRuns (qs : List Q4) : List (ℕ × ℕ × List Q4) := qs.foldr rkRunStep []

/-- **The row kind of an entry list.** -/
def rkOf (qs : List Q4) : RK := ⟨((rkRuns qs).map fun r => (r.1, r.2.1, (rkLines r.2.2).toArray)).toArray⟩

/-! ## The builder's entries -/

private theorem rkLines_ents (o x : ℕ) : ∀ qs : List Q4, (∀ q ∈ qs, q.2.1 = o ∧ q.2.2.1 = x) →
    (rkLines qs).flatMap (RL.ents o x) = qs
  | [], _ => rfl
  | q :: qs, h => by
    have ih := rkLines_ents o x qs (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    obtain ⟨ho, hx⟩ := h q List.mem_cons_self
    obtain ⟨c, o', x', y⟩ := q
    simp only at ho hx
    subst ho hx
    unfold rkLines at ih ⊢
    rw [List.foldr_cons]
    revert ih
    generalize qs.foldr rkLineStep [] = L
    intro ih
    cases L with
    | nil => simp [rkLineStep, RL.ents] at ih ⊢; exact ih
    | cons l ls =>
      simp only [rkLineStep]
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
        obtain ⟨⟨⟨hp, hy⟩, hl⟩, hcx⟩ := hc
        have e2 : 2 * (y / 2) = y := by omega
        rw [← ih]
        obtain ⟨lc, ly, lp⟩ := l
        simp only at hp hl hcx
        subst hp hl hcx
        simp [RL.ents, e2]
      · rw [List.flatMap_cons, ← ih]
        simp [RL.ents]

private theorem rkRuns_ents : ∀ qs : List Q4,
    (rkRuns qs).flatMap (fun r => r.2.2) = qs ∧ ∀ r ∈ rkRuns qs, ∀ q ∈ r.2.2, q.2.1 = r.2.1 ∧ q.2.2.1 = r.1
  | [] => by simp [rkRuns]
  | q :: qs => by
    obtain ⟨ih1, ih2⟩ := rkRuns_ents qs
    unfold rkRuns at ih1 ih2 ⊢
    rw [List.foldr_cons]
    revert ih1 ih2
    generalize qs.foldr rkRunStep [] = L
    intro ih1 ih2
    cases L with
    | nil =>
      simp only [List.flatMap_nil] at ih1
      subst ih1
      simp only [rkRunStep, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton, true_and,
        forall_eq]
    | cons r rs =>
      simp only [rkRunStep]
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine ⟨?_, ?_⟩
        · simp only [List.flatMap_cons] at ih1 ⊢
          rw [← ih1]; rfl
        · intro r' hr' q' hq'
          rcases List.mem_cons.1 hr' with rfl | hr'
          · rcases List.mem_cons.1 hq' with rfl | hq'
            · exact ⟨hc.2, hc.1⟩
            · exact ih2 r List.mem_cons_self q' hq'
          · exact ih2 r' (List.mem_cons_of_mem _ hr') q' hq'
      · refine ⟨?_, ?_⟩
        · simp only [List.flatMap_cons] at ih1 ⊢
          rw [← ih1]; rfl
        · intro r' hr' q' hq'
          rcases List.mem_cons.1 hr' with rfl | hr'
          · simp only [List.mem_singleton] at hq'; subst hq'; exact ⟨rfl, rfl⟩
          · exact ih2 r' hr' q' hq'

/-- **The builder keeps every entry, in order.** -/
theorem rkOf_ents (qs : List Q4) : (rkOf qs).ents = qs := by
  obtain ⟨h1, h2⟩ := rkRuns_ents qs
  unfold rkOf RK.ents
  simp only [List.flatMap_map]
  conv_rhs => rw [← h1]
  refine List.flatMap_congr fun r hr => ?_
  exact rkLines_ents r.2.1 r.1 r.2.2 (h2 r hr)

end Lvm6.V
