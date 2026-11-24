-- New for lvm6 (ST-4): the constructed class table on arrays, twin of `ptOfRowsG` (generic in the rows).
import Lvm6VPhiCons

/-!
# The constructed table on arrays

* `pushL`, **`foldl_app`**: a fold that appends `F x` per element builds `l.flatMap F` (the one twin lemma).
* `restA`: the rest's singles pushed in one pass (gaps' rows, then each accepted hint's differences);
  **`restA_eq`**: it is `restQ`'s list, in bounds. `ptOfRowsA`, **`ptOfRowsA_eq`**: `= ptOfRowsG`.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## The array twin -/

/-- Push `f` of every element of `l`. -/
@[inline] def pushL {α β : Type} (f : α → β) (a : Array β) (l : List α) : Array β := l.foldl (fun a x => a.push (f x)) a

theorem pushL_toList {α β : Type} (f : α → β) : ∀ (l : List α) (a : Array β), (pushL f a l).toList = a.toList ++ l.map f
  | [], a => by simp [pushL]
  | x :: l, a => by
    have ih := pushL_toList f l (a.push (f x))
    simp only [pushL, List.foldl_cons] at ih ⊢
    rw [ih, Array.toList_push, List.map_cons, List.append_assoc, List.singleton_append]

/-- **A fold appending `F x` per element builds `l.flatMap F`.** -/
theorem foldl_app {α β : Type} (G : Array β → α → Array β) (F : α → List β)
    (hG : ∀ a x, (G a x).toList = a.toList ++ F x) :
    ∀ (l : List α) (a : Array β), (l.foldl G a).toList = a.toList ++ l.flatMap F
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_app G F hG l, hG, List.flatMap_cons, List.append_assoc]

/-- An entry as pushed (the identity: the row kind takes the entries). -/
def toSgl (q : Q4) : Q4 := q

/-- The rest's singles in one pass: the gaps' rows, then each accepted hint's differences. -/
def restA (ρ : ℕ → List EntT) (N : ℕ) (A : List (HCls × CTpl × Array (List (ℕ × Q4)))) : Array Q4 :=
  let a0 := (gaps 0 (A.map (·.1)) N).foldl (fun a p =>
    (List.range' p.1 p.2).foldl (fun a g => pushL (fun e => toSgl (nrmB (toQ e))) a (ρ g)) a) #[]
  A.foldl (fun a c => (List.range c.1.n).foldl (fun a j => (List.range c.1.len).foldl (fun a t =>
    pushL (fun q => toSgl (nrmB q)) a (diffZ c.2.1 j (ρ (c.1.g0 + j * c.1.len + t)) (c.2.2.getD t []))) a) a) a0

theorem restA_eq (ρ : ℕ → List EntT) (N : ℕ) (A : List (HCls × CTpl × Array (List (ℕ × Q4)))) :
    (restA ρ N A).toList = ((restQ ρ N A).map nrmB).map toSgl := by
  have hrow : ∀ (a : Array Q4) (g : ℕ), (pushL (fun e => toSgl (nrmB (toQ e))) a (ρ g)).toList =
      a.toList ++ (((ρ g).map toQ).map nrmB).map toSgl := by
    intro a g; rw [pushL_toList]; simp [List.map_map, Function.comp_def]
  have hgap : ∀ (a : Array Q4) (p : ℕ × ℕ), ((List.range' p.1 p.2).foldl
      (fun a g => pushL (fun e => toSgl (nrmB (toQ e))) a (ρ g)) a).toList =
      a.toList ++ (((List.range' p.1 p.2).flatMap fun g => (ρ g).map toQ).map nrmB).map toSgl := by
    intro a p
    rw [foldl_app _ (fun g => (((ρ g).map toQ).map nrmB).map toSgl) hrow]
    simp [List.map_flatMap]
  have hd : ∀ (c : HCls × CTpl × Array (List (ℕ × Q4))) (j : ℕ) (a : Array Q4), ((List.range c.1.len).foldl
      (fun a t => pushL (fun q => toSgl (nrmB q)) a (diffZ c.2.1 j (ρ (c.1.g0 + j * c.1.len + t)) (c.2.2.getD t []))) a).toList =
      a.toList ++ (((List.range c.1.len).flatMap fun t => diffZ c.2.1 j (ρ (c.1.g0 + j * c.1.len + t)) (c.2.2.getD t [])).map
        nrmB).map toSgl := by
    intro c j a
    rw [foldl_app _ (fun t => ((diffZ c.2.1 j (ρ (c.1.g0 + j * c.1.len + t)) (c.2.2.getD t [])).map nrmB).map toSgl)
      (fun a t => by rw [pushL_toList]; simp [List.map_map, Function.comp_def])]
    simp [List.map_flatMap]
  have hc : ∀ (a : Array Q4) (c : HCls × CTpl × Array (List (ℕ × Q4))), ((List.range c.1.n).foldl (fun a j =>
      (List.range c.1.len).foldl (fun a t => pushL (fun q => toSgl (nrmB q)) a
        (diffZ c.2.1 j (ρ (c.1.g0 + j * c.1.len + t)) (c.2.2.getD t []))) a) a).toList =
      a.toList ++ ((clsDiff ρ c).map nrmB).map toSgl := by
    intro a c
    rw [foldl_app _ _ (fun a j => hd c j a)]
    simp [clsDiff, List.map_flatMap]
  unfold restA
  simp only
  rw [foldl_app _ (fun c => ((clsDiff ρ c).map nrmB).map toSgl) hc,
    foldl_app _ (fun p => (((List.range' p.1 p.2).flatMap fun g => (ρ g).map toQ).map nrmB).map toSgl) hgap]
  simp [restQ, List.map_flatMap]

/-- **The constructed table on arrays.** -/
def ptOfRowsA (ρ : ℕ → List EntT) (N : ℕ) (H : Array HCls) : PT :=
  let A := accH ρ N 0 H.toList
  ⟨(A.map (·.2.1)).toArray, sglCov [], #[], #[], #[], #[], rkOf (restA ρ N A).toList⟩

theorem ptOfRowsA_eq (ρ : ℕ → List EntT) (N : ℕ) (H : Array HCls) : ptOfRowsA ρ N H = ptOfRowsG ρ N H := by
  have h : (restA ρ N (accH ρ N 0 H.toList)).toList = (restQ ρ N (accH ρ N 0 H.toList)).map nrmB := by
    rw [restA_eq]; simp [toSgl]
  simp only [ptOfRowsA, ptOfRowsG, h]

end Lvm6.V
