-- New for lvm6 (GSP, guard speed): KSA's `KS` word map with its input-region lanes as one window table.
-- `cellOfWord` builds `List.range lanes` for every input region at every word; the guard's `regsOkB` (`2^18` `KS`
-- words) and `ksAliasB` call the map per word. `cowTbl lay` lists the lanes' windows once (input-region order,
-- lane order), and `cellOfWordT` reads the first window holding the word: **`cellOfWordT_eq`**. No statement
-- changes; the deployed instance's field (`tiOfLQ`) carries `ksWT (cowTbl lay)`, equal to `ksWOf lay` (`ksWT_eq`).
import Lvm6NodeDeploy

/-!
# The `KS` word map on a window table

* `Win`, `winsOf d` (a `K` input region's lanes as windows `[lo, hi)` ↦ cell `c0 + m·(y − lo) + a`), `cowTbl lay`.
* **`cellOfWordT_eq : cellOfWordT (cowTbl lay) y = cellOfWord lay y`**.
* `ksWT T y = ksP.cellTgt (cellOfWordT T y)`; **`ksWT_eq : ksWT (cowTbl lay) = ksWOf lay`**.
-/

set_option autoImplicit false

namespace Lvm6.Gsp

open Lvm.Typed Lvm6.KSP

/-- A window of words `[lo, hi)`; word `y` is cell `c0 + m·(y − lo) + a`. -/
structure Win where
  lo : ℕ
  hi : ℕ
  c0 : ℕ
  m : ℕ
  a : ℕ

/-- Lane `l`'s window of an input region. -/
def winOf (d : DReg) (l : ℕ) : Win :=
  if d.lanes ≤ 1 then ⟨d.bases.headD 0, d.bases.headD 0 + d.n, d.lo, 1, 0⟩
  else ⟨d.laneBases.getD l 0, d.laneBases.getD l 0 + d.n / d.lanes, d.lo, d.lanes, l⟩

/-- The windows of a `K` input region, in lane order (none for an `E` region). -/
def winsOf (d : DReg) : List Win := if d.ty == .K then (List.range (max d.lanes 1)).map (winOf d) else []

/-- **The window table** of the layout's input regions. -/
def cowTbl (lay : Lay) : List Win := lay.inp.flatMap winsOf

/-- Window `w` holds word `y`. -/
def Win.holds (y : ℕ) (w : Win) : Bool := decide (w.lo ≤ y ∧ y < w.hi)

/-- Word `y`'s cell in window `w`. -/
def Win.cell (y : ℕ) (w : Win) : ℕ := w.c0 + w.m * (y - w.lo) + w.a

/-- **`cellOfWord` on the table**: the first window holding the word. -/
def cellOfWordT (T : List Win) (y : ℕ) : ℕ := ((T.find? (Win.holds y)).map (Win.cell y)).getD 0

/-- `cellOfWord`'s value at a region `d` that holds `y`. -/
def cowVal (d : DReg) (y : ℕ) : ℕ :=
  if d.lanes ≤ 1 then d.lo + (y - d.bases.headD 0)
  else
    let l := ((List.range d.lanes).find? fun l ↦ inLane d l y).getD 0
    d.lo + d.lanes * (y - d.laneBases.getD l 0) + l

/-- `cellOfWord`'s region test. -/
def cowP (y : ℕ) (d : DReg) : Bool := d.ty == .K && (List.range (max d.lanes 1)).any fun l ↦ inLane d l y

theorem holds_winOf (d : DReg) (l y : ℕ) : (winOf d l).holds y = inLane d l y := by
  unfold winOf inLane Win.holds
  split <;> rfl

theorem winsOf_find (d : DReg) (y : ℕ) :
    ((winsOf d).find? (Win.holds y)).map (Win.cell y) = if cowP y d then some (cowVal d y) else none := by
  unfold winsOf cowP
  by_cases hK : (d.ty == .K) = true
  · simp only [hK, ↓reduceIte, Bool.true_and]
    rw [List.find?_map, Option.map_map]
    have hp : (Win.holds y ∘ winOf d) = fun l ↦ inLane d l y := funext fun l ↦ holds_winOf d l y
    rw [hp]
    by_cases h1 : d.lanes ≤ 1
    · have hm : max d.lanes 1 = 1 := by omega
      rw [hm]
      by_cases hi : inLane d 0 y = true
      · simp [hi, cowVal, h1, Function.comp_def, winOf, Win.cell]
      · simp [hi, Function.comp_def]
    · have hm : max d.lanes 1 = d.lanes := by omega
      rw [hm]
      cases hf : (List.range d.lanes).find? (fun l ↦ inLane d l y) with
      | none =>
        have ha : ((List.range d.lanes).any fun l ↦ inLane d l y) = false := by
          rw [List.find?_eq_none] at hf
          simpa using hf
        simp [ha]
      | some l0 =>
        have ha : ((List.range d.lanes).any fun l ↦ inLane d l y) = true :=
          List.any_eq_true.mpr ⟨l0, List.mem_of_find?_eq_some hf, by have := List.find?_some hf; exact this⟩
        simp only [ha, ↓reduceIte, Option.map_some, Function.comp_apply, Option.some.injEq]
        simp [Win.cell, winOf, h1, cowVal, hf]
  · simp [Bool.eq_false_iff.mpr hK]

theorem flatMap_find (y : ℕ) : ∀ ds : List DReg,
    ((ds.flatMap winsOf).find? (Win.holds y)).map (Win.cell y) = (ds.find? (cowP y)).map (cowVal · y)
  | [] => rfl
  | d :: ds => by
    rw [List.flatMap_cons, List.find?_append, List.find?_cons]
    have h := winsOf_find d y
    by_cases hp : cowP y d = true
    · simp only [hp, ↓reduceIte] at h
      cases hw : (winsOf d).find? (Win.holds y) with
      | none => rw [hw] at h; simp at h
      | some w => rw [hw] at h; simp [hp, h]
    · simp only [Bool.eq_false_iff.mpr hp, Bool.false_eq_true, ↓reduceIte] at h
      have hw : (winsOf d).find? (Win.holds y) = none := by simpa using h
      rw [hw, Option.none_or, flatMap_find y ds, Bool.eq_false_iff.mpr hp]

theorem cellOfWordT_eq (lay : Lay) (y : ℕ) : cellOfWordT (cowTbl lay) y = cellOfWord lay y := by
  rw [cellOfWordT, cowTbl, flatMap_find, cellOfWord]
  cases h : lay.inp.find? (cowP y) with
  | none =>
    have h' : lay.inp.find? (fun d ↦ d.ty == .K && (List.range (max d.lanes 1)).any fun l ↦ inLane d l y) = none :=
      h
    rw [h']
    rfl
  | some d =>
    have h' : lay.inp.find? (fun d ↦ d.ty == .K && (List.range (max d.lanes 1)).any fun l ↦ inLane d l y) = some d :=
      h
    rw [h']
    rfl

/-- **The deployed `KS` word map on the table.** -/
def ksWT (T : List Win) (y : ℕ) : ℕ := Lvm6.Node.Dep.ksP.cellTgt (cellOfWordT T y)

theorem ksWT_eq (lay : Lay) : ksWT (cowTbl lay) = Lvm6.Node.Dep.ksWOf lay := by
  funext y
  rw [ksWT, cellOfWordT_eq]
  rfl

end Lvm6.Gsp
