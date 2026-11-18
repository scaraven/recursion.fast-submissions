-- Vendored from `CompPoly/CompPoly/Data/List/Lemmas.lean` (the contract's pin of the package) as `LvmMlListLemmas` for lvm (WP-2).
/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Gregor Mitscha-Baude
-/

import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Cases

-- (GOLF2: 17 declarations that `certified` does not use moved verbatim to `LvmTypedVEqPhasesXOff`, outside its import closure.)

/-!
# Auxiliary lemmas for `List`
-/

section
universe u v w

namespace List

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)

@[simp]
theorem getLastI_append_single [Inhabited α] (x : α) : (l ++ [x]).getLastI = x := by
  simp only [List.getLastI_eq_getLast?_getD, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.getD_some]

variable {α : Type*} {unit : α}

@[simp] theorem leftpad_eq_self (l : List α) (n : Nat) (h : l.length ≥ n) :
    leftpad n unit l = l := by simp [leftpad, Nat.sub_eq_zero_of_le h]

@[simp] theorem rightpad_length (n : Nat) (unit : α) (l : List α) :
    (rightpad n unit l).length = max n l.length := by
  simp only [rightpad, length_append, length_replicate, Nat.add_comm l.length _, Nat.sub_add_eq_max]

@[simp] theorem rightpad_prefix (n : Nat) (unit : α) (l : List α) :
    l <+: rightpad n unit l := by
  simp only [IsPrefix, rightpad]
  exact Exists.intro (replicate (n - l.length) unit) rfl

@[simp] theorem rightpad_suffix (n : Nat) (unit : α) (l : List α) :
    replicate (n - l.length) unit <:+ rightpad n unit l := by
  simp only [IsSuffix, rightpad]
  exact Exists.intro l rfl

@[simp] theorem rightpad_eq_self (l : List α) (n : Nat) (h : n ≤ l.length) :
    rightpad n unit l = l := by simp [rightpad, Nat.sub_eq_zero_of_le h]

@[simp] theorem rightpad_twice_eq_rightpad_max (m n : Nat) (unit : α) (l : List α) :
    rightpad n unit (rightpad m unit l) = rightpad (max m n) unit l := by
  rw (config := { occs := .neg [0] }) [rightpad, rightpad_length]
  simp [rightpad]
  by_cases h : m.max n ≤ l.length
  · simp [Nat.max_le.mp h]
  · refine Nat.eq_sub_of_add_eq ?_
    conv => { enter [1, 1]; rw [Nat.add_comm] }
    rw [Nat.add_assoc, Nat.sub_add_eq_max, Nat.sub_add_eq_max]
    simp at h
    by_cases h' : m ≤ l.length <;> omega

-- lemma getD_eq_getElem {l : List α} {i : Nat} {unit : α} (hi : i < l.length) :
--     l.getD i unit = l[i] := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi, Option.getD_some]

-- lemma getD_eq_default {l : List α} {i : Nat} {unit : α} (hi : i ≥ l.length) :
--     l.getD i unit = unit := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_none hi, Option.getD_none]

@[simp] theorem rightpad_getD_eq_getD (l : List α) (n : Nat) (unit : α) (i : Nat) :
    (rightpad n unit l).getD i unit = l.getD i unit := by
  rcases (Nat.lt_or_ge i l.length) with h_lt | h_ge
  · have h_lt': i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    simp only [h_lt, h_lt', getD_eq_getElem] -- eliminate `getD`
    simp [h_lt]
  rw [getD_eq_default _ _ h_ge] -- eliminate second `getD` for `unit`
  rcases (Nat.lt_or_ge i n) with h_lt₂ | h_ge₂
  · have h_lt' : i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_getElem _ _ h_lt'] -- eliminate first `getD`
    simp [h_ge]
  · have h_ge' : i ≥ (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_default _ _ h_ge'] -- eliminate first `getD`

end List
