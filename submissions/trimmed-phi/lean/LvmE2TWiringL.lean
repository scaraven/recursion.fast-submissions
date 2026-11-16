-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): proof helpers of `LvmE2TWiring` (`wiringRelT_iff`, `PhiQCT_eq`).
import LvmTypedX
import LvmE2QFieldCorrect

/-!
# Helpers of `LvmE2TWiring`

Lemmas that do not mention `LvmE2TWiring`'s definitions: `FE`'s coordinates of sums and products, numerals of
`FK` (characteristic `2`), sparse sums over lists (`foldr` over a filter as a sum of `if`s, sums over `flatMap`
and `filterMap`), and the matrices of S1's entries are below `8` on a checked layout (`tw_entsX_o`).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-- A numeral of `FK` is its parity. -/
theorem tw_fk_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : FK) = ((n % 2 : ℕ) : FK) := by
  rw [← CharP.cast_eq_mod FK 2 n]; rfl

theorem tw_fe_add_def (x y : FE) : x + y = ⟨x.c₀ + y.c₀, x.c₁ + y.c₁, x.c₂ + y.c₂⟩ := rfl

theorem tw_fe_mul_def (x y : FE) : x * y =
    ⟨x.c₀ * y.c₀ + (x.c₁ + x.c₂) * (y.c₁ + y.c₂) + x.c₁ * y.c₁ + x.c₂ * y.c₂,
      (x.c₀ + x.c₁) * (y.c₀ + y.c₁) + x.c₀ * y.c₀ + (x.c₁ + x.c₂) * (y.c₁ + y.c₂),
      (x.c₀ + x.c₂) * (y.c₀ + y.c₂) + x.c₀ * y.c₀ + x.c₁ * y.c₁⟩ := rfl

/-- On a checked layout every entry of S1 has a matrix below `8`. -/
theorem tw_entsX_o (Q : Program) (lay : Lay) (hlay : lay.Ok Q) : ∀ e ∈ entsX Q lay, e.o < 8 := by
  intro e he
  simp only [entsX, auxEnts, List.mem_append, List.mem_flatMap, List.mem_range] at he
  rcases he with ⟨i, -, he⟩ | ⟨k, -, j, -, r, -, he⟩
  · exact instEntsX_o Q lay i e he
  · have := auxRowEnts_o' hlay k r j e he; omega

theorem tw_foldr_sum {α β : Type} [AddCommMonoid β] (l : List α) (f : α → β) :
    l.foldr (fun e acc ↦ f e + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, List.map_cons, List.sum_cons]

theorem tw_foldr_filter {α β : Type} [AddCommMonoid β] (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).foldr (fun e acc ↦ f e + acc) 0 = (l.map fun e ↦ if p e then f e else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

theorem tw_sum_filter_map {α β : Type} [AddCommMonoid β] (l : List α) (p : α → Bool) (f : α → β) :
    ((l.filter p).map f).sum = (l.map fun e ↦ if p e then f e else 0).sum := by
  rw [← tw_foldr_sum, tw_foldr_filter]

theorem tw_sum_flatMap {α β γ : Type} [AddCommMonoid γ] (l : List α) (f : α → List β) (h : β → γ) :
    ((l.flatMap f).map h).sum = (l.map fun a ↦ ((f a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- A sum over a `filterMap` dropping the zero coordinates is the sum over all (they contribute `0`). -/
theorem tw_sum_filterMap_ne {β γ : Type} [AddCommMonoid β] (l : List ℕ) (c : ℕ → FK) (F : ℕ → γ)
    (g : γ → β) (hg : ∀ j, c j = 0 → g (F j) = 0) :
    ((l.filterMap fun j ↦ if c j == 0 then none else some (F j)).map g).sum =
      (l.map fun j ↦ g (F j)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : c a = 0
    · rw [List.filterMap_cons_none (by simp [h])]
      simp only [ih, List.map_cons, List.sum_cons, hg a h, zero_add]
    · rw [List.filterMap_cons_some (b := F a) (by simp [h])]
      simp only [List.map_cons, List.sum_cons, ih]

theorem tw_fe2_sum_mk {α : Type} (l : List α) (f g : α → FK) :
    (l.map fun a ↦ (⟨f a, g a⟩ : FE2)).sum = ⟨(l.map f).sum, (l.map g).sum⟩ := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

/-- Coordinate `0` of `A·B + D + W` in `E3 ⊗_K E2` is `(relX0, relX1)`'s coordinate `0` (`relT`'s algebra). -/
theorem tw_alg0 (a0 a1 b0 b1 d0 d1 w0 w1 : FE) :
    (⟨a0.c₀, a1.c₀⟩ : FE2) * (⟨b0.c₀, b1.c₀⟩ : FE2) + ((⟨a0.c₁, a1.c₁⟩ : FE2) * (⟨b0.c₂, b1.c₂⟩ : FE2) + (⟨a0.c₂, a1.c₂⟩ : FE2) * (⟨b0.c₁, b1.c₁⟩ : FE2)) +
        ((⟨d0.c₀, d1.c₀⟩ : FE2) + (⟨w0.c₀, w1.c₀⟩ : FE2)) =
      ⟨(a0 * b0 + a1 * b1 + d0 + w0).c₀, (a0 * b1 + a1 * b0 + FE.ofK FK.x * (a1 * b1) + d1 + w1).c₀⟩ := by
  simp only [tw_fe_mul_def, tw_fe_add_def, FE.ofK, FE2.mul_def, FE2.add_def, FE2.mk.injEq]
  constructor <;> ring_nf <;>
    simp only [tw_fk_ofNat, Nat.reduceMod, Nat.cast_zero, mul_zero, add_zero]

/-- Coordinate `1` of `A·B + D + W` in `E3 ⊗_K E2` is `(relX0, relX1)`'s coordinate `1` (`relT`'s algebra). -/
theorem tw_alg1 (a0 a1 b0 b1 d0 d1 w0 w1 : FE) :
    (⟨a0.c₀, a1.c₀⟩ : FE2) * (⟨b0.c₁, b1.c₁⟩ : FE2) + (⟨a0.c₁, a1.c₁⟩ : FE2) * (⟨b0.c₀, b1.c₀⟩ : FE2) + ((⟨a0.c₁, a1.c₁⟩ : FE2) * (⟨b0.c₂, b1.c₂⟩ : FE2) + (⟨a0.c₂, a1.c₂⟩ : FE2) * (⟨b0.c₁, b1.c₁⟩ : FE2)) + (⟨a0.c₂, a1.c₂⟩ : FE2) * (⟨b0.c₂, b1.c₂⟩ : FE2) +
        ((⟨d0.c₁, d1.c₁⟩ : FE2) + (⟨w0.c₁, w1.c₁⟩ : FE2)) =
      ⟨(a0 * b0 + a1 * b1 + d0 + w0).c₁, (a0 * b1 + a1 * b0 + FE.ofK FK.x * (a1 * b1) + d1 + w1).c₁⟩ := by
  simp only [tw_fe_mul_def, tw_fe_add_def, FE.ofK, FE2.mul_def, FE2.add_def, FE2.mk.injEq]
  constructor <;> ring_nf <;>
    simp only [tw_fk_ofNat, Nat.reduceMod, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, add_zero]

/-- Coordinate `2` of `A·B + D + W` in `E3 ⊗_K E2` is `(relX0, relX1)`'s coordinate `2` (`relT`'s algebra). -/
theorem tw_alg2 (a0 a1 b0 b1 d0 d1 w0 w1 : FE) :
    (⟨a0.c₀, a1.c₀⟩ : FE2) * (⟨b0.c₂, b1.c₂⟩ : FE2) + (⟨a0.c₁, a1.c₁⟩ : FE2) * (⟨b0.c₁, b1.c₁⟩ : FE2) + (⟨a0.c₂, a1.c₂⟩ : FE2) * (⟨b0.c₀, b1.c₀⟩ : FE2) + (⟨a0.c₂, a1.c₂⟩ : FE2) * (⟨b0.c₂, b1.c₂⟩ : FE2) +
        ((⟨d0.c₂, d1.c₂⟩ : FE2) + (⟨w0.c₂, w1.c₂⟩ : FE2)) =
      ⟨(a0 * b0 + a1 * b1 + d0 + w0).c₂, (a0 * b1 + a1 * b0 + FE.ofK FK.x * (a1 * b1) + d1 + w1).c₂⟩ := by
  simp only [tw_fe_mul_def, tw_fe_add_def, FE.ofK, FE2.mul_def, FE2.add_def, FE2.mk.injEq]
  constructor <;> ring_nf <;>
    simp only [tw_fk_ofNat, Nat.reduceMod, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, add_zero]

end Lvm.Typed
