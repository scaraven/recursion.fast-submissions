-- New for lvm2 E2-FT (stage S2GT, E2F-T; E2AC-DES §1.2 with the roles of S1 swapped; transcript ref/s2gt.py,
-- AMENDMENTS 1-2): the typed zerocheck's relation at `E2`, `Φ_Q` at `E2` and its coordinate decomposition.
-- Frozen on day 0 (E2F-T); proofs E2F-T's.
import LvmTypedX
import LvmE2QFieldCorrect

-- ===== merged from `LvmE2TWiringL` (VQ module merge: `LvmE2TWiringL.lean` removed) =====
section
-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): proof helpers of `LvmE2TWiring` (`wiringRelT_iff`, `PhiQCT_eq`).

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
  | cons a l ih => by_cases h : p a <;> simp only [h, List.filter_cons_of_pos, List.foldr_cons, ih, List.map_cons, ↓reduceIte, List.sum_cons, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, zero_add]

theorem tw_sum_filter_map {α β : Type} [AddCommMonoid β] (l : List α) (p : α → Bool) (f : α → β) :
    ((l.filter p).map f).sum = (l.map fun e ↦ if p e then f e else 0).sum := by
  rw [← tw_foldr_sum, tw_foldr_filter]

theorem tw_sum_flatMap {α β γ : Type} [AddCommMonoid γ] (l : List α) (f : α → List β) (h : β → γ) :
    ((l.flatMap f).map h).sum = (l.map fun a ↦ ((f a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- A sum over a `filterMap` dropping the zero coordinates is the sum over all (they contribute `0`). -/
theorem tw_sum_filterMap_ne {β γ : Type} [AddCommMonoid β] (l : List ℕ) (c : ℕ → FK) (F : ℕ → γ)
    (g : γ → β) (hg : ∀ j, c j = 0 → g (F j) = 0) :
    ((l.filterMap fun j ↦ if c j == 0 then none else some (F j)).map g).sum =
      (l.map fun j ↦ g (F j)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : c a = 0
    · rw [List.filterMap_cons_none (by simp only [h, BEq.rfl, ↓reduceIte])]
      simp only [ih, List.map_cons, List.sum_cons, hg a h, zero_add]
    · rw [List.filterMap_cons_some (b := F a) (by simp only [beq_iff_eq, h, ↓reduceIte])]
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
end
-- ===== end of `LvmE2TWiringL` =====

/-!
# The wiring at `E2`: `K` and `E2` rows executable, `E3` cells foreign by three coordinates

S2GT runs the typed zerocheck in `E2 = FK[X]/(X² + xX + 1)` (`FE2`). The entries of S1 (`LvmWiringX.entsX`: matrix
`o = m + 4s`, `m ∈ {A, B, D, W}`, `s` the `E2` coordinate, coefficient in `FE = FK[y]/(y³ + y + 1)`) are re-tagged:

* **`splitEnt`**: an entry `(m + 4s, x, y, c)` becomes, for each `E3` coordinate `j < 3` with `c_j ≠ 0`, the entry
  `(m + 4j, x, y, c_j·X^s)`. A `K` row's coefficient is in `K` (`j = 0` only); an `E2` twin row's are in `K` with
  `X^s` (executable: one `E2` value at `j = 0`); an `E3` row's (`Ty.E`, the WHIR gadget's cells) are the coordinates
  of `y^j` (foreign: three `K` coordinates, `s = 0`). Slots `o' = m + 4j`, 12 of 16 used, 4 selector bits.
* **The relation** (`relT`, `WiringRelT`): at every slot `x`, in `E3 ⊗_K E2 = E2[y]/(y³ + y + 1)`, with
  `A_j = (M_{0+4j} z)(x)`, `B_j = (M_{1+4j} z)(x)`, `C_k = (M_{2+4k} z)(x) + (M_{3+4k} z)(x)`: coordinate `k` of
  `A·B + C` is zero (`mulY3`: `FE.mul`'s formula over any ring). The verifier batches the three coordinates by `ω`
  (`R = rel₀ + ω·rel₁ + ω²·rel₂`, `LvmE2TSpec`).
* **`wiringRelT_iff`**: `WiringRelT ↔ WiringRelX` (`E3 ⊗_K E2` is free over `E3` on `1, X`: the `E2`-relation's
  `y`-coordinates are those of `relX0 + X·relX1`), so **`holds_of_wiringT`** is `holds_of_wiringX`.
* **`Φ_Q` at `E2`** (`PhiQFT`, `PhiQT`): the sparse extension of the 16 matrices in `phiVarsT = 4 + 20 + 21 = 45`
  variables, the selector lowest (`m`: 2 bits, then `j`: 2 bits), then `x`, then `y`.
* **`PhiQCT_eq`** (the decomposition the fast evaluator uses): `Φ_Q` at `E2` is
  `Σ_{s<2, j<3} X^s·sel_j(p₂, p₃)·Φ_{s,j}(p')`, `Φ_{s,j}` the 43-variable extension of S1's coordinate-`s` entries'
  `j`-th `K` coordinates (`PhiPieceFT`) at an `E2` point; the fast evaluator supplies the six pieces (E2F-Q).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters

/-! ## Entries at `E2` -/

/-- **An entry at `E2`**: matrix `o' = m + 4j`, slot `x`, word `y`, coefficient in `FE2`. -/
structure EntT where
  /-- The matrix `m + 4j` (`j` the `E3` coordinate of a foreign row; `0` for executable rows). -/
  o : ℕ
  /-- The slot. -/
  x : ℕ
  /-- The word. -/
  y : ℕ
  /-- The coefficient. -/
  c : FE2
  deriving Inhabited

/-- Coordinate `j` of `c₀ + c₁y + c₂y²` (`j ≥ 2`: `c₂`). -/
def feCoord (a : FE) : ℕ → FK
  | 0 => a.c₀
  | 1 => a.c₁
  | _ => a.c₂

/-- `X^s` for `s ∈ {0, 1}` (`s ≥ 1`: `X`). -/
def xPowT (s : ℕ) : FE2 := if s = 0 then 1 else ⟨0, 1⟩

/-- **The re-tagging of an S1 entry**: `(m + 4s, x, y, c)` ↦ `(m + 4j, x, y, c_j·X^s)` for the nonzero `c_j`. -/
def splitEnt (e : Ent) : List EntT :=
  (List.range 3).filterMap fun j ↦
    if feCoord e.c j == 0 then none
    else some ⟨e.o % 4 + 4 * j, e.x, e.y, FE2.ofK (feCoord e.c j) * xPowT (e.o / 4)⟩

/-- **The sixteen matrices' entries at `E2`** (12 used). -/
def entsT (Q : Program) (lay : Lay) : List EntT := (entsX Q lay).flatMap splitEnt

/-- **`(M_{o'} z)(x)`** at `E2`. -/
def matZT (Q : Program) (lay : Lay) (o : ℕ) (z : ℕ → FK) (x : ℕ) : FE2 :=
  ((entsT Q lay).filter fun e ↦ e.o == o && e.x == x).foldr (fun e acc ↦ e.c * FE2.ofK (z e.y) + acc) 0

/-! ## The relation -/

/-- **The product of `E3 = K[y]/(y³ + y + 1)` in coordinates over any ring** (`FE.mul`'s formula: with
`d_k = Σ_{i+j=k} a_i b_j`, `(d₀ + d₃, d₁ + d₃ + d₄, d₂ + d₄)`); coordinate `k`, `k ≥ 2` read as `2`. -/
def mulY3 {R : Type} [Add R] [Mul R] (a b : ℕ → R) : ℕ → R
  | 0 => a 0 * b 0 + (a 1 * b 2 + a 2 * b 1)
  | 1 => a 0 * b 1 + a 1 * b 0 + (a 1 * b 2 + a 2 * b 1) + a 2 * b 2
  | _ => a 0 * b 2 + a 1 * b 1 + a 2 * b 0 + a 2 * b 2

/-- **Coordinate `k` of `A·B + C` at slot `x`** in `E3 ⊗_K E2` (`A_j = M_{4j}`, `B_j = M_{1+4j}`,
`C_k = M_{2+4k} + M_{3+4k}`). -/
def relT (Q : Program) (lay : Lay) (z : ℕ → FK) (x k : ℕ) : FE2 :=
  mulY3 (fun j ↦ matZT Q lay (4 * j) z x) (fun j ↦ matZT Q lay (1 + 4 * j) z x) k +
    (matZT Q lay (2 + 4 * k) z x + matZT Q lay (3 + 4 * k) z x)

/-- **The wiring relation at `E2`**: all three coordinates of `A z·B z + D z + W z` vanish at every slot. -/
def WiringRelT (Q : Program) (lay : Lay) (z : ℕ → FK) : Prop :=
  ∀ x k, k < 3 → relT Q lay z x k = 0

/-- **The relation at `E2` is S1's coordinate-split relation** (`E3 ⊗_K E2` is free over `E3` on `1, X`). -/
theorem wiringRelT_iff (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) :
    WiringRelT Q lay z ↔ WiringRelX Q lay z := by
  -- (A) `matZT` at `m + 4j` is the `j`-th coordinates of `matZX` at `m` and `m + 4`
  have cAdd : ∀ (a b : FE) (j : ℕ), feCoord (a + b) j = feCoord a j + feCoord b j := by
    intro a b j; rcases j with _ | _ | j <;> rfl
  have cZero : ∀ j, feCoord 0 j = 0 := by intro j; rcases j with _ | _ | j <;> rfl
  have cMul : ∀ (a : FE) (k : FK) (j : ℕ), feCoord (a * FE.ofK k) j = feCoord a j * k := by
    intro a k j
    rcases j with _ | _ | j <;> simp only [feCoord, tw_fe_mul_def, FE.ofK] <;> ring_nf <;>
      simp only [tw_fk_ofNat, Nat.reduceMod, Nat.cast_zero, mul_zero, zero_add]
  have cSum : ∀ {α : Type} (l : List α) (f : α → FE) (j : ℕ),
      feCoord (l.map f).sum j = (l.map fun a ↦ feCoord (f a) j).sum := by
    intro α l f j
    induction l with
    | nil => exact cZero j
    | cons a l ih => simp only [List.map_cons, List.sum_cons, cAdd, ih]
  have hEnt : ∀ e : Ent, e.o < 8 → ∀ m j, m < 4 → j < 3 → ∀ x,
      ((splitEnt e).map fun e' : EntT ↦
          if (e'.o == m + 4 * j && e'.x == x) = true then e'.c * FE2.ofK (z e'.y) else 0).sum =
        ⟨feCoord (if (e.o == m && e.x == x) = true then e.c * FE.ofK (z e.y) else 0) j,
         feCoord (if (e.o == m + 4 && e.x == x) = true then e.c * FE.ofK (z e.y) else 0) j⟩ := by
    intro e he m j hm hj x
    unfold splitEnt
    rw [tw_sum_filterMap_ne _ _ _ _ (fun j' hj' ↦ by simp only [Bool.and_eq_true, beq_iff_eq, hj', show FE2.ofK 0 = 0 from rfl, zero_mul, ite_self])]
    obtain ⟨o, ex, ey, c⟩ := e
    simp only at he ⊢
    have key : ∀ j', (o % 4 + 4 * j' == m + 4 * j) = (j' == j && o % 4 == m) := by
      intro j'
      apply Bool.eq_iff_iff.2
      simp only [beq_iff_eq, Bool.and_eq_true]
      exact ⟨fun h ↦ ⟨by omega, by omega⟩, fun h ↦ by omega⟩
    have k0 : (o == m) = (o / 4 == 0 && o % 4 == m) := by
      apply Bool.eq_iff_iff.2
      simp only [beq_iff_eq, Bool.and_eq_true]
      exact ⟨fun h ↦ ⟨by omega, by omega⟩, fun h ↦ by omega⟩
    have k1 : (o == m + 4) = (o / 4 == 1 && o % 4 == m) := by
      apply Bool.eq_iff_iff.2
      simp only [beq_iff_eq, Bool.and_eq_true]
      exact ⟨fun h ↦ ⟨by omega, by omega⟩, fun h ↦ by omega⟩
    rw [show List.range 3 = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, key, k0, k1]
    have hs : o / 4 = 0 ∨ o / 4 = 1 := by omega
    generalize o / 4 = s at hs ⊢
    generalize (o % 4 == m) = b1
    generalize (ex == x) = b2
    rcases hs with rfl | rfl <;> cases b1 <;> cases b2 <;> interval_cases j <;>
      simp only [BEq.rfl, Bool.and_false, Bool.and_self, Bool.false_eq_true, ↓reduceIte, Nat.reduceBEq, add_zero, cZero, Bool.and_true, FE2.ofK, xPowT, mul_one, FE2.mul_def, mul_zero, zero_mul, cMul, zero_add, one_ne_zero] <;> rfl
  have hA : ∀ m j, m < 4 → j < 3 → ∀ x,
      matZT Q lay (m + 4 * j) z x = ⟨feCoord (matZX Q lay m z x) j, feCoord (matZX Q lay (m + 4) z x) j⟩ := by
    intro m j hm hj x
    unfold matZT matZX entsT
    rw [tw_foldr_filter, tw_foldr_filter, tw_foldr_filter, tw_sum_flatMap, cSum, cSum, ← tw_fe2_sum_mk]
    apply congrArg
    apply List.map_congr_left
    intro e he
    exact hEnt e (tw_entsX_o Q lay hlay e he) m j hm hj x
  -- (B) the relation's coordinates are those of `relX0`, `relX1` (`E3 ⊗_K E2 = E3 ⊕ E3·X`)
  have hAlg : ∀ (a0 a1 b0 b1 d0 d1 w0 w1 : FE) (k : ℕ), k < 3 →
      mulY3 (fun j ↦ (⟨feCoord a0 j, feCoord a1 j⟩ : FE2)) (fun j ↦ (⟨feCoord b0 j, feCoord b1 j⟩ : FE2)) k +
          ((⟨feCoord d0 k, feCoord d1 k⟩ : FE2) + ⟨feCoord w0 k, feCoord w1 k⟩) =
        ⟨feCoord (a0 * b0 + a1 * b1 + d0 + w0) k,
          feCoord (a0 * b1 + a1 * b0 + FE.ofK FK.x * (a1 * b1) + d1 + w1) k⟩ := by
    intro a0 a1 b0 b1 d0 d1 w0 w1 k hk
    interval_cases k
    · exact tw_alg0 a0 a1 b0 b1 d0 d1 w0 w1
    · exact tw_alg1 a0 a1 b0 b1 d0 d1 w0 w1
    · exact tw_alg2 a0 a1 b0 b1 d0 d1 w0 w1
  have hCongr : ∀ (a a' b b' : ℕ → FE2), (∀ j < 3, a j = a' j) → (∀ j < 3, b j = b' j) →
      ∀ k, mulY3 a b k = mulY3 a' b' k := by
    intro a a' b b' ha hb k
    have a0 := ha 0 (by decide); have a1 := ha 1 (by decide); have a2 := ha 2 (by decide)
    have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
    rcases k with _ | _ | k <;> simp only [mulY3, a0, a1, a2, b0, b1, b2]
  have hRel : ∀ x k, k < 3 → relT Q lay z x k = ⟨feCoord (relX0 Q lay z x) k, feCoord (relX1 Q lay z x) k⟩ := by
    intro x k hk
    unfold relT
    rw [hCongr _ (fun j ↦ ⟨feCoord (matZX Q lay 0 z x) j, feCoord (matZX Q lay 4 z x) j⟩) _
        (fun j ↦ ⟨feCoord (matZX Q lay 1 z x) j, feCoord (matZX Q lay 5 z x) j⟩)
        (fun j hj ↦ by have h := hA 0 j (by omega) hj x; rwa [Nat.zero_add] at h)
        (fun j hj ↦ hA 1 j (by omega) hj x),
      hA 2 k (by omega) hk x, hA 3 k (by omega) hk x]
    exact hAlg _ _ _ _ _ _ _ _ k hk
  -- (C) an `FE` value is zero iff its three coordinates are
  have hZero : ∀ a : FE, a = 0 ↔ ∀ k < 3, feCoord a k = 0 := by
    intro a
    constructor
    · rintro rfl k _
      exact cZero k
    · intro h
      obtain ⟨c0, c1, c2⟩ := a
      have h0 := h 0 (by omega)
      have h1 := h 1 (by omega)
      have h2 := h 2 (by omega)
      simp only [feCoord] at h0 h1 h2
      subst h0 h1 h2
      rfl
  unfold WiringRelT WiringRelX
  constructor
  · intro h x
    rw [hZero, hZero]
    exact ⟨fun k hk ↦ congrArg FE2.re ((hRel x k hk).symm.trans (h x k hk)),
      fun k hk ↦ congrArg FE2.im ((hRel x k hk).symm.trans (h x k hk))⟩
  · intro h x k hk
    have h' := h x
    rw [hZero, hZero] at h'
    rw [hRel x k hk, h'.1 k hk, h'.2 k hk]
    rfl

/-- **The circuit theorem at `E2`** (S2GT's `holds_of_wiringX`): with the program and twin checks, on a checked
layout, with `z(one) = 1`, the relation at `E2` and the mini-bus obligation give every row relation and every
gated assertion on the memory read off `z`. -/
theorem holds_of_wiringT (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (htw : Q.twinsOk = true)
    (hlay : lay.Ok Q) (hone : z lay.one = 1) (h : WiringRelT Q lay z) (hrd : ReaddOk Q (memOf lay z)) :
    Q.Holds (memOf lay z) ∧ Q.Asserts (memOf lay z) :=
  holds_of_wiringX Q lay z hwf htw hlay hone ((wiringRelT_iff Q lay hlay z).mp h) hrd

/-! ## `Φ_Q` at `E2` in 45 variables -/

/-- The selector bits: `m` (2) then `j` (2). -/
abbrev selBitsT : ℕ := 4

/-- **`Φ_Q`'s variables at `E2`**: the selector (4), `x` (20), `y` (21). -/
abbrev phiVarsT : ℕ := selBitsT + xVars + yVars

/-- An entry's index on the 45-variable cube: `o'` the low 4 bits, then `x`, then `y`. -/
def EntT.idx (e : EntT) : ℕ := e.o + 16 * (e.x + 2 ^ xVars * e.y)

/-- `eq(r, ·)` at a cube point, over `FE2` (characteristic 2: `1 − r = 1 + r`). -/
def eqWT : List FE2 → ℕ → FE2
  | [], _ => 1
  | r :: rs, x => (if x % 2 = 1 then r else 1 + r) * eqWT rs (x / 2)

/-- **`Φ_Q` natively at `E2`**, at a point of `phiVarsT` coordinates (`o' ++ x ++ y`). -/
def PhiQFT (Q : Program) (lay : Lay) (pt : List FE2) : FE2 :=
  (entsT Q lay).foldr (fun e acc ↦ e.c * eqWT pt e.idx + acc) 0

/-- `E2` as machine words. -/
def ofE2 (a : E2) : FE2 := ⟨FK.ofBF64 a.re, FK.ofBF64 a.im⟩

/-- **`Φ_Q` over `E2`** (A23's `Φ` at S2GT, 45 variables). -/
def PhiQT (Q : Program) (lay : Lay) (pt : List E2) : E2 := FE2.toE2 (PhiQFT Q lay (pt.map ofE2))

/-- **Matrix `o'`'s extension at `(r_x, r_y)`** natively (`rxy = r_x ++ r_y`). -/
def matMleFT (Q : Program) (lay : Lay) (o : ℕ) (rxy : List FE2) : FE2 :=
  ((entsT Q lay).filter fun e ↦ e.o == o).foldr (fun e acc ↦ e.c * eqWT rxy (e.x + 2 ^ xVars * e.y) + acc) 0

/-- Matrix `o'`'s extension over `E2`. -/
def matMleT (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E2) : E2 :=
  FE2.toE2 (matMleFT Q lay o (rxy.map ofE2))

/-! ## The decomposition the fast evaluator uses -/

/-- **Piece `(s, j)`**: S1's coordinate-`s` entries' `j`-th `K` coordinates, as roll 8's 43-variable `Φ` (matrix
`m` in 2 bits, `x`, `y`) at an `E2` point. -/
def PhiPieceFT (Q : Program) (lay : Lay) (s j : ℕ) (pt : List FE2) : FE2 :=
  ((entsX Q lay).filter fun e ↦ e.o / 4 == s).foldr
    (fun e acc ↦ FE2.ofK (feCoord e.c j) * eqWT pt (e.o % 4 + 4 * (e.x + 2 ^ xVars * e.y)) + acc) 0

/-- The `j` selector at bits `(p₂, p₃)`: `j = 0, 1, 2` is `(0,0), (1,0), (0,1)`. -/
def selJT (j : ℕ) (p₂ p₃ : FE2) : FE2 :=
  match j with
  | 0 => (1 + p₂) * (1 + p₃)
  | 1 => p₂ * (1 + p₃)
  | _ => (1 + p₂) * p₃

/-- **The fast evaluator's form**: `Σ_{s<2, j<3} X^s·sel_j(p₂, p₃)·ev s j (p')`, `p'` the point without bits 2–3;
`ev` the six pieces' evaluators (E2F-Q's compiled evaluator generic in the point field). -/
def PhiQCT (ev : ℕ → ℕ → List FE2 → FE2) (pt : List FE2) : FE2 :=
  let p' := pt.take 2 ++ pt.drop 4
  ((List.range 2).map fun s ↦ ((List.range 3).map fun j ↦
    xPowT s * selJT j (pt.getD 2 0) (pt.getD 3 0) * ev s j p').sum).sum

/-- **`PhiQCT_eq`**: on a checked layout, with evaluators that are the pieces, the fast form is `Φ_Q` at `E2`
(E2F-LEAD: stated by E2F-T on day 0; the pieces' evaluator and its equality are E2F-Q's). -/
theorem PhiQCT_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (ev : ℕ → ℕ → List FE2 → FE2)
    (hev : ∀ s j pt, s < 2 → j < 3 → pt.length = phiVars → ev s j pt = PhiPieceFT Q lay s j pt)
    (pt : List FE2) (hpt : pt.length = phiVarsT) :
    PhiQCT ev pt = PhiQFT Q lay pt := by
  -- the bits `(p₂, p₃)` of a split entry's index are its `j` selector
  have hSplit : ∀ (p0 p1 p2 p3 : FE2) (rest : List FE2) (m j R : ℕ), m < 4 → j < 3 →
      eqWT (p0 :: p1 :: p2 :: p3 :: rest) (m + 4 * j + 16 * R) =
        selJT j p2 p3 * eqWT (p0 :: p1 :: rest) (m + 4 * R) := by
    intro p0 p1 p2 p3 rest m j R hm hj
    have hstep : ∀ (r : FE2) (rs : List FE2) (b x : ℕ), b < 2 →
        eqWT (r :: rs) (b + 2 * x) = (if b = 1 then r else 1 + r) * eqWT rs x := by
      intro r rs b x hb
      rw [eqWT, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.add_mul_div_left _ _ two_pos,
        Nat.div_eq_of_lt hb, Nat.zero_add]
    have hm2 : m % 2 < 2 := Nat.mod_lt _ two_pos
    have hj2 : j % 2 < 2 := Nat.mod_lt _ two_pos
    have hmd : m / 2 < 2 := by omega
    have hjd : j / 2 < 2 := by omega
    rw [show m + 4 * j + 16 * R = m % 2 + 2 * (m / 2 + 2 * (j % 2 + 2 * (j / 2 + 2 * R))) by omega,
      show m + 4 * R = m % 2 + 2 * (m / 2 + 2 * R) by omega,
      hstep p0 (p1 :: p2 :: p3 :: rest) _ _ hm2, hstep p1 (p2 :: p3 :: rest) _ _ hmd,
      hstep p2 (p3 :: rest) _ _ hj2, hstep p3 rest _ _ hjd, hstep p0 (p1 :: rest) _ _ hm2, hstep p1 rest _ _ hmd]
    generalize (if m % 2 = 1 then p0 else 1 + p0) = A
    generalize (if m / 2 = 1 then p1 else 1 + p1) = B
    generalize eqWT rest R = E
    interval_cases j <;> simp only [selJT, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte] <;> ring
  -- one S1 entry's split entries: `X^s` times the three coordinates' selected pieces
  have hEnt : ∀ (e : Ent) (p0 p1 p2 p3 : FE2) (rest : List FE2),
      ((splitEnt e).map fun e' ↦ e'.c * eqWT (p0 :: p1 :: p2 :: p3 :: rest) e'.idx).sum =
        xPowT (e.o / 4) *
          (selJT 0 p2 p3 * (FE2.ofK (feCoord e.c 0) *
              eqWT (p0 :: p1 :: rest) (e.o % 4 + 4 * (e.x + 2 ^ xVars * e.y))) +
            selJT 1 p2 p3 * (FE2.ofK (feCoord e.c 1) *
              eqWT (p0 :: p1 :: rest) (e.o % 4 + 4 * (e.x + 2 ^ xVars * e.y))) +
            selJT 2 p2 p3 * (FE2.ofK (feCoord e.c 2) *
              eqWT (p0 :: p1 :: rest) (e.o % 4 + 4 * (e.x + 2 ^ xVars * e.y)))) := by
    intro e p0 p1 p2 p3 rest
    unfold splitEnt
    rw [tw_sum_filterMap_ne _ _ _ _ (fun j' hj' ↦ by simp only [hj', show FE2.ofK 0 = 0 from rfl, zero_mul])]
    rw [show List.range 3 = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, EntT.idx]
    have hm : e.o % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [hSplit p0 p1 p2 p3 rest (e.o % 4) 0 (e.x + 2 ^ xVars * e.y) hm (by decide),
      hSplit p0 p1 p2 p3 rest (e.o % 4) 1 (e.x + 2 ^ xVars * e.y) hm (by decide),
      hSplit p0 p1 p2 p3 rest (e.o % 4) 2 (e.x + 2 ^ xVars * e.y) hm (by decide)]
    ring
  obtain ⟨p0, p1, p2, p3, rest, rfl⟩ : ∃ p0 p1 p2 p3 rest, pt = p0 :: p1 :: p2 :: p3 :: rest := by
    match pt, hpt with
    | p0 :: p1 :: p2 :: p3 :: rest, _ => exact ⟨p0, p1, p2, p3, rest, rfl⟩
  have hrest : (p0 :: p1 :: rest).length = phiVars := by
    simp only [List.length_cons, phiVarsT, phiVars, selBitsT] at hpt ⊢; omega
  unfold PhiQCT
  simp only [List.getD_cons_succ, List.getD_cons_zero, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append]
  rw [show List.range 2 = [0, 1] from rfl, show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hev 0 0 (p0 :: p1 :: rest) (by decide) (by decide) hrest, hev 0 1 (p0 :: p1 :: rest) (by decide) (by decide) hrest,
    hev 0 2 (p0 :: p1 :: rest) (by decide) (by decide) hrest, hev 1 0 (p0 :: p1 :: rest) (by decide) (by decide) hrest,
    hev 1 1 (p0 :: p1 :: rest) (by decide) (by decide) hrest, hev 1 2 (p0 :: p1 :: rest) (by decide) (by decide) hrest]
  unfold PhiPieceFT PhiQFT entsT
  simp only [tw_foldr_sum, tw_sum_filter_map, tw_sum_flatMap, ← List.sum_map_mul_left, ← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  rw [hEnt]
  have hs : e.o / 4 = 0 ∨ e.o / 4 = 1 := by have := tw_entsX_o Q lay hlay e he; omega
  rcases hs with h | h <;> simp only [h] <;> norm_num [xPowT] <;> ring

/-- **The fast form at `E2`'s own type**: `Φ_Q` over `E2` (A23's `PhiQT`) is the fast form through the executable field,
under `PhiQCT_eq`'s hypotheses (the bridge an `ev`-based `V_S` needs). -/
theorem PhiQT_eq_fast (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (ev : ℕ → ℕ → List FE2 → FE2)
    (hev : ∀ s j pt, s < 2 → j < 3 → pt.length = phiVars → ev s j pt = PhiPieceFT Q lay s j pt)
    (pt : List E2) (hpt : pt.length = phiVarsT) :
    PhiQT Q lay pt = FE2.toE2 (PhiQCT ev (pt.map ofE2)) := by
  rw [PhiQT, PhiQCT_eq Q lay hlay ev hev _ (by rw [List.length_map, hpt])]

end Lvm.Typed
