-- New for lvm2 roll 7 (WP E2-S, phase G0, gate G-S). The tensor switch (NOTE-FIELD Prop 7.1) and the
-- bit-slice switch through `E2 ⊗_{F₂} E3` (ARCH-7 §2.1; paper proof `docs/lvm2/design/E2-S-switch.md`).
import LvmFieldE2
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Algebra.ZMod

-- (GOLF2: 34 declarations that `certified` does not use moved verbatim to `LvmTensorSwitchOff`, outside its import closure.)

/-!
# The tensor switch and the bit-slice switch

Claims at an `E2` point on committed `K` data are handed to the unchanged `E3` PCS. Two kinds
(ARCH-7 §2.1):

**Word claims** (NOTE-FIELD Prop 7.1, in `Quad R t`, any commutative rings):
* `wordClaim_iff`: `f̃(z) = v₀ + v₁X` iff `Σ_u w₀(u) f(u) = v₀` and `Σ_u w₁(u) f(u) = v₁`, where
  `eq(z, u) = w₀(u) + w₁(u)X`;
* **`tensorSwitch`**: for any `φ : K →+* F` and `r ∈ F^m`, the two weights' extensions at `r` are
  the coordinates of `Π_l (z_l r_l + (1 − z_l)(1 − r_l))` in `Quad F (φ t)` (`E2 → Quad Ext3`:
  `tensorSwitch_E2`); a ring identity, no field property used;
* `card_batch2_le`: a false pair of claims survives the batching `v₀ + λ v₁` for one `λ` at most.

**Bit-slice claims** (the switch of gate G-S), for any commutative ring `R` (`= F₂`), an
`R`-algebra `A` (`= E2`) with basis `β` (its `128` coordinates), a ring `Kw` (`= K`) with
`R`-basis `γ` (the `64` bit positions) and a `Kw`-algebra `B` (`= E3`):
* the slices of a column `q` are `q_i(u) = γ.repr (q u) i`; the claims `s_i = Σ_u q_i(u)·eq(z, u)`
  (`SlicesTrue`);
* `rowsOf s j = Σ_i (β.repr s_i)_j · γ_i`, the transposed form (`128` words of `K`);
* **`slicesTrue_iff`**: the slice claims hold iff every row equals `trueRow j = Σ_u ε_j(u) q(u)`,
  `ε_j(u) = (β.repr eq(z, u))_j`;
* `claim_iff`: the switched claim `Σ_u W(u) q(u) = Σ_j ρ_j t_j`, `W(u) = Σ_j ρ_j ε_j(u)`, holds iff
  the batched row errors vanish;
* **`tensor_repr`**: in `B ⊗_R A`, the coordinates of `Π_l (r_l ⊗ z_l + (1 − r_l) ⊗ (1 − z_l))` in
  the basis `1 ⊗ β_j` are `Σ_u eq(r, u)·ε_j(u)`; `weight_ext`: so the verifier's
  `Σ_j ρ_j · (coordinate j)` is the multilinear extension of `W` at `r`;
* **`card_sz_le`** (Schwartz–Zippel over a ring on a product set): a nonzero table `δ` on
  `{0,1}^n` with values in a commutative ring `T`, challenges `σ(s_l)` from a sample set whose
  differences are regular: `Σ_b eq(σ∘s, b) δ(b) = 0` for at most `n·|S|^(n−1)` of the `|S|^n` points;
* **`switch_sound`**: false slice claims make the switched claim hold for at most `n·|S|^(n−1)`
  row-batching points (`ρ_j = eq(r'', j)`, `2^n` rows).
-/

set_option autoImplicit false

namespace Lvm.TS

open Finset
open scoped TensorProduct

/-! ## `eq` on the cube -/

section Eq

variable {S : Type*} [CommRing S] {m : ℕ}

/-- `eq(z, u) = Π_l (u_l ? z_l : 1 − z_l)` at a cube point `u`. -/
def eqPt (z : Fin m → S) (u : Fin m → Bool) : S := ∏ l, if u l then z l else 1 - z l

end Eq

/-! ## Word claims (NOTE-FIELD Prop 7.1) -/

section Word

variable {K : Type*} [CommRing K] {t : K} {m : ℕ}

end Word

/-! ## The bit-slice switch through `A ⊗_R B` -/

section Slice

variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R A)
  {Kw : Type*} [CommRing Kw] [Algebra R Kw] {κ : Type*} [Fintype κ] [DecidableEq κ] (γ : Module.Basis κ R Kw)
  {B : Type*} [CommRing B] [Algebra R B] [Algebra Kw B] [IsScalarTower R Kw B]
  {m : ℕ} (z : Fin m → A) (q : (Fin m → Bool) → Kw)

/-- **The slice claims** `s_i = Σ_u q_i(u)·eq(z, u)`, `q_i(u) = γ.repr (q u) i` the bit slices. -/
def SlicesTrue (s : κ → A) : Prop := ∀ i, s i = ∑ u, γ.repr (q u) i • eqPt z u

/-- The switched target `Σ_j ρ_j t_j`. -/
def target (ρ : ι → B) (t : ι → Kw) : B := ∑ j, ρ j * algebraMap Kw B (t j)

/-- The switched weight `W(u) = Σ_j ρ_j ε_j(u)`. -/
noncomputable def weight (ρ : ι → B) (u : Fin m → Bool) : B :=
  ∑ j, ρ j * algebraMap R B (β.repr (eqPt z u) j)

end Slice

/-! ## Schwartz–Zippel over a ring on a product set (multilinear) -/

section SZ

variable {T : Type*} [CommRing T] {Sm : Type*} [Fintype Sm] [DecidableEq Sm] (σ : Sm → T)

end SZ

/-! ## Soundness of the bit-slice switch -/

section Sound

variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R A)
  {Kw : Type*} [CommRing Kw] [Algebra R Kw] {κ : Type*} [Fintype κ] [DecidableEq κ] (γ : Module.Basis κ R Kw)
  {B : Type*} [CommRing B] [Algebra R B] [Algebra Kw B] [IsScalarTower R Kw B]
  {Sm : Type*} [Fintype Sm] [DecidableEq Sm] (σ : Sm → B)
  {m n : ℕ} (z : Fin m → A) (q : (Fin m → Bool) → Kw) (e : ι ≃ (Fin n → Bool))

end Sound

/-! ## The switch at `K`, `E2`, `E3` -/

section Concrete

open LeanVM.Parameters

/-- `GF(2)` acts on `K` (characteristic two); scoped, to keep `ZMod 2` diamonds out of other modules. -/
noncomputable scoped instance instAlgZ2K : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- `GF(2)` acts on `E3` (scoped). -/
noncomputable scoped instance instAlgZ2E : Algebra (ZMod 2) E := ZMod.algebra E 2

scoped instance instTowerZ2KE : IsScalarTower (ZMod 2) K E :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

end Concrete

end Lvm.TS
