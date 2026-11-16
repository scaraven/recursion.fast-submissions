-- New for lvm (WP-14a, H3): V_S's claim lists (LvmDecide `chFixedClaims`, LvmDecideV0 `ksOutputClaims0`,
-- `sumClaim`, `BlockClaim.onStack`) against LvmVEqMid's over `E`, through LvmVEqRel's `BCRel`/`CRel`/`SCRel`.
import LvmVEqRel
import LvmVEqArith

-- (GOLF2: 6 declarations that `certified` does not use moved verbatim to `LvmE2VMidSpecFOff`, outside its import closure.)

/-!
# The claim lists over `E`

* `point_rel`, `sumClaim_rel`: a native column claim (`BlockClaim.point`) and a native sum claim
  (`sumClaim`) agree with their `E` twins (`BClaim.point`, `sumClaimE`) on mapped arguments;
* `onStack_rel`: agreeing block claims put agreeing claims on the stack; `on_rel`: per commitment,
  for agreeing lists;
* `tapeClaims_rel` (lvm2 S2: the tape's claims), `ksOutputClaims_rel` (KS's 25 output
  lanes) at `P20`; `dBlk_eq`, `ksYPart_rel`: the P20 layout of `M3.real` is LvmVEqMid's.

Helpers live in `Lvm.VEq.Lk` (no clash with the other phases' helpers).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_mul tE_ofK)

namespace Lk

/-! ## Lists -/

theorem forall₂_map_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ (l : List α), (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_map_map l fun b hb ↦ h b (by simp [hb]))

theorem forall₂_append {α β : Type} {R : α → β → Prop} {a c : List α} {b d : List β}
    (h1 : List.Forall₂ R a b) (h2 : List.Forall₂ R c d) : List.Forall₂ R (a ++ c) (b ++ d) :=
  List.rel_append h1 h2

/-! ## Claims -/

/-- **A column claim.** -/
theorem point_rel (b : Lvm.Placement) (z : List FE) (v : FE) {b' : VPlacement} {z' : List E} {v' : E}
    (hb : b' = plE b) (hz : z' = z.map FE.toExt3) (hv : v' = FE.toExt3 v) :
    BCRel (BlockClaim.point b z v) (BClaim.point b' z' v') := by
  subst hb hz hv
  exact ⟨rfl, rfl, fun xs ↦ (toExt3_eqEval z xs).symm⟩

/-- A part of a native sum claim over `E`. -/
def partE (q : FE × Lvm.Placement × List FE) : E × VPlacement × List E :=
  (FE.toExt3 q.1, plE q.2.1, q.2.2.map FE.toExt3)

/-! ## The P20 layout -/

end Lk

open Lk

/-- **On the stack.** -/
theorem onStack_rel {c : BlockClaim} {c' : BClaim} (h : BCRel c c') : SCRel c.onStack c'.onStack := by
  obtain ⟨hb, hv, hw⟩ := h
  refine ⟨hv, fun xs ↦ ?_⟩
  simp only [BlockClaim.onStack, BClaim.onStack, hb, tE_mul]
  rw [← List.map_take, hw]
  exact congrArg (· * _) (toExt3_eqAbove c.block xs).symm

/-! ## The claim lists -/

end Lvm.VEq
