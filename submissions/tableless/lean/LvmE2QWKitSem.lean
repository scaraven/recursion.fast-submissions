-- New for lvm2 E2F (slice S1, E2F-QH2): the semantics of the `E2` gadget kit (`LvmE2QWKit`) in `Hs` form
-- (`LvmQAsmArith2WhirBasis0`): on a memory where a gadget's segments hold, its outputs are the field expressions.
import LvmE2QWKit
import LvmQAsmArith2WhirBasis

/-!
# The kit's semantics

* `hs_g2Mul`, `hs_g2Lin`, `hs_g2Add`, `hs_g2One`, `hs_g2Zero`, `hs_g2Const`: one twin pair each;
* `hs_mapB`, `hs_g2Sum`, `hs_g2Dot`, `hs_g2Prod`, `hs_g2EqTab` (`eqKernelF`'s fold from a table);
* **`hs_scRound2`**, **`hs_sc2`**: the round's challenge is the stream value at the answer lane, the next claim
  `polyEval [c₀, claim + c₂, c₂] r` (`scStep2`); `R` rounds fold it (`scFold2`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har

variable {c : Ctx} {M : Mem}

theorem fe2_add_self (a : FE2) : a + a = 0 := by
  apply FE2.ext_coord <;> simp only [FE2.add_def, FE2.coord_false, FE2.coord_true] <;> exact fk_add_self _

theorem hs_g2Mul (a b d : C2) : Hs c M (g2Mul a b d) (fun r => r.val M = a.val M * b.val M + d.val M) :=
  fun p h => gE2mul_sem c M p a b d h

theorem hs_g2Lin (k : FK) (k' : FE2) (a b : C2) :
    Hs c M (g2Lin k k' a b) (fun r => r.val M = a.val M + FE2.ofK k * b.val M + k') :=
  fun p h => gE2lin_sem c M p k k' a b h

theorem hs_g2Add (a b : C2) : Hs c M (g2Add a b) (fun r => r.val M = a.val M + b.val M) :=
  fun p h => add2_sem c M p a b h

theorem hs_g2Const (k : FE2) (a : C2) : Hs c M (g2Const k a) (fun r => r.val M = k) :=
  fun p h => const2_sem c M p k a h

theorem hs_g2Zero (a : C2) : Hs c M (g2Zero a) (fun r => r.val M = 0) :=
  fun p h => const2_sem c M p 0 a h

theorem hs_g2One (a : C2) : Hs c M (g2One a) (fun r => r.val M = 1 + a.val M) :=
  hs_mono (hs_g2Lin 0 1 a a) fun r hr => by
    rw [hr, show FE2.ofK 0 = 0 from rfl, zero_mul, add_zero, add_comm]

theorem hs_mapB {α : Type} (f : α → BM C2) (g : α → FE2) (hf : ∀ a, Hs c M (f a) (fun r => r.val M = g a)) :
    ∀ l : List α, Hs c M (mapB f l) (fun rs => rs.map (C2.val M) = l.map g)
  | [] => hs_pure rfl
  | a :: l => hs_bind (hf a) fun r hr => hs_bind (hs_mapB f g hf l) fun rs hrs =>
    hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

theorem hs_g2Sum : ∀ (s : C2) (cs : List C2),
    Hs c M (g2Sum s cs) (fun r => r.val M = s.val M + (cs.map (C2.val M)).sum)
  | s, [] => hs_pure (by simp)
  | s, x :: cs => hs_bind (hs_g2Add s x) fun s' hs' => hs_mono (hs_g2Sum s' cs) fun r hr => by
    rw [hr, hs', List.map_cons, List.sum_cons, add_assoc]

theorem hs_g2Dot : ∀ (acc : C2) (l : List (C2 × C2)),
    Hs c M (g2Dot acc l) (fun r => r.val M = acc.val M + (l.map fun e => e.1.val M * e.2.val M).sum)
  | acc, [] => hs_pure (by simp)
  | acc, (a, b) :: l => hs_bind (hs_g2Mul a b acc) fun s hs => hs_mono (hs_g2Dot s l) fun r hr => by
    rw [hr, hs, List.map_cons, List.sum_cons]; ring

theorem hs_g2Prod {z : C2} (hz : z.val M = 0) : ∀ (acc : C2) (xs : List C2),
    Hs c M (g2Prod z acc xs) (fun r => r.val M = acc.val M * (xs.map (C2.val M)).prod)
  | acc, [] => hs_pure (by simp)
  | acc, x :: xs => hs_bind (hs_g2Mul acc x z) fun s hs => hs_mono (hs_g2Prod hz s xs) fun r hr => by
    rw [hr, hs, hz, add_zero, List.map_cons, List.prod_cons, mul_assoc]

/-- One level of `eqKernelF`. -/
def eqStep2 (out : List FE2) (r : FE2) : List FE2 := out.map (· * (1 + r)) ++ out.map (· * r)

theorem hs_g2EqStep {z : C2} (hz : z.val M = 0) (tab : List C2) (r : C2) :
    Hs c M (g2EqStep z tab r) (fun t => t.map (C2.val M) = eqStep2 (tab.map (C2.val M)) (r.val M)) :=
  hs_bind (hs_g2One r) fun r1 hr1 =>
    hs_bind (hs_mapB (fun e => g2Mul e r1 z) (fun e => e.val M * (1 + r.val M))
      (fun e => hs_mono (hs_g2Mul e r1 z) fun x hx => by rw [hx, hr1, hz, add_zero]) tab) fun lo hlo =>
    hs_bind (hs_mapB (fun e => g2Mul e r z) (fun e => e.val M * r.val M)
      (fun e => hs_mono (hs_g2Mul e r z) fun x hx => by rw [hx, hz, add_zero]) tab) fun hi hhi =>
    hs_pure (by rw [List.map_append, hlo, hhi, eqStep2, List.map_map, List.map_map]; rfl)

/-- **The `eq` table** is `eqKernelF`'s fold from the table's values. -/
theorem hs_g2EqTab {z : C2} (hz : z.val M = 0) : ∀ (tab pt : List C2),
    Hs c M (g2EqTab z tab pt) (fun t => t.map (C2.val M) = (pt.map (C2.val M)).foldl eqStep2 (tab.map (C2.val M)))
  | tab, [] => hs_pure rfl
  | tab, r :: rs => hs_bind (hs_g2EqStep hz tab r) fun t ht => hs_mono (hs_g2EqTab hz t rs) fun u hu => by
    rw [hu, ht]; rfl

/-! ## The sumcheck rounds -/

/-- The next claim of a round: `polyEval [c₀, claim + c₂, c₂] r`. -/
def scStep2 (c0 c2 r claim : FE2) : FE2 := ((claim + c2) + c2 * r) * r + c0

theorem hs_scRound2 (q : Nat) (claim : C2) :
    Hs c M (scRound2 q claim) (fun rc => rc.1 = ld2 (q + 5) ∧
      rc.2.val M = scStep2 ((ld2 q).val M) ((ld2 (q + 2)).val M) ((ld2 (q + 5)).val M) (claim.val M)) :=
  hs_bind (hs_g2Add claim (ld2 (q + 2))) fun c1 hc1 => hs_bind (hs_g2Mul _ _ c1) fun t ht =>
    hs_bind (hs_g2Mul t _ _) fun nc hnc => hs_pure ⟨rfl, by rw [hnc, ht, hc1, scStep2]; ring⟩

/-- `R` rounds' final claim from lane `q`, on the stream values `v`. -/
def scFold2 (v : Nat → FE2) : Nat → Nat → FE2 → FE2
  | 0, _, claim => claim
  | R + 1, q, claim => scFold2 v R (q + roundLanes2) (scStep2 (v q) (v (q + 2)) (v (q + 5)) claim)

/-- **`R` rounds**: the challenges are the stream values at the answer lanes, the final claim `scFold2`. -/
theorem hs_sc2 : ∀ (R q : Nat) (claim : C2),
    Hs c M (sc2 R q claim) (fun res => res.1 = (sc2Ans R q).map ld2 ∧
      res.2.val M = scFold2 (fun k => (ld2 k).val M) R q (claim.val M))
  | 0, q, claim => hs_pure ⟨rfl, rfl⟩
  | R + 1, q, claim => hs_bind (hs_scRound2 q claim) fun rc ⟨h1, h2⟩ =>
    hs_bind (hs_sc2 R (q + roundLanes2) rc.2) fun res ⟨e1, e2⟩ => hs_pure ⟨by
      rw [e1, h1]
      simp only [sc2Ans, List.range_succ_eq_map, List.map_cons, List.map_map, roundLanes2, Nat.mul_zero,
        Nat.add_zero, List.cons.injEq, true_and]
      exact List.map_congr_left fun k _ => by simp only [Function.comp_apply]; congr 1; omega,
      by rw [e2, h2]; rfl⟩

end Lvm.Q2
