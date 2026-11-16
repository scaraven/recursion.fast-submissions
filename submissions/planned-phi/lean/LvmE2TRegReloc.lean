-- New for lvm2 U-TAPE (UT-V, UTAPE-STMT 22; moved from `LvmS2GTClaims` with their texts unchanged, `σ′`'s
-- relocation generalised over the stream block's offset): the typed phases' split region claims at `E2` against the
-- specification's, generic in the stage (S2GT, S2GU).
import LvmE2VDecClaims
import LvmE2TVClaim
import LvmE2TVEq

/-!
# The typed phases' split region claims at `E2`

* `tail_affWD`: a committed, `KS` or `σ′` split region claim has no tail (`tail_affW` at `E2`, through `kc_affWD`).
* `vrel_regND`: both split claims of such a region claim, with their tails, against `regClaimT`'s (`regClaimD_rel`).
* `regClaimT_relocSAt`: `σ′`'s split claims on the stream block at `S` are its `C_rec` claims relocated
  (`regClaim_relocS` at `E2`); `regClaimT_relocS` at M′'s `S`.
* `relocOK_relay`: the relayout's block moves onto `S`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.TypedV Lvm.Typed
open Lvm.E2T (TNatT TRefHypT TRelTT affWD regClaimsND typedClaimsND regClaimT typedClaimsT coordH coordE)
open LeanVM.Protocol.KeccakGkr (eqAt)

/-! ## The split region claims -/

/-- **A committed, `KS` or `σ′` split region claim has no tail** (`okB`: their targets lie in `[2^22, 2^ν)`). -/
theorem tail_affWD (N : TNatT) (nuRec : ℕ) (hok : N.toN.okB CMain.nu20 nuRec = true) (s : YSrc)
    (hs : s = .com ∨ s = .ks ∨ s = .sigma) (ry : List FE2) (h : Bool) (v : FE) :
    Shape.tailValueF (⟨⟨CMain.nu20, 0⟩, affWD N s ry h, v⟩ : BlockClaim).onStack.1 = 0 := by
  obtain ⟨hreg, -, -⟩ := fm_ok N.toN CMain.nu20 nuRec hok
  unfold Shape.tailValueF
  refine Finset.sum_eq_zero fun a ha ↦ ?_
  have ha' : a < 2 ^ 22 := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  have hx : (Shape.boolPointF CMain.nu20 a).take CMain.nu20 = Shape.boolPointF CMain.nu20 a :=
    List.take_of_length_le (by simp [Shape.boolPointF])
  have h0 : affWD N s ry h (Shape.boolPointF CMain.nu20 a) = 0 := by
    refine FE.toExt3_injective ?_
    rw [E2T.kc_affWD, FE.toExt3_zero, List.sum_eq_zero, E2T.coordH_zero]
    intro t ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
    obtain ⟨hgr, hgs⟩ := List.mem_filter.1 hg
    have hsrc : g.src = .com ∨ g.src = .ks ∨ g.src = .sigma := by
      rcases hs with rfl | rfl | rfl <;> simp_all
    obtain ⟨-, -, hc, -, -⟩ := hreg g hgr
    obtain ⟨-, hd2, hd3⟩ := hc hsrc
    have hd4 : g.dst + 2 ^ g.log ≤ 2 ^ 23 := le_trans hd3 (min_le_left _ _)
    have hl : g.log ≤ 22 := by
      have : 2 ^ g.log ≤ 2 ^ 22 := by (clear * - hd2 hd4; omega)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have hpos : 0 < 2 ^ g.log := by positivity
    have hd5 : g.dst / 2 ^ 22 = 1 := Nat.div_eq_of_lt_le (by omega) (by (clear * - hd4 hpos; omega))
    have hz : eqAt (((Shape.boolPointF CMain.nu20 a).map FE.toExt3).drop g.log) (g.dst >>> g.log) = 0 := by
      rw [← List.map_drop, ← fm_toExt3_eqAtF, fm_eqAtF_zero _ _ (22 - g.log), FE.toExt3_zero]
      · simp only [Shape.boolPointF, List.length_drop, List.length_map, List.length_range, CMain.nu20]
        (clear * - hl; omega)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' hl]
        simp [Shape.boolPointF, Nat.testBit_lt_two_pow ha']
      · rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' hl, Nat.testBit_eq_decide_div_mod_eq, hd5]
        rfl
    rw [hz, map_zero, mul_zero]
  simp only [BlockClaim.onStack]
  rw [hx, h0, mul_zero, zero_mul]

/-- **Both split claims of a committed, `KS` or `σ′` region claim, with their tails**, against `regClaimT`'s. -/
theorem vrel_regND {s : Bool} (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (nuRec : ℕ)
    (hok : N.toN.okB 23 nuRec = true) (hlay : N.toN.layOk lay = true) (src : YSrc)
    (hsrc : src = .com ∨ src = .ks ∨ src = .sigma) (ry : List FE2) (hry : ry.length = yVars) (v : FE2) :
    List.Forall₂ (VRel s) (regClaimsND N P20 src ry v)
      (regClaimT (N.inst Q lay) src N.toN.off (ry.map toE2) (toE2 v)) := by
  have hν := regsOf_dst hok src hsrc
  unfold regClaimsND regClaimT
  rw [nuMain_P20]
  simp only [List.map_cons, List.map_nil]
  exact .cons (vrel_of (E2T.regClaimD_rel N Q lay 23 nuRec hok hlay src 23 hν ry hry v false)
      fun _ ↦ ⟨inStack_full, (tail_affWD N nuRec hok src hsrc ry false _).symm⟩)
    (.cons (vrel_of (E2T.regClaimD_rel N Q lay 23 nuRec hok hlay src 23 hν ry hry v true)
      fun _ ↦ ⟨inStack_full, (tail_affWD N nuRec hok src hsrc ry true _).symm⟩) .nil)

/-- **`σ′`'s split claims on the stream block at `S` are its `C_rec` claims relocated** (`regClaim_relocS` at `E2`;
`S` a multiple of `2^19`, `σ′`'s regions in `[S, S + 2^19)`: `SigInSL S`). -/
theorem regClaimT_relocSAt (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (nuMain nuRec : ℕ)
    (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true) (S : ℕ) (hS : S % 2 ^ 19 = 0)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → S ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ S + 2 ^ 19) (r : List E2) (v : E2) :
    regClaimT (N.inst Q lay) .sigma N.toN.off r v =
      (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW r v).map (relocSAt S) := by
  obtain ⟨-, -, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  unfold regClaimT
  rw [List.map_map]
  refine List.map_congr_left fun h _ ↦ Prod.ext (funext fun X ↦ ?_) rfl
  show E2T.regSumW (N.inst Q lay) (fun s' ↦ s' == .sigma)
      (fun y ↦ coordE h (E2V.eqAtF r y) * eqAt X (N.toN.off y)) =
    (⟨19, S⟩ : VPlacement).eqAbove X * E2T.regSumW (N.inst Q lay) (fun s' ↦ s' == .sigma)
      (fun y ↦ coordE h (E2V.eqAtF r y) * eqAt (X.take 19) (N.toN.off y % 2 ^ 19))
  rw [E2T.kf_regSumWT N Q lay hlay, E2T.kf_regSumWT N Q lay hlay, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hgs : (g.src == .sigma) = true
  · simp only [hgs, ite_true]
    obtain ⟨h1, h2⟩ := hσ g hg (by simpa using hgs)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [eqAt_take19_mod, fm_off N.toN hpw g hg i hi', eqAt_relocAt S X (g.dst + i) ?_]
    · ring
    · simp only [Nat.shiftRight_eq_div_pow]
      have : 0 < 2 ^ g.log := by positivity
      norm_num at hS ⊢
      omega
  · simp [hgs]

/-- **`σ′`'s split claims on `S` are its `C_rec` claims relocated** (`regClaimT_relocSAt` at M′'s `S`). -/
theorem regClaimT_relocS (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (nuMain nuRec : ℕ)
    (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true) (hσ : SigInS N.toN) (r : List E2)
    (v : E2) :
    regClaimT (N.inst Q lay) .sigma N.toN.off r v =
      (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW r v).map relocS :=
  regClaimT_relocSAt N Q lay nuMain nuRec hok hlay CMain.sOff20 (by decide) hσ r v

/-- The relayout's point claim's block (`C_rec`'s whole cube) moves onto `S` (`relocS_sum`'s conditions). -/
theorem relocOK_relay (z : List E2) : RelocOK (1, ⟨relayRounds, 0⟩, z) := by
  unfold RelocOK
  dsimp only
  decide

end Lvm.VEq
