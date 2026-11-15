-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): V_S's split region claims at S2GT (`LvmE2TV.regClaimsND`, weight
-- `affWD`) are the specification's (`LvmE2TProg.regClaimT`) on the stack (roll 11's `LvmTypedVEqForms.regClaim_rel`
-- at S2GT: the `r`-side at `E2`, the `X`-side at `E3`, the product in `Quad Ext3`).
import LvmE2TVKernF
import LvmE2VTwins
import LvmE2VSwitch
import LvmVEqRel

/-!
# The split region claims at S2GT

On a native instance whose shape check holds (`TNat.okB`) and whose regions are the layout's (`TNat.layOk`):

* `kc_wordW_sum`: `wordW z r = Σ_n eq(r, n)·eq(z, n)` in `Quad Ext3` for an `E3` point `r` no longer than `z`;
* `kc_region`: a region's `Σ_i eq(R, base + i)·eq(X, dst + i)` in `Quad Ext3` (the closed form of `affWD`'s
  term, `LvmTypedVEqForms.fm_region` with `wordW` for `eqEval`);
* **`regClaimD_rel`**: coordinate `h` of a region claim on the whole stack,
  `⟨⟨ν, 0⟩, affWD N s r_y h, (v_h)⟩.onStack`, is `regClaimT`'s claim `h` (`Σ_{y ∈ s} eq(r_y, y)_h·eq(X, off y)`,
  value `v_h`) at every point (`SCRel`); **`regClaimsND_rel`**: both claims, in order.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm Lvm.TypedV Lvm.VEq
open Lvm.Typed (YSrc yVars Lay)
open LeanVM.Parameters (E E2 E6 e2ToE6)
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_nil)
open Finset (range)
open Lvm.FE2 (toE2)

/-- Coordinate `h` of a `Quad Ext3` value (`false`: re, `true`: im). -/
def coordH (h : Bool) (w : E6) : E := if h then w.im else w.re

theorem coordH_false (w : E6) : coordH false w = w.re := rfl

theorem coordH_true (w : E6) : coordH true w = w.im := rfl

theorem coordH_add (h : Bool) (a b : E6) : coordH h (a + b) = coordH h a + coordH h b := by
  cases h <;> rfl

theorem coordH_zero (h : Bool) : coordH h 0 = 0 := by cases h <;> rfl

theorem coordH_list_sum {α : Type} (h : Bool) (L : List α) (f : α → E6) :
    coordH h (L.map f).sum = (L.map fun a ↦ coordH h (f a)).sum := by
  induction L with
  | nil => exact coordH_zero h
  | cons a L ih => rw [List.map_cons, List.sum_cons, coordH_add, ih, List.map_cons, List.sum_cons]

theorem coordH_fsum (h : Bool) (n : ℕ) (f : ℕ → E6) :
    coordH h (∑ i ∈ range n, f i) = ∑ i ∈ range n, coordH h (f i) := by
  induction n with
  | zero => simp only [Finset.sum_range_zero]; exact coordH_zero h
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, coordH_add, ih]

theorem coordH_C_mul (h : Bool) (a : E) (w : E6) : coordH h (algebraMap E E6 a * w) = a * coordH h w := by
  rw [mul_comm, ← Lvm.Quad.C_eq_algebraMap]
  cases h
  · rw [coordH_false, coordH_false, Lvm.Quad.re_mul_C, mul_comm]
  · rw [coordH_true, coordH_true, Lvm.Quad.im_mul_C, mul_comm]

theorem coordH_e2_mul (h : Bool) (y : E2) (a : E) : coordH h (e2ToE6 y * algebraMap E E6 a) = coordE h y * a := by
  rw [← Lvm.Quad.C_eq_algebraMap]
  cases h
  · rw [coordH_false, Lvm.Quad.re_mul_C, E2V.e2ToE6_re]; rfl
  · rw [coordH_true, Lvm.Quad.im_mul_C, E2V.e2ToE6_im]; rfl

/-- **`wordW` as a sum** for an `E3` point no longer than the `E2` point. -/
theorem kc_wordW_sum : ∀ (z : List E2) (r : List E), r.length ≤ z.length →
    E2V.wordW z r = ∑ n ∈ range (2 ^ z.length), algebraMap E E6 (eqAt r n) * e2ToE6 (E2V.eqAtF z n)
  | [], [], _ => by simp [E2V.wordW_nil, E2V.eqAtF]
  | [], _ :: _, h => absurd h (by simp)
  | zl :: z, [], _ => by
    have h1 : E2V.wordW (zl :: z) [] = 1 := by
      unfold E2V.wordW; rw [List.zipWith_nil_right, List.foldl_nil]
    rw [h1]
    simp only [eqAt_nil, map_one, one_mul]
    rw [← map_sum, E2V.sum_eqAtF, map_one]
  | zl :: z, rl :: r, h => by
    rw [E2V.wordW_cons, kc_wordW_sum z r (by simpa using h), List.length_cons, E2V.sum_range_pow_succ,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [E2V.eqAt_two_mul, E2V.eqAt_two_mul_add_one, E2V.eqAtF_two_mul, E2V.eqAtF_two_mul_add_one]
    simp only [map_mul, map_add, map_one]
    ring

/-- **A region's `Σ_i eq(R, base + i)·eq(X, dst + i)`** in `Quad Ext3` (the closed form of `affWD`'s term). -/
theorem kc_region (R : List E2) (X : List E) (b d l ν : ℕ) (hR : l ≤ R.length) (hb : b % 2 ^ l = 0)
    (hd : d % 2 ^ l = 0) (hdν : d + 2 ^ l ≤ 2 ^ ν) :
    ∑ i ∈ range (2 ^ l), e2ToE6 (E2V.eqAtF R (b + i)) * algebraMap E E6 (eqAt X (d + i)) =
      algebraMap E E6 (eqAt (X.drop ν) 0) * (e2ToE6 (E2V.eqAtF (R.drop l) (b >>> l)) *
        E2V.wordW (R.take l) ((X.take ν).take l) * algebraMap E E6 (eqAt ((X.take ν).drop l) (d >>> l))) := by
  have hlν : l ≤ ν := by
    have : 2 ^ l ≤ 2 ^ ν := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have e : ∀ i ∈ range (2 ^ l), e2ToE6 (E2V.eqAtF R (b + i)) * algebraMap E E6 (eqAt X (d + i)) =
      e2ToE6 (E2V.eqAtF (R.drop l) (b >>> l)) * algebraMap E E6 (eqAt (X.drop l) (d >>> l)) *
        (algebraMap E E6 (eqAt (X.take l) i) * e2ToE6 (E2V.eqAtF (R.take l) i)) := by
    intro i hi
    rw [kf_eqAtF_split R b l i hb (Finset.mem_range.1 hi), fm_eqAt_split X d l i hd (Finset.mem_range.1 hi),
      map_mul, map_mul]
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have hRl : (R.take l).length = l := List.length_take_of_le hR
  have hs := kc_wordW_sum (R.take l) (X.take l) (by simp [hRl])
  rw [hRl] at hs
  rw [← hs, List.take_take, min_eq_left hlν, fm_eqAt_drop X d l ν hlν hdν, map_mul]
  ring

/-- `toE6` of `FE6`'s coordinatewise sum fold. -/
theorem kc_toE6_fold {α : Type} (L : List α) (T : α → FE6) (acc : FE6) :
    E2V.FE6.toE6 (L.foldl (fun (acc : FE6) t ↦ ⟨acc.re + (T t).re, acc.im + (T t).im⟩) acc) =
      E2V.FE6.toE6 acc + (L.map fun t ↦ E2V.FE6.toE6 (T t)).sum := by
  induction L generalizing acc with
  | nil => simp
  | cons t L ih => rw [List.foldl_cons, ih, E2V.toE6_add, List.map_cons, List.sum_cons, add_assoc]

/-- **`affWD` over `E3`**: coordinate `h` of the `Quad Ext3` sum of its regions' terms. -/
theorem kc_affWD (N : TNatT) (s : YSrc) (r : List FE2) (h : Bool) (Y : List FE) :
    FE.toExt3 (affWD N s r h Y) = coordH h ((N.toN.regsOf s).map fun g ↦
      e2ToE6 (E2V.eqAtF ((r.map toE2).drop g.log) (g.base >>> g.log)) *
        E2V.wordW ((r.map toE2).take g.log) ((Y.map FE.toExt3).take g.log) *
        algebraMap E E6 (eqAt ((Y.map FE.toExt3).drop g.log) (g.dst >>> g.log))).sum := by
  unfold affWD
  simp only [List.foldl_map]
  have hT := kc_toE6_fold (N.toN.regsOf s) (fun g ↦ FE6.mul (FE6.mul (FE6.ofE2 (hiWG r g.log g.base))
    (wordWD (r.take g.log) (Y.take g.log))) (FE6.ofE (eqAtF (Y.drop g.log) (g.dst >>> g.log)))) ⟨0, 0⟩
  have e : ∀ w : FE6, FE.toExt3 (if h then w.im else w.re) = coordH h (E2V.FE6.toE6 w) := by
    intro w; cases h <;> rfl
  rw [e, hT, E2V.toE6_zero, zero_add]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun g _ ↦ ?_)
  rw [E2V.toE6_mul, E2V.toE6_mul, E2V.toE6_ofE2, E2V.wordWD_twin, E2V.toE6_ofE, hiWG, E2V.toE2_eqAtF,
    fm_toExt3_eqAtF, ← Lvm.Quad.C_eq_algebraMap, List.map_take, List.map_take, List.map_drop, List.map_drop]

variable (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)

/-- **Coordinate `h` of a split region claim on the whole stack is `regClaimT`'s claim `h`** (`ν` the stack's
variables; every region of `s` aligned and inside the stack). -/
theorem regClaimD_rel (nuMain nuRec : ℕ) (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true)
    (s : YSrc) (ν : ℕ) (hν : ∀ g ∈ N.toN.regsOf s, g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ ν)
    (ry : List FE2) (hry : ry.length = yVars) (v : FE2) (h : Bool) :
    SCRel (⟨⟨ν, 0⟩, affWD N s ry h, FE.ofK (if h then v.im else v.re)⟩ : BlockClaim).onStack
      (fun X ↦ regSumW (N.toN.inst Q lay) (fun s' ↦ s' == s)
        (fun y ↦ coordE h (E2V.eqAtF (ry.map toE2) y) * eqAt X (N.toN.off y)), coordE h (toE2 v)) := by
  obtain ⟨hreg, -, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  refine ⟨?_, fun xs ↦ ?_⟩
  · cases h <;> (show _ = FE.toExt3 (FE.ofK _); rw [FE.toExt3_ofK]; rfl)
  simp only [BlockClaim.onStack]
  rw [fm_eqAbove0, FE.toExt3_mul, fm_toExt3_eqAtF, kc_affWD, kf_regSumW N.toN Q lay hlay, ← coordH_C_mul,
    ← List.sum_map_mul_left, coordH_list_sum, TNat.regsOf, fm_sum_filter]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hgs : (g.src == s) = true
  · simp only [hgs, ite_true]
    obtain ⟨hd1, hd2⟩ := hν g (List.mem_filter.2 ⟨hg, hgs⟩)
    obtain ⟨hb1, hb2, -⟩ := hreg g hg
    have hl : g.log ≤ (ry.map toE2).length := by
      have : 2 ^ g.log ≤ 2 ^ yVars := by omega
      rw [List.length_map, hry]
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [fm_off N.toN hpw g hg i (Finset.mem_range.1 hi),
      ← coordH_e2_mul], ← coordH_fsum, kc_region _ _ g.base g.dst g.log ν hl hb1 hd1 hd2, List.map_drop,
      List.map_take, List.take_take, min_eq_left (show g.log ≤ ν by
        have : 2 ^ g.log ≤ 2 ^ ν := by omega
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this)]
  · simp only [hgs, Bool.false_eq_true, ite_false]

/-- **Both split claims of a region claim** (re then im) are `regClaimT`'s, in order. -/
theorem regClaimsND_rel (p : Params) (nuRec : ℕ) (hok : N.toN.okB p.nuMain nuRec = true)
    (hlay : N.toN.layOk lay = true) (s : YSrc)
    (hν : ∀ g ∈ N.toN.regsOf s, g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ p.nuMain)
    (ry : List FE2) (hry : ry.length = yVars) (v : FE2) :
    List.Forall₂ (fun a b ↦ a.1 = .main ∧ a.2.2 = 0 ∧ SCRel a.2.1.onStack b) (regClaimsND N p s ry v)
      (regClaimT (N.toN.inst Q lay) s N.toN.off (ry.map toE2) (toE2 v)) := by
  unfold regClaimsND regClaimT
  simp only [List.map_cons, List.map_nil]
  exact .cons ⟨rfl, rfl, regClaimD_rel N Q lay _ nuRec hok hlay s _ hν ry hry v false⟩
    (.cons ⟨rfl, rfl, regClaimD_rel N Q lay _ nuRec hok hlay s _ hν ry hry v true⟩ .nil)

end Lvm.E2T
