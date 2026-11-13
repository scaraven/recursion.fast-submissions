-- New for lvm2 (roll 8 = B1, wave L, L-C): V_S's closed forms of the typed phases (`LvmTypedV`: `affW`,
-- `virtEF`, `relayKernF`) are the specification's region sums (`LvmTypedSpec`: `regClaim`, `virtE`,
-- `relayKern`) on the instance `N.inst Q lay`, through `FE.toExt3`.
import LvmTypedVInst
import LvmTypedVEqKern
import LvmVEqClaims
import LvmShape

/-!
# The typed phases' closed forms

On a native instance `N` whose shape check holds (`TNat.okB`) and whose regions are the layout's
(`TNat.layOk`), with `Ti = N.inst Q lay`:

* **`regClaim_rel`**: a region claim on the whole stack, `⟨⟨ν, 0⟩, affW N s r_y, v⟩.onStack`, is `regClaim Ti s
  N.off` (`Σ_{y ∈ s} eq(r_y, y)·eq(X, off y)`) at every point (`SCRel`);
* **`tail_affW`**: a committed or `KS` region claim has no mass on `D`'s tail (its words lie from `2^22` on);
* **`virtEF_rel`**: `virtEF` is `virtE` (the `PUB` region by its multilinear extension, the `1` region by its
  weight; the `QLT` part is `0`: `TNat.inst`'s `qltV` is `0`, and `okB` admits no `QLT` region);
* **`relayKernF_rel`**: `relayKernF` is `relayKern` (the long-division automaton and the comparator,
  `LvmTypedVEqKern`).

The helpers (`fm_*`): region lookup under `okB` (`fm_ok`, `fm_off`), `regSum` as a sum over the native regions
(`fm_regSum`), the split of an aligned index (`fm_eqAt_split`) and a region's cube sum (`fm_region`).
-/

set_option autoImplicit false

namespace Lvm.TypedV

open Lvm Lvm.Typed Lvm.VEq

section FmHelpers

open LeanVM.Parameters (E)
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons eqAt_nil eqAt_mod eqAt_append sum_eqAt sum_cube_succ)
open Finset (range)

/-- `eqAtF` maps to `eqAt`. -/
theorem fm_toExt3_eqAtF : ∀ (pt : List FE) (w : ℕ), FE.toExt3 (eqAtF pt w) = eqAt (pt.map FE.toExt3) w
  | [], _ => FE.toExt3_one
  | r :: rs, w => by
    rw [eqAtF, List.map_cons, eqAt_cons, FE.toExt3_mul, fm_toExt3_eqAtF rs, apply_ite FE.toExt3,
      FE.toExt3_add, FE.toExt3_one]

/-- An aligned index splits: the low `l` bits are `i`, the high ones `b >>> l` (any length of `X`). -/
theorem fm_eqAt_split (X : List E) (b l i : ℕ) (hb : b % 2 ^ l = 0) (hi : i < 2 ^ l) :
    eqAt X (b + i) = eqAt (X.take l) i * eqAt (X.drop l) (b >>> l) := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  conv_lhs => rw [← List.take_append_drop l X]
  rw [eqAt_append]
  congr 1
  · rw [eqAt_mod, eqAt_mod _ i]
    have hd : 2 ^ (X.take l).length ∣ 2 ^ l := Nat.pow_dvd_pow 2 (by simp)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_trans hd (dvd_mul_right _ _)), zero_add, Nat.mod_mod]
  · rcases le_or_gt l X.length with hl | hl
    · rw [List.length_take_of_le hl, Nat.shiftRight_eq_div_pow, Nat.mul_add_div (by positivity),
        Nat.div_eq_of_lt hi, add_zero, Nat.mul_div_cancel_left _ (by positivity)]
    · rw [List.drop_of_length_le hl.le, eqAt_nil, eqAt_nil]

/-- `eqEval` over `E` as a product. -/
theorem fm_eqEval_prod (l r : List E) :
    LeanVM.Protocol.Verifier.eqEval l r = (List.zipWith (fun x z ↦ 1 + x + z) l r).prod := by
  unfold LeanVM.Protocol.Verifier.eqEval; rw [List.prod_eq_foldl]

/-- The cube sum of two `eq` weights is `eqEval` (`c` no longer than `a`; characteristic two). -/
theorem fm_sum_eqAt_mul : ∀ (a c : List E), c.length ≤ a.length →
    ∑ i ∈ range (2 ^ a.length), eqAt a i * eqAt c i = LeanVM.Protocol.Verifier.eqEval a c
  | [], [], _ => by simp [fm_eqEval_prod]
  | [], _ :: _, h => by simp at h
  | r :: a, [], _ => by
    simp only [eqAt_nil, mul_one, sum_eqAt, fm_eqEval_prod, List.zipWith_nil_right, List.prod_nil]
  | r :: a, x :: c, h => by
    rw [List.length_cons, sum_cube_succ, fm_eqEval_prod, List.zipWith_cons_cons, List.prod_cons,
      ← fm_eqEval_prod, ← fm_sum_eqAt_mul a c (by simpa using h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [eqAt_cons]
    have h1 : 2 * w % 2 = 0 := by omega
    have h2 : (2 * w + 1) % 2 = 1 := by omega
    have h3 : 2 * w / 2 = w := by omega
    have h4 : (2 * w + 1) / 2 = w := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false]
    linear_combination (r * x * eqAt a w * eqAt c w) * (CharTwo.two_eq_zero : (2 : E) = 0)

/-- The high part of a target inside a cube of `ν` coordinates. -/
theorem fm_eqAt_drop (X : List E) (d l ν : ℕ) (hlν : l ≤ ν) (hdν : d + 2 ^ l ≤ 2 ^ ν) :
    eqAt (X.drop l) (d >>> l) = eqAt ((X.take ν).drop l) (d >>> l) * eqAt (X.drop ν) 0 := by
  rcases le_or_gt ν X.length with hX | hX
  · conv_lhs => rw [← List.take_append_drop ν X]
    rw [List.drop_append_of_le_length (by simp [hX, hlν]), eqAt_append]
    congr 1
    rw [List.length_drop, List.length_take_of_le hX, Nat.shiftRight_eq_div_pow]
    congr 1
    refine Nat.div_eq_of_lt ((Nat.div_lt_iff_lt_mul (by positivity)).2 ?_)
    rw [← pow_add, Nat.sub_add_cancel hlν]
    have : 0 < 2 ^ l := by positivity
    omega
  · rw [List.take_of_length_le hX.le, List.drop_of_length_le hX.le, eqAt_nil, mul_one]

/-- **A region's sum of `eq(r, base + i)·eq(X, dst + i)`** (the closed form of `affW`'s term). -/
theorem fm_region (R X : List E) (b d l ν : ℕ) (hR : l ≤ R.length) (hb : b % 2 ^ l = 0)
    (hd : d % 2 ^ l = 0) (hdν : d + 2 ^ l ≤ 2 ^ ν) :
    ∑ i ∈ range (2 ^ l), eqAt R (b + i) * eqAt X (d + i) =
      eqAt (X.drop ν) 0 * (eqAt (R.drop l) (b >>> l) *
        LeanVM.Protocol.Verifier.eqEval (R.take l) ((X.take ν).take l) *
          eqAt ((X.take ν).drop l) (d >>> l)) := by
  have hlν : l ≤ ν := by
    have : 2 ^ l ≤ 2 ^ ν := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have e : ∀ i ∈ range (2 ^ l), eqAt R (b + i) * eqAt X (d + i) =
      eqAt (R.drop l) (b >>> l) * eqAt (X.drop l) (d >>> l) * (eqAt (R.take l) i * eqAt (X.take l) i) := by
    intro i hi
    rw [fm_eqAt_split R b l i hb (Finset.mem_range.1 hi), fm_eqAt_split X d l i hd (Finset.mem_range.1 hi)]
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have hRl : (R.take l).length = l := List.length_take_of_le hR
  have hs := fm_sum_eqAt_mul (R.take l) (X.take l) (by simp [hRl])
  rw [hRl] at hs
  rw [hs, List.take_take, min_eq_left hlν, fm_eqAt_drop X d l ν hlν hdν]
  ring

/-- **What `okB` gives** per region, `S_flat`'s one region, and the adjacent-pairs order. -/
theorem fm_ok (N : TNat) (a c : ℕ) (h : N.okB a c = true) :
    (∀ g ∈ N.regs, g.base % 2 ^ g.log = 0 ∧ g.base + 2 ^ g.log ≤ 2 ^ yVars ∧
      (g.src = .com ∨ g.src = .ks →
        g.dst % 2 ^ g.log = 0 ∧ 2 ^ 22 ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ min (2 ^ a) (7 * 2 ^ 20)) ∧
      (g.src = .pub → g.log = 10 ∧ g.dst = 0) ∧ (g.src = .one → g.log = 0)) ∧
    (∃ g, N.regsOf .sflat = [g] ∧ g.log = posBits ∧ g.dst = 0) ∧
    (∀ x ∈ N.regs.zip N.regs.tail, x.1.base + 2 ^ x.1.log ≤ x.2.base) := by
  simp only [TNat.okB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, h7⟩ := h
  refine ⟨fun g hg ↦ ?_, ?_, fun x hx ↦ by simpa using h7 x hx⟩
  · obtain ⟨⟨hb1, hb2⟩, hm⟩ := h1 g hg
    refine ⟨by simpa using hb1, by simpa using hb2, ?_⟩
    rcases g with ⟨b, l, src, d⟩
    cases src <;> simp_all
  · obtain ⟨g, hg⟩ := List.length_eq_one_iff.1 (by simpa using h2)
    refine ⟨g, hg, ?_⟩
    have := h3 g (by simp [hg])
    simpa using this

/-- Adjacent pairs ordered: all pairs ordered. -/
theorem fm_pairwise : ∀ L : List NReg, (∀ x ∈ L.zip L.tail, x.1.base + 2 ^ x.1.log ≤ x.2.base) →
    L.Pairwise fun a b ↦ a.base + 2 ^ a.log ≤ b.base
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: L, h => by
    have hab : a.base + 2 ^ a.log ≤ b.base := h (a, b) (by simp)
    have ih := fm_pairwise (b :: L) fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    refine List.Pairwise.cons (fun c hc ↦ ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · have := (List.pairwise_cons.1 ih).1 c hc
      have : 0 < 2 ^ b.log := by positivity
      omega

/-- In ordered regions, the first region holding `base + i` of `g` is `g`. -/
theorem fm_find (L : List NReg) (hL : L.Pairwise fun a b ↦ a.base + 2 ^ a.log ≤ b.base) (g : NReg)
    (hg : g ∈ L) (i : ℕ) (hi : i < 2 ^ g.log) :
    L.find? (fun r ↦ decide (r.base ≤ g.base + i ∧ g.base + i < r.base + 2 ^ r.log)) = some g := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.find?_cons_of_pos (by simp [hi])
    · have := hL.1 g hg'
      rw [List.find?_cons_of_neg (by simp; omega)]
      exact ih hL.2 hg'

/-- **A region's words have their region's targets.** -/
theorem fm_off (N : TNat) (hL : N.regs.Pairwise fun a b ↦ a.base + 2 ^ a.log ≤ b.base) (g : NReg)
    (hg : g ∈ N.regs) (i : ℕ) (hi : i < 2 ^ g.log) : N.off (g.base + i) = g.dst + i := by
  unfold TNat.off TNat.regAt
  rw [fm_find _ hL g hg i hi]
  exact congrArg (g.dst + ·) (Nat.add_sub_cancel_left ..)

/-- `regSum` on `N.inst` is a sum over the native regions. -/
theorem fm_regSum (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (hlay : N.layOk lay = true)
    (S : YSrc → Bool) (f : ℕ → E) (r : List E) :
    regSum (N.inst Q lay) S f r = (N.regs.map fun g ↦ if S g.src then
      ∑ i ∈ range (2 ^ g.log), eqAt r (g.base + i) * f (g.base + i) else 0).sum := by
  have hy : lay.yregs = N.regs.map fun r ↦ (⟨r.base, r.log, r.src⟩ : YReg) := by
    simpa [TNat.layOk] using hlay
  simp only [regSum, TNat.inst, hy, List.map_map, Function.comp_def, KG.list_sum_map_range]

/-- A filtered sum is a sum with an indicator. -/
theorem fm_sum_filter {α M : Type} [AddCommMonoid M] (L : List α) (p : α → Bool) (f : α → M) :
    ((L.filter p).map f).sum = (L.map fun g ↦ if p g then f g else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : p a <;> simp [h, ih]

/-- A left fold adding terms is the sum. -/
theorem fm_foldl {α : Type} (L : List α) (F : FE → α → FE) (T : α → FE) (h : ∀ acc g, F acc g = acc + T g)
    (a : FE) : L.foldl F a = a + (L.map T).sum := by
  induction L generalizing a with
  | nil => simp
  | cons g L ih => rw [List.foldl_cons, ih, h, List.map_cons, List.sum_cons, add_assoc]

/-- `toExt3` of a sum. -/
theorem fm_toExt3_sum {α : Type} (L : List α) (f : α → FE) :
    FE.toExt3 (L.map f).sum = (L.map fun g ↦ FE.toExt3 (f g)).sum := by
  rw [← FE.ringEquivExt3_apply, map_list_sum, List.map_map]; rfl

/-- `affW` is the sum of its regions' terms. -/
theorem fm_affW (N : TNat) (s : YSrc) (r X : List FE) :
    affW N s r X = ((N.regsOf s).map fun g ↦ hiW r g.log g.base * eqEval (r.take g.log) (X.take g.log) *
      eqAtF (X.drop g.log) (g.dst >>> g.log)).sum := by
  unfold affW
  simp only [List.foldl_map]
  rw [fm_foldl _ _ _ (fun _ _ ↦ rfl), zero_add]

/-- The stack's selector above `⟨ν, 0⟩`: `eq(X_{≥ν}, 0)`. -/
theorem fm_eqAbove0 (ν : ℕ) (xs : List FE) : (⟨ν, 0⟩ : Placement).eqAbove xs = eqAtF (xs.drop ν) 0 := by
  unfold Placement.eqAbove
  rw [← List.length_drop]
  generalize xs.drop ν = Y
  have hs : ∀ n, selectorPoint (0 >>> ν) n = List.replicate n 0 := by
    intro n
    simp only [selectorPoint, Nat.zero_shiftRight, Nat.zero_mod, Shape.eOfNat_zero, List.map_const',
      List.length_range]
  rw [hs]
  induction Y with
  | nil => rfl
  | cons y Y ih =>
    rw [List.length_cons, List.replicate_succ, Shape.eqEval_cons, ih, eqAtF]
    simp

/-- A region family with one region of `s`: its sum is that region's. -/
theorem fm_regSum_single (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (hlay : N.layOk lay = true)
    (s : YSrc) (g : NReg) (hg : N.regsOf s = [g]) (f : ℕ → E) (r : List E) :
    regSum (N.inst Q lay) (fun s' ↦ s' == s) f r =
      ∑ i ∈ range (2 ^ g.log), eqAt r (g.base + i) * f (g.base + i) := by
  rw [fm_regSum N Q lay hlay]
  have := fm_sum_filter N.regs (fun g ↦ g.src == s)
    (fun g ↦ ∑ i ∈ range (2 ^ g.log), eqAt r (g.base + i) * f (g.base + i))
  rw [show N.regs.filter (fun g ↦ g.src == s) = [g] from hg] at this
  simpa using this.symm

/-- `eqAtF` vanishes where the point is `0` and the index's bit is `1`. -/
theorem fm_eqAtF_zero : ∀ (x : List FE) (w j : ℕ), j < x.length → x.getD j 0 = 0 → w.testBit j = true →
    eqAtF x w = 0
  | [], _, _, h, _, _ => absurd h (by simp)
  | r :: rs, w, 0, _, hr, hw => by
    rw [Nat.testBit_zero, decide_eq_true_eq] at hw
    simp only [List.getD_cons_zero] at hr
    rw [eqAtF, ite_eq_left hw, hr, zero_mul]
  | r :: rs, w, j + 1, hj, hr, hw => by
    rw [Nat.testBit_succ] at hw
    rw [eqAtF, fm_eqAtF_zero rs (w / 2) j (by simpa using hj) (by simpa using hr) hw, mul_zero]

/-- `mleK` over `E`. -/
theorem fm_mleK (log : ℕ) (v : ℕ → FK) (pt : List FE) (hpt : log ≤ pt.length) :
    FE.toExt3 (mleK log v pt) =
      ∑ i ∈ range (2 ^ log), FE.toExt3 (FE.ofK (v i)) * eqAt ((pt.take log).map FE.toExt3) i := by
  unfold mleK
  dsimp only
  rw [fm_foldl _ _ (fun i ↦ FE.smulBase (v i) ((eqKernelA (pt.take log)).getD i 0)) (fun _ _ ↦ rfl),
    zero_add, fm_toExt3_sum, KG.list_sum_map_range]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [FE.smulBase_eq_mul, FE.toExt3_mul, getD_eqKernelA, ← getD_map_toExt3, map_eqKernel,
    LeanVM.Protocol.KeccakGkr.eqKernel_getD, ite_eq_left]
  simpa [List.length_take, hpt] using Finset.mem_range.1 hi

/-- `toExt3` of a `sumE` over a range. -/
theorem fm_toExt3_sumE_range (n : ℕ) (f : ℕ → FE) :
    FE.toExt3 (sumE ((List.range n).map f)) = ∑ i ∈ range n, FE.toExt3 (f i) := by
  rw [toExt3_sumE, LeanVM.Protocol.Whir.Complete.sumE_eq, List.map_map, KG.list_sum_map_range]; rfl

/-- `toExt3` of a `sumE` over the range's tail from `c`. -/
theorem fm_toExt3_sumE_filter (n c : ℕ) (f : ℕ → FE) :
    FE.toExt3 (sumE (((List.range n).filter fun i ↦ decide (c ≤ i)).map f)) =
      ∑ i ∈ Finset.Ico c n, FE.toExt3 (f i) := by
  rw [toExt3_sumE, LeanVM.Protocol.Whir.Complete.sumE_eq, List.map_map, fm_sum_filter,
    KG.list_sum_map_range]
  simp only [Function.comp_def, decide_eq_true_eq]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [and_comm]

/-- A stream position's `C_rec` word splits into its row (`i / 17`) and its lane (`i mod 17`). -/
theorem fm_sflat (R : List E) (i : ℕ) (hi : i < sPos) :
    eqAt R (sflatWord i) = eqAt (R.take recRowBits) (i / sLanes) * eqAt (R.drop recRowBits) (i % sLanes) := by
  rw [sflatWord, ite_eq_left hi, fm_eqAt_split R _ recRowBits _ (Nat.mul_mod_left _ _)]
  · rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by positivity)]
  · exact (Nat.div_lt_iff_lt_mul (by norm_num [sLanes, recStreamCols])).2 (by rw [mul_comm]; exact hi)

end FmHelpers

variable (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay)

/-- **A region claim on the whole stack is the specification's region claim** (`ν` the stack's variables;
every region of `s` aligned and inside the stack). -/
theorem regClaim_rel (nuMain nuRec : ℕ) (hok : N.okB nuMain nuRec = true) (hlay : N.layOk lay = true)
    (s : YSrc) (ν : ℕ) (hν : ∀ g ∈ N.regsOf s, g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ ν)
    (ry : List FE) (hry : ry.length = yVars) (v : FE) :
    SCRel (⟨⟨ν, 0⟩, affW N s ry, v⟩ : BlockClaim).onStack
      (regClaim (N.inst Q lay) s N.off (ry.map FE.toExt3) (FE.toExt3 v)) := by
  obtain ⟨hreg, -, hsort⟩ := fm_ok N nuMain nuRec hok
  have hpw := fm_pairwise N.regs hsort
  refine ⟨rfl, fun xs ↦ ?_⟩
  simp only [regClaim, BlockClaim.onStack]
  rw [fm_regSum N Q lay hlay, FE.toExt3_mul, fm_affW, fm_toExt3_sum, ← List.sum_map_mul_left, TNat.regsOf,
    fm_sum_filter]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hgs : (g.src == s) = true
  · simp only [hgs, ite_true]
    obtain ⟨hd1, hd2⟩ := hν g (List.mem_filter.2 ⟨hg, hgs⟩)
    obtain ⟨hb1, hb2, -⟩ := hreg g hg
    have hl : g.log ≤ (ry.map FE.toExt3).length := by
      have : 2 ^ g.log ≤ 2 ^ yVars := by omega
      rw [List.length_map, hry]
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [fm_off N hpw g hg i (Finset.mem_range.1 hi)],
      fm_region _ _ g.base g.dst g.log ν hl hb1 hd1 hd2, fm_eqAbove0, hiW]
    simp only [FE.toExt3_mul, fm_toExt3_eqAtF, toExt3_eqEval, List.map_drop, List.map_take]
  · simp [hgs]

/-- **A committed or `KS` region claim has no tail** (`okB`: their targets lie in `[2^22, 2^ν)`). -/
theorem tail_affW (nuRec : ℕ) (hok : N.okB CMain.nu20 nuRec = true) (s : YSrc) (hs : s = .com ∨ s = .ks)
    (ry : List FE) (v : FE) :
    Shape.tailValueF (⟨⟨CMain.nu20, 0⟩, affW N s ry, v⟩ : BlockClaim).onStack.1 = 0 := by
  obtain ⟨hreg, -, -⟩ := fm_ok N CMain.nu20 nuRec hok
  unfold Shape.tailValueF
  refine Finset.sum_eq_zero fun a ha ↦ ?_
  have ha' : a < 2 ^ 22 := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  have hx : (Shape.boolPointF CMain.nu20 a).take CMain.nu20 = Shape.boolPointF CMain.nu20 a :=
    List.take_of_length_le (by simp [Shape.boolPointF])
  simp only [BlockClaim.onStack]
  rw [hx, fm_affW, List.sum_eq_zero, mul_zero, zero_mul]
  intro t ht
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
  obtain ⟨hgr, hgs⟩ := List.mem_filter.1 hg
  have hsrc : g.src = .com ∨ g.src = .ks := by
    rcases hs with rfl | rfl <;> simp_all
  obtain ⟨-, -, hc, -, -⟩ := hreg g hgr
  obtain ⟨-, hd2, hd3⟩ := hc hsrc
  have hd4 : g.dst + 2 ^ g.log ≤ 2 ^ 23 := le_trans hd3 (min_le_left _ _)
  have hl : g.log ≤ 22 := by
    have : 2 ^ g.log ≤ 2 ^ 22 := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hpos : 0 < 2 ^ g.log := by positivity
  have hd5 : g.dst / 2 ^ 22 = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [fm_eqAtF_zero _ _ (22 - g.log), mul_zero]
  · simp only [Shape.boolPointF, List.length_drop, List.length_map, List.length_range, CMain.nu20]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' hl]
    simp [Shape.boolPointF, Nat.testBit_lt_two_pow ha']
  · rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' hl, Nat.testBit_eq_decide_div_mod_eq, hd5]
    rfl

/-- **`virtEF` is `virtE`.** -/
theorem virtEF_rel (nuMain nuRec : ℕ) (hok : N.okB nuMain nuRec = true) (hlay : N.layOk lay = true)
    (pub : Pub) (ry : List FE) (hry : ry.length = yVars) :
    FE.toExt3 (virtEF N pub ry) = virtE (N.inst Q lay) pub (ry.map FE.toExt3) := by
  obtain ⟨hreg, -, hsort⟩ := fm_ok N nuMain nuRec hok
  have hpw := fm_pairwise N.regs hsort
  let T : NReg → FE := fun g ↦
    (if g.src = .pub then
      hiW ry g.log g.base * mleK g.log (fun i ↦ pub.hdrLanes.toArray.getD (g.dst + i) 0) ry else 0) +
    (if g.src = .one then hiW ry g.log g.base else 0)
  have hv : virtEF N pub ry = (N.regs.map T).sum := by
    unfold virtEF
    refine (fm_foldl _ _ T (fun acc g ↦ ?_) 0).trans (zero_add _)
    rcases g with ⟨b, l, src, d⟩
    cases src <;> simp [T]
  rw [hv, fm_toExt3_sum]
  unfold virtE
  rw [fm_regSum N Q lay hlay, fm_regSum N Q lay hlay, fm_regSum N Q lay hlay, ← List.sum_map_add,
    ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  obtain ⟨hb1, hb2, -, hpub, hone⟩ := hreg g hg
  have hoff := fm_off N hpw g hg
  rcases g with ⟨b, l, src, d⟩
  cases src
  · simp [T]
  · simp [T]
  · obtain ⟨rfl, rfl⟩ := hpub rfl
    simp only [T, ite_true, reduceCtorEq, ite_false, add_zero, beq_self_eq_true, FE.toExt3_mul, hiW,
      fm_toExt3_eqAtF, TNat.inst]
    have hl : 10 ≤ ry.length := by rw [hry]; norm_num
    rw [fm_mleK _ _ _ hl, Finset.mul_sum]
    simp only [beq_iff_eq, reduceCtorEq, ite_false, add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 2 ^ 10 := Finset.mem_range.1 hi
    rw [hoff i hi', fm_eqAt_split _ b 10 i hb1 hi', List.map_take, List.map_drop, zero_add,
      Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    ring
  · simp [T]
  · simp [T]
  · simp [T, TNat.inst, Lvm.M3.ofK_zero']
  · obtain rfl := hone rfl
    simp [T, hiW, fm_toExt3_eqAtF]

/-- **`relayKernF` is `relayKern`.** -/
theorem relayKernF_rel (nuMain nuRec : ℕ) (hok : N.okB nuMain nuRec = true) (hlay : N.layOk lay = true)
    (ry r : List FE) (hry : ry.length = yVars) (hr : r.length = relayRoundsN) :
    FE.toExt3 (relayKernF N ry r) = relayKern (N.inst Q lay) (ry.map FE.toExt3) (r.map FE.toExt3) := by
  obtain ⟨hreg, ⟨g, hg1, hlog, hdst⟩, hsort⟩ := fm_ok N nuMain nuRec hok
  have hpw := fm_pairwise N.regs hsort
  have hgm : g ∈ N.regs := (List.mem_filter.1 (hg1 ▸ List.mem_singleton_self g : g ∈ N.regsOf .sflat)).1
  obtain ⟨hb1, -⟩ := hreg g hgm
  have hoff := fm_off N hpw g hgm
  unfold relayKernF relayKern
  rw [hg1, fm_regSum_single N Q lay hlay .sflat g hg1]
  rcases g with ⟨b, l, src, d⟩
  simp only at hlog hdst hb1 hoff
  subst hlog hdst
  have hidp : ¬ (0 + 2 ^ posBits ≤ sPos) := by norm_num [sPos, sLanes, recStreamCols, recRowBits]
  have hρ : (ry.take posBits).length = posBits := List.length_take_of_le (by rw [hry]; norm_num)
  have hlo : (r.take recRowBits).length = recRowBits := List.length_take_of_le (by rw [hr]; norm_num)
  have hc : sPos < 2 ^ posBits := by norm_num [sPos, sLanes, recStreamCols, recRowBits]
  simp only [List.foldl_cons, List.foldl_nil, zero_add, Nat.zero_shiftRight, Nat.min_zero,
    Nat.sub_zero, List.drop_of_length_le (le_of_eq hr), List.take_of_length_le (le_of_eq hr)]
  rw [divKern_eq _ _ _ hρ hlo, geKern_eq _ _ _ _ hρ hr hc, ite_eq_right (by simpa using hidp), eqAtF,
    one_mul, FE.toExt3_mul, FE.toExt3_add, hiW, fm_toExt3_eqAtF, fm_toExt3_sumE_range,
    fm_toExt3_sumE_filter]
  simp only [TNat.inst]
  have e : ∀ i ∈ Finset.range (2 ^ posBits), LeanVM.Protocol.KeccakGkr.eqAt (ry.map FE.toExt3) (b + i) *
      LeanVM.Protocol.KeccakGkr.eqAt (r.map FE.toExt3) (sflatWord (N.off (b + i))) =
        LeanVM.Protocol.KeccakGkr.eqAt ((ry.map FE.toExt3).drop posBits) (b >>> posBits) *
          (LeanVM.Protocol.KeccakGkr.eqAt ((ry.map FE.toExt3).take posBits) i *
            LeanVM.Protocol.KeccakGkr.eqAt (r.map FE.toExt3) (sflatWord i)) := by
    intro i hi
    rw [hoff i (Finset.mem_range.1 hi), zero_add, fm_eqAt_split _ b posBits i hb1 (Finset.mem_range.1 hi)]
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ hc.le, List.map_drop]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· + ·) ?_ ?_)
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [fm_sflat _ i (Finset.mem_range.1 hi), FE.toExt3_mul, FE.toExt3_mul, fm_toExt3_eqAtF, fm_toExt3_eqAtF,
      fm_toExt3_eqAtF, List.map_take, List.map_drop, List.map_take]
    ring
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := (Finset.mem_Ico.1 hi).1
    rw [sflatWord, ite_eq_right (by omega), FE.toExt3_mul, fm_toExt3_eqAtF, fm_toExt3_eqAtF, List.map_take]

end Lvm.TypedV
