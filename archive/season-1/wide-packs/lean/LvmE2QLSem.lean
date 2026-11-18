-- New for lvm2 E2F (slice S1, E2F-QH2): the `KS` link at `E2` is sound: the interval shift sums (`LvmQLinkArith`'s
-- `preCF`, here over any field of characteristic 2 with V's `eqAtF`) give V's `contShiftF contRowsF`; the gadget's
-- cells are the stream's values and its assertion is V's check.
import LvmE2QL
import LvmE2QWKitSem
import LvmE2VBaseLemmas
import LvmE2VProgKS

/-!
# The `KS` link's soundness

* **`preCFF_eq`** (generic `F`): the low-bit recursion `preCFF x y H` is `(pre(H), E(H), eq(y,H)·eq(x,H))`,
  `pre(H) = Σ_{k<H} eq(y, k)·eq(x, k + 1)`, for `H < 2^|x|`; **`contShiftF_pre`**: `contShiftF` on
  `[1, B) ∪ [K + 1, K + 32)` is `pre(B − 1) + pre(K + 31) + pre(K)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.E2V Finset

section Gen

variable {F : Type} [Field F] [CharP F 2]

/-- `pre(H) = Σ_{k<H} eq(y, k)·eq(x, k + 1)`. -/
def preSumF (x y : List F) (H : ℕ) : F := ∑ k ∈ range H, E2V.eqAtF y k * E2V.eqAtF x (k + 1)

/-- `E(H) = Σ_{k<H} eq(y, k)·eq(x, k)`. -/
def eSumF (x y : List F) (H : ℕ) : F := ∑ k ∈ range H, E2V.eqAtF y k * E2V.eqAtF x k

/-- One level of the recursion (`LvmQLinkArith.preStep`). -/
def preStepF (x0 y0 : F) (h : Bool) (r : F × F × F) : F × F × F :=
  let E1 := if h then r.2.1 + r.2.2 else r.2.1
  ((1 + y0) * x0 * E1 + y0 * (1 + x0) * r.1,
   (1 + y0) * (1 + x0) * E1 + y0 * x0 * r.2.1,
   (if h then y0 * x0 else (1 + y0) * (1 + x0)) * r.2.2)

/-- **The recursion**, base `(0, 0, 1)`. -/
def preCFF : List F → List F → ℕ → F × F × F
  | x0 :: x, y0 :: y, H => preStepF x0 y0 (H % 2 = 1) (preCFF x y (H / 2))
  | _, _, _ => (0, 0, 1)

theorem eqAtF_even' (r : F) (rs : List F) (w : ℕ) : E2V.eqAtF (r :: rs) (2 * w) = (1 + r) * E2V.eqAtF rs w := by
  show (if 2 * w % 2 = 1 then r else 1 + r) * E2V.eqAtF rs (2 * w / 2) = _
  rw [if_neg (by omega), show 2 * w / 2 = w by omega]

theorem eqAtF_odd' (r : F) (rs : List F) (w : ℕ) : E2V.eqAtF (r :: rs) (2 * w + 1) = r * E2V.eqAtF rs w := by
  show (if (2 * w + 1) % 2 = 1 then r else 1 + r) * E2V.eqAtF rs ((2 * w + 1) / 2) = _
  rw [if_pos (by omega), show (2 * w + 1) / 2 = w by omega]

theorem sum_range_two_mulF (g : ℕ → F) : ∀ N : ℕ,
    ∑ x ∈ range (2 * N), g x = ∑ x ∈ range N, (g (2 * x) + g (2 * x + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_two_mulF g N,
      sum_range_succ]
    ring

theorem sum_range_parityF (f : ℕ → F) (H : ℕ) :
    ∑ k ∈ range H, f k = ∑ k ∈ range (H / 2 + H % 2), f (2 * k) + ∑ k ∈ range (H / 2), f (2 * k + 1) := by
  rcases Nat.mod_two_eq_zero_or_one H with h0 | h1
  · have hH : H = 2 * (H / 2) := by omega
    rw [h0, Nat.add_zero]
    conv_lhs => rw [hH]
    rw [sum_range_two_mulF, sum_add_distrib]
  · have hH : H = 2 * (H / 2) + 1 := by omega
    rw [h1]
    conv_lhs => rw [hH]
    rw [sum_range_succ, sum_range_two_mulF, sum_add_distrib, sum_range_succ]
    ring

theorem preSumF_cons (x0 y0 : F) (x y : List F) (H : ℕ) :
    preSumF (x0 :: x) (y0 :: y) H =
      (1 + y0) * x0 * eSumF x y (H / 2 + H % 2) + y0 * (1 + x0) * preSumF x y (H / 2) := by
  unfold preSumF eSumF
  rw [sum_range_parityF (fun k => E2V.eqAtF (y0 :: y) k * E2V.eqAtF (x0 :: x) (k + 1)) H, mul_sum, mul_sum]
  refine congrArg₂ (· + ·) (sum_congr rfl fun k _ => ?_) (sum_congr rfl fun k _ => ?_)
  · rw [eqAtF_even', eqAtF_odd']; ring
  · rw [eqAtF_odd', show 2 * k + 1 + 1 = 2 * (k + 1) by ring, eqAtF_even']; ring

theorem eSumF_cons (x0 y0 : F) (x y : List F) (H : ℕ) :
    eSumF (x0 :: x) (y0 :: y) H =
      (1 + y0) * (1 + x0) * eSumF x y (H / 2 + H % 2) + y0 * x0 * eSumF x y (H / 2) := by
  unfold eSumF
  rw [sum_range_parityF (fun k => E2V.eqAtF (y0 :: y) k * E2V.eqAtF (x0 :: x) k) H, mul_sum, mul_sum]
  refine congrArg₂ (· + ·) (sum_congr rfl fun k _ => ?_) (sum_congr rfl fun k _ => ?_)
  · rw [eqAtF_even', eqAtF_even']; ring
  · rw [eqAtF_odd', eqAtF_odd']; ring

theorem ptF_cons (x0 y0 : F) (x y : List F) (H : ℕ) :
    E2V.eqAtF (y0 :: y) H * E2V.eqAtF (x0 :: x) H =
      (if H % 2 = 1 then y0 * x0 else (1 + y0) * (1 + x0)) * (E2V.eqAtF y (H / 2) * E2V.eqAtF x (H / 2)) := by
  show (if H % 2 = 1 then y0 else 1 + y0) * E2V.eqAtF y (H / 2) *
    ((if H % 2 = 1 then x0 else 1 + x0) * E2V.eqAtF x (H / 2)) = _
  split <;> ring

theorem eSumF_succ_bit (x y : List F) (H : ℕ) :
    (if H % 2 = 1 then eSumF x y (H / 2) + E2V.eqAtF y (H / 2) * E2V.eqAtF x (H / 2) else eSumF x y (H / 2)) =
      eSumF x y (H / 2 + H % 2) := by
  rcases Nat.mod_two_eq_zero_or_one H with h0 | h1
  · rw [h0]; simp
  · rw [h1, if_pos rfl, eSumF, eSumF, sum_range_succ]

/-- **The recursion's closed form** (`H < 2^|x|`). -/
theorem preCFF_eq : ∀ (x y : List F) (H : ℕ), x.length = y.length → H < 2 ^ x.length →
    preCFF x y H = (preSumF x y H, eSumF x y H, E2V.eqAtF y H * E2V.eqAtF x H)
  | [], [], H, _, hH => by
    obtain rfl : H = 0 := by simpa using hH
    simp [preCFF, preSumF, eSumF]
    rw [show E2V.eqAtF ([] : List F) 0 = 1 from rfl, one_mul]
  | x0 :: x, y0 :: y, H, h, hH => by
    have ih := preCFF_eq x y (H / 2) (by simpa using h) (by
      simp only [List.length_cons, pow_succ] at hH; omega)
    rw [show preCFF (x0 :: x) (y0 :: y) H = preStepF x0 y0 (H % 2 = 1) (preCFF x y (H / 2)) from rfl, ih,
      preSumF_cons, eSumF_cons, ptF_cons, ← eSumF_succ_bit]
    unfold preStepF
    by_cases hb : H % 2 = 1 <;> simp [hb]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

/-- The rows `[1, B) ∪ [K + 1, K + 32)` (V's `contRowsF` with `B = spongeBlocksF`, `K = ksSplit + 399`). -/
def rowsBK (B K : ℕ) : List ℕ := (List.range (B - 1)).map (· + 1) ++ (List.range 31).map (K + 1 + ·)

theorem lsum_range (f : ℕ → F) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, lsum_range f n, sum_range_succ]; simp

/-- **`contShiftF` on the two intervals** is `pre(B − 1) + pre(K + 31) + pre(K)`. -/
theorem contShiftF_pre (B K : ℕ) (rho rho' : List F) :
    contShiftF (rowsBK B K) rho rho' = preSumF rho rho' (B - 1) + preSumF rho rho' (K + 31) + preSumF rho rho' K := by
  rw [contShiftF, sumF_eq_sum, rowsBK, List.map_append, List.sum_append, List.map_map, List.map_map, lsum_range,
    lsum_range]
  have e1 : ∑ i ∈ range (B - 1), ((fun i => E2V.eqAtF rho i * E2V.eqAtF rho' (i - 1)) ∘ (· + 1)) i =
      preSumF rho rho' (B - 1) := by
    unfold preSumF
    refine sum_congr rfl fun k _ => ?_
    simp only [Function.comp_apply, Nat.add_sub_cancel]; ring
  have e2 : preSumF rho rho' (K + 31) = preSumF rho rho' K +
      ∑ i ∈ range 31, ((fun i => E2V.eqAtF rho i * E2V.eqAtF rho' (i - 1)) ∘ (K + 1 + ·)) i := by
    unfold preSumF
    rw [sum_range_add]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    simp only [Function.comp_apply, show K + 1 + k - 1 = K + k by omega, show K + k + 1 = K + 1 + k by omega]; ring
  rw [e1, e2]
  linear_combination (-preSumF rho rho' K) * CharTwo.two_eq_zero (R := F)

end Gen

/-! ## The gadget -/

instance charP_FE2 : CharP FE2 2 :=
  charP_of_injective_algebraMap (fun a b h => by
    have := congrArg FE2.re h
    rw [FE2.algebraMap_eq_ofK, FE2.algebraMap_eq_ofK] at this
    exact this) 2

open Lvm.Loop Lvm.Loop.Build Lvm.Har

variable {c : Ctx} {M : Mem}

/-- **Holds and asserts**: on a memory where the gadget's segments hold and its assertions hold, `P` of its output. -/
def HsA {α : Type} (c : Ctx) (M : Mem) (m : BM α) (P : α → Prop) : Prop :=
  ∀ p : Ptr, SegsHold c M p (m p).2 → SegsAssert M p (m p).2 → P (m p).1

theorem hsA_of_hs {α : Type} {m : BM α} {P : α → Prop} (h : Hs c M m P) : HsA c M m P := fun p hh _ => h p hh

theorem hsA_bind {α β : Type} {m : BM α} {f : α → BM β} {P : α → Prop} {Q : β → Prop}
    (hm : HsA c M m P) (hf : ∀ a, P a → HsA c M (f a) Q) : HsA c M (m >>= f) Q := by
  intro p hh ha
  rw [hold_bind] at hh; rw [assert_bind] at ha
  have := hf _ (hm p hh.1 ha.1) _ hh.2 ha.2
  rwa [bind_apply] at *

theorem hsA_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : HsA c M (pure a) P := fun _ _ _ => h

theorem hsA_mono {α : Type} {m : BM α} {P Q : α → Prop} (h : HsA c M m P) (hPQ : ∀ a, P a → Q a) : HsA c M m Q :=
  fun p hh ha => hPQ _ (h p hh ha)

/-- **An `E2` assertion with gate `1`** makes the value `0`. -/
theorem hsA_g2Assert (a : C2) (gate : Cell) (hg : gate.val M = 1) : HsA c M (g2Assert a gate) (fun _ => a.val M = 0) := by
  intro p _ ha
  simp only [g2Assert] at ha
  rw [assert_bind] at ha
  have h0 := assert0_spec ha.1
  have h1 := assert0_spec ha.2
  rw [hg, one_mul] at h0 h1
  apply FE2.ext_coord
  · show (a.re.val M).c₀ = (0 : FE2).re
    rw [h0]; rfl
  · show (a.im.val M).c₀ = (0 : FE2).im
    rw [h1]; rfl

/-- One level's values. -/
theorem hs_g2PreLevel {z : C2} (hz : z.val M = 0) (h : Bool) (x0 y0 : C2) (r : C2 × C2 × C2) :
    Hs c M (g2PreLevel z h x0 y0 r) (fun o => (o.1.val M, o.2.1.val M, o.2.2.val M) =
      preStepF (x0.val M) (y0.val M) h (r.1.val M, r.2.1.val M, r.2.2.val M)) := by
  unfold g2PreLevel
  refine hs_bind (hs_g2One _) fun l0 h0 => hs_bind (hs_g2One _) fun l1 h1 =>
    hs_bind (hs_g2Mul _ _ _) fun l2 h2 => hs_bind (hs_g2Mul _ _ _) fun l3 h3 =>
    hs_bind (hs_g2Mul _ _ _) fun l4 h4 => hs_bind (hs_g2Mul _ _ _) fun l5 h5 =>
    hs_bind (hs_g2Add _ _) fun l6 h6 => hs_bind (hs_g2Mul _ _ _) fun l7 h7 =>
    hs_bind (hs_g2Mul _ _ _) fun np hnp => hs_bind (hs_g2Mul _ _ _) fun l9 h9 =>
    hs_bind (hs_g2Mul _ _ _) fun nE hnE => hs_bind (hs_g2Mul _ _ _) fun nPt hnPt => hs_pure ?_
  simp only [preStepF]
  cases h
  · simp only [Bool.false_eq_true, if_false] at h6 hnPt ⊢
    rw [hnp, hnE, hnPt, h7, h9, h6, h2, h3, h4, h5, h0, h1, hz]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  · simp only [if_true] at h6 hnPt ⊢
    rw [hnp, hnE, hnPt, h7, h9, h6, h2, h3, h4, h5, h0, h1, hz]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

/-- **The recursion's values** are `preCFF`'s (base `(0, 0, 1)`). -/
theorem hs_g2PreRec {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) : ∀ (x y : List C2) (H : ℕ),
    Hs c M (g2PreRec z x y H (z, z, one)) (fun o => (o.1.val M, o.2.1.val M, o.2.2.val M) =
      preCFF (x.map (C2.val M)) (y.map (C2.val M)) H)
  | x0 :: x, y0 :: y, H => hs_bind (hs_g2PreRec hz ho x y (H / 2)) fun r hr =>
    hs_mono (hs_g2PreLevel hz _ x0 y0 r) fun o ho' => by
      rw [ho', List.map_cons, List.map_cons, preCFF, ← hr]
  | [], _, H => hs_pure (by simp [preCFF, hz, ho])
  | _ :: _, [], H => hs_pure (by simp [preCFF, hz, ho])

theorem eqEvalF_cons' (a b : FE2) (x y : List FE2) :
    E2V.eqEvalF (a :: x) (b :: y) = (1 + a + b) * E2V.eqEvalF x y := by
  unfold E2V.eqEvalF
  rw [List.zipWith_cons_cons, ← List.prod_eq_foldl, ← List.prod_eq_foldl, List.prod_cons]

theorem hs_g2EqEval {z : C2} (hz : z.val M = 0) : ∀ (acc : C2) (xs ys : List C2), xs.length = ys.length →
    Hs c M (g2EqEval z acc xs ys) (fun r => r.val M = acc.val M * E2V.eqEvalF (xs.map (C2.val M)) (ys.map (C2.val M)))
  | acc, x :: xs, y :: ys, h => hs_bind (hs_g2Lin 1 1 x y) fun f hf => hs_bind (hs_g2Mul acc f z) fun a ha =>
    hs_mono (hs_g2EqEval hz a xs ys (by simpa using h)) fun r hr => by
      rw [hr, ha, hf, hz, List.map_cons, List.map_cons, eqEvalF_cons', show FE2.ofK 1 = (1 : FE2) from rfl]
      ring
  | acc, [], [], _ => hs_pure (by simp [E2V.eqEvalF])
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem prodF_eq (l : List FE2) : E2V.prodF l = l.prod := by
  unfold E2V.prodF; rw [← List.prod_eq_foldl]

theorem sc2Ans_length (R q : ℕ) : (sc2Ans R q).length = R := by simp [sc2Ans]

/-- **The `KS` link gadget is sound**: with the gate on, where its rows hold and its assertion holds, its outputs
are the stream's values and V's `ksLinkD` check holds on them (`contShiftF` on `[1, B) ∪ [K + 1, K + 32)`). -/
theorem ksLinkG2_sound {hk xl B K qa : ℕ} {gate : Cell} (hg : gate.val M = 1) (hB : B - 1 < 2 ^ hk)
    (hK : K + 31 < 2 ^ hk) :
    HsA c M (ksLinkG2 hk xl B K qa gate) (fun o =>
      o.kchal = (List.range (hk + 5)).map (fun i => ld2 (qa + 10 * i)) ∧
      o.shift = (sc2Ans hk (ksLinkQ1 hk qa)).map ld2 ∧
      o.vals = (List.range 4).map (fun k => ld2 (ksLinkQV hk qa + 2 * k)) ∧
      o.final.val M = scFold2 (fun k => (ld2 k).val M) hk (ksLinkQ1 hk qa) 0 ∧
      o.om.map (C2.val M) = E2V.eqKernelF ((o.kchal.drop hk).map (C2.val M)) ∧
      o.sel.val M = E2V.selXF xl (o.shift.map (C2.val M)) ∧
      o.final.val M = contShiftF (rowsBK B K) ((o.kchal.take hk).map (C2.val M)) (o.shift.map (C2.val M)) *
          (o.vals.getD 0 default).val M +
        E2V.eqEvalF ((o.kchal.take hk).map (C2.val M)) (o.shift.map (C2.val M)) *
          ((o.vals.getD 1 default).val M + (o.vals.getD 2 default).val M +
            E2V.selXF xl (o.shift.map (C2.val M)) * (o.vals.getD 3 default).val M)) := by
  unfold ksLinkG2
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz => hsA_bind (hsA_of_hs (hs_g2One z)) fun one ho => ?_
  rw [hz, add_zero] at ho
  refine hsA_bind (hsA_of_hs (hs_sc2 hk (ksLinkQ1 hk qa) z)) fun sh ⟨hs1, hs2⟩ => ?_
  have hlr : (((List.range (hk + 5)).map fun i => ld2 (qa + 10 * i)).take hk).length = hk := by simp
  have hl' : sh.1.length = hk := by rw [hs1, List.length_map, sc2Ans_length]
  have hlv : ((((List.range (hk + 5)).map fun i => ld2 (qa + 10 * i)).take hk).map (C2.val M)).length = hk := by
    simp
  have hl'v : (sh.1.map (C2.val M)).length = hk := by simp [hl']
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ (B - 1))) fun p1 hp1 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ (K + 31))) fun p2 hp2 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ K)) fun p3 hp3 => ?_
  rw [preCFF_eq _ _ _ (by rw [hlv, hl'v]) (by rw [hlv]; exact hB)] at hp1
  rw [preCFF_eq _ _ _ (by rw [hlv, hl'v]) (by rw [hlv]; exact hK)] at hp2
  rw [preCFF_eq _ _ _ (by rw [hlv, hl'v]) (by rw [hlv]; omega)] at hp3
  simp only [Prod.mk.injEq] at hp1 hp2 hp3
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s12 h12 => hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun cs hcs => ?_
  refine hsA_bind (hsA_of_hs (hs_g2EqEval hz one _ _ (by rw [hlr, hl']))) fun ee hee => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Prod hz one _)) fun sel hsel => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun im him => hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun inner hin => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t1 ht1 => hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun rhs hrhs => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun e he => hsA_bind (hsA_g2Assert e gate hg) fun _ hE => ?_
  refine hsA_of_hs (hs_bind (hs_g2EqTab hz [one] _) fun om hom => hs_pure ?_)
  have hsel' : sel.val M = E2V.selXF xl (sh.1.map (C2.val M)) := by
    rw [hsel, ho, one_mul, E2V.selXF, prodF_eq, List.map_drop]
  refine ⟨rfl, hs1, rfl, by rw [hs2, hz], by rw [hom, List.map_cons, ho]; rfl, hsel', ?_⟩
  have hfin : sh.2.val M = rhs.val M := by
    rw [he] at hE
    linear_combination hE - (rhs.val M) * CharTwo.two_eq_zero (R := FE2)
  simp only
  rw [hfin, hrhs, ht1, hin, him, hsel', hee, ho, one_mul, hz, add_zero, hcs, h12, contShiftF_pre, ← hp1.1, ← hp2.1,
    ← hp3.1]
  ring

end Lvm.Q2
