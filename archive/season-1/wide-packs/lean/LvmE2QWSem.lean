-- New for lvm2 E2F (slice S1, E2F-QH2): the wiring gadget's automata at `E2` (`LvmE2QW`) compute V's `thrTailF`,
-- `msTailF` (`LvmE2VProg`) with the bits of `t` in the cells (`bitsF t`).
import LvmE2QW
import LvmE2QWKitSem
import LvmE2VWireAlg
import LvmE2VProg
import LvmE2VGkrBase
import LvmE2QLSem
import LvmQEqKeccakAlgG

/-!
# The wire gadget's automata

* **`hs_g2ThrTail`**: with the bit cells holding `bitsF t |ρ|` (`t < 2^|ρ|`), the threshold automaton's two values are
  `thrTailF ρ t`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.E2V

variable {c : Ctx} {M : Mem}

theorem fe2_two : (2 : FE2) = 0 := CharTwo.two_eq_zero

/-- One bit of the threshold automaton: the rows' values are V's step. -/
theorem thrStep_eq (r q1 q2 : FE2) (t : ℕ) :
    ((r + (if t % 2 = 1 then 1 else 0) * r) * (q1 + q2) + q1, ((if t % 2 = 1 then 1 else 0) +
      (if t % 2 = 1 then 1 else 0) * r) * (q1 + q2) + q2) =
    ((1 + r) * (if WK.nextS false false (t % 2 == 1) then q2 else q1) +
        r * (if WK.nextS true false (t % 2 == 1) then q2 else q1),
      (1 + r) * (if WK.nextS false true (t % 2 == 1) then q2 else q1) +
        r * (if WK.nextS true true (t % 2 == 1) then q2 else q1)) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have hb : (t % 2 == 1) = false := by rw [h]; rfl
    rw [hb, if_neg (by omega)]
    simp only [WK.nextS, Bool.false_eq_true, if_false, Bool.or_self, Bool.true_or, Bool.or_true, if_true, zero_mul,
      add_zero, zero_add]
    refine Prod.ext ?_ ?_
    · show _ = _; ring
    · show _ = _; linear_combination (-r * q2) * fe2_two
  · have hb : (t % 2 == 1) = true := by rw [h]; rfl
    rw [hb, if_pos h]
    simp only [WK.nextS, Bool.and_self, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false, if_true, one_mul]
    refine Prod.ext ?_ ?_
    · show _ = _; linear_combination (r * q2) * fe2_two
    · show _ = _; linear_combination q2 * fe2_two

theorem hs_g2ThrStep {z : C2} (hz : z.val M = 0) (r b : C2) (q : C2 × C2) :
    Hs c M (g2ThrStep z r b q) (fun n => (n.1.val M, n.2.val M) =
      ((r.val M + b.val M * r.val M) * (q.1.val M + q.2.val M) + q.1.val M,
       (b.val M + b.val M * r.val M) * (q.1.val M + q.2.val M) + q.2.val M)) := by
  unfold g2ThrStep
  refine hs_bind (hs_g2Add _ _) fun d hd => hs_bind (hs_g2Mul _ _ _) fun t ht => hs_bind (hs_g2Add _ _) fun u hu =>
    hs_bind (hs_g2Mul _ _ _) fun n1 hn1 => hs_bind (hs_g2Add _ _) fun w hw => hs_bind (hs_g2Mul _ _ _) fun n2 hn2 =>
    hs_pure ?_
  rw [hn1, hn2, hu, hw, ht, hd, hz, add_zero]

/-- **The threshold automaton** (`thrTailF`), the bit cells holding `bitsF t`. -/
theorem hs_g2ThrTail {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) : ∀ (ρ tb : List C2) (t : ℕ),
    tb.map (C2.val M) = bitsF t ρ.length → t < 2 ^ ρ.length →
    Hs c M (g2ThrTail z one ρ tb) (fun q => (q.1.val M, q.2.val M) = E2V.thrTailF (ρ.map (C2.val M)) t)
  | [], _, t, _, ht => hs_pure (by
      have : t = 0 := by simpa using ht
      subst this; simp [E2V.thrTailF, hz, ho])
  | r :: ρ, b :: tb, t, hb, ht => by
    simp only [List.map_cons, List.length_cons, bitsF, List.cons.injEq] at hb
    refine hs_bind (hs_g2ThrTail hz ho ρ tb (t / 2) hb.2 (by simp only [List.length_cons, pow_succ] at ht; omega)) fun q hq => ?_
    refine hs_mono (hs_g2ThrStep hz r b q) fun n hn => ?_
    rw [hn, hb.1]
    simp only [List.map_cons, E2V.thrTailF]
    rw [← hq]
    exact thrStep_eq _ _ _ t
  | r :: ρ, [], t, hb, _ => by simp [bitsF] at hb

/-! ## The `MS` automaton -/

/-- A `Q4` of cells as V's value vector. -/
def q4v (M : Mem) (q : Q4) : E2V.MS4F FE2 := ⟨q.1.val M, q.2.1.val M, q.2.2.1.val M, q.2.2.2.val M⟩

/-- One known-bit step's four values (`g2MsStep`), `al, be, ga, de` the four weights. -/
def msStepT (al be ga de : FE2) (t : Bool) (q : E2V.MS4F FE2) : E2V.MS4F FE2 :=
  if t then ⟨al * q.v00 + be * q.v00, al * q.v00 + be * q.v01, ga * q.v00 + de * q.v10, ga * q.v01 + de * q.v10⟩
  else ⟨al * q.v00 + be * q.v01, al * q.v01 + be * q.v01, ga * q.v01 + de * q.v10, ga * q.v01 + de * q.v11⟩

theorem hs_g2MsStep {z : C2} (hz : z.val M = 0) (al be ga de : C2) (t : Bool) (q : Q4) :
    Hs c M (g2MsStep z al be ga de t q) (fun f => q4v M f =
      msStepT (al.val M) (be.val M) (ga.val M) (de.val M) t (q4v M q)) := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  cases t
  · simp only [g2MsStep, Bool.false_eq_true, if_false]
    refine hs_bind (hs_g2Dot _ _) fun f00 h00 => hs_bind (hs_g2Dot _ _) fun f01 h01 =>
      hs_bind (hs_g2Dot _ _) fun f10 h10 => hs_bind (hs_g2Dot _ _) fun f11 h11 => hs_pure ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hz, zero_add] at h00 h01 h10 h11
    simp only [q4v, msStepT, Bool.false_eq_true, if_false, h00, h01, h10, h11]
  · simp only [g2MsStep, if_true]
    refine hs_bind (hs_g2Dot _ _) fun f00 h00 => hs_bind (hs_g2Dot _ _) fun f01 h01 =>
      hs_bind (hs_g2Dot _ _) fun f10 h10 => hs_bind (hs_g2Dot _ _) fun f11 h11 => hs_pure ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hz, zero_add] at h00 h01 h10 h11
    simp only [q4v, msStepT, if_true, h00, h01, h10, h11]

/-- `f₀ + b·(f₁ + f₀)` on the four entries. -/
def mix4 (b : FE2) (f1 f0 : E2V.MS4F FE2) : E2V.MS4F FE2 :=
  ⟨b * (f1.v00 + f0.v00) + f0.v00, b * (f1.v01 + f0.v01) + f0.v01, b * (f1.v10 + f0.v10) + f0.v10,
    b * (f1.v11 + f0.v11) + f0.v11⟩

theorem hs_g2Mix (b f1 f0 : C2) : Hs c M (g2Mix b f1 f0) (fun r => r.val M = b.val M * (f1.val M + f0.val M) + f0.val M) :=
  hs_bind (hs_g2Add _ _) fun d hd => hs_mono (hs_g2Mul _ _ _) fun r hr => by rw [hr, hd]

/-- **One `MS` step with a bit cell** (`g2MsStepA`) is V's `E2V.msStepF` at the bit. -/
theorem msStep_eq (a r : FE2) (t : ℕ) (q : E2V.MS4F FE2) :
    mix4 (if t % 2 = 1 then 1 else 0)
      (msStepT (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) true q)
      (msStepT (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) false q) =
    E2V.msStepF a r (t % 2 == 1) q := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have hb : (t % 2 == 1) = false := by rw [h]; rfl
    rw [hb, if_neg (by omega)]
    simp only [mix4, msStepT, E2V.msStepF, E2V.eqBitF, E2V.MS4F.get, WK.nextS, Bool.not_true, Bool.not_false, if_true,
      Bool.false_eq_true, if_false, Bool.or_self, Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true, zero_mul,
      zero_add, E2V.MS4F.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  · have hb : (t % 2 == 1) = true := by rw [h]; rfl
    rw [hb, if_pos h]
    simp only [mix4, msStepT, E2V.msStepF, E2V.eqBitF, E2V.MS4F.get, WK.nextS, Bool.not_true, Bool.not_false, if_true,
      Bool.false_eq_true, if_false, Bool.and_self, Bool.false_and, Bool.and_false, Bool.true_and, one_mul,
      E2V.MS4F.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (a * r * q01 + a * q00 + q00 + r * q00 + a * r * q00) * fe2_two
    · linear_combination (2 * a * r * q01 + a * q01 + r * q01 + q01) * fe2_two
    · linear_combination (r * a * q01 + r * q01 + a * r * q10 + a * q10) * fe2_two
    · linear_combination (r * a * q01 + r * a * q11 + r * q01 + a * q11) * fe2_two

theorem hs_g2MsStepA {z : C2} (hz : z.val M = 0) (a r b : C2) (q : Q4) :
    Hs c M (g2MsStepA z a r b q) (fun n => q4v M n = mix4 (b.val M)
      (msStepT (1 + (a.val M + r.val M + a.val M * r.val M)) (a.val M * r.val M) (r.val M + a.val M * r.val M)
        (a.val M + a.val M * r.val M) true (q4v M q))
      (msStepT (1 + (a.val M + r.val M + a.val M * r.val M)) (a.val M * r.val M) (r.val M + a.val M * r.val M)
        (a.val M + a.val M * r.val M) false (q4v M q))) := by
  unfold g2MsStepA
  refine hs_bind (hs_g2Mul _ _ _) fun ar har => hs_bind (hs_g2Add _ _) fun s hs => hs_bind (hs_g2Add _ _) fun al0 hal0 =>
    hs_bind (hs_g2One _) fun al hal => hs_bind (hs_g2Add _ _) fun ga hga => hs_bind (hs_g2Add _ _) fun de hde => ?_
  rw [hz, add_zero] at har
  rw [hal0, hs, har] at hal
  rw [har] at hga hde
  refine hs_bind (hs_g2MsStep hz al ar ga de true q) fun f1 hf1 =>
    hs_bind (hs_g2MsStep hz al ar ga de false q) fun f0 hf0 => ?_
  rw [hal, hga, hde, har] at hf1 hf0
  refine hs_bind (hs_g2Mix _ _ _) fun n00 h00 => hs_bind (hs_g2Mix _ _ _) fun n01 h01 =>
    hs_bind (hs_g2Mix _ _ _) fun n10 h10 => hs_bind (hs_g2Mix _ _ _) fun n11 h11 => hs_pure ?_
  rw [← hf1, ← hf0]
  simp only [q4v, mix4, h00, h01, h10, h11]

/-- **The `MS` automaton** (`msTailF`), the bit cells holding `bitsF t`. -/
theorem hs_g2MsTail {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) : ∀ (σ ρ tb : List C2) (t : ℕ),
    σ.length = ρ.length → tb.map (C2.val M) = bitsF t σ.length → t < 2 ^ σ.length →
    Hs c M (g2MsTail z one σ ρ tb) (fun q => q4v M q = E2V.msTailF (σ.map (C2.val M)) (ρ.map (C2.val M)) t)
  | [], _, _, t, _, _, ht => hs_pure (by
      have : t = 0 := by simpa using ht
      subst this; simp [E2V.msTailF, q4v, hz, ho, g2MsTail])
  | a :: σ, r :: ρ, b :: tb, t, hl, hb, ht => by
    simp only [List.map_cons, List.length_cons, bitsF, List.cons.injEq] at hb
    refine hs_bind (hs_g2MsTail hz ho σ ρ tb (t / 2) (by simpa using hl) hb.2
      (by simp only [List.length_cons, pow_succ] at ht; omega)) fun q hq => ?_
    refine hs_mono (hs_g2MsStepA hz a r b q) fun n hn => ?_
    rw [hn, hb.1, hq]
    simp only [List.map_cons, E2V.msTailF]
    exact msStep_eq _ _ t _
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, hb, _ => by simp [bitsF] at hb

/-! ## `lt`, `thrEvalF` -/

theorem bitsF_drop1 (z m : ℕ) : ((bitsF z (m + 1) : List FE2)).drop 1 = bitsF (z / 2) m := rfl

theorem bitsF_drop5 (z m : ℕ) : ((bitsF z (m + 5) : List FE2)).drop 5 = bitsF (z / 32) m := by
  show (bitsF (z / 2 / 2 / 2 / 2 / 2) m : List FE2) = _
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

theorem bitsF_take5 (z m : ℕ) : ((bitsF z (m + 5) : List FE2)).take 5 = bitsF (z % 32) 5 := by
  show [_, _, _, _, _] = [_, _, _, _, _]
  simp only [show z % 32 % 2 = z % 2 by omega, show z % 32 / 2 % 2 = z / 2 % 2 by omega,
    show z % 32 / 2 / 2 % 2 = z / 2 / 2 % 2 by omega, show z % 32 / 2 / 2 / 2 % 2 = z / 2 / 2 / 2 % 2 by omega,
    show z % 32 / 2 / 2 / 2 / 2 % 2 = z / 2 / 2 / 2 / 2 % 2 by omega]

theorem sum_take_eq (l : List FE2) : ∀ k, k ≤ l.length → (l.take k).sum = ∑ j ∈ Finset.range k, l.getD j 0
  | 0, _ => by simp
  | k + 1, hk => by
    rw [List.take_succ, List.sum_append, sum_take_eq l k (by omega), Finset.sum_range_succ,
      List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp

/-- `Σ_{j<k} eq(bits u, j) = [u < k]`. -/
theorem lt_bits {u : ℕ} (hu : u < 32) (k : ℕ) (hk : k ≤ 32) :
    (((eqKernelF (bitsF u 5 : List FE2)).take k).sum) = if u < k then 1 else 0 := by
  have hl : (eqKernelF (bitsF u 5 : List FE2)).length = 32 := by rw [eqKernelF_length, bitsF_length]; norm_num
  rw [sum_take_eq _ k (by omega)]
  have : ∀ j ∈ Finset.range k, (eqKernelF (bitsF u 5 : List FE2)).getD j 0 = if j = u then 1 else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [eqKernelF_getD, bitsF_length, if_pos (by omega), eqAtF_bitsF_lt (by omega) (by omega)]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range k) u (fun _ => (1 : FE2))]
  simp [Finset.mem_range]

/-- **The `lt` table**: `lt_k = Σ_{j<k} eq(tb4, j)`. -/
theorem hs_g2LtTab {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (tb4 : List C2) :
    Hs c M (g2LtTab z one tb4) (fun lt => lt.map (C2.val M) =
      (List.range 33).map fun k => ((eqKernelF (tb4.map (C2.val M))).take k).sum) := by
  unfold g2LtTab
  refine hs_bind (hs_g2EqTab hz [one] tb4) fun e he => ?_
  refine hs_mapB _ _ (fun k => hs_mono (hs_g2Sum z (e.take k)) fun r hr => ?_) (List.range 33)
  rw [hr, hz, zero_add, List.map_take, he]
  simp only [List.map_cons, List.map_nil, ho]
  rfl

theorem getD_val (l : List C2) {d : ℕ} (hd : d < l.length) :
    (l.getD d default).val M = (l.map (C2.val M)).getD d 0 := by
  simp [List.getD_eq_getElem?_getD, hd]

theorem list_eq_range (l : List FE2) : l = (List.range l.length).map fun d => l.getD d 0 := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, h1]

/-- **`thrEvalF`**: the gadget's value with `μ` (32 cells), `ρ`, and the bit cells holding `bitsF t (|ρ| + 5)`. -/
theorem hs_g2Thr {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (ρ μ tb lt : List C2) (t : ℕ)
    (hμ : μ.length = 32) (htb : tb.map (C2.val M) = bitsF t (ρ.length + 5)) (ht : t < 2 ^ (ρ.length + 5))
    (hlt : lt.map (C2.val M) = (List.range 33).map fun k => ((eqKernelF ((tb.take 5).map (C2.val M))).take k).sum) :
    Hs c M (g2Thr z one ρ μ tb lt) (fun r => r.val M = E2V.thrEvalF (ρ.map (C2.val M)) (μ.map (C2.val M)) t) := by
  unfold g2Thr
  have hdrop : (tb.drop 5).map (C2.val M) = bitsF (t / 32) ρ.length := by rw [List.map_drop, htb, bitsF_drop5]
  have htake : (tb.take 5).map (C2.val M) = bitsF (t % 32) 5 := by rw [List.map_take, htb, bitsF_take5]
  have hll : lt.length = 33 := by have := congrArg List.length hlt; simpa using this
  have hlt' : ∀ d < 32, (lt.getD d default).val M = if t % 32 < d then 1 else 0 := by
    intro d hd
    rw [getD_val lt (by omega), hlt, htake]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show d < 33 by omega),
      Option.map_some, Option.getD_some]
    exact lt_bits (by omega) d (by omega)
  have hQ : t / 32 < 2 ^ ρ.length := by rw [pow_add] at ht; omega
  refine hs_bind (hs_g2ThrTail hz ho ρ (tb.drop 5) (t / 32) hdrop hQ) fun q hq => ?_
  refine hs_bind (hs_g2Sum z μ) fun sm hsm => hs_bind (hs_g2Dot z _) fun L hL => ?_
  refine hs_bind (hs_g2Add _ _) fun d hd => hs_bind (hs_g2Mul _ _ _) fun x hx => hs_mono (hs_g2Mul _ _ _) fun r hr => ?_
  have hq1 : q.1.val M = (E2V.thrTailF (ρ.map (C2.val M)) (t / 32)).1 := congrArg Prod.fst hq
  have hq2 : q.2.val M = (E2V.thrTailF (ρ.map (C2.val M)) (t / 32)).2 := congrArg Prod.snd hq
  have hsum : (μ.map (C2.val M)).sum = ∑ d ∈ Finset.range 32, (μ.map (C2.val M)).getD d 0 := by
    conv_lhs => rw [list_eq_range (μ.map (C2.val M))]
    rw [List.length_map, hμ, lsum_range]
  rw [hr, hd, hx, hL, hsm, hz, zero_add, zero_add, add_zero, hq1, hq2, E2V.thrEvalF, sumF_eq_sum, hsum, List.map_map,
    lsum_range, lsum_range, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dd hdd => ?_
  have hdd' := Finset.mem_range.mp hdd
  simp only [Function.comp_apply]
  rw [hlt' dd hdd', getD_val μ (by omega)]
  split_ifs
  · linear_combination ((μ.map (C2.val M)).getD dd 0 * (E2V.thrTailF (ρ.map (C2.val M)) (t / 32)).1) * fe2_two
  · ring

/-- **`msEvalF ρ μ σ 0 t`**: the gadget's value (`|ρ| = |σ| − 5`, `μ` 32 cells, bit cells `bitsF t |σ|`). -/
theorem hs_g2Ms {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (ρ μ σ tb lt : List C2) (t : ℕ)
    (h5 : 5 ≤ σ.length) (hρ : ρ.length = σ.length - 5) (hμ : μ.length = 32)
    (htb : tb.map (C2.val M) = bitsF t σ.length) (ht : t < 2 ^ σ.length)
    (hlt : lt.map (C2.val M) = (List.range 33).map fun k => ((eqKernelF ((tb.take 5).map (C2.val M))).take k).sum) :
    Hs c M (g2Ms z one ρ μ σ tb lt) (fun r => r.val M =
      E2V.msEvalF (ρ.map (C2.val M)) (μ.map (C2.val M)) (σ.map (C2.val M)) 0 t) := by
  unfold g2Ms
  obtain ⟨m, hm⟩ : ∃ m, σ.length = m + 5 := ⟨σ.length - 5, by omega⟩
  have hdrop : (tb.drop 5).map (C2.val M) = bitsF (t / 32) (σ.drop 5).length := by
    rw [List.map_drop, htb, hm, bitsF_drop5, List.length_drop, hm, Nat.add_sub_cancel]
  have htake : (tb.take 5).map (C2.val M) = bitsF (t % 32) 5 := by rw [List.map_take, htb, hm, bitsF_take5]
  have hlt' : ∀ d < 32, (lt.getD d default).val M = if t % 32 < d then 1 else 0 := by
    intro d hd
    have hll : lt.length = 33 := by have := congrArg List.length hlt; simpa using this
    rw [getD_val lt (by omega), hlt, htake]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show d < 33 by omega),
      Option.map_some, Option.getD_some]
    exact lt_bits (by omega) d (by omega)
  have hQ : t / 32 < 2 ^ (σ.drop 5).length := by
    rw [List.length_drop, hm, Nat.add_sub_cancel]; rw [hm, pow_add] at ht; omega
  refine hs_bind (hs_g2MsTail hz ho (σ.drop 5) (ρ.take (σ.length - 5)) (tb.drop 5) (t / 32)
    (by simp; omega) hdrop hQ) fun q hq => ?_
  refine hs_bind (hs_g2EqTab hz [one] (σ.take 5)) fun e4 he4 => ?_
  refine hs_bind (hs_mapB _ (fun d => (e4.getD d default).val M * (μ.getD ((d + 1) % 32) default).val M)
    (fun d => hs_mono (hs_g2Mul _ _ _) fun x hx => by simp only [hx, hz, add_zero]) (List.range 32)) fun A hA => ?_
  refine hs_bind (hs_g2Sum z _) fun sA hsA => hs_bind (hs_g2Dot z _) fun L hL => ?_
  refine hs_bind (hs_g2Mul _ _ _) fun x1 hx1 => hs_bind (hs_g2Mul _ _ _) fun x2 hx2 => ?_
  refine hs_bind (hs_g2Add _ _) fun d hd => hs_mono (hs_g2Mul _ _ _) fun r hr => ?_
  have hAl : A.length = 32 := by have := congrArg List.length hA; simpa using this
  have he4' : e4.map (C2.val M) = eqKernelF ((σ.take 5).map (C2.val M)) := by
    rw [he4, List.map_cons, List.map_nil, ho]; rfl
  have he4l : e4.length = 32 := by
    have := congrArg List.length he4'
    rw [List.length_map, eqKernelF_length, List.length_map, List.length_take] at this
    rw [this, show min 5 σ.length = 5 by omega]; norm_num
  have hAd : ∀ dd < 32, (A.getD dd default).val M =
      E2V.eqAtF ((σ.take 5).map (C2.val M)) dd * (μ.map (C2.val M)).getD ((dd + 1) % 32) 0 := by
    intro dd hdd
    rw [getD_val A (by omega), hA]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hdd, Option.map_some,
      Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, getD_val e4 (by omega),
      getD_val μ (by have := Nat.mod_lt (dd + 1) (show 32 > 0 by norm_num); omega), he4', eqKernelF_getD,
      if_pos (by rw [List.length_map, List.length_take, show min 5 σ.length = 5 by omega]; norm_num; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  have hv00 := congrArg E2V.MS4F.v00 hq
  have hv01 := congrArg E2V.MS4F.v01 hq
  have hv10 := congrArg E2V.MS4F.v10 hq
  simp only [q4v] at hv00 hv01 hv10
  rw [hr, hd, hx2, hx1, hL, hsA, hz, zero_add, zero_add, add_zero, E2V.msEvalF]
  have hρd : (ρ.map (C2.val M)).drop ((σ.map (C2.val M)).length - 5) = [] := by simp [hρ]
  rw [hρd, show E2V.eqAtF ([] : List FE2) (0 / 2 ^ (σ.map (C2.val M)).length) = 1 from rfl, one_mul, sumF_eq_sum,
    lsum_range, Finset.sum_range_succ, List.map_take, sum_take_eq _ 31 (by simp [hAl]), List.map_map, lsum_range]
  simp only [List.length_map, ← List.map_drop, ← List.map_take] at hv00 hv01 hv10 ⊢
  rw [hv00, hv01, hv10, Finset.mul_sum, Finset.sum_mul,
    show ∀ X Y Z : FE2, X + (Y + Z) = (X + Z) + Y from fun _ _ _ => by ring, ← Finset.sum_add_distrib,
    hAd 31 (by norm_num)]
  congr 1
  · refine Finset.sum_congr rfl fun dd hdd => ?_
    have hdd' := Finset.mem_range.mp hdd
    simp only [Function.comp_apply]
    rw [hAd dd (by omega), hlt' (dd + 1) (by omega), ← getD_val A (by omega), hAd dd (by omega),
      show (dd == 31) = false by simp; omega, show (dd + 1) % 32 = dd + 1 by omega]
    by_cases hc : t % 32 < dd + 1
    · rw [if_pos hc, decide_eq_true hc]
      simp only [E2V.MS4F.get]
      linear_combination (E2V.eqAtF ((σ.take 5).map (C2.val M)) dd * (μ.map (C2.val M)).getD (dd + 1) 0 *
          (E2V.msTailF ((σ.drop 5).map (C2.val M)) ((ρ.take (σ.length - 5)).map (C2.val M)) (t / 32)).v00) * fe2_two
    · rw [if_neg hc, decide_eq_false hc]
      simp only [E2V.MS4F.get]
      ring

/-! ## `ω` -/

theorem hs_g2LaneForm {z : C2} (hz : z.val M = 0) {B : List C2} (hB : B.length = 25) (R : ℕ → C2) {l : ℕ}
    (hl : l < 25) :
    Hs c M (g2LaneForm z B R l)
      (fun r => r.val M = Lvm.Q1.laneFormF (B.map (C2.val M)) (fun s => (R s).val M) l) := by
  unfold g2LaneForm
  have hp : ∀ i < 25, keccakPi i < 25 := fun i hi => by unfold keccakPi; omega
  refine hs_bind (hs_g2Mul _ _ _) fun t1 h1 => hs_bind (hs_g2Dot _ _) fun t2 h2 => hs_mono (hs_g2Dot _ _) fun r hr => ?_
  rw [hr, h2, h1, hz, add_zero, Lvm.Q1.laneFormF, sumF_eq_sum, sumF_eq_sum, getD_val B (by rw [hB]; exact hp l hl),
    List.map_map, List.map_map]
  congr 2
  · refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    have := List.mem_range.mp hy
    simp only [Function.comp_apply]
    rw [getD_val B (by rw [hB]; exact hp _ (by omega))]
  · refine List.map_congr_left fun y hy => ?_
    have := List.mem_range.mp hy
    simp only [Function.comp_apply]
    rw [getD_val B (by rw [hB]; exact hp _ (by omega))]

theorem hs_g2Eq0 {z : C2} (hz : z.val M = 0) : ∀ (acc : C2) (rs : List C2),
    Hs c M (g2Eq0 z acc rs) (fun r => r.val M = acc.val M * E2V.eqAtF (rs.map (C2.val M)) 0)
  | acc, [] => hs_pure (by rw [List.map_nil, show E2V.eqAtF ([] : List FE2) 0 = 1 from rfl, mul_one])
  | acc, r :: rs => hs_bind (hs_g2One r) fun r1 h1 => hs_bind (hs_g2Mul acc r1 z) fun a ha =>
    hs_mono (hs_g2Eq0 hz a rs) fun x hx => by
      rw [hx, ha, h1, hz, add_zero, List.map_cons,
        show E2V.eqAtF (r.val M :: rs.map (C2.val M)) 0 = (1 + r.val M) * E2V.eqAtF (rs.map (C2.val M)) 0 from by
          show (if 0 % 2 = 1 then r.val M else 1 + r.val M) * E2V.eqAtF (rs.map (C2.val M)) (0 / 2) = _; simp]
      ring

theorem hs_g2Omega {z : C2} (hz : z.val M = 0) {B eZ : List C2} (hB : B.length = 25) {j : ℕ} (hj : j < 1600) :
    Hs c M (g2Omega z B eZ j) (fun r => r.val M =
      Lvm.Q1.laneFormF (B.map (C2.val M)) (fun s => (eZ.getD ((j % 64 + s) % 64) default).val M) (j / 64)) :=
  hs_g2LaneForm hz hB _ (by omega)

/-! ## The target block -/

section PreW
variable (M) (P : ℕ) (cv : ℕ → C2)

/-- The input claim's parts from `cv` (`LvmQWire`'s layout). -/
def cvMu : List FE2 := (List.range 32).map fun i => (cv (1 + i)).val M
def cvRho : List FE2 := (List.range (P + 1)).map fun i => (cv (34 + i)).val M
def cvB : List FE2 := (List.range 25).map fun l => (cv (35 + P + l)).val M
def cvA : List FE2 := (List.range 6).map fun i => (cv (60 + P + i)).val M

/-- `ω_j` from `B` and `eq(a, ·)`. -/
def omegaF (j : ℕ) : FE2 :=
  Lvm.Q1.laneFormF (cvB M P cv) (fun s => (eqKernelF (cvA M P cv)).getD ((j % 64 + s) % 64) 0) (j / 64)

/-- `⟨ω, 0x43⟩`: the five constant positions. -/
def c43F : FE2 := omegaF M P cv 0 + omegaF M P cv 1 + omegaF M P cv 6 + omegaF M P cv 264 + omegaF M P cv 1087

/-- `ι(0)`. -/
def io0F : FE2 := E2V.eqAtF (cvRho M P cv) 0 * (cvMu M cv).getD 0 0

/-- **The wiring sumcheck's target** as the rows compute it. -/
def targetF (sbv : List FE2) (t : ℕ) : FE2 :=
  (cv 0).val M + io0F M P cv * (c43F M P cv + ((List.range 256).map fun p => omegaF M P cv (8 + p) * sbv.getD p 0).sum) +
    c43F M P cv * (E2V.thrEvalF (cvRho M P cv) (cvMu M cv) t + io0F M P cv)

end PreW

theorem wPos_length : wPos.length = 261 := by simp [wPos]

theorem wPos_ix (p : ℕ) (hp : p ≤ 256) : wPos.getD (wIx p) 0 = 8 + p := by
  simp only [wPos, wIx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil, List.getElem?_map, List.getElem?_range (show 3 + p - 3 < 257 by omega),
    Option.map_some, Option.getD_some]
  omega

theorem wPos_small : wPos.getD 0 0 = 0 ∧ wPos.getD 1 0 = 1 ∧ wPos.getD 2 0 = 6 := by
  simp [wPos, List.getD_eq_getElem?_getD]

theorem wPos_last : wPos.getD 260 0 = 1087 := by
  simp only [wPos, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem getD_omega {om : List C2} {f : ℕ → FE2} (h : om.map (C2.val M) = wPos.map f) {i : ℕ} (hi : i < 261) :
    (om.getD i default).val M = f (wPos.getD i 0) := by
  have hl : om.length = 261 := by have := congrArg List.length h; simpa [wPos_length] using this
  rw [getD_val om (by omega), h]
  simp [List.getD_eq_getElem?_getD, wPos_length, hi]

theorem hs_mapB' {α : Type} (f : α → BM C2) (g : α → FE2) :
    ∀ l : List α, (∀ a ∈ l, Hs c M (f a) (fun r => r.val M = g a)) →
      Hs c M (mapB f l) (fun rs => rs.map (C2.val M) = l.map g)
  | [], _ => hs_pure rfl
  | a :: l, hf => hs_bind (hf a (List.mem_cons_self ..)) fun r hr =>
    hs_bind (hs_mapB' f g l fun b hb => hf b (List.mem_cons_of_mem _ hb)) fun rs hrs =>
    hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

theorem wPos_lt {j : ℕ} (hj : j ∈ wPos) : j < 1600 := by
  simp only [wPos, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.mem_nil_iff, or_false] at hj
  omega

/-- **The target block's values.** -/
theorem hs_preW2 (P : ℕ) (cv : ℕ → C2) (mb sb : List C2) (t : ℕ) (hmb : mb.map (C2.val M) = bitsF t (P + 6))
    (ht : t < 2 ^ (P + 6)) (hsb : sb.length = 256) :
    Hs c M (preW2 P cv mb sb) (fun G => G.z.val M = 0 ∧ G.one.val M = 1 ∧
      G.om.map (C2.val M) = wPos.map (omegaF M P cv) ∧
      G.lt.map (C2.val M) = (List.range 33).map (fun k => ((eqKernelF ((mb.take 5).map (C2.val M))).take k).sum) ∧
      G.target.val M = targetF M P cv (sb.map (C2.val M)) t) := by
  unfold preW2
  refine hs_bind (hs_g2Zero _) fun z hz => hs_bind (hs_g2One z) fun one ho => ?_
  rw [hz, add_zero] at ho
  refine hs_bind (hs_g2EqTab hz [one] _) fun eZ heZ => ?_
  have heZ' : eZ.map (C2.val M) = eqKernelF (cvA M P cv) := by
    rw [heZ, List.map_cons, List.map_nil, ho, cvA, List.map_map]; rfl
  have heZl : eZ.length = 64 := by
    have := congrArg List.length heZ'; rw [List.length_map, eqKernelF_length, cvA] at this; simpa using this
  refine hs_bind (hs_mapB' _ (omegaF M P cv) wPos fun j hj => hs_mono (hs_g2Omega hz (by simp) (wPos_lt hj))
    fun r hr => ?_) fun om hom => ?_
  · rw [hr, omegaF, cvB, List.map_map]
    congr 1
    funext s
    rw [getD_val eZ (by rw [heZl]; omega), heZ']
  refine hs_bind (hs_g2Eq0 hz one _) fun e0 he0 => hs_bind (hs_g2Mul _ _ _) fun io0 hio0 => ?_
  refine hs_bind (hs_g2LtTab hz ho (mb.take 5)) fun lt hlt => ?_
  refine hs_bind (hs_g2Thr hz ho _ _ mb lt t (by simp) (by rw [hmb]; simp) (by simpa using ht) hlt) fun thr hthr => ?_
  refine hs_bind (hs_g2Sum z _) fun c43 hc43 => hs_bind (hs_g2Dot c43 _) fun pd hpd => ?_
  refine hs_bind (hs_g2Add _ _) fun ti hti => hs_bind (hs_g2Mul _ _ _) fun t1 ht1 =>
    hs_bind (hs_g2Mul _ _ _) fun tgt htgt => hs_pure ⟨hz, ho, hom, hlt, ?_⟩
  have g := fun i (hi : i < 261) => getD_omega hom hi
  have hmu0 : (((List.range 32).map (fun i => cv (1 + i))).getD 0 default).val M = (cvMu M cv).getD 0 0 := by
    rw [getD_val _ (by simp), cvMu, List.map_map]; rfl
  have hc : c43.val M = c43F M P cv := by
    rw [hc43, hz, zero_add]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [g 0 (by norm_num), g 1 (by norm_num), g 2 (by norm_num), g 259 (by norm_num), g 260 (by norm_num),
      show wPos.getD 259 0 = 264 from by simpa [wIx] using wPos_ix 256 le_rfl, wPos_small.1, wPos_small.2.1,
      wPos_small.2.2, wPos_last, c43F]
    ring
  have hp : pd.val M = c43F M P cv + ((List.range 256).map fun p => omegaF M P cv (8 + p) * (sb.map (C2.val M)).getD p 0).sum := by
    rw [hpd, hc, List.map_map]
    refine congrArg (fun x => c43F M P cv + x) ?_
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hp' := List.mem_range.mp hp
    simp only [Function.comp_apply]
    rw [g (wIx p) (by simp [wIx]; omega), wPos_ix p (by omega), getD_val sb (by omega)]
  have hi0 : io0.val M = io0F M P cv := by
    rw [hio0, he0, ho, hz, one_mul, add_zero, hmu0, io0F, cvRho, List.map_map]; rfl
  have hth : thr.val M = E2V.thrEvalF (cvRho M P cv) (cvMu M cv) t := by
    rw [hthr, cvRho, cvMu, List.map_map, List.map_map]; rfl
  rw [htgt, ht1, hti, hth, hp, hc, hi0, targetF]
  ring

/-! ## The final check and the slot check -/

/-- **The final check** (`postW2`): with the gate on, the wiring sumcheck's final claim is `msEvalF ρ μ σ 0 t · g_D`. -/
theorem postW2_sound (P qg : ℕ) (cv : ℕ → C2) (mb σ lt : List C2) {z one : C2} (final : C2) {gate : Cell} (t : ℕ)
    (hz : z.val M = 0) (ho : one.val M = 1) (hg : gate.val M = 1) (hσ : σ.length = P + 6)
    (hmb : mb.map (C2.val M) = bitsF t (P + 6)) (ht : t < 2 ^ (P + 6))
    (hlt : lt.map (C2.val M) = (List.range 33).map fun k => ((eqKernelF ((mb.take 5).map (C2.val M))).take k).sum) :
    HsA c M (postW2 P qg cv mb σ lt z one final gate) (fun g => g = ld2 qg ∧
      final.val M = E2V.msEvalF (cvRho M P cv) (cvMu M cv) (σ.map (C2.val M)) 0 t * (ld2 qg).val M) := by
  unfold postW2
  refine hsA_bind (hsA_of_hs (hs_g2Ms hz ho _ _ σ mb lt t (by omega) (by simp [hσ]) (by simp) (by rw [hmb, hσ])
    (by rw [hσ]; exact ht) hlt)) fun ms hms => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun e he => hsA_bind (hsA_g2Assert e gate hg) fun _ hE =>
    hsA_pure ⟨rfl, ?_⟩
  rw [he] at hE
  have hf : final.val M = ms.val M * (ld2 qg).val M := by
    linear_combination hE - (ms.val M * (ld2 qg).val M) * fe2_two
  rw [hf, hms, cvRho, cvMu, List.map_map, List.map_map]
  rfl

/-- **The slot check** (`slotW2`): with the gate on, the slot sumcheck's final claim is
`Σ_z W_z(τ)·slice_z`, `W_z(τ) = Σ_{o<4} eq(τ, o)·ω_{8+64o+z}`. -/
theorem slotW2_sound (qs : ℕ) {om : List C2} {f : ℕ → FE2} (hom : om.map (C2.val M) = wPos.map f) (τ : List C2)
    {z one : C2} (final : C2) {gate : Cell} (hz : z.val M = 0) (ho : one.val M = 1) (hg : gate.val M = 1)
    (hτ : τ.length = 2) :
    HsA c M (slotW2 qs om τ z one final gate) (fun _ => final.val M =
      ((List.range 64).map fun zz => ((List.range 4).map fun o =>
        (eqKernelF (τ.map (C2.val M))).getD o 0 * f (8 + 64 * o + zz)).sum * (ld2 (qs + 2 * zz)).val M).sum) := by
  unfold slotW2
  refine hsA_bind (hsA_of_hs (hs_g2EqTab hz [one] τ)) fun et het => ?_
  have het' : et.map (C2.val M) = eqKernelF (τ.map (C2.val M)) := by
    rw [het, List.map_cons, List.map_nil, ho]; rfl
  have hetl : et.length = 4 := by
    have := congrArg List.length het'; rw [List.length_map, eqKernelF_length, List.length_map, hτ] at this
    simpa using this
  refine hsA_bind (hsA_of_hs (hs_mapB' _ (fun zz => ((List.range 4).map fun o =>
      (eqKernelF (τ.map (C2.val M))).getD o 0 * f (8 + 64 * o + zz)).sum) (List.range 64) fun zz hzz =>
        hs_mono (hs_g2Dot z _) fun r hr => ?_)) fun W hW => ?_
  · have hzz' := List.mem_range.mp hzz
    rw [hr, hz, zero_add, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun o ho' => ?_)
    have ho'' := List.mem_range.mp ho'
    simp only [Function.comp_apply]
    rw [getD_val et (by omega), het', getD_omega hom (by simp [wIx]; omega), wPos_ix _ (by omega)]
    congr 2; omega
  refine hsA_bind (hsA_of_hs (hs_g2Dot final _)) fun e he => hsA_mono (hsA_g2Assert e gate hg) fun _ hE => ?_
  have hWl : W.length = 64 := by have := congrArg List.length hW; simpa using this
  rw [he] at hE
  have hs : ((List.range 64).map ((fun e : C2 × C2 => e.1.val M * e.2.val M) ∘
      fun zz => (W.getD zz default, (slices2 qs).getD zz default))).sum =
      ((List.range 64).map fun zz => ((List.range 4).map fun o =>
        (eqKernelF (τ.map (C2.val M))).getD o 0 * f (8 + 64 * o + zz)).sum * (ld2 (qs + 2 * zz)).val M).sum := by
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    simp only [Function.comp_apply]
    rw [getD_val W (by omega), hW]
    simp [List.getD_eq_getElem?_getD, hzz', slices2]
  rw [List.map_map, hs] at hE
  linear_combination hE - (((List.range 64).map fun zz => ((List.range 4).map fun o =>
        (eqKernelF (τ.map (C2.val M))).getD o 0 * f (8 + 64 * o + zz)).sum * (ld2 (qs + 2 * zz)).val M).sum) * fe2_two

/-! ## The wire gadget -/

/-- **The wire gadget is sound** (gate on): its points are the stream's challenges, the wiring sumcheck runs from
`targetF`, its final claim is `msEvalF ρ μ σ 0 t · g_D`, the slot sumcheck runs from `g_D` and its final claim is the
slot weights against the slices. `mb`'s cells hold `t`'s bits (`t < 2^(P+5)`), `zk` is a `K` zero. -/
theorem wireG2_sound (P qw : ℕ) (cv : ℕ → C2) (mb sb : List Cell) (zk gate : Cell) (t : ℕ)
    (hzk : zk.val M = 0) (hg : gate.val M = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => kC2 b zk).map (C2.val M) = bitsF t (P + 6)) (ht : t < 2 ^ (P + 6)) :
    HsA c M (wireG2 P qw cv mb sb zk gate) (fun o =>
      o.sigma = (sc2Ans (P + 6) qw).map ld2 ∧
      o.final.val M = scFold2 (fun k => (ld2 k).val M) (P + 6) qw
        (targetF M P cv ((sb.map fun b => kC2 b zk).map (C2.val M)) t) ∧
      o.gD = ld2 (wireLanes (P + 6) qw).gD ∧
      o.final.val M = E2V.msEvalF (cvRho M P cv) (cvMu M cv) (o.sigma.map (C2.val M)) 0 t * o.gD.val M ∧
      o.tau = (sc2Ans 2 (wireLanes (P + 6) qw).slot).map ld2 ∧
      o.slices = slices2 (wireLanes (P + 6) qw).slices ∧
      scFold2 (fun k => (ld2 k).val M) 2 (wireLanes (P + 6) qw).slot (o.gD.val M) =
        ((List.range 64).map fun zz => ((List.range 4).map fun ob =>
          (eqKernelF (o.tau.map (C2.val M))).getD ob 0 * omegaF M P cv (8 + 64 * ob + zz)).sum *
            (ld2 ((wireLanes (P + 6) qw).slices + 2 * zz)).val M).sum) := by
  unfold wireG2
  refine hsA_bind (hsA_of_hs (hs_preW2 P cv _ _ t hmb ht (by simp [hsb]))) fun G ⟨hz, ho, hom, hlt, htg⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_sc2 (P + 6) qw G.target)) fun sc ⟨hs1, hs2⟩ => ?_
  refine hsA_bind (postW2_sound P _ cv _ sc.1 G.lt sc.2 t hz ho hg (by rw [hs1]; simp [sc2Ans]) hmb ht hlt)
    fun g ⟨hg1, hg2⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_sc2 2 _ g)) fun sl ⟨hl1, hl2⟩ => ?_
  refine hsA_bind (slotW2_sound _ hom sl.1 sl.2 hz ho hg (by rw [hl1]; simp [sc2Ans])) fun _ hsl => ?_
  refine hsA_pure ⟨hs1, by rw [hs2, htg], hg1, by rw [hg1]; exact hg2, hl1, rfl, ?_⟩
  rw [← hl2, ← hsl]

end Lvm.Q2
