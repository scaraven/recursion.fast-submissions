/- `LvmE2VWidthsFOff` (GOLF2 off-path move, group 27 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmWiringK, LvmTyped, LvmQTypedGuard, LvmCertTInst, LvmTypedVEqTop, LvmMPVEq, LvmE2VFol, LvmE2VWidthsF,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmWiringK
import LvmTyped
import LvmQTypedGuard
import LvmCertTInst
import LvmTypedVEqTop
import LvmMPVEq
import LvmE2VFol
import LvmE2VWidthsF
import LvmE2QNodeChkGOff
import LvmE2QPinOpenFOff
import LvmE2VMidSpecFOff
import LvmMPMidTOff
import LvmTypedVEqPhasesXOff
import LvmVEqTapeOff
import LvmVEqTopOff
import LvmVEqWireOff
import LvmVerifierSTOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmSpecRulesCert
import LvmTensorSwitch
import LvmVEqTape
import LvmVerifierF
import LvmVerifierST

-- ===== from `LvmWiringK` =====

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- **The limb factor.** -/
theorem limbVal_eq (a b : 𝔽) :
    limbValG a b = ((List.range 3).map fun m ↦ eqWG [a, b] m * (KRing.ofE FE.y ^ m)).sum := by
  simp [limbValG, List.range_succ, eqWG]
  ring

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

omit [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
/-- `1 − a − c` is the one-bit sum `Σ_b eq(a, b)·eq(c, b)` in characteristic 2. -/
theorem pair_sum (a c : 𝔽) : 1 - a - c = ((List.range 2).map fun b ↦ eqWG [a] b * eqWG [c] b).sum := by
  simp [List.range_succ, eqWG]
  have h2 : (2 : 𝔽) = 0 := CharTwo.two_eq_zero
  linear_combination (- a * c) * h2

/-- **The paired factor is the one-bit sum** (characteristic 2). -/
theorem kfVal_pair (P : PtG 𝔽) (i j : ℕ) :
    kfValG P (.pair i j) = ((List.range 2).map fun b ↦
      eqWG [P.rx.getD i 0] b * eqWG [P.ry.getD j 0] b).sum := pair_sum _ _

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]

/-- Sum out relative bit `p` of a table (`Σ_b eq(r, b) = 1`): additions only. -/
def sumOut (t : Array 𝔽) (p : ℕ) : Array 𝔽 :=
  (Array.range (t.size / 2)).map fun i ↦
    let lo := i % 2 ^ p
    let hi := (i >>> p) <<< (p + 1)
    t.getD (hi ||| lo) 0 + t.getD (hi ||| 2 ^ p ||| lo) 0

end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]

theorem tab_eqLevels_get (r : Array 𝔽) (lo n k v : ℕ) (hk : k ≤ n) (hv : v < 2 ^ (n - k)) :
    ((eqLevelsG r lo n).getD k #[]).getD v 0 = eqWG (sub r (lo + k) (n - k)) v :=
  (tab_eqLevels_rep r lo n k hk).2 v (by simpa [sub] using hv)

end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]

theorem tab_eqW_mod (r : List 𝔽) (x : ℕ) : eqWG r (x % 2 ^ r.length) = eqWG r x := by
  induction r generalizing x with
  | nil => simp [eqWG]
  | cons a r ih =>
    simp only [eqWG, List.length_cons]
    simp only [Nat.mod_mod_of_dvd x (dvd_pow_self 2 (by (clear * -; omega) : r.length + 1 ≠ 0))]
    simp only [pow_succ', Nat.mod_mul_right_div_self, ih]

theorem tab_bound (l q b P Q : ℕ) (hl : l < P) (hq : q < Q) (hb : b ≤ 1) : l + P * (b + 2 * q) < P * (2 * Q) :=
  calc l + P * (b + 2 * q) < P + P * (b + 2 * q) := by (clear * - hl; omega)
    _ = P * (b + 2 * q + 1) := by ring
    _ ≤ P * (2 * Q) := Nat.mul_le_mul_left _ (by (clear * - hq hb; omega))

theorem tab_sumOut_rep (t : Array 𝔽) (A B : List 𝔽) (c : 𝔽) (h : tab_Rep t (A ++ c :: B)) :
    tab_Rep (sumOut t A.length) (A ++ B) := by
  obtain ⟨h1, h2⟩ := h
  have hs : 2 ^ (A ++ c :: B).length = 2 ^ A.length * (2 * 2 ^ B.length) := by
    simp only [List.length_append, List.length_cons]
    rw [show A.length + (B.length + 1) = A.length + B.length + 1 by (clear * -; omega), pow_succ, pow_add]; ring
  have hs' : 2 ^ (A ++ B).length = 2 ^ A.length * 2 ^ B.length := by simp [pow_add]
  have hs2 : 2 ^ A.length * (2 * 2 ^ B.length) = 2 * (2 ^ A.length * 2 ^ B.length) := by ring
  have hsz : (sumOut t A.length).size = 2 ^ (A ++ B).length := by
    simp only [sumOut, Array.size_map, Array.size_range, h1, hs, hs', hs2]; (clear * -; omega)
  refine ⟨hsz, fun i hi => ?_⟩
  have hi2 : i < t.size / 2 := by rw [h1, hs, hs2]; rw [hs'] at hi; (clear * - hs' hsz hi; omega)
  simp only [sumOut, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hi2, ↓reduceIte,
    Option.map_some, Option.getD_some]
  have hPpos : 0 < 2 ^ A.length := by positivity
  obtain ⟨l, q, hl, rfl⟩ : ∃ l q, l < 2 ^ A.length ∧ i = l + 2 ^ A.length * q :=
    ⟨_, _, Nat.mod_lt _ hPpos, (Nat.mod_add_div i _).symm⟩
  have hq : q < 2 ^ B.length := by
    rw [hs'] at hi
    by_contra hc
    have : 2 ^ A.length * 2 ^ B.length ≤ 2 ^ A.length * q := Nat.mul_le_mul_left _ (by (clear * - hc; omega))
    (clear * - h1 hs hs' hs2 hsz hi2 this; omega)
  have hmod : (l + 2 ^ A.length * q) % 2 ^ A.length = l := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have hdiv : (l + 2 ^ A.length * q) >>> A.length = q := by
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hPpos, Nat.div_eq_of_lt hl, zero_add]
  have hl1 : l < 2 ^ (A.length + 1) := by rw [pow_succ]; (clear * - hl hmod; omega)
  have e0 : q <<< (A.length + 1) ||| l = l + 2 ^ A.length * (0 + 2 * q) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl1, Nat.shiftLeft_eq, pow_succ]; ring
  have e1 : q <<< (A.length + 1) ||| 2 ^ A.length ||| l = l + 2 ^ A.length * (1 + 2 * q) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by rw [pow_succ]; (clear * - hPpos; omega) : 2 ^ A.length < 2 ^ (A.length + 1)),
      show q <<< (A.length + 1) + 2 ^ A.length = (2 * q + 1) <<< A.length by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_succ]; ring,
      ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]; ring
  rw [hmod, hdiv, e0, e1, ← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?, h2 _ (by rw [hs]; exact tab_bound _ _ _ _ _ hl hq (by (clear * -; omega))),
    h2 _ (by rw [hs]; exact tab_bound _ _ _ _ _ hl hq le_rfl), tab_eqW_append _ _ _ _ hl,
    tab_eqW_append _ _ _ _ hl, tab_eqW_append _ _ _ _ hl]
  simp only [eqWG]
  rw [show (0 + 2 * q) % 2 = 0 by (clear * - hdiv; omega), show (1 + 2 * q) % 2 = 1 by (clear * - hdiv; omega), show (0 + 2 * q) / 2 = q by (clear * - hdiv; omega),
    show (1 + 2 * q) / 2 = q by (clear * - hdiv; omega)]
  simp only [show (0 : ℕ) ≠ 1 from by (clear * -; omega), ↓reduceIte]
  ring

theorem tab_range_split (N m : ℕ) (hm : m < N) :
    List.range N = List.range m ++ m :: List.range' (m + 1) (N - m - 1) := by
  conv_lhs => rw [show N = m + (N - m - 1 + 1) by omega]
  rw [List.range_eq_range', List.range_eq_range', ← List.range'_append_1, List.range'_succ]
  simp

theorem tab_marg_loop (N : ℕ) (c : ℕ → 𝔽) (Q : ℕ → Bool) (m : ℕ) (hm : m ≤ N) (t : Array 𝔽)
    (h : tab_Rep t (((List.range N).filter fun i ↦ decide (i < m) || Q i).map c)) :
    tab_Rep ((((List.range m).filter fun i ↦ !Q i).reverse).foldl (fun b a ↦ sumOut b a) t)
      (((List.range N).filter Q).map c) := by
  induction m generalizing t with
  | zero => simpa using h
  | succ m ih =>
    have hsplit := tab_range_split N m (by (clear * - hm; omega))
    have hhi : ∀ (P : ℕ → Bool), (∀ i, m + 1 ≤ i → P i = Q i) →
        (List.range' (m + 1) (N - m - 1)).filter P = (List.range' (m + 1) (N - m - 1)).filter Q := by
      intro P hP
      apply List.filter_congr
      intro i hi
      rw [List.mem_range'_1] at hi
      exact hP i hi.1
    have hlo : ∀ (P : ℕ → Bool), (∀ i, i < m → P i = true) → (List.range m).filter P = List.range m := by
      intro P hP
      apply List.filter_eq_self.2
      intro i hi
      exact hP i (List.mem_range.1 hi)
    rw [List.range_succ, List.filter_append, List.reverse_append, List.foldl_append]
    cases hQ : Q m
    · simp only [List.filter_cons, List.filter_nil, hQ, Bool.not_false, ↓reduceIte, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.foldl_cons, List.foldl_nil]
      apply ih (by (clear * - hm; omega))
      have L1 : (List.range N).filter (fun i ↦ decide (i < m + 1) || Q i) =
          List.range m ++ m :: (List.range' (m + 1) (N - m - 1)).filter Q := by
        rw [hsplit, List.filter_append, List.filter_cons, hlo _ (fun i hi ↦ by simp; (clear * - hi; omega)),
          hhi _ (fun i hi ↦ by simp; (clear * - hi; omega))]
        simp
      have L2 : (List.range N).filter (fun i ↦ decide (i < m) || Q i) =
          List.range m ++ (List.range' (m + 1) (N - m - 1)).filter Q := by
        rw [hsplit, List.filter_append, List.filter_cons, hlo _ (fun i hi ↦ by simp; (clear * - hi; omega)),
          hhi _ (fun i hi ↦ by simp; (clear * - hi; omega))]
        simp [hQ]
      rw [L1, List.map_append, List.map_cons] at h
      have := tab_sumOut_rep t _ _ _ h
      rw [L2, List.map_append]
      simpa using this
    · simp only [List.filter_cons, List.filter_nil, hQ, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.reverse_nil, List.foldl_nil]
      apply ih (by (clear * - hm; omega))
      rwa [List.filter_congr (q := fun i ↦ decide (i < m) || Q i) (fun i _ ↦ by
        by_cases him : i = m
        · subst him; simp [hQ]
        · show (decide (i < m + 1) || Q i) = (decide (i < m) || Q i)
          rw [decide_eq_decide.2 (by (clear * - him; omega) : i < m + 1 ↔ i < m)])] at h

end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]

/-- B1-K's `margTab` (one `sumOut` per missing bit), verbatim. -/
def marg_margTab0 (lv : Array (Array 𝔽)) (lo n : ℕ) (bits : List ℕ) : Array 𝔽 := Id.run do
  match bits.head? with
  | none => return #[1]
  | some b0 =>
    let k := b0 - lo
    let mut t := lv.getD k #[]
    let miss := ((List.range (n - k)).filter fun i ↦ !bits.contains (lo + k + i)).reverse
    for p in miss do
      t := sumOut t p
    return t

/-- B1-K's proof of `tab_margTab_rep`, for `marg_margTab0`. -/
theorem marg_margTab0_rep (r : Array 𝔽) (lo n b0 : ℕ) (bs : List ℕ) (hs : (b0 :: bs).Pairwise (· < ·))
    (hb : ∀ b ∈ b0 :: bs, lo ≤ b ∧ b < lo + n) :
    tab_Rep (marg_margTab0 (eqLevelsG r lo n) lo n (b0 :: bs)) ((b0 :: bs).map fun b ↦ r.getD b 0) := by
  unfold marg_margTab0
  simp only [Id.run, List.head?_cons, List.forIn_pure_yield_eq_foldl, pure_bind]
  have h0 := hb b0 List.mem_cons_self
  have hk : lo + (b0 - lo) = b0 := by (clear * - h0; omega)
  have hrep := tab_eqLevels_rep r lo n (b0 - lo) (by (clear * - h0 hk; omega))
  have := tab_marg_loop (n - (b0 - lo)) (fun i ↦ r.getD (lo + (b0 - lo) + i) 0)
    (fun i ↦ (b0 :: bs).contains (lo + (b0 - lo) + i)) (n - (b0 - lo)) le_rfl _ (by
      rw [List.filter_eq_self.2 (fun i hi ↦ by simp at hi; simp [hi])]
      exact hrep)
  have hbits := tab_bits_filter (b0 :: bs) b0 (n - (b0 - lo)) hs (fun b hb' ↦ by
    have := hb b hb'
    refine ⟨?_, by (clear * - h0 hk this; omega)⟩
    rcases List.mem_cons.1 hb' with rfl | hb''
    · exact le_rfl
    · exact le_of_lt (List.rel_of_pairwise_cons hs hb''))
  have heq : (b0 :: bs).map (fun b ↦ r.getD b 0) = List.map (fun i ↦ r.getD (lo + (b0 - lo) + i) 0)
      (List.filter (fun i ↦ (b0 :: bs).contains (lo + (b0 - lo) + i)) (List.range (n - (b0 - lo)))) := by
    rw [hk]
    conv_lhs => rw [← hbits]
    rw [List.map_map]
    rfl
  rw [heq]
  exact this

theorem marg_rep_unique (t t' : Array 𝔽) (L : List 𝔽) (h : tab_Rep t L) (h' : tab_Rep t' L) : t = t' := by
  apply Array.ext (h.1.trans h'.1.symm)
  intro i hi hi'
  have e := (h.2 i (h.1 ▸ hi)).trans (h'.2 i (h.1 ▸ hi)).symm
  simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] using e

/-- **The one-pass `margTab` (B1-K2) equals B1-K's** on the level tables, for sorted bits inside the range. -/
theorem marg_margTab_eq (r : Array 𝔽) (lo n : ℕ) (bits : List ℕ) (hs : bits.Pairwise (· < ·))
    (hb : ∀ b ∈ bits, lo ≤ b ∧ b < lo + n) :
    margTabG (eqLevelsG r lo n) lo n bits = marg_margTab0 (eqLevelsG r lo n) lo n bits := by
  cases bits with
  | nil => rfl
  | cons b0 bs =>
    exact marg_rep_unique _ _ _ (tab_margTab_rep r lo n b0 bs hs hb) (marg_margTab0_rep r lo n b0 bs hs hb)

end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The end of the run of atoms from `i` (below `hi`) that agree with atom `i` at level `d`. -/
def runEnd (as : Array Atom) (d i hi : ℕ) : ℕ := Id.run do
  let k := (as.getD i default).keys.getD d (0, 0)
  let mut j := i + 1
  while j < hi && (as.getD j default).keys.getD d (0, 0) == k do
    j := j + 1
  return j

/-- **The atom sum over `[lo, hi)` from level `d`** (levels `[d, D)`): each maximal run of equal level-`d`
keys is one product with the run's sum over the deeper levels; at level `D` the weights are summed. A key of
table `0` multiplies by nothing. -/
def evalRuns (T : Array (Array 𝔽)) (as : Array Atom) (D : ℕ) : ℕ → ℕ → ℕ → ℕ → 𝔽
  | 0, _, _, _ => 0
  | fuel + 1, d, lo, hi =>
    if d ≥ D then
      (List.range (hi - lo)).foldl (fun acc i ↦ acc + KRing.ofE (as.getD (lo + i) default).w) 0
    else Id.run do
      let mut acc : 𝔽 := 0
      let mut i := lo
      let mut guard := hi - lo
      while i < hi && guard > 0 do
        let j := runEnd as d i hi
        let k := (as.getD i default).keys.getD d (0, 0)
        let s := evalRuns T as D fuel (d + 1) i j
        acc := acc + (if k.1 == 0 then s else if s == 1 then keyValG T k else keyValG T k * s)
        i := j
        guard := guard - 1
      return acc

theorem runs_loop {β : Type} (c : β → Bool) (n : β → β) (P Q : β → Prop) (μ : β → ℕ)
    (hstep : ∀ s, P s → c s = true → P (n s) ∧ μ (n s) < μ s)
    (hstop : ∀ s, P s → c s = false → Q s) (s : β) (hs : P s) :
    Q (forIn (m := Id) Lean.Loop.mk s fun _ s ↦
      if c s = true then pure (ForInStep.yield (n s)) else pure (ForInStep.done s)) := by
  induction h : μ s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    change Q (Lean.Loop.forIn (m := Id) _ _ _)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    by_cases hc : c s = true
    · obtain ⟨hP, hμ⟩ := hstep s hs hc
      simp only [hc, ite_true]
      exact ih _ (h ▸ hμ) _ hP rfl
    · simp only [hc]
      exact hstop s hs (by simpa using hc)

theorem runs_FE_beq {a b : FE} (h : (a == b) = true) : a = b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  change (a0 == b0 && a1 == b1 && a2 == b2) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- `runEnd`: the run `[i, j)` is nonempty, stops by `hi` when `i < hi`, shares atom `i`'s level-`d` key, and is
maximal. -/
theorem runs_runEnd (as : Array Atom) (d i hi : ℕ) :
    i < runEnd as d i hi ∧ (i < hi → runEnd as d i hi ≤ hi) ∧
    (∀ t, i ≤ t → t < runEnd as d i hi →
      (as.getD t default).keys.getD d (0, 0) = (as.getD i default).keys.getD d (0, 0)) ∧
    (runEnd as d i hi < hi →
      (as.getD (runEnd as d i hi) default).keys.getD d (0, 0) ≠ (as.getD i default).keys.getD d (0, 0)) := by
  unfold runEnd
  refine runs_loop _ _
    (fun s ↦ i < s ∧ (i < hi → s ≤ hi) ∧ ∀ t, i ≤ t → t < s →
      (as.getD t default).keys.getD d (0, 0) = (as.getD i default).keys.getD d (0, 0))
    (fun s ↦ i < s ∧ (i < hi → s ≤ hi) ∧
      (∀ t, i ≤ t → t < s →
        (as.getD t default).keys.getD d (0, 0) = (as.getD i default).keys.getD d (0, 0)) ∧
      (s < hi → (as.getD s default).keys.getD d (0, 0) ≠ (as.getD i default).keys.getD d (0, 0)))
    (fun s ↦ hi - s) ?_ ?_ _ ?_
  · intro s ⟨h1, h2, h3⟩ hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    refine ⟨⟨by (clear * - h1; omega), fun _ ↦ by (clear * - hc; omega), fun t ht1 ht2 ↦ ?_⟩, by (clear * - hc; omega)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht2 with ht | rfl
    · exact h3 t ht1 ht
    · exact hc.2
  · intro s ⟨h1, h2, h3⟩ hc
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hc
    refine ⟨h1, h2, h3, fun hs ↦ ?_⟩
    rcases hc with hc | hc
    · exact absurd hs hc
    · exact hc
  · refine ⟨by omega, fun _ ↦ by omega, fun t ht1 ht2 ↦ ?_⟩
    rw [show t = i by omega]

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

theorem runs_key_mem (a : Atom) (d : ℕ) (h : d < a.keys.size) :
    a.keys.getD d (0, 0) ∈ a.keys.toList.drop d := by
  have h' : d < a.keys.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons h', runs_getD_toList a d h']
  exact List.mem_cons_self

theorem runs_valFrom_ge (T : Array (Array 𝔽)) (d : ℕ) (a : Atom) (h : a.keys.size ≤ d) :
    runs_valFrom T d a = KRing.ofE a.w := by
  unfold runs_valFrom
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

theorem runs_sum_split (f : ℕ → 𝔽) (i j hi : ℕ) (hij : i ≤ j) (hjh : j ≤ hi) :
    ((List.range (hi - i)).map fun t ↦ f (i + t)).sum =
      ((List.range (j - i)).map fun t ↦ f (i + t)).sum + ((List.range (hi - j)).map fun t ↦ f (j + t)).sum := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hjh
  rw [show i + a + b - i = a + b by omega, show i + a - i = a by (clear * - hij; omega), show i + a + b - (i + a) = b by (clear * - hjh; omega),
    List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 2
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp, Nat.add_assoc]

/-- On a run of equal keys at level `d`, the sum from level `d` is the key times the sum from `d + 1`. -/
theorem runs_sum_run (T : Array (Array 𝔽)) (as : Array Atom) (D d i j : ℕ) (hD : ∀ a ∈ as, a.keys.size = D)
    (hd : d < D) (hj : j ≤ as.size)
    (hk : ∀ t, i ≤ t → t < j →
      (as.getD t default).keys.getD d (0, 0) = (as.getD i default).keys.getD d (0, 0)) :
    ((List.range (j - i)).map fun t ↦ runs_valFrom T d (as.getD (i + t) default)).sum =
      keyValG T ((as.getD i default).keys.getD d (0, 0)) *
        ((List.range (j - i)).map fun t ↦ runs_valFrom T (d + 1) (as.getD (i + t) default)).sum := by
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
  rw [List.mem_range] at ht
  have hm := runs_getD_mem as (i + t) (by (clear * - hj ht; omega))
  rw [runs_valFrom_succ T d _ (by rw [hD _ hm]; exact hd), hk (i + t) (by (clear * -; omega)) (by (clear * - ht; omega))]

theorem runs_evalRuns_sum (T : Array (Array 𝔽)) (as : Array Atom) (D fuel d lo hi : ℕ)
    (hD : ∀ a ∈ as, a.keys.size = D) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys.toList.drop d, k.1 = 0 → k.2 = 0)
    (hfuel : D - d < fuel) (hhi : hi ≤ as.size) :
    evalRuns T as D fuel d lo hi =
      ((List.range (hi - lo)).map fun i ↦ runs_valFrom T d (as.getD (lo + i) default)).sum := by
  induction fuel generalizing d lo hi with
  | zero => (clear * - hfuel; omega)
  | succ fuel ih =>
    rw [evalRuns]
    by_cases hdD : d ≥ D
    · rw [ite_eq_left hdD, runs_foldl_add, zero_add]
      refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
      rw [List.mem_range] at ht
      rw [runs_valFrom_ge T d _ (by rw [hD _ (runs_getD_mem as _ (by (clear * - hhi ht; omega)))]; exact hdD)]
    · rw [ite_eq_right hdD]
      have h0' : ∀ a ∈ as, ∀ k ∈ a.keys.toList.drop (d + 1), k.1 = 0 → k.2 = 0 := by
        intro a ha k hk
        refine h0 a ha k ?_
        rw [← List.drop_drop] at hk
        exact List.drop_subset _ _ hk
      refine runs_loop _ _
        (fun s : 𝔽 × ℕ × ℕ ↦ s.1 + ((List.range (hi - s.2.1)).map fun i ↦ runs_valFrom T d (as.getD (s.2.1 + i) default)).sum =
            ((List.range (hi - lo)).map fun i ↦ runs_valFrom T d (as.getD (lo + i) default)).sum ∧
          hi - s.2.1 ≤ s.2.2)
        (fun s : 𝔽 × ℕ × ℕ ↦ s.1 = ((List.range (hi - lo)).map fun i ↦ runs_valFrom T d (as.getD (lo + i) default)).sum)
        (fun s : 𝔽 × ℕ × ℕ ↦ s.2.2) ?_ ?_ _ ⟨zero_add _, le_rfl⟩
      · rintro ⟨acc, i, g⟩ ⟨h1, h2⟩ hc
        dsimp only at h1 h2 hc ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hij, hjh, hk, -⟩ := runs_runEnd as d i hi
        have hjh := hjh hc.1
        have hmi := runs_getD_mem as i (by (clear * - hhi hc; omega))
        have hdi : d < (as.getD i default).keys.size := by rw [hD _ hmi]; (clear * - hdD; omega)
        refine ⟨⟨?_, by omega⟩, by (clear * - hc; omega)⟩
        have hsp := runs_sum_split (fun t ↦ runs_valFrom T d (as.getD t default)) i (runEnd as d i hi) hi hij.le hjh
        beta_reduce at hsp
        rw [← h1, hsp, ← add_assoc]
        refine congrArg (· + _) ?_
        rw [runs_sum_run T as D d i _ hD (by (clear * - hdD; omega)) (by (clear * - hhi hjh; omega)) hk,
          ← ih (d + 1) i (runEnd as d i hi) h0' (by omega) (by (clear * - hhi hjh; omega))]
        refine congrArg (acc + ·) ?_
        have hkm := runs_key_mem _ d hdi
        have h0i := h0 _ hmi
        generalize (as.getD i default).keys.getD d (0, 0) = k at hkm ⊢
        generalize evalRuns T as D fuel (d + 1) i (runEnd as d i hi) = e
        by_cases ha : (k.1 == 0) = true
        · rw [ite_eq_left ha]
          rw [beq_iff_eq] at ha
          obtain ⟨k1, k2⟩ := k
          have hk2 := h0i _ hkm ha
          dsimp only at ha hk2
          subst ha hk2
          rw [hT, one_mul]
        · rw [ite_eq_right ha]
          by_cases hb : (e == 1) = true
          · rw [ite_eq_left hb, beq_iff_eq.1 hb, mul_one]
          · rw [ite_eq_right hb]
      · rintro ⟨acc, i, g⟩ ⟨h1, h2⟩ hc
        dsimp only at h1 h2 hc ⊢
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
        rw [← h1, show hi - i = 0 by (clear * - h2 hc; omega), List.range_zero, List.map_nil, List.sum_nil, add_zero]

theorem runs_range_map (as : Array Atom) (g : Atom → 𝔽) :
    (List.range (as.size - 0)).map (fun i ↦ g (as.getD (0 + i) default)) = as.toList.map g := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.length_map, Array.length_toList] at h2
    simp [h2]

/-- **The atom sum is the sum of the atoms' values** (any order; sorting only shares the products). Owner L-A. -/
theorem evalRuns_eq (T : Array (Array 𝔽)) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size = D) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys, k.1 = 0 → k.2 = 0) :
    evalRuns T as D (D + 1) 0 0 as.size = (as.toList.map (atomVal T)).sum := by
  rw [runs_evalRuns_sum T as D (D + 1) 0 0 as.size hD hT
    (fun a ha k hk ↦ h0 a ha k (by simpa using hk)) (by (clear * -; omega)) le_rfl, runs_range_map]
  congr 1
  refine List.map_congr_left fun a _ ↦ ?_
  simp only [runs_valFrom, List.drop_zero, atomVal, Array.foldl_toList]

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The code of the atoms `[lo, hi)` from level `d` (levels `< D`): each maximal run of equal level-`d` keys is a
leaf at the last level (its weights summed, statically), is transparent if its key is trivial, else a closed
sum over the deeper levels. -/
def genCode (as : Array Atom) (D : ℕ) : ℕ → ℕ → ℕ → ℕ → Code → Code
  | 0, _, _, _, c => c
  | fuel + 1, d, lo, hi, c0 => Id.run do
    let mut c := c0
    let mut i := lo
    let mut guard := hi - lo
    while i < hi && guard > 0 do
      let j := runEnd as d i hi
      let k := (as.getD i default).keys.getD d (0, 0)
      if d + 1 ≥ D then
        let w := (List.range (j - i)).foldl (fun acc m ↦ acc + (as.getD (i + m) default).w) 0
        if !(w == 0) then
          if w == 1 then c := c.emit 2 k.1 k.2 0
          else c := { c.emit 2 k.1 k.2 c.ws.size with ws := c.ws.push w }
      else if k.1 == 0 then
        c := genCode as D fuel (d + 1) i j c
      else
        c := genCode as D fuel (d + 1) i j (c.emit 0 0 0 0)
        c := c.emit 1 k.1 k.2 0
      i := j
      guard := guard - 1
    return c

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The code of an atom sum. -/
def atomCode (as : Array Atom) (D : ℕ) : Code := genCode as D (D + 1) 0 0 as.size ⟨#[], #[], #[], #[], #[1]⟩

/-- The code of a pass's initial states: per run of equal level-0 keys (the state), its sum, emitted. -/
def initCode (as : Array Atom) (D : ℕ) : Code := Id.run do
  let mut c : Code := ⟨#[], #[], #[], #[], #[1]⟩
  let mut i := 0
  let mut guard := as.size
  while i < as.size && guard > 0 do
    let j := runEnd as 0 i as.size
    let st := ((as.getD i default).keys.getD 0 (0, 0)).2
    c := genCode as D (D + 1) 1 i j (c.emit 0 0 0 0)
    c := c.emit 3 0 st 0
    i := j
    guard := guard - 1
  return c

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

theorem code_fmul (a b : FE) : fmul a b = a * b := by
  obtain ⟨b0, b1, b2⟩ := b
  unfold fmul
  simp only [Bool.and_eq_true, beq_iff_eq]
  split_ifs with h1 h2 h3
  · obtain ⟨rfl, rfl⟩ := h1
    rw [FE.smulBase_eq_mul, mul_comm]; rfl
  · obtain ⟨rfl, rfl⟩ := h2
    rw [code_mulY, FE.smulBase_eq_mul]
    have : (⟨0, b1, 0⟩ : FE) = FE.ofK b1 * ⟨0, 1, 0⟩ := by
      apply FE.toExt3_injective
      rw [FE.toExt3_mul, FE.toExt3_ofK, FE.toExt3_eq, FE.toExt3_eq ⟨0, 1, 0⟩]
      simp only [FK.toBF64_zero, FK.toBF64_one, map_zero, map_one]; ring
    rw [this]; ring
  · obtain ⟨rfl, rfl⟩ := h3
    rw [code_mulY, code_mulY, FE.smulBase_eq_mul]
    have : (⟨0, 0, b2⟩ : FE) = FE.ofK b2 * (⟨0, 1, 0⟩ * ⟨0, 1, 0⟩) := by
      apply FE.toExt3_injective
      rw [FE.toExt3_mul, FE.toExt3_mul, FE.toExt3_ofK, FE.toExt3_eq, FE.toExt3_eq ⟨0, 1, 0⟩]
      simp only [FK.toBF64_zero, FK.toBF64_one, map_zero, map_one]; ring
    rw [this]; ring
  · rfl

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- A guarded `while` loop over `(x, i, guard)` as a recursion on the guard. -/
def code_wl {X : Type} (hi : ℕ) (f : X → ℕ → X) (n : ℕ → ℕ) : ℕ → X → ℕ → X
  | 0, x, _ => x
  | g + 1, x, i => if i < hi then code_wl hi f n g (f x i) (n i) else x

theorem code_loop {X : Type} (hi : ℕ) (f : X → ℕ → X) (n : ℕ → ℕ)
    (B : Unit → X × ℕ × ℕ → Id (ForInStep (X × ℕ × ℕ)))
    (hB : ∀ x i g, B () (x, i, g) = if (decide (i < hi) && decide (g > 0)) = true then
      pure (ForInStep.yield (f x i, n i, g - 1)) else pure (ForInStep.done (x, i, g))) :
    ∀ g x i, (Id.run (forIn Lean.Loop.mk (x, i, g) B)).1 = code_wl hi f n g x i := by
  intro g
  induction g with
  | zero =>
    intro x i
    show (Id.run (Lean.Loop.forIn Lean.Loop.mk (x, i, _) B)).1 = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hB]
    simp [code_wl]
  | succ g ih =>
    intro x i
    show (Id.run (Lean.Loop.forIn Lean.Loop.mk (x, i, _) B)).1 = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hB]
    by_cases h : i < hi
    · simp only [h, decide_true, gt_iff_lt, Nat.zero_lt_succ, Bool.and_self, ite_true, code_wl,
        Nat.add_sub_cancel]
      exact ih _ _
    · simp [h, code_wl]

/-- A guarded sum loop. -/
def code_ws (hi : ℕ) (t : ℕ → 𝔽) (n : ℕ → ℕ) : ℕ → ℕ → 𝔽
  | 0, _ => 0
  | g + 1, i => if i < hi then t i + code_ws hi t n g (n i) else 0

theorem code_wl_sum (hi : ℕ) (t : ℕ → 𝔽) (n : ℕ → ℕ) :
    ∀ g a i, code_wl hi (fun acc i ↦ acc + t i) n g a i = a + code_ws hi t n g i := by
  intro g
  induction g with
  | zero => intro a i; simp [code_wl, code_ws]
  | succ g ih =>
    intro a i
    simp only [code_wl, code_ws]
    split_ifs
    · rw [ih]; ring
    · simp

theorem code_incLoop (hi : ℕ) (B : Unit → ℕ → Id (ForInStep ℕ))
    (hB : ∀ j, j < hi → B () j = pure (ForInStep.yield (j + 1)))
    (hB' : ∀ j, hi ≤ j → B () j = pure (ForInStep.done j)) :
    ∀ r j, hi - j = r → forIn Lean.Loop.mk j B = (pure (max j hi) : Id ℕ) := by
  intro r
  induction r with
  | zero =>
    intro j hj
    show Lean.Loop.forIn Lean.Loop.mk j B = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hB' j (by (clear * - hj; omega))]
    show (pure j : Id ℕ) = pure (max j hi)
    congr 1; (clear * - hj; omega)
  | succ r ih =>
    intro j hj
    show Lean.Loop.forIn Lean.Loop.mk j B = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hB j (by (clear * - hj; omega))]
    show forIn Lean.Loop.mk (j + 1) B = _
    rw [ih (j + 1) (by (clear * - hj; omega))]
    congr 1; (clear * - hj; omega)

/-- `runEnd` when every level-`d` key agrees: the whole range. -/
theorem code_runEnd_const (as : Array Atom) (d i hi : ℕ)
    (hk : ∀ m, (as.getD m default).keys.getD d (0, 0) = (as.getD i default).keys.getD d (0, 0))
    (hi' : i < hi) : runEnd as d i hi = hi := by
  unfold runEnd
  simp only [Id.run, bind_pure]
  rw [code_incLoop hi _ (fun j hj ↦ by simp only [hj, hk j, decide_true, beq_self_eq_true, Bool.and_self, ite_true])
    (fun j hj ↦ by simp [Nat.not_lt.2 hj]) _ _ rfl]
  show max (i + 1) hi = hi
  (clear * - hi'; omega)

theorem code_wl_stop {X : Type} (hi : ℕ) (f : X → ℕ → X) (n : ℕ → ℕ) (g : ℕ) (x : X) (i : ℕ)
    (h : ¬ i < hi) : code_wl hi f n g x i = x := by
  cases g <;> simp [code_wl, h]

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- One iteration of `genCode`'s loop (run from `i`). -/
def code_gStep (as : Array Atom) (D fuel d hi : ℕ) (c : Code) (i : ℕ) : Code :=
  if d + 1 ≥ D then
    code_leaf c ((as.getD i default).keys.getD d (0, 0))
      ((List.range (runEnd as d i hi - i)).foldl (fun acc m ↦ acc + (as.getD (i + m) default).w) 0)
  else if ((as.getD i default).keys.getD d (0, 0)).1 == 0 then
    genCode as D fuel (d + 1) i (runEnd as d i hi) c
  else
    (genCode as D fuel (d + 1) i (runEnd as d i hi) (c.emit 0 0 0 0)).emit 1
      ((as.getD i default).keys.getD d (0, 0)).1 ((as.getD i default).keys.getD d (0, 0)).2 0

theorem code_genCode_eq (as : Array Atom) (D fuel d lo hi : ℕ) (c : Code) :
    genCode as D (fuel + 1) d lo hi c =
      code_wl hi (code_gStep as D fuel d hi) (fun i ↦ runEnd as d i hi) (hi - lo) c lo := by
  rw [genCode]
  refine code_loop _ _ _ _ (fun x i g ↦ ?_) _ _ _
  simp only [code_gStep, code_leaf]
  generalize List.foldl (fun acc m => acc + (as.getD (i + m) default).w) 0 (List.range (runEnd as d i hi - i)) = W
  by_cases h0 : (decide (i < hi) && decide (g > 0)) = true
  · rw [if_pos h0, if_pos h0]
    by_cases h1 : d + 1 ≥ D
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : (!W == 0) = true
      · rw [if_pos h2, if_pos h2]
        by_cases h3 : (W == 1) = true
        · rw [if_pos h3, if_pos h3]
        · rw [if_neg h3, if_neg h3]
      · rw [if_neg h2, if_neg h2]
    · rw [if_neg h1, if_neg h1]
      by_cases h4 : (((as.getD i default).keys.getD d (0, 0)).1 == 0) = true
      · rw [if_pos h4, if_pos h4]
      · rw [if_neg h4, if_neg h4]
  · rw [if_neg h0, if_neg h0]

/-- One iteration of `evalRuns`'s loop. -/
def code_eTerm (T : Array (Array 𝔽)) (as : Array Atom) (D fuel d hi : ℕ) (i : ℕ) : 𝔽 :=
  if ((as.getD i default).keys.getD d (0, 0)).1 == 0 then evalRuns T as D fuel (d + 1) i (runEnd as d i hi)
  else if evalRuns T as D fuel (d + 1) i (runEnd as d i hi) == 1 then
    keyValG T ((as.getD i default).keys.getD d (0, 0))
  else keyValG T ((as.getD i default).keys.getD d (0, 0)) * evalRuns T as D fuel (d + 1) i (runEnd as d i hi)

theorem code_evalRuns_eq (T : Array (Array 𝔽)) (as : Array Atom) (D fuel d lo hi : ℕ) (h : ¬ d ≥ D) :
    evalRuns T as D (fuel + 1) d lo hi =
      code_ws hi (code_eTerm T as D fuel d hi) (fun i ↦ runEnd as d i hi) (hi - lo) lo := by
  rw [evalRuns, ite_eq_right_of_eq_false _ _ (eq_false h), ← zero_add (code_ws _ _ _ _ _), ← code_wl_sum]
  exact code_loop _ _ _ _ (fun x i g ↦ rfl) _ _ _

/-- The weights' map of a sum of weights. -/
theorem runs_ofE_foldl (l : List ℕ) (f : ℕ → FE) :
    KRing.ofE (l.foldl (fun acc i ↦ acc + f i) 0) = l.foldl (fun acc i ↦ acc + KRing.ofE (f i)) (0 : 𝔽) := by
  suffices h : ∀ a : FE, KRing.ofE (l.foldl (fun acc i ↦ acc + f i) a) =
      l.foldl (fun acc i ↦ acc + KRing.ofE (f i)) (KRing.ofE a : 𝔽) by
    simpa using h 0
  induction l with
  | nil => intro a; rfl
  | cons x l ih => intro a; simp only [List.foldl_cons, ih, map_add]

/-- **`genCode` appends a block adding `evalRuns`.** -/
theorem code_genCode (T : Array (Array 𝔽)) (as : Array Atom) (D d0 : ℕ) (hT : keyValG T (0, 0) = 1)
    (hK : ∀ i m, d0 ≤ m → ((as.getD i default).keys.getD m (0, 0)).1 = 0 →
      keyValG T ((as.getD i default).keys.getD m (0, 0)) = 1)
    (hZ : ∀ i m, D ≤ m → (as.getD i default).keys.getD m (0, 0) = (0, 0)) :
    ∀ fuel d lo hi (c : Code), d0 ≤ d → D + 1 ≤ d + fuel → code_Al c → 0 < c.ws.size →
      code_Spec T c (genCode as D fuel d lo hi c) (evalRuns T as D fuel d lo hi) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d lo hi c _ _ hc _
    rw [genCode, evalRuns]
    exact code_Spec_zero T c hc
  | succ f ih =>
    intro d lo hi c hd hf hc hw
    rw [code_genCode_eq]
    by_cases hdD : d ≥ D
    · rw [evalRuns, ite_eq_left_of_eq_true _ _ (eq_true hdD)]
      rcases Nat.lt_or_ge lo hi with hlo | hlo
      · obtain ⟨g, hg⟩ : ∃ g, hi - lo = g + 1 := ⟨hi - lo - 1, by (clear * - hlo; omega)⟩
        have hE : runEnd as d lo hi = hi :=
          code_runEnd_const as d lo hi (fun m ↦ by rw [hZ m d hdD, hZ lo d hdD]) hlo
        rw [hg, code_wl, ite_eq_left_of_eq_true _ _ (eq_true hlo), hE, code_wl_stop _ _ _ _ _ _ (lt_irrefl hi)]
        simp only [code_gStep, ite_eq_left_of_eq_true _ _ (eq_true (show d + 1 ≥ D by (clear * - hdD; omega))), hE]
        have := code_Spec_leaf T c ((as.getD lo default).keys.getD d (0, 0))
          ((List.range (hi - lo)).foldl (fun acc m ↦ acc + (as.getD (lo + m) default).w) 0) hc hw
        rw [hZ lo d hdD, ← hg]
        rwa [hZ lo d hdD, hT, one_mul, runs_ofE_foldl] at this
      · rw [show hi - lo = 0 by (clear * - hlo; omega), code_wl]
        simpa using code_Spec_zero T c hc
    · rw [code_evalRuns_eq T as D f d lo hi hdD]
      -- one iteration
      have hstep : ∀ i (c : Code), code_Al c → 0 < c.ws.size →
          code_Spec T c (code_gStep as D f d hi c i) (code_eTerm T as D f d hi i) := by
        intro i c hc hw
        have hk := hK i d hd
        unfold code_eTerm
        rw [code_term T _ _ hk]
        unfold code_gStep
        split_ifs with h1 h2
        · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by (clear * - hf hdD h1; omega)⟩
          rw [evalRuns, ite_eq_left_of_eq_true _ _ (eq_true h1)]
          have := code_Spec_leaf T c ((as.getD i default).keys.getD d (0, 0))
            ((List.range (runEnd as d i hi - i)).foldl (fun acc m ↦ acc + (as.getD (i + m) default).w) 0) hc hw
          rwa [runs_ofE_foldl] at this
        · rw [hk (by simpa using h2), one_mul]
          exact ih (d + 1) _ _ c (by (clear * - hd; omega)) (by (clear * - hf; omega)) hc hw
        · have ht : ((as.getD i default).keys.getD d (0, 0)).1 ≠ 0 := by simpa using h2
          obtain ⟨hA0, -, hW0⟩ := code_emit c 0 0 0 0 hc
          exact code_Spec_wrap T c _ _ _ _ hc ht
            (ih (d + 1) _ _ _ (by (clear * - hd; omega)) (by (clear * - hf; omega)) hA0 (by rw [hW0]; exact hw))
      -- the loop
      suffices ∀ g i (c : Code), code_Al c → 0 < c.ws.size →
          code_Spec T c (code_wl hi (code_gStep as D f d hi) (fun i ↦ runEnd as d i hi) g c i)
            (code_ws hi (code_eTerm T as D f d hi) (fun i ↦ runEnd as d i hi) g i) from
        this _ _ c hc hw
      intro g
      induction g with
      | zero => intro i c hc _; exact code_Spec_zero T c hc
      | succ g ihg =>
        intro i c hc hw
        simp only [code_wl, code_ws]
        split_ifs
        · have h1 := hstep i c hc hw
          obtain ⟨hA1, ⟨R1, hR1⟩, -⟩ := id h1
          exact code_Spec_trans T _ _ _ _ _ h1
            (ihg _ _ hA1 (by rw [hR1, Array.size_append]; (clear * - hw; omega)))
        · exact code_Spec_zero T c hc

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

theorem code_hZ (as : Array Atom) (D : ℕ) (hD : ∀ a ∈ as, a.keys.size = D) :
    ∀ i m, D ≤ m → (as.getD i default).keys.getD m (0, 0) = (0, 0) := by
  intro i m hm
  rcases code_key as i m with h | ⟨a, ha, hm', _⟩
  · exact h
  · exact absurd hm' (by rw [hD a ha]; (clear * - hm; omega))

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- **The code computes the atom sum** (statement). Owner L-A. -/
theorem runCode_atomCode (T : Array (Array 𝔽)) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size = D) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys, k.1 = 0 → k.2 = 0) :
    (runCodeG T (atomCode as D)).1 = evalRuns T as D (D + 1) 0 0 as.size := by
  have hK : ∀ i m, 0 ≤ m → ((as.getD i default).keys.getD m (0, 0)).1 = 0 →
      keyValG T ((as.getD i default).keys.getD m (0, 0)) = 1 := by
    intro i m _ h1
    rcases code_key as i m with h | ⟨a, ha, hm, h⟩
    · rw [h]; exact hT
    · have h2 := h0 a ha _ (Array.getElem_mem hm) (h ▸ h1)
      rw [h, ← hT]
      congr 1
      exact Prod.ext (h ▸ h1) h2
  obtain ⟨-, -, L, hL, hf⟩ := code_genCode T as D 0 hT hK (code_hZ as D hD) (D + 1) 0 0 as.size _
    (le_refl _) (by (clear * -; omega)) code_atom0 (by decide)
  rw [code_runCode]
  unfold atomCode
  have := hf #[] 0 #[] #[]
  rw [Array.append_empty] at this
  have hn : code_instrs (⟨#[], #[], #[], #[], #[1]⟩ : Code) = [] := rfl
  rw [hL, hn, List.nil_append, this, zero_add]

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
open private Array.qpartition.loop from Init.Data.Array.QSort.Basic
open private Array.qsort.sort from Init.Data.Array.QSort.Basic

theorem fuse_pk_b (op m a b w : ℕ) (hop : op < 16) (hm : m < 4) (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) :
    (pkI op m a b w >>> 26) &&& 0xFFFFF = b := by
  rw [fuse_pk_hi op m a b w hop hm ha, fuse_and_mask _ 20 0xFFFFF rfl]; (clear * - hb; omega)

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
open private Array.qpartition.loop from Init.Data.Array.QSort.Basic
open private Array.qsort.sort from Init.Data.Array.QSort.Basic

theorem fuse_wmul (v w : FE) : wmul (wKind w) v w = v * w := by
  rw [← code_fmul]
  unfold wmul wKind fmul
  by_cases h1 : (w.c₁ == 0 && w.c₂ == 0) = true
  · rw [if_pos h1, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (w.c₀ == 0 && w.c₂ == 0) = true
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : (w.c₀ == 0 && w.c₁ == 0) = true
      · rw [if_pos h3, if_pos h3]; rfl
      · rw [if_neg h3, if_neg h3]; rfl

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
open private Array.qpartition.loop from Init.Data.Array.QSort.Basic
open private Array.qsort.sort from Init.Data.Array.QSort.Basic

theorem fuse_ofold_size (l : List TRec) : ∀ (acc : Array ℕ), (l.foldl fuse_ostep acc).size = acc.size + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons r l ih => intro acc; simp only [List.foldl_cons, ih, fuse_ostep, Array.size_push, List.length_cons]; (clear * -; omega)

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The initial states of a pass: per run of equal level-0 keys, the state and the run's atom sum. -/
def passInit (T : Array (Array 𝔽)) (p : Pass) : Array (ℕ × 𝔽) := Id.run do
  let mut out : Array (ℕ × 𝔽) := #[]
  let mut i := 0
  let mut guard := p.atoms.size
  while i < p.atoms.size && guard > 0 do
    let j := runEnd p.atoms 0 i p.atoms.size
    let s := ((p.atoms.getD i default).keys.getD 0 (0, 0)).2
    out := out.push (s, evalRuns T p.atoms p.depth (p.depth + 1) 1 i j)
    i := j
    guard := guard - 1
  return out

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]
section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- One iteration of `initCode`'s loop. -/
def code_iStep (as : Array Atom) (D : ℕ) (c : Code) (i : ℕ) : Code :=
  (genCode as D (D + 1) 1 i (runEnd as 0 i as.size) (c.emit 0 0 0 0)).emit 3 0
    ((as.getD i default).keys.getD 0 (0, 0)).2 0

/-- One iteration of `passInit`'s loop. -/
def code_pStep (T : Array (Array 𝔽)) (as : Array Atom) (D : ℕ) (out : Array (ℕ × 𝔽)) (i : ℕ) :
    Array (ℕ × 𝔽) :=
  out.push (((as.getD i default).keys.getD 0 (0, 0)).2, evalRuns T as D (D + 1) 1 i (runEnd as 0 i as.size))

theorem code_runCode_initCode (T : Array (Array 𝔽)) (p : Pass)
    (hD : ∀ a ∈ p.atoms, a.keys.size = p.depth) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ p.atoms, ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0) :
    (runCodeG T (initCode p.atoms p.depth)).2 = passInit T p := by
  have hK : ∀ i m, 1 ≤ m → ((p.atoms.getD i default).keys.getD m (0, 0)).1 = 0 →
      keyValG T ((p.atoms.getD i default).keys.getD m (0, 0)) = 1 := by
    intro i m hm1 h1
    rcases code_key p.atoms i m with h | ⟨a, ha, hm, h⟩
    · rw [h]; exact hT
    · have hmem : a.keys[m] ∈ a.keys.toList.drop 1 := by
        rw [List.mem_iff_getElem]
        exact ⟨m - 1, by simp; (clear * - hm1 hm; omega), by simp; congr 1; (clear * - hm1; omega)⟩
      have h2 := h0 a ha _ hmem (h ▸ h1)
      rw [h, ← hT]
      congr 1
      exact Prod.ext (h ▸ h1) h2
  have hG := code_genCode T p.atoms p.depth 1 hT hK (code_hZ p.atoms p.depth hD)
  have hI : initCode p.atoms p.depth = code_wl p.atoms.size (code_iStep p.atoms p.depth)
      (fun i ↦ runEnd p.atoms 0 i p.atoms.size) p.atoms.size ⟨#[], #[], #[], #[], #[1]⟩ 0 := by
    unfold initCode
    exact code_loop _ _ _ _ (fun x i g ↦ rfl) _ _ _
  have hP : passInit T p = code_wl p.atoms.size (code_pStep T p.atoms p.depth)
      (fun i ↦ runEnd p.atoms 0 i p.atoms.size) p.atoms.size #[] 0 := by
    unfold passInit
    exact code_loop _ _ _ _ (fun x i g ↦ rfl) _ _ _
  suffices ∀ g i (c : Code) out, code_Al c → 0 < c.ws.size → ∃ O,
      code_ISpec T c (code_wl p.atoms.size (code_iStep p.atoms p.depth)
        (fun i ↦ runEnd p.atoms 0 i p.atoms.size) g c i) O ∧
      code_wl p.atoms.size (code_pStep T p.atoms p.depth) (fun i ↦ runEnd p.atoms 0 i p.atoms.size) g out i =
        out ++ O by
    obtain ⟨O, ⟨-, -, L, hL, hf⟩, hO⟩ := this p.atoms.size 0 _ #[] code_atom0 (by decide)
    rw [hP, hO, code_runCode, hI, hL]
    have := hf #[] 0 #[] #[]
    rw [Array.append_empty] at this
    have hn : code_instrs (⟨#[], #[], #[], #[], #[1]⟩ : Code) = [] := rfl
    rw [hn, List.nil_append, this]
  intro g
  induction g with
  | zero => intro i c out hc _; exact ⟨#[], code_ISpec_zero T c hc, by simp [code_wl]⟩
  | succ g ihg =>
    intro i c out hc hw
    simp only [code_wl]
    split_ifs
    · obtain ⟨hA0, -, hW0⟩ := code_emit c 0 0 0 0 hc
      have h1 := code_ISpec_wrap T c _ _ ((p.atoms.getD i default).keys.getD 0 (0, 0)).2 hc
        (hG (p.depth + 1) 1 i (runEnd p.atoms 0 i p.atoms.size) _ (le_refl _) (by (clear * -; omega)) hA0
          (by rw [hW0]; exact hw))
      obtain ⟨hA1, ⟨R1, hR1⟩, -⟩ := id h1
      obtain ⟨O2, h2, hO2⟩ := ihg (runEnd p.atoms 0 i p.atoms.size) (code_iStep p.atoms p.depth c i)
        (code_pStep T p.atoms p.depth out i) hA1 (by rw [code_iStep, hR1, Array.size_append]; (clear * - hw; omega))
      refine ⟨_, code_ISpec_trans T _ _ _ _ _ h1 h2, ?_⟩
      rw [hO2, code_pStep, Array.push_eq_append, Array.append_assoc]
    · exact ⟨#[], code_ISpec_zero T c hc, by simp⟩

/-- passInit: the initial states of a pass and their sums. -/
theorem runs_passInit_sum (T : Array (Array 𝔽)) (p : Pass) (hD : ∀ a ∈ p.atoms, a.keys.size = p.depth)
    (hT : keyValG T (0, 0) = 1) (h0 : ∀ a ∈ p.atoms, ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0) (g : ℕ → 𝔽) :
    ((passInit T p).toList.map fun sv ↦ sv.2 * g sv.1).sum =
      (p.atoms.toList.map fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2).sum := by
  rw [← runs_range_map p.atoms (fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2)]
  unfold passInit
  refine runs_loop _ _
    (fun s : Array (ℕ × 𝔽) × ℕ × ℕ ↦ (s.1.toList.map fun sv ↦ sv.2 * g sv.1).sum +
        ((List.range (p.atoms.size - s.2.1)).map fun i ↦
          runs_valFrom T 1 (p.atoms.getD (s.2.1 + i) default) *
            g ((p.atoms.getD (s.2.1 + i) default).keys.getD 0 (0, 0)).2).sum =
        ((List.range (p.atoms.size - 0)).map fun i ↦
          runs_valFrom T 1 (p.atoms.getD (0 + i) default) *
            g ((p.atoms.getD (0 + i) default).keys.getD 0 (0, 0)).2).sum ∧
      p.atoms.size - s.2.1 ≤ s.2.2)
    (fun s : Array (ℕ × 𝔽) × ℕ × ℕ ↦ (s.1.toList.map fun sv ↦ sv.2 * g sv.1).sum =
        ((List.range (p.atoms.size - 0)).map fun i ↦
          runs_valFrom T 1 (p.atoms.getD (0 + i) default) *
            g ((p.atoms.getD (0 + i) default).keys.getD 0 (0, 0)).2).sum)
    (fun s : Array (ℕ × 𝔽) × ℕ × ℕ ↦ s.2.2) ?_ ?_ _
    ⟨by simp only [List.map_nil, List.sum_nil, zero_add], le_rfl⟩
  · rintro ⟨out, i, gd⟩ ⟨h1, h2⟩ hc
    dsimp only at h1 h2 hc ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hij, hjh, hk, -⟩ := runs_runEnd p.atoms 0 i p.atoms.size
    have hjh := hjh hc.1
    refine ⟨⟨?_, by omega⟩, by (clear * - hc; omega)⟩
    have hsp := runs_sum_split (fun t ↦ runs_valFrom T 1 (p.atoms.getD t default) *
      g ((p.atoms.getD t default).keys.getD 0 (0, 0)).2) i (runEnd p.atoms 0 i p.atoms.size) p.atoms.size
      hij.le hjh
    beta_reduce at hsp
    rw [← h1, hsp, Array.toList_push, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      add_assoc]
    congr 2
    rw [runs_evalRuns_sum T p.atoms p.depth (p.depth + 1) 1 i _ hD hT h0 (by (clear * -; omega)) hjh]
    dsimp only
    rw [← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
    rw [List.mem_range] at ht
    rw [hk (i + t) (by (clear * -; omega)) (by (clear * - hij ht; omega))]
  · rintro ⟨out, i, gd⟩ ⟨h1, h2⟩ hc
    dsimp only at h1 h2 hc ⊢
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
    rw [← h1, show p.atoms.size - i = 0 by (clear * - h2 hc; omega), List.range_zero, List.map_nil, List.sum_nil, add_zero]

theorem runs_sorted_getD (as : Array Atom) (R : Atom → Atom → Prop) (hs : as.toList.Pairwise R) (t u : ℕ)
    (htu : t < u) (hu : u < as.size) : R (as.getD t default) (as.getD u default) := by
  rw [List.pairwise_iff_getElem] at hs
  have := hs t u (by simp; (clear * - htu hu; omega)) (by simpa using hu) htu
  simpa [show t < as.size by (clear * - htu hu; omega), hu] using this

/-- passInit: the states are strictly increasing (atoms sorted by level-0 index, level-0 keys of table `0`). -/
theorem runs_passInit_sorted (T : Array (Array 𝔽)) (p : Pass)
    (h1 : ∀ a ∈ p.atoms, (a.keys.getD 0 (0, 0)).1 = 0)
    (hs : p.atoms.toList.Pairwise fun a b ↦ (a.keys.getD 0 (0, 0)).2 ≤ (b.keys.getD 0 (0, 0)).2) :
    (passInit T p).toList.Pairwise fun a b ↦ a.1 < b.1 := by
  unfold passInit
  refine runs_loop _ _
    (fun s : Array (ℕ × 𝔽) × ℕ × ℕ ↦ (s.1.toList.Pairwise fun a b ↦ a.1 < b.1) ∧
      (s.2.1 < p.atoms.size → ∀ x ∈ s.1.toList, x.1 < ((p.atoms.getD s.2.1 default).keys.getD 0 (0, 0)).2))
    (fun s : Array (ℕ × 𝔽) × ℕ × ℕ ↦ s.1.toList.Pairwise fun a b ↦ a.1 < b.1)
    (fun s : Array (ℕ × 𝔽) × ℕ × ℕ ↦ s.2.2) ?_ (fun s hs _ ↦ hs.1) _ ?_
  swap
  · exact ⟨List.Pairwise.nil, fun _ x hx ↦ by simp at hx⟩
  rintro ⟨out, i, gd⟩ ⟨hP, hlt⟩ hc
  dsimp only at hP hlt hc ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hij, -, -, hmax⟩ := runs_runEnd p.atoms 0 i p.atoms.size
  have hlt := hlt hc.1
  refine ⟨⟨?_, fun hj x hx ↦ ?_⟩, by (clear * - hc; omega)⟩
  · rw [Array.toList_push, List.pairwise_append]
    refine ⟨hP, List.pairwise_singleton _ _, fun x hx y hy ↦ ?_⟩
    rw [List.mem_singleton] at hy
    subst hy
    exact hlt x hx
  · have hle := runs_sorted_getD p.atoms _ hs i _ hij hj
    have hne := hmax hj
    have hi1 := h1 _ (runs_getD_mem p.atoms i hc.1)
    have hj1 := h1 _ (runs_getD_mem p.atoms _ hj)
    have hij2 : ((p.atoms.getD i default).keys.getD 0 (0, 0)).2 <
        ((p.atoms.getD (runEnd p.atoms 0 i p.atoms.size) default).keys.getD 0 (0, 0)).2 :=
      lt_of_le_of_ne hle fun he ↦ hne (Prod.ext (hj1.trans hi1.symm) he.symm)
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hlt x hx).trans hij2
    · exact hij2

end L1
end Lvm.Typed.K
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Lvm.Typed.K
open Lvm.Loop
variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]

theorem keyVal_eqG (T : Array (Array FE)) (k : ℕ × ℕ) : keyVal T k = keyValG T k := rfl

end Lvm.Typed.K
end

-- ===== from `LvmTyped` =====

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop

theorem noE2_of (Q : Program) (h : Q.noE2B = true) : NoE2 Q := by
  intro i hi f hh hop
  obtain ⟨b, hb, jf, -, t, ht, rfl⟩ := Lvm.Typed.lh_mem_insts hi
  simp only [Program.noE2B, List.all_eq_true] at h
  have hB : Q.blk b ∈ Q.blocks := by
    simp only [Program.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
    exact List.getElem_mem hb
  have hR : (Q.blk b).tpl.getD t default ∈ (Q.blk b).tpl := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  have h1 := h _ hB _ hR
  have hop' : ((Q.blk b).tpl.getD t default).op = .e2 f hh := hop
  rw [hop'] at h1
  exact absurd h1 (by simp)

/-- **Every non-`readd` instance's relation holds** without the mini-bus (L-D's `nodeT20`: QLT's static reads need
the address rows' relations first): with the program check, on a checked layout, with `z(one) = 1` and the wiring
relation. -/
theorem rowDef_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) {i : Inst} (hi : i ∈ Q.insts)
    (hop : ∀ lo m, i.row.op ≠ .readd lo m) (he2 : ∀ f h, i.row.op ≠ .e2 f h) : Q.RowDef (memOf lay z) i :=
  (lh_row Q lay z hwf hlay hone h hi (fun lo m h' ↦ absurd h' (hop lo m)) he2).1

/-- **Every instance's gated assertion holds** (no `ReaddOk` needed). -/
theorem rowAssert_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) {i : Inst} (hi : i ∈ Q.insts) :
    Program.RowAssert (memOf lay z) i := by
  by_cases hrd : ∃ lo m, i.row.op = .readd lo m
  · obtain ⟨lo, m, hop⟩ := hrd
    simp only [Program.RowAssert, hop]
  by_cases he : ∃ f hh, i.row.op = .e2 f hh
  · obtain ⟨f, hh, hop⟩ := he
    simp only [Program.RowAssert, hop]
  · exact (lh_row Q lay z hwf hlay hone h hi (fun lo m h' ↦ absurd ⟨lo, m, h'⟩ hrd)
      fun f hh h' ↦ he ⟨f, hh, h'⟩).2

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop

/-- **The wiring relation is the program's relations** (B-DES §2): with the program check (for the operand
counts: a `loadE` row has its three operands), on a checked layout, with `z(one) = 1`, the relation at every slot
and the mini-bus obligation, every row relation and every gated assertion holds on the memory read off `z`.
Owner **L-B**. -/
theorem holds_of_wiring (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) (hrd : ReaddOk Q (memOf lay z)) (hno : NoE2 Q) :
    Q.Holds (memOf lay z) ∧ Q.Asserts (memOf lay z) := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ rowAssert_of_wiring Q lay z hwf hlay hone h hi⟩
  by_cases hr : ∃ lo m, i.row.op = .readd lo m
  · obtain ⟨lo, m, hop⟩ := hr
    exact hrd i hi lo m hop
  · exact rowDef_of_wiring Q lay z hwf hlay hone h hi (fun lo m h' ↦ hr ⟨lo, m, h'⟩) (hno i hi)

/-- **The typed backend's circuit theorem** (B-DES §2): `holds_of_wiring`, then `Program.interp_unique`
(`LvmLoopInterp`, unchanged). The memory read off the words is the interpreter's on every cell, and the
interpreter's assertions hold. -/
theorem typed_sound (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (inK : Array FK)
    (inE : Array FE) (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (hlay : lay.Ok Q) (hone : z lay.one = 1)
    (h : WiringRel Q lay z) (hrd : ReaddOk Q (memOf lay z)) (hno : NoE2 Q) (hin : Q.Inputs (memOf lay z) inK inE)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) (hinb : (Q.interp inK inE).inb = true) :
    (memOf lay z).Agrees (Q.interpMem inK inE) (Q.cells .K) (Q.cells .E) ∧
      (Q.interp inK inE).ok = true := by
  obtain ⟨hH, hA⟩ := holds_of_wiring Q lay z hwf hlay hone h hrd hno
  obtain ⟨hag, hiff⟩ := Q.interp_unique hwf inK inE hsz _ hin hH hinj hinb
  exact ⟨hag, hiff.mpr hA⟩

end Lvm.Typed
end

-- ===== from `LvmQTypedGuard` =====

section
section
set_option autoImplicit false
namespace Lvm.Typed.K
open Lvm.Loop

theorem look3_tab3 {α : Type} (n : ℕ) (m : ℕ → ℕ) (k : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ → α) (i j l : ℕ) :
    look3 (tab3 n m k f) i j l (fun _ ↦ f i j l) = f i j l := by
  unfold look3 tab3
  by_cases hi : i < n
  · by_cases hj : j < m i
    · by_cases hl : l < k i j
      · simp [hi, hj, hl]
      · simp [hi, hj, hl]
    · simp [hi, hj]
  · simp [hi]

end Lvm.Typed.K
end
end

section
section
set_option autoImplicit false
namespace Lvm.Typed.K
open Lvm.Loop

/-- **The table's lookup is the entry function.** -/
theorem EntTab.get_of (G : FLF) : (EntTab.of G).get G = fun s jf ↦ (G.srcEnts s jf).toArray := by
  funext s jf
  cases s with
  | row b t => exact look3_tab3 _ _ _ (fun b t jf ↦ (G.srcEnts (.row b t) jf).toArray) b t jf
  | aux k r => exact look3_tab3 _ _ _ (fun k r j ↦ (G.srcEnts (.aux k r) j).toArray) k r jf

end Lvm.Typed.K
end
end

section
section
set_option autoImplicit false
namespace Lvm.Typed.K
open Lvm.Loop

theorem termsChecked_fst (Q : Program) (lay : Lay) : (termsChecked (FLF.ofLay Q lay)).1 = deriveTerms Q lay := by
  show deriveTermsG ((EntTab.of (FLF.ofLay Q lay)).get (FLF.ofLay Q lay)) (FLF.ofLay Q lay).F = _
  rw [EntTab.get_of]
  rfl

/-- The check on the table is `checkTerms`. -/
theorem checkTab_eq (Q : Program) (lay : Lay) (ts : Array CTerm) :
    checkTermsGA ((EntTab.of (FLF.ofLay Q lay)).get (FLF.ofLay Q lay)) CTerm.atF ts = checkTerms Q lay ts := by
  rw [EntTab.get_of, cterm_atF, flf_srcEnts, checkTerms_eqG, checkTermsG_eqA]

theorem termsChecked_snd (Q : Program) (lay : Lay) :
    (termsChecked (FLF.ofLay Q lay)).2 = checkTerms Q lay (termsChecked (FLF.ofLay Q lay)).1 :=
  checkTab_eq Q lay _

end Lvm.Typed.K
end
end

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)
section
open Lvm.Har Lvm.Loop.QRing Lvm.Q1

theorem wireGadgetF_eq : wireGadgetF = Lvm.Q1.wireGadget := by
  funext P qw cv mb sb b zE
  unfold wireGadgetF
  rw [VF.loopF_eq]
  rfl

end
end Lvm.QTyped
end

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)
section
open Lvm.Har Lvm.Loop.QRing Lvm.Q1

theorem phases47S_eq (C : QCfg) : phases47S C = VF.phases47F C := by
  unfold phases47S VF.phases47F
  rw [wireGadgetF_eq]

end
end Lvm.QTyped
end

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

theorem qprogBF_eq (C : QCfg) (T : TData) : qprogBF C T = qprogB C T := by
  unfold qprogBF qprogB
  rw [phases47S_eq, show VF.phases47F C = Lvm.Har.phases47 C by
    unfold VF.phases47F Lvm.Har.phases47; rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]]

/-- The B program from its one-pass builder. -/
theorem QB_eqF (C : QCfg) (T : TData) : QB C T = toProgram (nK C) 0 (qprogBF C T) := by
  rw [qprogBF_eq]; rfl

end Lvm.QTyped
end

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

/-- **The typed static guard** of a configuration on its static data, the program's segments `δ` (`segsOkF`'s
one pass; `δ` the B program's, `(qprogBF C T ⟨nK C, 0⟩).2`), program, layout, cache, instance and the verdict `ck`
of `Φ_Q`'s entry check (`K.checkTerms Q lay c.terms.toArray`: `staticFactsTC`'s `hck`; B1-IX-S: computed where the
terms are, `K.termsChecked`, or by `K.checkTermsF`). The rest of `PhiCache.okB` is `keysBF = keysB` (`okB_keys`);
QLT's constants on `qltCstF = qltCst`; `mbFitBF = mbFitB` on the checked layout. -/
def staticOkTC (C : QCfg) (F : TFrz) (δ : List Seg) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) (ck : Bool) : Bool :=
  Lvm.Fin.segsOkF ⟨nK C, 0⟩ δ && lay.okB Q && (c.keysBF Q lay && ck) &&
    N.okB C.p.nuMain C.p.nuRec && layOkN N lay && TypedV.fitsMiniB C.p N.mbT && mbFitBF C Q lay &&
    F.mbW.all (fun e => e.2 == (layout0 C.p).t + lay.wordK e.1) && lay.cst == qltCstF C &&
    decide (max (Q.cells .K) (Q.cells .E) < 2 ^ 64 - 1) && Q.noE2B

/-- The typed static guard with `Φ_Q`'s entry check on the fast entries (`K.checkTermsF = K.checkTerms`). -/
def staticOkTS (C : QCfg) (F : TFrz) (δ : List Seg) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) : Bool :=
  staticOkTC C F δ Q lay c N (K.checkTermsF Q lay c.terms.toArray)

/-- **The typed static guard** of a configuration on its static data, program, layout, cache and instance. -/
def staticOkTOf (C : QCfg) (T : TData) (F : TFrz) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) : Bool :=
  staticOkTS C F (qprogBF C T ⟨nK C, 0⟩).2 Q lay c N

end Lvm.QTyped
end

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

theorem staticFactsTC {C : QCfg} {T : TData} {F : TFrz} {δ : List Seg} {Q : Program} {lay : Typed.Lay}
    {c : PhiCache} {N : TypedV.TNat} {ck : Bool} (hQ : Q = QB C T) (hδ : δ = (qprogBF C T ⟨nK C, 0⟩).2)
    (hck : ck = K.checkTerms Q lay c.terms.toArray) (h : staticOkTC C F δ Q lay c N ck = true) :
    StaticFactsT C T F Q lay c N := by
  unfold staticOkTC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hl⟩, hc⟩, hr⟩, hk⟩, hm⟩, hf⟩, hW⟩, hcs⟩, hi⟩, hno⟩ := h
  refine ⟨?_, hl, ?_, hr, hk, hm, mbFit_of C lay ((mbFitBF_eq C Q lay hl).symm.trans hf), ?_,
    (beq_iff_eq.mp hcs).trans (qltCstF_eq C), ?_, Typed.noE2_of Q hno⟩
  · rw [hQ, QB_eqF]
    exact toProgram_wf _ _ _ (by rw [← Lvm.Fin.segsOkF_eq, ← hδ]; exact hw)
  · rw [PhiCache.okB_keys, ← PhiCache.keysBF_eq, ← hck, hc.1, hc.2]
    rfl
  · intro e he
    simp only [List.all_eq_true, beq_iff_eq] at hW
    exact hW e he
  · have hm : max (Q.cells .K) (Q.cells .E) < 2 ^ 64 - 1 := of_decide_eq_true hi
    intro a b ha hb hab
    exact FK.FKx_pow_inj (by omega) (by omega) hab

theorem staticFactsTS {C : QCfg} {T : TData} {F : TFrz} {δ : List Seg} {Q : Program} {lay : Typed.Lay}
    {c : PhiCache} {N : TypedV.TNat} (hQ : Q = QB C T) (hδ : δ = (qprogBF C T ⟨nK C, 0⟩).2)
    (h : staticOkTS C F δ Q lay c N = true) : StaticFactsT C T F Q lay c N :=
  staticFactsTC hQ hδ (K.checkTermsF_eq Q lay _) h

theorem staticFactsTOf {C : QCfg} {T : TData} {F : TFrz} {Q : Program} {lay : Typed.Lay} {c : PhiCache}
    {N : TypedV.TNat} (hQ : Q = QB C T) (h : staticOkTOf C T F Q lay c N = true) :
    StaticFactsT C T F Q lay c N :=
  staticFactsTS hQ rfl h

end Lvm.QTyped
end

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

theorem cacheOfTerms_terms (ts : Array CTerm) : (cacheOfTerms ts).terms.toArray = ts := Array.toArray_toList

end Lvm.QTyped
end

-- ===== from `LvmCertTInst` =====

section
section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

/-- **The typed static guard at `P20`** (`staticOkTOf` on the shared segments and `phi20`'s entry check:
`staticOkT20_eq`). -/
def staticOkT20 : Bool := staticOkTC cfg20 frz20 segs20 QB20 layT20 cacheT20 NT20 phi20.2

theorem cacheT20_eq : cacheT20 = cacheW QB20 layT20 := by
  unfold cacheT20 cacheOfTerms phi20 cacheW
  rw [K.compileTF_eq, K.termsChecked_fst]

theorem phi20_snd : phi20.2 = K.checkTerms QB20 layT20 phi20.1 := by
  unfold phi20
  exact K.termsChecked_snd QB20 layT20

theorem cacheT20_terms : cacheT20.terms.toArray = phi20.1 := by
  rw [show cacheT20 = cacheOfTerms phi20.1 from rfl]
  exact cacheOfTerms_terms _

theorem phi20_check : phi20.2 = K.checkTerms QB20 layT20 cacheT20.terms.toArray := by
  rw [cacheT20_terms]
  exact phi20_snd

theorem tdata20_eq : tdata20 = tdataOf cfg20 frz20 := rfl
theorem NT20_eq : NT20 = tnatOf cfg20 layT20 frz20 cacheT20 := rfl
theorem QB20_eq : QB20 = QB cfg20 tdata20 := (QB_eqF _ _).symm
theorem layT20_eq : layT20 = layBD cfg20 tdata20 dints20 := by rw [layBD, ← QB20_eq]; rfl
theorem staticOkT20_eq : staticOkT20 = staticOkTOf cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20 := by
  unfold staticOkT20 staticOkTOf staticOkTS
  rw [phi20_check, K.checkTermsF_eq, segs20]

theorem staticFactsT20 (h : staticOkT20 = true) :
    StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20 :=
  staticFactsTC QB20_eq rfl phi20_check h

end Lvm.QTyped
end
end

section
section
set_option autoImplicit false
namespace Lvm.T
open RecursionFast

/-- The guard's region check is B1-V's `TNat.layOk`. -/
theorem layOkN_eq : Lvm.QTyped.layOkN = Lvm.TypedV.TNat.layOk := rfl

/-- **V_S of the typed backend at `P20`.** -/
def VSB20 : SProg := Lvm.VST Lvm.P20 Lvm.QTyped.NT20

end Lvm.T
end
end

section
section
set_option autoImplicit false
namespace Lvm.T
open RecursionFast

/-- **The typed guard at `P20`**: `staticOkT20`, the word `1`'s region, `σ′`'s regions in the stream block `S` (M′,
R11: `Lvm.TypedV.sigInSB`), the layout checks the typed `NodeSound` reads (`nodeChkB`: the input map's cells, the
`readd` targets, the mini-bus's seed blocks) and the typed HAR's (`harChkB`: Q_arith's claim list in both shapes,
the circuit's regions are V_S's) (wave L). -/
def staticOkB20 : Bool :=
  Lvm.QTyped.staticOkT20 && oneOkB Lvm.QTyped.layT20 && Lvm.TypedV.sigInSB Lvm.QTyped.NT20 &&
    Lvm.QTyped.nodeChkB Lvm.QAsm.cfg20 Lvm.QTyped.frz20 Lvm.QTyped.QB20 Lvm.QTyped.layT20 Lvm.QTyped.NT20 &&
    Lvm.QTyped.harChkB Lvm.QAsm.cfg20 Lvm.QTyped.tdata20 Lvm.QTyped.NT20

/-- **The typed submission**: `V_S` at `P20` behind the typed static guard, M′'s extractor (lvm2 roll 11, R11-X:
`subGM`, `EXM`, `extXM`). -/
def submissionB20 : Submission := Lvm.Fin.subGM staticOkB20 VSB20

end Lvm.T
end
end

section
set_option autoImplicit false
namespace Lvm.CT
open Lvm.Typed Lvm.QTyped

/-- **The guard's facts** from `staticOkB20 = true`. -/
theorem sf20 (h : Lvm.T.staticOkB20 = true) : SF20 :=
  have h' : (((staticOkT20 = true ∧ Lvm.T.oneOkB layT20 = true) ∧ Lvm.TypedV.sigInSB NT20 = true) ∧
      nodeChkB Lvm.QAsm.cfg20 frz20 QB20 layT20 NT20 = true) ∧ harChkB Lvm.QAsm.cfg20 tdata20 NT20 = true := by
    simpa only [Lvm.T.staticOkB20, Bool.and_eq_true] using h
  { staticFactsT20 h'.1.1.1.1 with
    one := h'.1.1.1.2
    sig := Lvm.TypedV.sigInS_of h'.1.1.2
    chk := h'.1.2
    har := h'.2 }

end Lvm.CT
end

-- ===== from `LvmTypedVEqTop` =====

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.Replay (P20_eq)

/-- **The root** against `commitI P20`. -/
theorem folP_commit : FolP capS shpS idxS (Verifier.commitRootUd cfgMain24G)
    (atomsOf P20 (commitI P20)) fun _ ↦ True := by
  rw [atomsOf_commitI]
  exact folP_commitRootUd cfgMain24G rfl cap_main0 rfl

theorem atomsOf_schedule : atomsOf P20 (schedule P20) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20 Lvm.ASM.midItems ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [schedule_eq P20 (by decide), midItems_eq]
  simp only [atomsOf_append, List.append_assoc, List.append_nil, atomsOf_commitI]

/-- **`P_S` at M′ follows the schedule** at P20 (`LvmMPCert.PSWithM mid x`'s body: one root, the middle phases,
`C_main`'s opening), for any middle phases that follow `midItems`. -/
theorem fol_PSOfM (mid : List UInt8 → VerifierProgram (List VStackClaim))
    (hmid : ∀ x, FolP capS shpS idxS (mid x) (atomsOf P20 Lvm.ASM.midItems) fun _ ↦ True) (x : List UInt8) :
    Fol capS shpS idxS (do
        Verifier.commitRootUd cfgMain24G
        let cl ← mid x
        Verifier.verifyStackedJ (cfgMain23Jq 1) cl
        return true) (atomsOf P20 (schedule P20)) [] fun _ _ ↦ True := by
  rw [atomsOf_schedule]
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine Fol.bindP (hmid x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgRec20G)
section Typed
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- The zerocheck against `zeroI`. -/
theorem folP_zeroProg : FolP cap shp idx Typed.zeroProg (atomsOf p zeroI) fun _ ↦ True := by
  simp only [zeroI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.zeroProg
  exact (folP_sampleChallenges Typed.xVars).bind fun τ hτ ↦
    (folP_sumcheck p rfl (by norm_num) (τ.map some) Typed.xVars 0 (by simp [hτ])).bind fun _ _ ↦
    (folP_readScalars 3).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The wiring against `wiringI`. -/
theorem folP_wireProg (Ti : Typed.TInst) (pub : Pub) (abc : E × E × E) :
    FolP cap shp idx (Typed.wireProg Ti pub abc) (atomsOf p wiringI) fun _ ↦ True := by
  simp only [wiringI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.wireProg
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ Typed.yVars _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 4).bind fun _ _ ↦ (folP_readScalars 4).bind_nil fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The relayout against `relayI`. -/
theorem folP_relayProg (Ti : Typed.TInst) (ry : List E) (vS : E) :
    FolP cap shp idx (Typed.relayProg Ti ry vS) (atomsOf p relayI) fun _ ↦ True := by
  simp only [relayI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rd]
  unfold Typed.relayProg
  exact (folP_sumcheck p rfl (by norm_num) _ TypedV.relayRoundsN _ (List.length_replicate ..)).bind fun _ _ ↦
    folP_readScalar.bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

end Typed
end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgRec20G)
section Typed
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **The typed phases** against `typedI p`, the record's mini-bus numbers those of `Ti.mbT` (one
leaf-decomposition scalar, depth `miniDepth`, the tallest table's rounds, the widths' sum). -/
theorem folP_typedProg (Ti : Typed.TInst) (pub : Pub) (hl : p.leafdecReads = 1)
    (hd : p.busDepth = Typed.miniDepth) (hr : p.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : p.tableEvals = (Ti.mbT.map (·.w)).sum) :
    FolP cap shp idx (Typed.typedProg Ti pub) (atomsOf p (typedI p)) fun _ ↦ True := by
  simp only [typedI, atomsOf_append]
  rw [← atomsOf_append p (miniBusI p)]
  unfold Typed.typedProg
  exact (folP_zeroProg p).bind fun _ _ ↦ (folP_wireProg p Ti pub _).bind fun _ _ ↦
    (folP_relayProg p Ti _ _).bind fun _ _ ↦
    (folP_accProg p 2 TypedV.phiVarsN _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusProg p Ti hl hd hr he).bind_ret fun _ _ ↦ trivial

/-- **The typed middle phases follow `midItems`** (`P20`'s mini-bus numbers those of `Ti.mbT`). -/
theorem folP_midT₂ (Ti : Typed.TInst) (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    FolP cap shp idx (Typed.midT₂ Ti x) (atomsOf P20 Lvm.ASM.midItems) fun _ ↦ True := by
  have e : atomsOf P20 Lvm.ASM.midItems = atomsOf P20 (typedI P20) ++
      atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))) := by
    rw [midItems_eq]
    simp only [atomsOf_append, List.append_nil]
  rw [e]
  unfold Typed.midT₂
  exact (folP_typedProg P20 Ti (pubX x) hl hd hr he).bind fun _ _ ↦
    (folP_kgProgS _ _).bind_ret fun _ _ ↦ trivial

end Typed
end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgRec20G)

/-- **WP-14d's shape obligation, typed**: every accepted run of `midT₂ Ti x` has the kinds of `midItems`. -/
theorem midFollows_midT₂ (Ti : Typed.TInst) (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum) :
    Lvm.ASM.MidFollows (Typed.midT₂ Ti) := by
  intro x l a hl'
  rw [(@fol_after capS shpS idxS _ (atomsOf P20 Lvm.ASM.midItems) (Typed.midT₂ Ti x) []
    (fun _ pp' ↦ pp' = []) (@FolP.fol capS shpS idxS _ (Typed.midT₂ Ti x) (atomsOf P20 Lvm.ASM.midItems)
      (fun _ ↦ True) (folP_midT₂ Ti hl hd hr he x) []) l a hl').1, atomKinds_atomsOf P20 _ midItems_noPos]

end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm

set_option maxRecDepth 200000 in
/-- **The static check at P20.** -/
theorem stA_P20 : stA P20 (atomsOf P20 (schedule P20)) 0 [] [] = true := by
  rw [stA_atomsOf, schedule, phases_P20_lit, Lvm.Replay.P20_eq]; decide +kernel

end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm

/-- Widths that are all 24 at the constant width 24. -/
theorem wAt_24 {l : List ℕ} (h : ∀ x ∈ l, x = 24) (i : ℕ) : WAt (fun _ ↦ 24) i l := fun k hk ↦ by
  rw [List.getD_eq_getElem _ _ hk, h _ (List.getElem_mem hk)]

end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

theorem entOff_one (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) 1 = 48 := by
  simp [entOff, traceBytes_cons, traceBytes_nil, length_enc64, length_blb, size_q0Query]

theorem size_seedQuery (π : ByteArray) (a₀ : Digest) (hH : headerBytes ≤ π.size) :
    (seedQuery π a₀).size = 32 + (headerBytes - 8) := by
  rw [seedQuery, ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]
  simp [length_blb]; omega

theorem entOff_two (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) (hH : headerBytes ≤ π.size) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) 2 = RS.start.ent := by
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest).drop 1 = (seedQuery π a₀, st₀) :: rest := rfl
  rw [(stream_entry hd1).2.2, entOff_one, size_seedQuery π a₀ hH]
  rfl

/-- The header bytes in the stream: the seed entry holds `π`'s bytes 8…4927. -/
theorem seed_bytes (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) (hH : headerBytes ≤ π.size) :
    ∀ t < headerBytes - 8, (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest)).get!
      (headerAt 8 + t) = π.get! (8 + t) := by
  intro t ht
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest).drop 1 = (seedQuery π a₀, st₀) :: rest := rfl
  have he := (stream_entry hd1).1 (32 + t) 1 (by rw [size_seedQuery π a₀ hH]; omega)
  rw [entOff_one, show 48 + 8 + (32 + t) = headerAt 8 + t by simp [headerAt]; omega] at he
  have hg := getD_sb (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest)) (headerAt 8 + t) 1 0
    (by omega)
  rw [Nat.add_zero] at hg
  rw [← hg, show sb = sbs from rfl, he, get!_blb]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero,
    seedQuery, blb_append, blb_digestBytes, List.getElem?_append_right (by simp),
    show 32 + t - (Vector.toList a₀).length = t by simp, blb_extract, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem decideF_ok {p : Params} {m : M3} {vk c : Digest} {sig : ByteArray}
    (h : decideF p m vk c sig = true) : (runD (decideProg p m vk c) sig RS.start).2.ok = true := by
  rw [decideF_eq, Bool.and_eq_true] at h
  have h1 := h.1
  unfold decideCore DM.runOn at h1
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e] at h1
  rcases hr : runD (decideProg p m vk c) sig RS.start with ⟨u, s⟩
  rw [hr] at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1

/-- A23: `decideF` also checks the folded claim of the run (`AccOk`). -/
theorem decideF_acc {p : Params} {m : M3} {vk c : Digest} {sig : ByteArray}
    (h : decideF p m vk c sig = true) :
    AccOk p m (pubOf vk c sig) (runD (decideProg p m vk c) sig RS.start).1 = true := by
  rw [decideF_eq, Bool.and_eq_true] at h
  have h2 := h.2
  unfold accOutOf DM.runOn at h2
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e] at h2
  exact h2

end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile
section Main
variable (tabs : Pub → List M3.Tab) (mid : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram
  (List VStackClaim × List VStackClaim))

/-- **V_S's decision refines `PSWith mid`** on every stream whose header is the statement's (roll 7:
the chain below is generic in the middle phases `mid`; `ref_decide` gives it for `midS₂ tabs`). -/
def RefD : Prop :=
  ∀ (sig : ByteArray) (vk c : Digest) (x : List UInt8), pubOf vk c sig = pubX x →
    RefAtP capS occS shpS sig (decideProg P20 (M3.real P20 tabs) vk c) (Lvm.ASM.PSWith mid x)
      (fun _ b ↦ b = true) (fun a ↦ AccOk P20 (M3.real P20 tabs) (pubX x) a = true)

/-- **V_S ⇒ S.V on a trace**, given the program's shape and the parse facts. -/
theorem refines_seqOf (href : RefD tabs mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (hhdr : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes))
    (hok : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.okS vk c (xOf π) = true)
    (hpubeq : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true → ∀ {sig : ByteArray},
      (∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      pubOf vk c sig = pubX (xOf π))
    (vk c : Digest) (π : ByteArray) (tr : Trace)
    (h : (VSL P20 tabs vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runSeq tr = some true := by
  -- the header check
  unfold VSL VS at h
  by_cases hp : parseOk P20 vk c π = true
  swap
  · rw [if_neg hp] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  rw [if_pos hp] at h
  have hp' := hp
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
  have hsize : π.size = piSize P20 := hp'.1.1.1
  have hHle : headerBytes ≤ π.size := by rw [hsize, sizes_P20.1]; decide
  -- the driver: q₀, the seed, the schedule
  rw [drive_of (p := P20) rfl (by decide)] at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  -- the driver's final state: the whole trace logged, the body used up, `F` on the stream
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run P20 π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  have hlog : streamOf sf.log =
      traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest with htr
  set x := xOf π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpub := hpubeq hp (sig := traceBytesB tr) (seed_bytes π a₀ st₀ rest hHle)
  have hok0 : (runD (decideProg P20 (M3.real P20 tabs) vk c) (traceBytesB tr) RS.start).2.ok = true :=
    decideF_ok hF
  have hacc : AccOk P20 (M3.real P20 tabs) (pubX x)
      (runD (decideProg P20 (M3.real P20 tabs) vk c) (traceBytesB tr) RS.start).1 = true := by
    rw [← hpub]; exact decideF_acc hF
  obtain ⟨b, hb1, -, -, rfl⟩ :=
    href (traceBytesB tr) vk c x hpub RS.start hok0 hacc
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS occS shpS (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  obtain ⟨⟨o, rsW, nW⟩, hW⟩ : ∃ r, ivpW capS occS shpS (fun _ ↦ 24) (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start 0 = r :=
    ⟨_, rfl⟩
  have hWI := ivpW_ivp (cap := capS) (occ := occS) (shp := shpS) (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start 0
  rw [hW, hivp] at hWI
  simp only at hWI
  obtain ⟨rfl, rfl⟩ := hWI
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    simW (S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq occOfS_eq (atomsOf P20 (schedule P20)) (Lvm.ASM.PSWith mid x) [] _ _ st₀ [] []
      _ RS.start 2 [] [] _ true _ 0 nW (hfol x) (by simpa using stA_P20) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        rw [hb.1])
      h2 (wAt_24 (mem_widthsA_atomsOf P20 _ noWB_P20) 0) hW
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hx5976 : x.length = Lvm.ASM.hdrLen := by
    rw [hx, xOf, List.length_take, List.length_drop, length_blb]
    simp only [Lvm.ASM.hdrLen]; omega
  have hseed : toQ (a₀.toList ++ x) = seedQuery π a₀ := by
    apply toQ_eq
    rw [seedQuery, blb_append, blb_digestBytes, blb_extract, hx, xOf]
    rfl
  have hqc : 32 + x.length ≤ queryCap := by rw [hx5976]; decide
  set S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid) with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hhdr hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [hok hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = Lvm.ASM.PSWith mid x from rfl, runW_eq_runKW,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

/-- **V_S ⇒ S.V on every log** (WP-14's `OpenS.refines` form), given the program's shape and the
parse facts. -/
theorem refines_logOf (href : RefD tabs mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (hhdr : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes))
    (hok : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.okS vk c (xOf π) = true)
    (hpubeq : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true → ∀ {sig : ByteArray},
      (∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      pubOf vk c sig = pubX (xOf π)) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runLog L = some true :=
  fun vk L c π _ h ↦ runLog_of_seq
    (fun tr ht ↦ refines_seqOf tabs mid href hfol hhdr hok hpubeq vk c π tr ht) L h

/-- **V_S ⇒ S.V on every log** (O5b, WP-14's `OpenS.refines`), given the program's shape against
the schedule. -/
theorem refines_logF (href : RefD tabs mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runLog L = some true :=
  refines_logOf tabs mid href hfol (fun h ↦ hdrS_of_parseOk h) (fun h ↦ okS_of_parseOk h)
    (fun h _ hs ↦ pubOf_eq_pubX h hs)

end Main
end Lvm.VEq
end
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-- A bus result with no claim (the typed path has no bus; the mini-bus's claims are its table phase's). -/
def busNil : BusOut := ⟨true, [], [], []⟩

/-- **Phases 2–7 of the typed decision** (the typed phases, then roll 7's `dKg`), grouped as `midT₂`: the claims
and the folded accumulator. -/
def dMidT (p : Params) (N : TNat) (pub : Pub) : DM (List (Com × BlockClaim × FE) × Acc) :=
  dTypedT p N (N.m3 p) pub >>= fun t ↦ dKg p (N.m3 p) pub >>= fun kg ↦
    pure (t.2.1 ++ dClaimsT (N.m3 p) p pub busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2, t.1)

/-- **`decideProgT` grouped as `P_S`** (its value: the folded accumulator; M′ `S2GM`: one cap). -/
def dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) : DM Acc :=
  MonadReader.read >>= fun sig ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap) >>= fun _ ↦
    dMidT p N (pubOf vk c sig) >>= fun r ↦ dOpenT p (smallT p (pubOf vk c sig)) r.1 >>= fun _ ↦ pure r.2

theorem decideProgT_dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) :
    decideProgT p N vk c = dTopT p N vk c := by
  simp only [decideProgT, dTopT, dMidT, dKg, dKec, dKsLink, dClaimsT, busNil, bind_assoc, pure_bind]

theorem monoD_dMidT (p : Params) (N : TNat) (pub : Pub) : MonoD (dMidT p N pub) :=
  (monoD_dTypedT _ _ _ _).bind fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-- The typed shape bit is roll 7's (`nuT = CMain.nu20 = 23`, `2^18`). -/
theorem smallT_eq (p : Params) (pub : Pub) : smallT p pub = Shape.smallP p pub := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

theorem onStackZsF_append (s : Bool) (a b : List (BlockClaim × FE)) :
    Shape.onStackZsF s (a ++ b) = Shape.onStackZsF s a ++ Shape.onStackZsF s b := by
  unfold Shape.onStackZsF; split <;> simp

theorem onStackZs_append (x : List UInt8) (a b : List VStackClaim) :
    Shape.onStackZs x (a ++ b) = Shape.onStackZs x a ++ Shape.onStackZs x b := by
  unfold Shape.onStackZs; split <;> simp

theorem m3_eq (N : TNat) (p : Params) : N.m3 p = M3.real p fun _ ↦ N.mbT := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
section Ref
variable {sig : ByteArray}

theorem monoD_dOpenT (p : Params) (s : Bool) (claims : List (Com × BlockClaim × FE)) : MonoD (dOpenT p s claims) :=
  (MonoD.require _).bind fun _ ↦ monoD_verifyStacked _ _ _ _ _ _

/-- **The M′ opening at `P20`** (`S2GM`: `C_main`'s claims only, on the statement's shape's stack): V_S's
`dOpenT` refines `verifyStackedJ (cfgMain23Jq 1)` on a list `SCRel`-related to `onStackZsF`'s, where its
`require` (every claim on `C_main`) held. -/
theorem ref_dOpenT (s : Bool) (claims : List (Com × BlockClaim × FE)) (cl : List VStackClaim)
    (h : claims.all (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2))) cl) :
    RefAtP capS occS shpS sig (dOpenT P20 s claims) (Verifier.verifyStackedJ (cfgMain23Jq 1) cl)
      (fun _ _ ↦ True) (fun _ ↦ True) := by
  unfold dOpenT
  refine RefAtP.require_left (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _) fun hall ↦ ?_
  have h' := h hall
  have e : (if s then ((claims.filter (·.1 == .main)).map (·.2)).map fun e ↦ onStackZBN P20.nuMain e.1 e.2
      else ((claims.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2)) := by
    unfold Shape.onStackZsF; rw [nuMain_P20]; rfl
  dsimp only
  rw [e, nuMain_P20]
  exact (ref_verifyStackedJ _ (cfgMain23Jq 1) _ _ _ _ _ h' mainOod_P20 rfl rfl rfl rfl rfl corrMain24).toP _

end Ref
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-- `decideFT` holds: the run's checks held and its folded claim passes `Φ_Q`. -/
theorem decideFT_ok {p : Params} {N : TNat} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFT p N vk c sig = true) :
    (runD (decideProgT p N vk c) sig RS.start).2.ok = true ∧
      N.phi (runD (decideProgT p N vk c) sig RS.start).1.pt = (runD (decideProgT p N vk c) sig RS.start).1.y := by
  -- `decideFT`'s body by `delta` on the bare constant (GOLF-HAR's pattern): `unfold … at h` left a cast the kernel
  -- checked by reducing the run (GOLF-DEC3)
  have eF : @decideFT = @decideFT := rfl
  conv at eF => rhs; delta decideFT
  rw [eF] at h
  beta_reduce at h
  rw [decideProgTS_eq, DM.runOn.eq_1] at h
  -- `StateT.run`'s equation, not `rfl`: the kernel's lazy unfolding took `decideProgT` (the higher definition) first
  -- and reduced the program (GOLF-DEC2, 2 s)
  have e : (decideProgT p N vk c sig).run RS.start = runD (decideProgT p N vk c) sig RS.start :=
    StateT.run.eq_1 _ _
  rw [e] at h
  rcases hr : runD (decideProgT p N vk c) sig RS.start with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, Lvm.M3.FE_eq_of_beq h.2⟩

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
section Main
variable (N : TNat) (PS : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool)

/-- **V_S's typed decision refines the IOP verifier `PS`** on every stream whose header is the statement's (lvm2
roll 11: generic in `PS`; M′'s is `PSWithM`, B1's was `PSWith mid`). -/
def RefDT : Prop :=
  ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), pubOf vk c sig = pubX x →
    RefAtP capS occS shpS sig (decideProgT P20 N vk c) (PS x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y)

/-- **V_S ⇒ S.V on a trace, typed** (roll 7's `refines_seqOf` for `VST`/`decideFT`). -/
theorem refines_seqOfT (href : RefDT N PS)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VST P20 N vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk PS).V c π).runSeq tr = some true := by
  -- the header check
  unfold VST at h
  by_cases hp : parseOk P20 vk c π = true
  swap
  · rw [if_neg hp] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  rw [if_pos hp] at h
  have hp' := hp
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
  have hsize : π.size = piSize P20 := hp'.1.1.1
  have hHle : headerBytes ≤ π.size := by rw [hsize, sizes_P20.1]; decide
  -- the driver: q₀, the seed, the schedule
  rw [drive_of (p := P20) rfl (by decide)] at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run P20 π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  have hlog : streamOf sf.log =
      traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest with htr
  set x := xOf π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpub := pubOf_eq_pubX hp (sig := traceBytesB tr) (seed_bytes π a₀ st₀ rest hHle)
  obtain ⟨hok0, hacc⟩ := decideFT_ok hF
  obtain ⟨b, hb1, -, -, rfl⟩ := href (traceBytesB tr) vk c x hpub RS.start hok0 hacc
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS occS shpS (PS x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  obtain ⟨⟨o, rsW, nW⟩, hW⟩ : ∃ r, ivpW capS occS shpS (fun _ ↦ 24) (PS x) (traceBytesB tr) RS.start 0 = r :=
    ⟨_, rfl⟩
  have hWI := ivpW_ivp (cap := capS) (occ := occS) (shp := shpS) (PS x) (traceBytesB tr) RS.start 0
  rw [hW, hivp] at hWI
  simp only at hWI
  obtain ⟨rfl, rfl⟩ := hWI
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk PS) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    simW (S := Lvm.ASM.schemeS vk PS) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq occOfS_eq (atomsOf P20 (schedule P20)) (PS x) [] _ _ st₀ [] []
      _ RS.start 2 [] [] _ true _ 0 nW (hfol x) (by simpa using stA_P20) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        rw [hb.1])
      h2 (wAt_24 (mem_widthsA_atomsOf P20 _ noWB_P20) 0) hW
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hx5976 : x.length = Lvm.ASM.hdrLen := by
    rw [hx, xOf, List.length_take, List.length_drop, length_blb]
    simp only [Lvm.ASM.hdrLen]; omega
  have hseed : toQ (a₀.toList ++ x) = seedQuery π a₀ := by
    apply toQ_eq
    rw [seedQuery, blb_append, blb_digestBytes, blb_extract, hx, xOf]
    rfl
  have hqc : 32 + x.length ≤ queryCap := by rw [hx5976]; decide
  set S := Lvm.ASM.schemeS vk PS with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hdrS_of_parseOk hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [okS_of_parseOk hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = PS x from rfl, runW_eq_runKW,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

end Main
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-- **The typed middle phases follow the schedule** (`MidFollows`), the mini-bus's numbers from `TRefHyp`. -/
theorem midFollows_T (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) :
    Lvm.ASM.MidFollows (midT₂ (N.inst Q lay)) := by
  obtain ⟨hl, hr, he, -, -⟩ := H.fits
  exact midFollows_midT₂ (N.inst Q lay) hl busDepth_P20 hr he

open Lvm.CT Lvm.QTyped in
/-- **`TRefHyp` at `P20`** from the guard's facts and `THyp`: `PhiQC cacheT20` is `PhiQF` (`cacheT20_eq`, then
`PhiQC_eq`, rewriting only). -/
theorem trefHyp20 (S : SF20) (H : THyp Ti20) : TRefHyp NT20 QB20 layT20 where
  ok := S.regs
  hlay := S.hlayOk
  mini := S.mini
  sc := H.sc
  phi pt hpt := by
    have e : NT20.phi = PhiQC cacheT20 := rfl
    have hc : (cacheW QB20 layT20).okB QB20 layT20 = true := by rw [← cacheT20_eq]; exact S.cache
    rw [e, cacheT20_eq]
    exact PhiQC_eq QB20 layT20 S.hlay hc pt hpt

open Lvm.CT Lvm.QTyped Lvm.ASM in
/-- **`LvmCertT20.midFollowsT20`** (statement verbatim). -/
theorem midFollowsT20L (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  midFollows_T NT20 QB20 layT20 (trefHyp20 S H)

end Lvm.VEq
end

-- ===== from `LvmMPVEq` =====

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
section
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- `midM` follows what its pair-form phases follow. -/
theorem folP_midM (reloc : List UInt8 → VStackClaim → VStackClaim)
    (mid : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims) (x : List UInt8) (as : List Atom)
    (h : FolP cap shp idx (mid x) as fun _ ↦ True) :
    FolP cap shp idx (Lvm.ASM.midM reloc mid x) as fun _ ↦ True :=
  h.bind_ret fun _ _ ↦ trivial

end
end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- **M′'s typed `P_S` follows the schedule** at P20. -/
theorem fol_PSTM (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.ASM.midM reloc (Typed.midT₂ Ti)) x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True :=
  fol_PSOfM _ (fun x ↦ folP_midM reloc _ x _ (folP_midT₂ Ti hl hd hr he x)) x

/-- **`MidFollows` through the relocation**: `midM` adds no transcript item. -/
theorem midFollows_midM (reloc : List UInt8 → VStackClaim → VStackClaim)
    {mid : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims} (h : Lvm.ASM.MidFollows mid) :
    Lvm.ASM.MidFollows (Lvm.ASM.midM reloc mid) := by
  intro x l a hl
  obtain ⟨b, l₁, l₂, rfl, h1, h2⟩ := Lvm.ASM.after_bind_ret hl
  cases l₂ with
  | nil => simpa using h x l₁ b h1
  | cons e l₂ => simp [VerifierProgram.after] at h2

open Lvm.CT Lvm.QTyped in
/-- **`MidFollows` at M′, `P20`** (R11-X's `ext_eqM20`): M′'s middle phases follow `midItems`, for every
relocation (in particular `LvmCertM20.reloc20`). -/
theorem midFollowsM20 (S : SF20) (H : Typed.THyp Ti20)
    (reloc : List UInt8 → VStackClaim → VStackClaim) :
    Lvm.ASM.MidFollows (Lvm.ASM.midM reloc (Typed.midT₂ Ti20)) :=
  midFollows_midM reloc (midFollowsT20L S H)

end Lvm.VEq
end
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.KeccakGkr (eqAt)

theorem relocV_eq (x : List UInt8) (c : VStackClaim) :
    relocV relocS x c = (fun w ↦ if Shape.small x then Shape.onStackZ w else w) (relocS c) := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.KeccakGkr (eqAt)

/-- **V_S's claim list against `ordM` of `assembleT₂`'s relocated pair** (M′, both shapes): where V_S's
`require` held (every claim on `C_main`), its claims, on the statement's shape's stack, are the spec's in
V_S's phase order, the stream claims (the relayout's point claim, `σ′`'s, the `KS` link's `M`) relocated onto
`S`. -/
theorem typedClaimsM_rel (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (x : List UInt8) (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims)
    (hT : TRelT N Q lay t a)
    (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') (hi : ∃ i, kg.2.2 = ((N.m3 P20).ksLink i).2)
    (hall : (t.2.1 ++ dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2).all
      (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.smallP P20 (pubX x))
        (((t.2.1 ++ dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2).filter
          (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordM ((assembleT₂ x a kg').1.map (relocV relocS x)) (assembleT₂ x a kg').2) := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, hrr, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.fits
  set D := dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2 with hD
  set cl := M3.claimsOfEvs N.mbT t.2.2
  have hsx : Shape.smallP P20 (pubX x) = Shape.small x := smallP_P20 x
  have hall' : ∀ e ∈ t.2.1 ++ D, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he], hsx]
  have hok := H.ok
  rw [nuMain_P20] at hok
  -- phases 3–7's claims (`D`), claim for claim
  have hDfst : D.map (fun e ↦ (e.1, e.2.1)) = M3.tableClaimsR N.mbT t.2.2 ++
      ((tapeClaims P20 kg.1.1 kg.1.2.1 (pubX x) ++ keccakClaims (M3.real P20 fun _ ↦ N.mbT).ksBlock
        kg.2.1.2.2.1 kg.2.1.2.2.2).map (.main, ·) ++
        (M3.real P20 fun _ ↦ N.mbT).ksOutputClaims kg.2.1.1 kg.2.1.2.1) ++ kg.2.2 := by
    have htc : (M3.real P20 fun _ ↦ N.mbT).tableClaims (pubX x) t.2.2 = M3.tableClaimsR N.mbT t.2.2 := by
      conv_rhs => rw [← H.sc_eq]
      rfl
    rw [hD, Shape.dClaimsT_fst, m3_eq]
    unfold dClaims
    rw [show busNil.claims = [] from rfl, List.nil_append, htc]
    simp only [List.append_assoc]
  have hpre := dClaims_rel (fun _ ↦ N.mbT) (pubX x) kg kg' hk
  have hDrel : List.Forall₂ CRelM (D.map fun e ↦ (e.1, e.2.1)) (tableClaimsE N.mbT cl ++
      ((tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
        ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1) ++ ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2) := by
    rw [hDfst]
    exact Lk.forall₂_append (Lk.forall₂_append (hcl.imp fun _ _ h ↦ CRel.crelM h) (hpre.imp fun _ _ h ↦ CRel.crelM h))
      hk.2.2
  have hDtail : Shape.small x = true → ∀ e ∈ D, e.1 = .main →
      Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1 := fun hsm ↦ by
    obtain ⟨⟨-, -, -, hwr, hr, hring⟩, -⟩ := hk
    rw [hD, m3_eq]
    exact Shape.tails_main (fun _ ↦ N.mbT) (pubX x) hfc hfh busNil rfl t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2
      hr hwr.2.2.2.2.2.2.1 hwr.2.2.2.2.2.2.2.2.1 hring (by rw [← m3_eq]; exact hi) (of_decide_eq_true hsm)
      (by simp [pubX, pubOf])
  have hDV := forall₂_crelM (s := Shape.small x) hDrel (fun e he ↦ hall' e (List.mem_append_right _ he)) hDtail
  -- the mini-bus's claims are on `C_main`
  have hmbV : ∀ e ∈ M3.tableClaimsR N.mbT t.2.2, e.1 = .main := fun e he ↦ by
    have h1 : e ∈ D.map (fun e ↦ (e.1, e.2.1)) := by
      rw [hDfst]; exact List.mem_append_left _ (List.mem_append_left _ he)
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 h1
    exact hall' e' (List.mem_append_right _ he')
  have hmbE := main_of_crel hcl hmbV
  -- the typed claims
  have hin : Shape.InStack ⟨23, 0⟩ := ⟨le_rfl, rfl, by norm_num⟩
  have hrelay : SCRel (BlockClaim.point ⟨P20.nuRec, (layout0 P20).s⟩ rr vR).onStack
      (relocS (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack) := by
    rw [← relocS_point]
    exact onStack_rel (Lk.point_rel _ _ _ (by rw [nuRec_P20, layout0_s]; rfl) rfl rfl)
  have hsg : SCRel (⟨⟨23, 0⟩, affW N .sigma ry, rv.getD 2 0⟩ : BlockClaim).onStack
      (relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map FE.toExt3)
        ((rv.map FE.toExt3).getD 2 0))) := by
    rw [← regClaim_relocS N Q lay 23 P20.nuRec hok H.hlay hσ, getD_map_toExt3]
    exact regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .sigma 23 (regsOf_dst hok .sigma (.inr (.inr rfl))) ry hry _
  have hcom := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .com 23
    (regsOf_dst hok .com (.inl rfl)) ry hry (rv.getD 0 0)
  have hks := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .ks 23
    (regsOf_dst hok .ks (.inr (.inl rfl))) ry hry (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      [relocS (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack,
        relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map FE.toExt3)
          ((rv.map FE.toExt3).getD 2 0)),
        regClaim (N.inst Q lay) .com N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 0 0)),
        regClaim (N.inst Q lay) .ks N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 3 0))] := by
    rw [ht1]
    unfold typedClaimsN
    rw [nuMain_P20]
    refine .cons (vrel_of hrelay fun _ ↦ ⟨offOK_relay.inStack, (Shape.OffOK.tail offOK_relay).symm⟩)
      (.cons (vrel_of hsg fun _ ↦ ⟨hin, (tail_affW N P20.nuRec hok .sigma (.inr (.inr rfl)) _ _).symm⟩)
        (.cons (vrel_of hcom fun _ ↦ ⟨hin, (tail_affW N P20.nuRec hok .com (.inl rfl) _ _).symm⟩)
          (.cons (vrel_of hks fun _ ↦ ⟨hin, (tail_affW N P20.nuRec hok .ks (.inr (.inl rfl)) _ _).symm⟩) .nil)))
  have hV := forall₂_onStackZsF (Lk.forall₂_append hTV hDV)
  -- the spec's list in V_S's order
  obtain ⟨yE, inE, mE, xE, hK⟩ : ∃ a b c d, ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2 =
      [(.main, a), (.main, b), (.crec, c), (.main, d)] := ⟨_, _, _, _, rfl⟩
  have hpreE : ∀ b ∈ (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
      ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1, b.1 = .main := by
    intro b hb
    simp only [List.mem_append, List.mem_map, ksOutputClaimsE] at hb
    rcases hb with ⟨c, -, rfl⟩ | ⟨l, -, rfl⟩ <;> rfl
  convert hV using 1
  set P := (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (fun c : BClaim ↦ (Com.main, c)) ++
    ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1 with hP
  have hP1 : ∀ b ∈ (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map
      (fun c : BClaim ↦ (Com.main, c)), b.1 = .main := fun b hb ↦ hpreE b (List.mem_append_left _ hb)
  have hP2 : ∀ b ∈ ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1, b.1 = .main :=
    fun b hb ↦ hpreE b (List.mem_append_right _ hb)
  have hS : assembleS [] (pubX x) [] kg' =
      ([mE.onStack], P.map (·.2.onStack) ++ [yE.onStack, inE.onStack, xE.onStack]) := by
    unfold assembleS
    dsimp only
    rw [hK, show tableClaimsE [] [] = [] from rfl, List.nil_append, hP]
    have hmc : (Com.main == Com.crec) = false := rfl
    have hcc : (Com.crec == Com.main) = false := rfl
    simp [List.filter_append, List.filter_map, Function.comp_def, ksOutputClaimsE, hmc, hcc]
  have hmb : (N.inst Q lay).mbT = N.mbT := rfl
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (relocV relocS x) = (l.map relocS).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold assembleT₂ typedClaims miniClaims
  rw [hmb, filter_main_self hmbE, filter_crec_nil hmbE, hS, onStackZs_eq_map, hρ, ordM_map]
  congr 1
  rw [hK]
  simp only [List.map_append, inplM_main hmbE, inplM_main hpreE, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]
  have hm : ∀ (a b : VStackClaim) (A B : List VStackClaim) (c d e : VStackClaim),
      a :: b :: (A ++ (B ++ [c, d, e])) = (a :: b :: (A ++ (B ++ [c, d]))) ++ [e] := by intros; simp
  rw [hm, Lvm.ASM.ordM, List.dropLast_concat, List.getLast?_concat]
  simp only [getD_map_toExt3]
  simp [inplM]
  exact ⟨rfl, rfl⟩

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.KeccakGkr (eqAt)
section Ref
variable {sig : ByteArray}

/-- `midM` on the typed phases, as one program. -/
theorem midM_midT₂ (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : TInst) (x : List UInt8) :
    Lvm.ASM.midM reloc (midT₂ Ti) x = typedProg Ti (pubX x) >>= fun a ↦ kgProgS (hdX x).s (pubX x).n >>= fun k ↦
      VerifierProgram.ret (Lvm.ASM.ordM ((assembleT₂ x a k).1.map (reloc x)) (assembleT₂ x a k).2) := by
  unfold Lvm.ASM.midM midT₂
  simp only [bind_assoc, ret_bindM]

/-- **Phases 2–7 refine `midM (relocV relocS) (midT₂ Ti)`** under the promise that the folded claim holds: where
every claim is on `C_main` (V_S's `require`), V_S's claims, on the statement's shape's stack, are `midM`'s. -/
theorem ref_dMidTM (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (x : List UInt8) (hacc : (pubX x).accIn.pt.length = phiVars) :
    RefAtP capS occS shpS sig (dMidT P20 N (pubX x)) (Lvm.ASM.midM (relocV relocS) (midT₂ (N.inst Q lay)) x)
      (fun r cl ↦ r.1.all (·.1 == .main) = true →
        List.Forall₂ SCRel (Shape.onStackZsF (Shape.smallP P20 (pubX x)) ((r.1.filter (·.1 == .main)).map (·.2))) cl)
      (fun r ↦ N.phi r.2.pt = r.2.y) := by
  rw [midM_midT₂]
  unfold dMidT
  apply RefAtP.bind (Q := fun t ↦ N.phi t.1.pt = t.1.y)
  · exact fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_dTypedT N Q lay H (pubX x) hacc
  · intro t s h; rw [runD_bind_pure_snd] at h; exact h
  · rintro t a hT -
    refine (RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKg (fun _ ↦ N.mbT) (pubX x) (hdX x).s (pubX_s x)) ?_).toP _
    rintro kg kg' ⟨hk, hi⟩
    exact RefAt.pure fun hall ↦ typedClaimsM_rel N Q lay H hσ x t a hT kg kg' hk hi hall

/-- **V_S's typed decision refines `P_S = PSWithM (midM (relocV relocS) (midT₂ Ti))`** under the promise that its
value (the folded accumulator) passes `Φ_Q` (`decideFT`'s check after the run). -/
theorem ref_decideTM (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (vk c : RecursionFast.Digest) (x : List UInt8) (hacc : (pubX x).accIn.pt.length = phiVars)
    (hpub : pubOf vk c sig = pubX x) :
    RefAtP capS occS shpS sig (decideProgT P20 N vk c)
      (Lvm.ASM.PSWithM (Lvm.ASM.midM (relocV relocS) (midT₂ (N.inst Q lay))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y) := by
  rw [decideProgT_dTopT]
  unfold dTopT Lvm.ASM.PSWithM
  rw [commitRootUd_mainT]
  refine RefAtP.read_left ?_
  simp only [hpub, smallT_eq]
  -- the cap
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ (monoD_dMidT _ _ _).bind fun _ ↦ (monoD_dOpenT _ _ _).bind fun _ ↦ MonoD.pure _
  · exact (ref_skip (n := nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap) rfl).toP _
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  -- phases 2–7
  apply RefAtP.bind (Q := fun r ↦ N.phi r.2.pt = r.2.y)
  · exact fun _ ↦ (monoD_dOpenT _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_dMidTM N Q lay H hσ x hacc
  · intro r s h; rw [runD_bind_pure] at h; exact h
  rintro r cl h -
  -- the opening
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ MonoD.pure _
  · exact ref_dOpenT _ r.1 cl h
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  exact (RefAt.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) (b := r.2) (a := true) rfl).toP _

end Ref
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.KeccakGkr (eqAt)

/-- **O5b at M′** (`OpenSM.refines`' form): whenever `VST P20 N` accepts a proof on a log, so does the compiled
verifier of `PSWithM (midM (relocV relocS) (midT₂ (N.inst Q lay)))`. -/
theorem refines_VSTM (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (hacc : ∀ x, (pubX x).accIn.pt.length = phiVars) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VST P20 N vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWithM (Lvm.ASM.midM (relocV relocS) (midT₂ (N.inst Q lay))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.fits
  intro vk L c π _ h
  exact runLog_of_seq (fun tr ht ↦ refines_seqOfT N _
    (fun sig vk c x hpub ↦ ref_decideTM N Q lay H hσ vk c x (hacc x) hpub)
    (fol_PSTM (relocV relocS) (N.inst Q lay) hl busDepth_P20 hr he) vk c π tr ht) L h

open Lvm.CT Lvm.QTyped Lvm.T Lvm.ASM in
/-- **`LvmCertM20.refinesM20`** (its statement, with `reloc20 = relocV relocS`): `VST P20 NT20` refines the compiled
verifier of `PSWithM (midM (relocV relocS) (midT₂ Ti20))`, from the guard's facts (`σ′` in `S`: `S.sig`, the
guard's `sigInSB`) and `THyp Ti20`. -/
theorem refinesM20L (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWithM (midM (relocV relocS) (midT₂ Ti20)))).V c π).runLog L = some true :=
  refines_VSTM NT20 QB20 layT20 (trefHyp20 S H) S.sig H.acc

end Lvm.VEq
end

-- ===== from `LvmE2VFol` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V
section Items
variable (p : Params)

/-- The coordinate-split zerocheck: `τ` (20), `ω`, 20 equality-mode rounds of 2, the six values at `r_x`. -/
def zeroIX : List Item := List.flatten [smp 20, smp 1, sumcheckI 20 2, rd 6]
/-- The coordinate-split wiring: `γ`, 21 rounds of 2, the 8 matrix and 4 region values. -/
def wiringIX : List Item := List.flatten [smp 1, sumcheckI 21 2, rd 8, rd 4]
/-- A23: `κ` (3), `h` (`accV + 1`), `t`, the zero scalar. -/
def accIX : List Item := List.flatten [smp 3, rd (p.accV + 1), smp 1, rd 1]
/-- **The typed phases' items at S2GF** (the schedule's `bus` and `tables` phases). -/
def typedIX : List Item := zeroIX ++ (wiringIX ++ (relayI ++ (accIX p ++ (miniBusI p ++ miniTabI p))))
/-- **The pinned middle phases' items**: the pin, the typed phases, the tape, the wire, `KS`, the `KS` link. -/
def midItemsF : List Item := pinI p ++ (typedIX p ++ (tapeIF p ++ (wireIF p ++ (ksIF p ++ ksLinkIF p))))

/-- **S2GF's schedule by phase.** -/
theorem phasesF_eq (h : p.stage = 1) : phases p = [(.commit, commitI p ++ pinI p),
    (.bus, zeroIX ++ (wiringIX ++ (relayI ++ (accIX p ++ miniBusI p)))), (.tables, miniTabI p), (.tape, tapeIF p),
    (.wire, wireIF p), (.ks, ksIF p), (.ksLink, ksLinkIF p), (.openMain, openMainI p)] := by
  rw [phases, h]
  rfl

/-- S2GF's schedule: the root, the pinned middle phases, `C_main`'s opening. -/
theorem scheduleF_eq (h : p.stage = 1) : schedule p = commitI p ++ (midItemsF p ++ (openMainI p ++ [])) := by
  rw [schedule, phasesF_eq p h]
  simp only [midItemsF, typedIX, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]

end Items
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V
section Typed
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- The coordinate-split zerocheck against `zeroIX`. -/
theorem folP_zeroProgX : FolP cap shp idx Typed.zeroProgX (atomsOf p zeroIX) fun _ ↦ True := by
  simp only [zeroIX, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.zeroProgX
  exact (folP_sampleChallenges Typed.xVars).bind fun τ hτ ↦ folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) (τ.map some) Typed.xVars 0 (by rw [List.length_map, hτ])).bind fun _ _ ↦
    (folP_readScalars 6).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The coordinate-split wiring against `wiringIX`. -/
theorem folP_wireProgX (Ti : Typed.TInst) (pub : Pub) (v : List E) :
    FolP cap shp idx (Typed.wireProgX Ti pub v) (atomsOf p wiringIX) fun _ ↦ True := by
  simp only [wiringIX, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.wireProgX
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ Typed.yVars _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 8).bind fun _ _ ↦ (folP_readScalars 4).bind_nil fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

/-- A23 at `Φ_Q` in `phiVarsX = 44` variables against `accIX` (`accV = 44`). -/
theorem folP_accProgQX (hacc : p.accV = Typed.phiVarsX) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (ok : Bool)
    (yIn : E) (a rxy vs : List E) :
    FolP cap shp idx (Typed.accProgQX Q lay ok yIn a rxy vs) (atomsOf p (accIX p)) fun _ ↦ True := by
  rw [accIX, hacc]
  unfold Typed.accProgQX
  exact folP_accProg p 3 Typed.phiVarsX ok yIn a _ _ _

/-- **The coordinate-split typed phases** against `typedIX p` (`accV = 44`; the record's mini-bus numbers those
of `Ti.mbT`, as `folP_typedProg`). -/
theorem folP_typedProgX (Ti : Typed.TInst) (pub : Pub) (hacc : p.accV = Typed.phiVarsX)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth)
    (hr : p.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : p.tableEvals = (Ti.mbT.map (·.w)).sum) :
    FolP cap shp idx (Typed.typedProgX Ti pub) (atomsOf p (typedIX p)) fun _ ↦ True := by
  simp only [typedIX, atomsOf_append]
  rw [← atomsOf_append p (miniBusI p)]
  unfold Typed.typedProgX
  exact (folP_zeroProgX p).bind fun _ _ ↦ (folP_wireProgX p Ti pub _).bind fun _ _ ↦
    (folP_relayProg p Ti _ _).bind fun _ _ ↦ (folP_accProgQX p hacc _ _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusProg p Ti hl hd hr he).bind_ret fun _ _ ↦ trivial

end Typed
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V
section Mid
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **S2GF's middle phases** (`midF₂ Ti`) against the typed and the front items at `P20F.withF accVF`. -/
theorem folP_midF₂ (Ti : Typed.TInst) (hl : (P20F.withF accVF).leafdecReads = 1)
    (hd : (P20F.withF accVF).busDepth = Typed.miniDepth)
    (hr : (P20F.withF accVF).tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : (P20F.withF accVF).tableEvals = (Ti.mbT.map (·.w)).sum) (x : List UInt8) :
    FolP cap shp idx (midF₂ Ti x) (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF) ++
      (tapeIF (P20F.withF accVF) ++ (wireIF (P20F.withF accVF) ++ (ksIF (P20F.withF accVF) ++
        ksLinkIF (P20F.withF accVF)))))) fun _ ↦ True := by
  rw [atomsOf_append]
  unfold midF₂ midFWith midFWithR
  exact (folP_typedProgX _ Ti _ rfl hl hd hr he).bind fun _ _ ↦
    (folP_kgProgFR _ rfl rfl _ _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinI : atomsOf (P20F.withF accVF) (pinI (P20F.withF accVF)) =
    List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **The pinned middle phases follow `midItemsF`** at `P20F.withF accVF`, for every relocation. -/
theorem folP_midPF (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : (P20F.withF accVF).leafdecReads = 1) (hd : (P20F.withF accVF).busDepth = Typed.miniDepth)
    (hr : (P20F.withF accVF).tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : (P20F.withF accVF).tableEvals = (Ti.mbT.map (·.w)).sum) (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midM reloc (midF₂ Ti)) x)
      (atomsOf (P20F.withF accVF) (midItemsF (P20F.withF accVF))) fun _ ↦ True := by
  rw [midItemsF, atomsOf_append, atomsOf_pinI]
  exact folP_midP _ x _ (folP_midM reloc _ x _ (folP_midF₂ Ti hl hd hr he x))

end Mid
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

theorem level_F : (P20F.withF accVF).level = P20.level := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

theorem commitI_F : commitI (P20F.withF accVF) = commitI P20 := by
  unfold commitI
  rw [level_F]

theorem atomsOf_scheduleF : atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF)) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf (P20F.withF accVF) (midItemsF (P20F.withF accVF)) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleF_eq _ rfl, atomsOf_append, atomsOf_append, atomsOf_append, openMainI_F, atomsOf_F (openMainI P20),
    commitI_F, atomsOf_F (commitI P20), atomsOf_commitI, atomsOf_nil]

/-- **S2GF's `P_S` follows the schedule** at `P20F.withF accVF`: the root, the pin, the coordinate-split typed
phases, the `E2` front, `C_main`'s opening (`P20`'s levels), from no pending positions. -/
theorem fol_PSOfF (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : (P20F.withF accVF).leafdecReads = 1) (hd : (P20F.withF accVF).busDepth = Typed.miniDepth)
    (hr : (P20F.withF accVF).tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : (P20F.withF accVF).tableEvals = (Ti.mbT.map (·.w)).sum) (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midM reloc (midF₂ Ti))) x)
      (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleF]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midM reloc (midF₂ Ti)) x) _
    (atomsOf (P20F.withF accVF) (midItemsF (P20F.withF accVF))) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPF reloc Ti hl hd hr he x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

/-- S2GF's record with `P20`'s levels as literals (`LvmReplay.P20_eq`). -/
theorem PF_eq : P20F.withF accVF = { Lvm.Replay.P20L with name := "P20F", stage := 1, accV := accVF } := by
  unfold Params.withF P20F
  rw [Lvm.Replay.P20_eq]

set_option maxRecDepth 200000 in
/-- **The static check at S2GF** (one kernel evaluation over the items, `stA_atomsOf`). -/
theorem stA_P20F :
    stA (P20F.withF accVF) (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) 0 [] [] = true := by
  rw [stA_atomsOf, PF_eq]
  decide +kernel

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

theorem readWidthsF_eq :
    readWidthsF P20F accVF = widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) := by
  rw [widthsA_atomsOf]
  unfold readWidthsF
  congr 1

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

/-- **`rwF20` is the S2GF schedule's read widths** from read `0`. -/
theorem wAt_rwF20 : WAt rwF20 0 (widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF)))) := by
  rw [← readWidthsF_eq]
  exact wAt_getD _ _

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

theorem noWB_typedIX (p : Params) : noWB (typedIX p) = true := by
  simp only [typedIX, zeroIX, wiringIX, relayI, accIX, miniBusI, miniTabI, gpI, List.flatten_cons,
    List.flatten_nil, List.append_nil, noWB_append, noWB_smp, noWB_rd, noWB_sumcheckI, noWB_gpLayersI,
    Bool.and_self]

/-- The pin reads one 24-byte scalar. -/
theorem mem_widthsA_pinF : ∀ x ∈ widthsA (atomsOf (P20F.withF accVF) (pinI (P20F.withF accVF))), x = 24 :=
  mem_widthsA_atomsOf _ _ (by rw [pinI, noWB_append, noWB_smp, noWB_rd]; rfl)

/-- The coordinate-split typed phases read 24-byte scalars only. -/
theorem mem_widthsA_typedF :
    ∀ x ∈ widthsA (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF))), x = 24 :=
  mem_widthsA_atomsOf _ _ (noWB_typedIX _)

end Lvm.VEq
end

-- ===== from `LvmE2VWidthsF` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol.Compile

/-- **The `E2` front's read widths at S2GF** are E2F-V's per-phase width lists. -/
theorem widthsA_frontF :
    widthsA (atomsOf (P20F.withF accVF) (tapeIF (P20F.withF accVF) ++ (wireIF (P20F.withF accVF) ++
      (ksIF (P20F.withF accVF) ++ ksLinkIF (P20F.withF accVF))))) = wTape 20 ++ wCaller 13 ++ wKsLink 13 :=
  widthsA_frontG _ rfl rfl

/-- **The S2GF schedule's read widths** in V_S's decision order: the pin's read, the typed phases', the front's,
the opening's. -/
theorem widthsA_scheduleF :
    widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) =
      [24] ++ widthsA (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF))) ++
        (wTape 20 ++ wCaller 13 ++ wKsLink 13) ++ widthsA (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  rw [atomsOf_scheduleF, midItemsF, atomsOf_append (P20F.withF accVF) (pinI _),
    atomsOf_append (P20F.withF accVF) (typedIX _), atomsOf_pinI]
  simp only [widthsA_append, widthsA_frontF, hp, List.append_nil, List.nil_append, List.append_assoc]
  rfl

end Lvm.VEq
end
