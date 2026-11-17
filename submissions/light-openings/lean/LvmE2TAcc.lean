-- New for lvm2 E2-FT (stage S2GT, E2F-T; helper T-H2): A23's specification at `E2` with grinding, the twin of roll
-- 11's `Lvm.Typed.accSpecQ` (`LvmTypedAcc`) on `LvmAccSpec`'s `accBadSpec`/`accSpecG`, with E2F-V's ground rules
-- (`zeroSpecE2`, `doomE2SampleSpec`, `e2ReadsSpec`, `e2ReadSpec`, `sampleG_escape`).
import LvmE2TProg
import LvmE2VZero
import LvmAccSpec

/-!
# A23 at `E2` (`accProgT`)

`accProgT` samples `κ ∈ E2^4` (`e2Samples gKappa 4`, one nonce each), reads the 46 coefficients of the line
polynomial `h`, samples `t` (`e2Sample gT`), reads the zero scalar and checks `ok`, `h(0) = y_in`,
`h(1) = y_own(κ)`, `z = 0` and `Φ_Q(line(a, κ ++ r_xy, t)) = h(t)`.

* `Φ_Q` at `E2` as a sparse sum (`phiQT_eq_sum`): `Σ_{e ∈ entsT} e.c·eq(pt, e.idx)`; matrix `o'`'s extension
  likewise (`matMleT_eq_sum`); every entry has `o' < 12` (`entsT_o`), so no layout hypothesis is needed;
* **`phiQT_fold`**: the selector split `y_own(κ) − Φ_Q(κ ++ r_xy) = Σ_{w<16} eq(κ, w)·δ_w`;
* **`lineDegT`**: `Φ_Q` on a line is a polynomial of degree `≤ 45`;
* **`accBadSpecT`**: outside `AccGoodT` the phase never returns in doom: `κ` by the zero test at `E2`
  (`errG gKappa 1` each, lead `0`), `t` by a wrong line polynomial (`errG gT 45`), the reads keep doom;
* **`accSpecQT`**: from `¬AccGoodT ∨ M` to `M` (`Spec.orStable`), lead `T`;
* **`accProgT_complete`** (non-vacuity): under `AccGoodT` the honest coefficients pass for every `κ`, `t`.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V Lvm.Acc LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Polynomial Finset
open scoped ENNReal

/-! ## The line and the line polynomial at `E2` -/

theorem lineT_zero : ∀ (a b : List E2), a.length = b.length → lineT a b 0 = a
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | x :: a, v :: b, h => by
    have ih := lineT_zero a b (by simpa using h)
    simp only [lineT, List.zipWith_cons_cons, zero_mul, add_zero] at ih ⊢
    rw [ih]

theorem lineT_one : ∀ (a b : List E2), a.length = b.length → lineT a b 1 = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, v :: b, h => by
    have ih := lineT_one a b (by simpa using h)
    simp only [lineT, List.zipWith_cons_cons, one_mul] at ih ⊢
    rw [ih, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem hEvalT_cons (c : E2) (hs : List E2) (t : E2) : hEvalT (c :: hs) t = c + t * hEvalT hs t := rfl

/-- Horner over a run of indices is the power sum. -/
theorem hEvalT_range' (f : ℕ → E2) (t : E2) : ∀ (m k : ℕ),
    hEvalT ((List.range' k m).map f) t * t ^ k = ∑ i ∈ Finset.Ico k (k + m), f i * t ^ i
  | 0, k => by simp [hEvalT]
  | m + 1, k => by
    rw [List.range'_succ, List.map_cons, hEvalT_cons,
      Finset.sum_eq_sum_Ico_succ_bot (by (clear * - k m; omega) : k < k + (m + 1)),
      show k + (m + 1) = k + 1 + m by (clear * - k m; omega), ← hEvalT_range' f t m (k + 1), pow_succ]
    ring

/-- The polynomial of a coefficient list. -/
noncomputable def hPolyT (hs : List E2) : E2[X] := hs.foldr (fun c acc ↦ C c + X * acc) 0

theorem eval_hPolyT (hs : List E2) (t : E2) : (hPolyT hs).eval t = hEvalT hs t := by
  induction hs with
  | nil => simp [hPolyT, hEvalT]
  | cons c hs ih =>
    simp only [hPolyT, List.foldr_cons, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X] at ih ⊢
    rw [ih]; rfl

theorem natDegree_hPolyT : ∀ (hs : List E2) (n : ℕ), hs.length ≤ n + 1 → (hPolyT hs).natDegree ≤ n
  | [], _, _ => by simp [hPolyT]
  | c :: hs, n, h => by
    simp only [hPolyT, List.foldr_cons]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    rcases hs with _ | ⟨c', hs'⟩
    · simp
    · have hn : 1 ≤ n := by simp at h; (clear * - n hs' h; omega)
      refine (natDegree_mul_le).trans ?_
      have := natDegree_hPolyT (c' :: hs') (n - 1) (by simp at h ⊢; (clear * - hs' n hn h; omega))
      have hX : (X : E2[X]).natDegree ≤ 1 := natDegree_X_le
      simp only [hPolyT] at this
      (clear * - c' hs' n c hn this hX; omega)

/-- `eq(line(t), w)` as a polynomial in `t`. -/
noncomputable def eqPolyT : List E2 → List E2 → ℕ → E2[X]
  | x :: a, v :: b, w =>
    (if w % 2 = 1 then C x + X * C (x + v) else 1 + (C x + X * C (x + v))) * eqPolyT a b (w / 2)
  | _, _, _ => 1

theorem eval_eqPolyT : ∀ (a b : List E2) (w : ℕ) (t : E2),
    (eqPolyT a b w).eval t = E2V.eqAtF (lineT a b t) w
  | [], _, _, _ => by simp [eqPolyT, lineT]
  | _ :: _, [], _, _ => by simp [eqPolyT, lineT]
  | x :: a, v :: b, w, t => by
    simp only [eqPolyT, lineT, List.zipWith_cons_cons, eval_mul, E2V.eqAtF_succ]
    rw [← lineT, ← eval_eqPolyT a b (w / 2) t]
    split_ifs <;> simp

theorem natDegree_eqPolyT : ∀ (a b : List E2) (w : ℕ), (eqPolyT a b w).natDegree ≤ a.length
  | [], _, _ => by simp [eqPolyT]
  | _ :: _, [], _ => by simp [eqPolyT]
  | x :: a, v :: b, w => by
    simp only [eqPolyT, List.length_cons]
    have ha := natDegree_eqPolyT a b (w / 2)
    have hl : (C x + X * C (x + v) : E2[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_mul_le).trans (by
        have := natDegree_X_le (R := E2); simp only [natDegree_C]; (clear * - this; omega))))
    split_ifs
    · exact (natDegree_mul_le).trans (by (clear * - x v a b w ha hl; omega))
    · refine (natDegree_mul_le).trans ?_
      have : (1 + (C x + X * C (x + v)) : E2[X]).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) hl)
      (clear * - x v a b w ha this; omega)

/-- **The line-degree lemma at `E2`**: on the line from `a` to `b`, a sparse sum `Σ_{(n, c)} c·eq(·, n)` is a
polynomial of degree at most `|a|` in `t`. -/
theorem lineDeg_sparseT (es : List (ℕ × E2)) (a b : List E2) :
    ∃ g : E2[X], g.natDegree ≤ a.length ∧
      ∀ t, g.eval t = (es.map fun p ↦ p.2 * E2V.eqAtF (lineT a b t) p.1).sum := by
  induction es with
  | nil => exact ⟨0, by simp, fun t ↦ by simp⟩
  | cons p es ih =>
    obtain ⟨g, hg, hgv⟩ := ih
    refine ⟨C p.2 * eqPolyT a b p.1 + g, ?_, fun t ↦ ?_⟩
    · exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_C_mul_le _ _).trans (natDegree_eqPolyT a b p.1)) hg)
    · rw [eval_add, eval_mul, eval_C, eval_eqPolyT, hgv, List.map_cons, List.sum_cons]

/-! ## `Φ_Q` and the matrices at `E2` as sums -/

theorem toE2_ofE2T (y : E2) : FE2.toE2 (ofE2 y) = y := rfl

/-- The native equality weight read over `E2`. -/
theorem toE2_eqWT : ∀ (l : List E2) (w : ℕ), FE2.toE2 (eqWT (l.map ofE2) w) = E2V.eqAtF l w
  | [], _ => by simp [eqWT, E2V.eqAtF]
  | r :: l, w => by
    simp only [List.map_cons, eqWT, E2V.eqAtF_succ, FE2.fe2_mul_eq, toE2_eqWT l]
    split_ifs
    · rw [toE2_ofE2T]
    · rw [FE2.toE2_add, FE2.toE2_one, toE2_ofE2T]

/-- A fold of a sum, read over `E2`, is the sum of the read terms. -/
theorem toE2_foldr {α : Type} (l : List α) (g : α → FE2) :
    FE2.toE2 (l.foldr (fun e acc ↦ g e + acc) 0) = (l.map fun e ↦ FE2.toE2 (g e)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => rw [List.foldr_cons, FE2.toE2_add, ih, List.map_cons, List.sum_cons]

/-- **`Φ_Q` at `E2` is the sparse multilinear sum** of the sixteen matrices' entries. -/
theorem phiQT_eq_sum (Q : Program) (lay : Lay) (pt : List E2) :
    PhiQT Q lay pt = ((entsT Q lay).map fun e ↦ FE2.toE2 e.c * E2V.eqAtF pt e.idx).sum := by
  unfold PhiQT PhiQFT
  rw [toE2_foldr]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE2.fe2_mul_eq, toE2_eqWT])

/-- **Matrix `o'`'s extension at `E2`** is the sum over its entries (`rxy = r_x ++ r_y`). -/
theorem matMleT_eq_sum (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E2) :
    matMleT Q lay o rxy = (((entsT Q lay).filter fun e ↦ e.o == o).map fun e ↦
      FE2.toE2 e.c * E2V.eqAtF rxy (e.x + 2 ^ xVars * e.y)).sum := by
  unfold matMleT matMleFT
  rw [toE2_foldr]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE2.fe2_mul_eq, toE2_eqWT])

/-- Every entry at `E2` sits in one of the twelve used slots `m + 4j` (`m < 4`, `j < 3`). -/
theorem entsT_o (Q : Program) (lay : Lay) : ∀ e ∈ entsT Q lay, e.o < 12 := by
  intro e he
  unfold entsT at he
  obtain ⟨e₀, -, he₀⟩ := List.mem_flatMap.mp he
  unfold splitEnt at he₀
  obtain ⟨j, hj, hje⟩ := List.mem_filterMap.mp he₀
  have hj3 : j < 3 := List.mem_range.mp hj
  split at hje
  · exact absurd hje (by simp)
  · rw [Option.some.injEq] at hje
    rw [← hje]
    dsimp only
    (clear * - e₀ j hj3; omega)

/-- A selector-weighted sum of the per-matrix sums is the weighted sum over all entries (every `o' < 16`). -/
theorem sum_sel_filterT (g : ℕ → E2) (f : EntT → E2) :
    ∀ l : List EntT, (∀ e ∈ l, e.o < 16) →
      ∑ w ∈ range (2 ^ selBitsT), g w * ((l.filter fun e ↦ e.o == w).map f).sum =
        (l.map fun e ↦ g e.o * f e).sum
  | [], _ => by simp
  | e :: l, hl => by
    have ih := sum_sel_filterT g f l fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have he : e.o < 2 ^ selBitsT := hl e (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih]
    rw [Finset.sum_congr rfl fun w _ ↦ show g w * ((((e :: l).filter fun e ↦ e.o == w)).map f).sum =
        (if e.o = w then g e.o * f e else 0) + g w * ((l.filter fun e ↦ e.o == w).map f).sum by
      by_cases h : e.o = w
      · subst h; simp [mul_add]
      · simp [h]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr he)]

/-! ## The instance -/

/-- **The matrices' errors at `E2`** (`o' < 16`; slots 12–15 carry no entries). -/
def deltaT (Q : Program) (lay : Lay) (vs rxy : List E2) (o : ℕ) : E2 := vs.getD o 0 - matMleT Q lay o rxy

/-- **Nothing to fold away at `E2`**: the pass check holds, the incoming claim is true (`Φ_Q(a) = y_in`) and every
matrix value is (`δ = 0`). -/
def AccGoodT (ok : Bool) (yIn : E2) (a : List E2) (Q : Program) (lay : Lay) (vs rxy : List E2) : Prop :=
  ok = true ∧ PhiQT Q lay a = yIn ∧ ∀ w < 2 ^ selBitsT, deltaT Q lay vs rxy w = 0

/-- `zipWith` reads only as many entries of the left list as the right one has. -/
theorem zipWith_take_left {α : Type} (f : α → α → α) : ∀ (a b : List α),
    List.zipWith f a b = List.zipWith f (a.take b.length) b
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: a, u :: b => by
    rw [List.length_cons, List.take_succ_cons, List.zipWith_cons_cons, List.zipWith_cons_cons,
      zipWith_take_left f a b]

/-- `y_own(κ)` as the selector-weighted sum of the twelve values. -/
theorem yOwnT_eq (vs κ : List E2) (hvs : vs.length = 12) (hκ : κ.length = selBitsT) :
    yOwnT vs κ = ∑ w ∈ range (2 ^ selBitsT), E2V.eqAtF κ w * vs.getD w 0 := by
  have hn : vs.length ≤ 2 ^ κ.length := by rw [hvs, hκ]; norm_num
  unfold yOwnT
  rw [show dotF (eqKernelF κ) vs = dotF ((eqKernelF κ).take vs.length) vs by
      unfold dotF; rw [zipWith_take_left], dot_eqKernelF κ vs hn, hvs,
    show 2 ^ selBitsT = 12 + 4 from rfl, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := range 4) fun i _ ↦ by
    rw [List.getD_eq_default _ _ (by (clear * - vs i κ hvs; omega)), mul_zero], add_zero]

/-- **The selector split at `E2`**: at `κ ++ r_xy`, `y_own − Φ_Q` is the selector extension of the matrices'
errors. -/
theorem phiQT_fold (Q : Program) (lay : Lay) (rxy vs : List E2) (hvs : vs.length = 12) (κ : List E2)
    (hκ : κ.length = selBitsT) :
    yOwnT vs κ - PhiQT Q lay (κ ++ rxy) =
      ∑ w ∈ range (2 ^ selBitsT), E2V.eqAtF κ w * deltaT Q lay vs rxy w := by
  have hphi : PhiQT Q lay (κ ++ rxy) =
      ∑ w ∈ range (2 ^ selBitsT), E2V.eqAtF κ w * matMleT Q lay w rxy := by
    simp only [matMleT_eq_sum]
    rw [sum_sel_filterT (E2V.eqAtF κ) _ _ fun e he ↦ by have := entsT_o Q lay e he; (clear * - e vs κ this; omega),
      phiQT_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    have ho := entsT_o Q lay e he
    rw [E2V.eqAtF_append, hκ, E2V.eqAtF_mod κ, hκ, EntT.idx,
      show (e.o + 16 * (e.x + 2 ^ xVars * e.y)) % 2 ^ selBitsT = e.o by
        rw [show (2 : ℕ) ^ selBitsT = 16 from rfl]; (clear * - e vs κ ho; omega),
      show (e.o + 16 * (e.x + 2 ^ xVars * e.y)) / 2 ^ selBitsT = e.x + 2 ^ xVars * e.y by
        rw [show (2 : ℕ) ^ selBitsT = 16 from rfl]; (clear * - e vs κ ho; omega)]
    ring
  rw [yOwnT_eq vs κ hvs hκ, hphi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [deltaT, mul_sub]

/-- **The line-degree bound at `Φ_Q`**: on the line from `a` to `κ ++ r_xy`, `Φ_Q` at `E2` is a polynomial of
degree at most `45`. -/
theorem lineDegT (Q : Program) (lay : Lay) (a b : List E2) (ha : a.length = phiVarsT) :
    ∃ g : E2[X], g.natDegree ≤ phiVarsT ∧ ∀ t, g.eval t = PhiQT Q lay (lineT a b t) := by
  obtain ⟨g, hg, hgv⟩ := lineDeg_sparseT ((entsT Q lay).map fun e ↦ (e.idx, FE2.toE2 e.c)) a b
  refine ⟨g, ha ▸ hg, fun t ↦ ?_⟩
  rw [hgv, phiQT_eq_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ rfl)

theorem length_bOfT (κ rxy : List E2) (a : List E2) (ha : a.length = phiVarsT)
    (hr : rxy.length = xVars + yVars) (hκ : κ.length = selBitsT) : a.length = (κ ++ rxy).length := by
  rw [List.length_append, ha, hr, hκ]
  rfl

/-! ## Outside `AccGoodT`: the phase never returns in doom -/

section Bad

variable {Q : Program} {lay : Lay} {ok : Bool} {yIn : E2} {a rxy vs : List E2} {εmax T : ℝ≥0∞}

/-- The pass checks at `t` but the zero scalar's. -/
def PassT (Q : Program) (lay : Lay) (ok : Bool) (yIn : E2) (a rxy vs κ hs : List E2) (t : E2) : Prop :=
  ok = true ∧ hEvalT hs 0 = yIn ∧ hEvalT hs 1 = yOwnT vs κ ∧ hEvalT hs t = PhiQT Q lay (lineT a (κ ++ rxy) t)

/-- The zero test's alive predicate after `κ` (its length carried inside). -/
def AliveKT (Q : Program) (lay : Lay) (ok : Bool) (yIn : E2) (a rxy vs κ : List E2) (_ : Unit) : Prop :=
  κ.length = selBitsT →
    ZeroOnF (deltaT Q lay vs rxy) κ selBitsT ∧ (ok = true ∧ PhiQT Q lay a = yIn)

/-- `AliveKT` after `h` (its length carried inside). -/
def AliveHT (Q : Program) (lay : Lay) (ok : Bool) (yIn : E2) (a rxy vs κ hs : List E2) (q : Unit) : Prop :=
  hs.length = phiVarsT + 1 → AliveKT Q lay ok yIn a rxy vs κ q

/-- **The escape at `t`**: a wrong line polynomial agrees with `Φ_Q ∘ line` at an accepted challenge with
probability `≤ errG gT 45`. -/
theorem escape_tT (ha : a.length = phiVarsT) (hr : rxy.length = xVars + yVars) (hvs : vs.length = 12)
    (κ hs : List E2) (q : Unit) (hq : ¬ AliveHT Q lay ok yIn a rxy vs κ hs q) :
    avgE (fun c ↦ indE (powOK gT c ∧ PassT Q lay ok yIn a rxy vs κ hs (e2OfE c))) ≤ errG gT phiVarsT := by
  unfold AliveHT AliveKT at hq
  have hhs : hs.length = phiVarsT + 1 := not_imp.mp hq |>.1
  have hκ : κ.length = selBitsT := not_imp.mp (not_imp.mp hq).2 |>.1
  have hd := not_imp.mp (not_imp.mp hq).2 |>.2
  by_cases hp : ok = true ∧ hEvalT hs 0 = yIn ∧ hEvalT hs 1 = yOwnT vs κ
  · obtain ⟨g, hg, hgv⟩ := lineDegT Q lay a (κ ++ rxy) ha
    have hlen := length_bOfT κ rxy a ha hr hκ
    have hne : hPolyT hs ≠ g := by
      intro he
      have e0 := hgv 0
      have e1 := hgv 1
      rw [← he, eval_hPolyT, lineT_zero _ _ hlen] at e0
      rw [← he, eval_hPolyT, lineT_one _ _ hlen] at e1
      refine hd ⟨(zeroOnF_full _ hκ).mpr ?_, hp.1, by rw [← e0, hp.2.1]⟩
      rw [← phiQT_fold Q lay rxy vs hvs κ hκ, ← e1, hp.2.2, sub_self]
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
      (sampleG_escape (by norm_num) hne (natDegree_hPolyT hs phiVarsT hhs.le) hg)
    rw [eval_hPolyT, hgv]
    exact hc.2.2.2.2
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ ?_).trans
      ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
    exact hp ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

/-- **Outside `AccGoodT` the phase never returns in doom**: each `κ_j` escapes with `errG gKappa 1` (E2F-V's zero
test at `E2`, lead `0`: every sample follows its nonce), `t` with `errG gT 45` (a wrong line polynomial), the reads
keep doom, and the checks reject. -/
noncomputable def accBadSpecT (ha : a.length = phiVarsT) (hr : rxy.length = xVars + yVars)
    (hvs : vs.length = 12) (hκ : errG gKappa 1 ≤ εmax) (ht : errG gT phiVarsT ≤ εmax) (hT : T ≤ εmax) :
    Spec (accProgT Q lay ok yIn a rxy vs) (fun _ ↦ ¬ AccGoodT ok yIn a Q lay vs rxy) (fun _ _ ↦ False)
      εmax 0 T :=
  ((zeroSpecE2 (C := unitC) (L₀ := 1) (T := 0) (εmax := εmax) stable_unitC ncard_unitC (g := gKappa)
      (by norm_num) (fun _ ↦ deltaT Q lay vs rxy) (fun _ ↦ ok = true ∧ PhiQT Q lay a = yIn)
      (n := selBitsT) (m := 3) le_rfl (by rw [Nat.cast_one, one_mul, add_zero]; exact hκ)).bind' fun κ ↦
    ((e2ReadsSpec (T := 0) (εmax := εmax) stable_unitC (AliveKT Q lay ok yIn a rxy vs κ) zero_le
        phiVarsT).mono
      (fun _ ⟨hl, hd⟩ ↦ Doomed.mono hd fun _ hk ↦ hk hl) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun hs ↦
      ((doomE2SampleSpec (T := 0) (εmax := εmax) stable_unitC ncard_unitC (g := gT)
          (AliveHT Q lay ok yIn a rxy vs κ hs) (fun t _ ↦ PassT Q lay ok yIn a rxy vs κ hs t)
          (errG gT phiVarsT) (escape_tT ha hr hvs κ hs)
          (by rw [Nat.cast_one, one_mul, add_zero]; exact ht)).mono
        (fun _ ⟨hl, hd⟩ ↦ Doomed.mono hd fun _ hk ↦ hk hl) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
        fun t ↦
        (e2ReadSpec (T := T) (εmax := εmax) stable_unitC (fun _ ↦ PassT Q lay ok yIn a rxy vs κ hs t)
            hT).bind' fun z ↦
          Spec.require (Pre := Doomed unitC fun _ ↦ PassT Q lay ok yIn a rxy vs κ hs t)
            (Post := fun _ _ ↦ False)
            fun _ hd hc ↦ doomed_unitC.mp hd ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.2.symm⟩).mono
    (fun _ hg ↦ by
      rw [doomed_unitC]
      rintro ⟨hz, hok, hΦ⟩
      exact hg ⟨hok, hΦ, (zeroOnF_nil _ _).mp hz⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Bad

/-! ## The phase's specification -/

/-- **A23's specification at `E2`** (the twin of `accSpecQ`): from `¬AccGoodT ∨ M` to `M`, for a predicate `M` of
the history the phase keeps. Escape `errG gKappa 1` per `κ_j`, `errG gT 45` at `t`; lead `T` (the phase starts
with `κ₁`'s nonce, a prover move). `hlay` is not needed (every entry at `E2` has `o' < 12`). -/
noncomputable def accSpecQT (Q : Program) (lay : Lay) (_hlay : lay.Ok Q) {ok : Bool} {yIn : E2}
    (a rxy vs : List E2) (ha : a.length = phiVarsT) (hr : rxy.length = xVars + yVars) (hvs : vs.length = 12)
    (M : List Ev → Prop) (hM : ∀ h₀ l, (accProgT Q lay ok yIn a rxy vs).Reach h₀ l → M h₀ → M (h₀ ++ l))
    {εmax T : ℝ≥0∞} (hκ : errG gKappa 1 ≤ εmax) (ht : errG gT phiVarsT ≤ εmax) (hT : T ≤ εmax) :
    Spec (accProgT Q lay ok yIn a rxy vs) (fun h ↦ ¬ AccGoodT ok yIn a Q lay vs rxy ∨ M h)
      (fun _ h ↦ M h) εmax T T :=
  ((accBadSpecT ha hr hvs hκ ht hT).orStable hM hT).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
    (max_le zero_le le_rfl) le_rfl

/-- **Completeness (non-vacuity)**: under `AccGoodT`, the honest coefficients (those of `Φ_Q ∘ line`) pass every
check of the phase, for every `κ` and `t`, with the zero scalar `0`. -/
theorem accProgT_complete (Q : Program) (lay : Lay) {ok : Bool} {yIn : E2} (a rxy vs : List E2)
    (ha : a.length = phiVarsT) (hr : rxy.length = xVars + yVars) (hvs : vs.length = 12)
    (hg : AccGoodT ok yIn a Q lay vs rxy) (κ : List E2) (hκ : κ.length = selBitsT) :
    ∃ hs : List E2, hs.length = phiVarsT + 1 ∧ ∀ t : E2,
      ok = true ∧ hEvalT hs 0 = yIn ∧ hEvalT hs 1 = yOwnT vs κ ∧ (0 : E2) = 0 ∧
        PhiQT Q lay (lineT a (κ ++ rxy) t) = hEvalT hs t := by
  obtain ⟨g, hgd, hgv⟩ := lineDegT Q lay a (κ ++ rxy) ha
  have hlen := length_bOfT κ rxy a ha hr hκ
  have hev : ∀ t, hEvalT ((List.range (phiVarsT + 1)).map g.coeff) t = g.eval t := fun t ↦ by
    have key := hEvalT_range' g.coeff t (phiVarsT + 1) 0
    rw [pow_zero, mul_one, zero_add, ← List.range_eq_range', ← Finset.range_eq_Ico] at key
    rw [key, eval_eq_sum_range' (n := phiVarsT + 1) (by (clear * - g a rxy vs ha κ hgd hlen; omega))]
  refine ⟨(List.range (phiVarsT + 1)).map g.coeff, by simp, fun t ↦ ⟨hg.1, ?_, ?_, rfl, ?_⟩⟩
  · rw [hev, hgv, lineT_zero _ _ hlen, hg.2.1]
  · rw [hev, hgv, lineT_one _ _ hlen, ← sub_eq_zero, ← neg_sub, phiQT_fold Q lay rxy vs hvs κ hκ, neg_eq_zero]
    exact Finset.sum_eq_zero fun w hw ↦ by rw [hg.2.2 w (Finset.mem_range.mp hw), mul_zero]
  · rw [hev, hgv]

end Lvm.E2T
