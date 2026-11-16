-- New for lvm2 U-TAPE (UT-C2, STMT 25b): the values of blob U's front gadgets at `E2`: T1 (`tOneU` is V's
-- `t1ValsF`), the `ρ` truncations of QH2's threshold and `MS` gadgets at `|ρ| = 17`, the constant-bound `MS` automaton
-- (`msTailC`, `msConstU`) and the kernels `K̃_ch`, `K̃_ks`, `Ĩ_ks`, `e'` (`kernU`).
import LvmE2QWSem
import LvmE2QWU
import LvmE2QAsmU
import LvmE2UProg
import LvmS2GUFront
import LvmE2QOpenPhaseT

/-!
# Blob U's front values (`harithU20`'s 25b)

* **`hs_tOneU`**: T1's output cells are V's `t1ValsF 20 13 (r ‖ r₂₀) (a ‖ b)`.
* **`msEvalF_top`**, **`thrEvalF_top`**: at `|ρ| = 17` and `|σ| = 20`, V's kernels are `(1 + ρ₁₆)` times the kernels on
  `ρ_{<16}` (the top row bit is `0`); `g2Ms_take`, `g2Thr_take`: the gadgets read `ρ_{<16}` only.
* **`hs_msTailC`**, **`hs_msConstU`**: the constant-bound automaton is V's `msTailF`; `msConstU` is V's `msEvalF`
  without its top factor.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.E2V

variable {c : Ctx} {M : Mem}

/-- `mapB`'s outputs, by index, and their number (`Lvm.E2Q.hs_mapB_getD`'s twin). -/
theorem hs_mapB_getDU {α β : Type} [Inhabited β] (f : α → BM β) (P : α → β → Prop) (hf : ∀ a, Hs c M (f a) (P a)) :
    ∀ l : List α, Hs c M (mapB f l) (fun rs => rs.length = l.length ∧ ∀ i (h : i < l.length), P l[i] (rs.getD i default))
  | [] => hs_pure ⟨rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | a :: l => hs_bind (hf a) fun r hr => hs_bind (hs_mapB_getDU f P hf l) fun rs hrs => hs_pure ⟨by
      simp [hrs.1], fun i h => by
      cases i with
      | zero => exact hr
      | succ i => exact hrs.2 i (by simp at h; omega)⟩

/-! ## `eq` at `0` and `e` -/

theorem eqAtF_zero2 : ∀ xs : List FE2, E2V.eqAtF xs 0 = (xs.map (1 + ·)).prod
  | [] => rfl
  | x :: xs => by
    show (if 0 % 2 = 1 then x else 1 + x) * E2V.eqAtF xs (0 / 2) = _
    rw [List.map_cons, List.prod_cons, ← eqAtF_zero2 xs]; simp

theorem eTailF_eq_prod (r : List FE2) (hr : r.length = 20) (rw : FE2) :
    Lvm.E2U.eTailF 13 20 (r ++ [rw]) = (((r.drop 13).take 7).map (1 + ·)).prod := by
  unfold Lvm.E2U.eTailF
  rw [prodF_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.take_of_length_le (by simp; omega)]
  exact congrArg List.prod (List.map_congr_left fun x _ => by rw [CharTwo.sub_eq_add])

/-- `z*_l` of the circuit (`zStarE2`) is V's `Lvm.E2V.kF (Lvm.E2U.zStarK l)`. -/
theorem zStarE2_kF (l : ℕ) : FE2.ofK (Lvm.zStarE2 l).re = Lvm.E2V.kF (Lvm.E2U.zStarK l) := by
  have h : (Lvm.zStarE2 l).re = FK.ofBF64 (Lvm.Shape.zStar l) := congrArg FE.c₀ (Lvm.Shape.zStarF_eq l)
  rw [h]
  -- `kF = FE2.ofK ∘ ofBF64` (`instAlgebraKFE2`); `Shape.zStar` and `zStarK` are the same lane of `Keccak-f(0)`
  rfl

/-! ## T1 -/

theorem getD_map_range0 (f : ℕ → FE2) {n l : ℕ} (hl : l < n) : ((List.range n).map f).getD l 0 = f l := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range]

/-- **T1's output cells** (`tOneU`) are V's `t1ValsF 20 13 (r ‖ r₂₀) (a ‖ b)`. -/
theorem hs_tOneU (F : FCtx) (hz : F.z2.val M = 0) (ho : F.o2.val M = 1) (r : List C2) (hr : r.length = 20)
    (r20 : C2) (a b : List C2) :
    Hs c M (Lvm.E2Q.tOneU F r r20 a b) (fun v => ∀ l < 25, (v.getD l default).val M =
      (Lvm.E2U.t1ValsF 20 13 (r.map (C2.val M) ++ [r20.val M])
        (((List.range 25).map fun l => (a.getD l default).val M) ++
          (List.range 25).map fun l => (b.getD l default).val M)).getD l 0) := by
  unfold Lvm.E2Q.tOneU
  refine hs_bind (hs_g2Eq0 hz _ _) fun e he => hs_bind (hs_g2Mul _ _ _) fun f hf =>
    hs_bind (hs_g2Add _ _) fun w hw => ?_
  refine hs_mono (hs_mapB_getDU _ (fun l v => v.val M = (b.getD l default).val M * f.val M +
      ((a.getD l default).val M * r20.val M + (a.getD l default).val M) + FE2.ofK (Lvm.zStarE2 l).re * w.val M)
    (fun l => hs_bind (hs_g2Mul _ _ _) fun x1 h1 => hs_bind (hs_g2Mul _ _ _) fun x2 h2 =>
      hs_mono (hs_g2Lin _ _ _ _) fun v hv => by rw [hv, h2, h1, add_zero]; ring) _) fun v hv l hl => ?_
  have hv' := hv.2 l (by simpa using hl)
  simp only [List.getElem_range] at hv'
  rw [hv']
  have hrl : (r.map (C2.val M)).length = 20 := by simp [hr]
  have he' : e.val M = Lvm.E2U.eTailF 13 20 (r.map (C2.val M) ++ [r20.val M]) := by
    rw [he, ho, one_mul, eTailF_eq_prod _ hrl, eqAtF_zero2, List.map_take, List.map_drop]
  unfold Lvm.E2U.t1ValsF
  rw [getD_map_range0 _ hl]
  have hw20 : (r.map (C2.val M) ++ [r20.val M]).getD 20 0 = r20.val M := by
    rw [List.getD_append_right _ _ _ _ (by omega), hrl]; rfl
  have hab1 : (((List.range 25).map fun l => (a.getD l default).val M) ++
      (List.range 25).map fun l => (b.getD l default).val M).getD l 0 = (a.getD l default).val M := by
    rw [List.getD_append _ _ _ _ (by simpa using hl)]; simp [List.getD_eq_getElem?_getD, hl]
  have hab2 : (((List.range 25).map fun l => (a.getD l default).val M) ++
      (List.range 25).map fun l => (b.getD l default).val M).getD (25 + l) 0 = (b.getD l default).val M := by
    rw [List.getD_append_right _ _ _ _ (by simp)]; simp [List.getD_eq_getElem?_getD, hl]
  rw [hw20, hab1, hab2, ← he', hw, hf, hz, add_zero, zStarE2_kF]
  linear_combination (r20.val M * (a.getD l default).val M +
    r20.val M * e.val M * Lvm.E2V.kF (Lvm.E2U.zStarK l)) * fe2_two

/-! ## `|ρ| = 17`: the top row bit -/

/-- The threshold automaton with one more coordinate `r` above `t`'s range scales by `1 + r`. -/
theorem thrTailF_snoc (r : FE2) : ∀ (ρ : List FE2) (t : ℕ), t < 2 ^ ρ.length →
    E2V.thrTailF (ρ ++ [r]) t = ((1 + r) * (E2V.thrTailF ρ t).1, (1 + r) * (E2V.thrTailF ρ t).2)
  | [], t, ht => by
    have : t = 0 := by simpa using ht
    subst this
    simp [E2V.thrTailF, WK.nextS]
  | x :: ρ, t, ht => by
    have ih := thrTailF_snoc r ρ (t / 2) (by simp only [List.length_cons, pow_succ] at ht; omega)
    simp only [List.cons_append, E2V.thrTailF, ih]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> split_ifs <;> ring

/-- **`thrEvalF` at `|ρ| = 17`** (`m < 2^20`): `(1 + ρ₁₆)·thrEvalF ρ_{<16}`. -/
theorem thrEvalF_top (ρ μ : List FE2) (hρ : ρ.length = 17) {t : ℕ} (ht : t < 2 ^ 20) :
    E2V.thrEvalF ρ μ t = (1 + ρ.getD 16 0) * E2V.thrEvalF (ρ.take 16) μ t := by
  have e : ρ = ρ.take 16 ++ [ρ.getD 16 0] := by
    apply List.ext_getElem (by simp [hρ])
    intro i h1 h2
    rcases Nat.lt_or_ge i 16 with hi | hi
    · rw [List.getElem_append_left (by simp [hρ]; omega), List.getElem_take]
    · have : i = 16 := by omega
      subst this
      rw [List.getElem_append_right (by simp [hρ])]
      simp [List.getD_eq_getElem?_getD, hρ]
  unfold E2V.thrEvalF
  conv_lhs => rw [e]
  rw [thrTailF_snoc _ _ _ (by rw [List.length_take, hρ]; norm_num; omega), sumF_eq_sum, sumF_eq_sum,
    ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
  split_ifs <;> ring

/-- **`msEvalF` at `|ρ| = 17`, `|σ| = 20`, base `0`**: `(1 + ρ₁₆)·msEvalF ρ_{<16}`. -/
theorem msEvalF_top (ρ μ σ : List FE2) (hρ : ρ.length = 17) (hσ : σ.length = 20) (t : ℕ) :
    E2V.msEvalF ρ μ σ 0 t = (1 + ρ.getD 16 0) * E2V.msEvalF (ρ.take 16) μ σ 0 t := by
  unfold E2V.msEvalF
  rw [hσ, List.take_take, min_self, List.drop_take, show 16 - 16 = 0 from rfl, List.take_zero, Nat.zero_div]
  have e : ρ.drop 16 = [ρ.getD 16 0] := by
    apply List.ext_getElem (by simp [hρ])
    intro i h1 h2
    have : i = 0 := by simp [hρ] at h1; omega
    subst this
    simp [List.getD_eq_getElem?_getD, hρ]
  rw [e]
  simp [E2V.eqAtF]

/-- `g2Ms` reads `ρ_{<|σ|−4}` only. -/
theorem g2Ms_take (z one : C2) (ρ μ σ tb lt : List C2) :
    g2Ms z one ρ μ σ tb lt = g2Ms z one (ρ.take (σ.length - 4)) μ σ tb lt := by
  unfold g2Ms; rw [List.take_take, min_self]

/-- `g2ThrTail` reads as many coordinates of `ρ` as there are bits. -/
theorem g2ThrTail_take (z one : C2) : ∀ (ρ tb : List C2), g2ThrTail z one ρ tb = g2ThrTail z one (ρ.take tb.length) tb
  | [], _ => by simp [g2ThrTail]
  | _ :: _, [] => by simp [g2ThrTail]
  | r :: ρ, b :: tb => by
    simp only [List.length_cons, List.take_succ_cons, g2ThrTail]
    rw [g2ThrTail_take z one ρ tb]

/-- `g2Thr` on `tb` reads `ρ_{<|tb|−4}` only. -/
theorem g2Thr_take (z one : C2) (ρ μ tb lt : List C2) :
    g2Thr z one ρ μ tb lt = g2Thr z one (ρ.take (tb.length - 4)) μ tb lt := by
  unfold g2Thr
  rw [g2ThrTail_take z one ρ (tb.drop 4), g2ThrTail_take z one (ρ.take (tb.length - 4)) (tb.drop 4),
    List.length_drop, List.take_take, min_self]

/-! ## The constant-bound `MS` automaton -/

theorem mix4_bit (b : Bool) (f1 f0 : E2V.MS4F FE2) : mix4 (if b then 1 else 0) f1 f0 = if b then f1 else f0 := by
  obtain ⟨a0, a1, a2, a3⟩ := f1
  obtain ⟨b0, b1, b2, b3⟩ := f0
  cases b
  · simp [mix4]
  · simp only [mix4, if_true, one_mul, E2V.MS4F.mk.injEq]
    exact ⟨by linear_combination b0 * fe2_two, by linear_combination b1 * fe2_two,
      by linear_combination b2 * fe2_two, by linear_combination b3 * fe2_two⟩

/-- A step of the automaton at a known bit with `msCoef`'s weights is V's `msStepF`. -/
theorem msStepT_eq (a r : FE2) (t : ℕ) (q : E2V.MS4F FE2) :
    msStepT (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) (t % 2 == 1) q = E2V.msStepF a r (t % 2 == 1) q := by
  rw [← msStep_eq a r t q]
  have hb : (if t % 2 = 1 then (1 : FE2) else 0) = if (t % 2 == 1) = true then 1 else 0 := by
    simp only [beq_iff_eq]
  rw [hb, mix4_bit]
  cases (t % 2 == 1) <;> rfl

theorem hs_msCoef {z : C2} (hz : z.val M = 0) (a r : C2) :
    Hs c M (msCoef z a r) (fun q => q.1.val M = 1 + (a.val M + r.val M + a.val M * r.val M) ∧
      q.2.1.val M = a.val M * r.val M ∧ q.2.2.1.val M = r.val M + a.val M * r.val M ∧
      q.2.2.2.val M = a.val M + a.val M * r.val M) := by
  unfold msCoef
  refine hs_bind (hs_g2Mul _ _ _) fun ar har => hs_bind (hs_g2Add _ _) fun s hs => hs_bind (hs_g2Add _ _)
    fun al0 hal0 => hs_bind (hs_g2One _) fun al hal => hs_bind (hs_g2Add _ _) fun ga hga =>
    hs_bind (hs_g2Add _ _) fun de hde => hs_pure ?_
  rw [hz, add_zero] at har
  exact ⟨by rw [hal, hal0, hs, har], har, by rw [hga, har], by rw [hde, har]⟩

/-- **`msTailC` is V's `msTailF`** on the coefficients' points (the bound `t < 2^k`). -/
theorem hs_msTailC {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) :
    ∀ (cs : List Q4) (as rs : List FE2) (t : ℕ), cs.length = as.length → as.length = rs.length →
      (∀ i (hi : i < cs.length), (cs[i]).1.val M = 1 + (as.getD i 0 + rs.getD i 0 + as.getD i 0 * rs.getD i 0) ∧
        (cs[i]).2.1.val M = as.getD i 0 * rs.getD i 0 ∧
        (cs[i]).2.2.1.val M = rs.getD i 0 + as.getD i 0 * rs.getD i 0 ∧
        (cs[i]).2.2.2.val M = as.getD i 0 + as.getD i 0 * rs.getD i 0) → t < 2 ^ cs.length →
      Hs c M (msTailC z one cs t) (fun q => q4v M q = E2V.msTailF as rs t)
  | [], as, rs, t, h1, h2, _, ht => hs_pure (by
      have : t = 0 := by simpa using ht
      subst this
      have ha : as = [] := List.eq_nil_of_length_eq_zero (by simpa using h1.symm)
      have hr : rs = [] := List.eq_nil_of_length_eq_zero (by rw [← h2, ha]; rfl)
      subst ha hr
      simp [E2V.msTailF, q4v, hz, ho])
  | cq :: cs, a :: as, r :: rs, t, h1, h2, hc, ht => by
    simp only [msTailC]
    refine hs_bind (hs_msTailC hz ho cs as rs (t / 2) (by simpa using h1) (by simpa using h2)
      (fun i hi => by
        have := hc (i + 1) (by simp; omega)
        simpa only [List.getElem_cons_succ, List.getD_cons_succ] using this)
      (by simp only [List.length_cons, pow_succ] at ht; omega)) fun q hq => ?_
    refine hs_mono (hs_g2MsStep hz _ _ _ _ _ q) fun n hn => ?_
    obtain ⟨c1, c2, c3, c4⟩ := hc 0 (by simp)
    simp only [List.getElem_cons_zero, List.getD_cons_zero] at c1 c2 c3 c4
    rw [hn, hq, c1, c2, c3, c4, msStepT_eq]
    rfl
  | _ :: _, [], _, _, h1, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, h2, _, _ => by simp at h2

/-- **`msConstU`'s value**: the automaton's state `q` (`msTailF` at `t / 16`) against the low digit's sums. -/
theorem hs_msConstU {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (cs : List Q4) (as rs : List FE2)
    (A : List C2) (t : ℕ) (h1 : cs.length = as.length) (h2 : as.length = rs.length)
    (hc : ∀ i (hi : i < cs.length), (cs[i]).1.val M = 1 + (as.getD i 0 + rs.getD i 0 + as.getD i 0 * rs.getD i 0) ∧
        (cs[i]).2.1.val M = as.getD i 0 * rs.getD i 0 ∧
        (cs[i]).2.2.1.val M = rs.getD i 0 + as.getD i 0 * rs.getD i 0 ∧
        (cs[i]).2.2.2.val M = as.getD i 0 + as.getD i 0 * rs.getD i 0) (ht : t / 16 < 2 ^ cs.length) :
    Hs c M (msConstU z one cs A t) (fun m => m.val M =
      (E2V.msTailF as rs (t / 16)).v00 * ((List.range (t % 16)).map fun d => (A.getD d default).val M).sum +
      (E2V.msTailF as rs (t / 16)).v01 *
        (((List.range 15).drop (t % 16)).map fun d => (A.getD d default).val M).sum +
      (E2V.msTailF as rs (t / 16)).v10 * (A.getD 15 default).val M) := by
  unfold msConstU
  refine hs_bind (hs_msTailC hz ho cs as rs (t / 16) h1 h2 hc ht) fun q hq => ?_
  refine hs_bind (hs_g2Sum z _) fun lo hlo => hs_bind (hs_g2Sum z _) fun hi hhi => hs_mono (hs_g2Dot z _)
    fun m hm => ?_
  have e : E2V.msTailF as rs (t / 16) = q4v M q := hq.symm
  rw [hm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hlo, hhi, hz, e]
  simp only [q4v, List.map_map, Function.comp_def, zero_add]
  ring

/-- The low digit's sum against the automaton's state (`msEvalF` without its top factor), split at `u = t mod 16`. -/
theorem msLow_split (q : E2V.MS4F FE2) (A : ℕ → FE2) {u : ℕ} (hu : u < 16) :
    ((List.range 16).map fun d => A d * q.get (d == 15) (decide (u < (d + 1) % 16))).sum =
      q.v00 * ((List.range u).map A).sum + q.v01 * (((List.range 15).drop u).map A).sum + q.v10 * A 15 := by
  rw [List.range_succ, List.map_append, List.sum_append]
  have h15 : (List.range 15) = List.range u ++ (List.range 15).drop u := by
    rw [← List.take_append_drop u (List.range 15), List.take_range, Nat.min_eq_left (by omega)]
    simp
  conv_lhs => rw [h15]
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have e1 : ((List.range u).map fun d => A d * q.get (d == 15) (decide (u < (d + 1) % 16))) =
      (List.range u).map fun d => q.v00 * A d := List.map_congr_left fun d hd => by
    have := List.mem_range.mp hd
    rw [show (d == 15) = false by simp; omega, show decide (u < (d + 1) % 16) = false by
      simp only [decide_eq_false_iff_not, not_lt]; rw [Nat.mod_eq_of_lt (by omega)]; omega]
    simp only [E2V.MS4F.get]; ring
  have e2 : (((List.range 15).drop u).map fun d => A d * q.get (d == 15) (decide (u < (d + 1) % 16))) =
      ((List.range 15).drop u).map fun d => q.v01 * A d := List.map_congr_left fun d hd => by
    have hd' : u ≤ d ∧ d < 15 := by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      simp only [List.getElem_drop, List.getElem_range, List.length_drop, List.length_range] at hi ⊢
      omega
    rw [show (d == 15) = false by simp; omega, show decide (u < (d + 1) % 16) = true by
      simp only [decide_eq_true_eq]; rw [Nat.mod_eq_of_lt (by omega)]; omega]
    simp only [E2V.MS4F.get]; ring
  rw [e1, e2, List.sum_map_mul_left, List.sum_map_mul_left]
  simp only [show ((15 : ℕ) == 15) = true from rfl, show decide (u < (15 + 1) % 16) = false by simp,
    E2V.MS4F.get]
  ring

/-- **`MS(·; 0)`'s automaton** has `v01 = v10 = 0`. -/
theorem msTailF_zero : ∀ (as rs : List FE2), (E2V.msTailF as rs 0).v01 = 0 ∧ (E2V.msTailF as rs 0).v10 = 0
  | a :: as, r :: rs => by
    obtain ⟨h1, h2⟩ := msTailF_zero as rs
    simp only [E2V.msTailF, Nat.zero_mod, Nat.zero_div, show ((0 : ℕ) == 1) = false from rfl, E2V.msStepF,
      E2V.MS4F.get, WK.nextS, Bool.false_eq_true, if_false, Bool.or_true, Bool.or_false, Bool.not_false,
      Bool.not_true, Bool.false_or, Bool.true_or, h1, h2]
    constructor <;> ring
  | [], _ => by simp [E2V.msTailF]
  | _ :: _, [] => by simp [E2V.msTailF]

/-- `eq` at the index `2^|xs|` of a list with one more coordinate: `Π(1 + x)·y`. -/
theorem eqAtF_top : ∀ (xs : List FE2) (y : FE2), E2V.eqAtF (xs ++ [y]) (2 ^ xs.length) = (xs.map (1 + ·)).prod * y
  | [], y => by simp [E2V.eqAtF]
  | x :: xs, y => by
    have ih := eqAtF_top xs y
    have h1 : 2 ^ (xs.length + 1) % 2 = 0 := by rw [pow_succ]; omega
    have h2 : 2 ^ (xs.length + 1) / 2 = 2 ^ xs.length := by rw [pow_succ]; omega
    show (if 2 ^ (xs.length + 1) % 2 = 1 then x else 1 + x) * E2V.eqAtF (xs ++ [y]) (2 ^ (xs.length + 1) / 2) = _
    rw [if_neg (by omega), h2, ih, List.map_cons, List.prod_cons]
    ring

/-! ## The kernels (`kernU`) -/

/-- The top factor at `w = 13`, base `2^20`, `|ρ| = 17`: `eq(ρ_{9…16}, 2^7) = ρ₁₆·eq(ρ_{9…15}, 0)`. -/
theorem cTop_eq (ρ : List FE2) (hρ : ρ.length = 17) :
    E2V.eqAtF (ρ.drop 9) (2 ^ 20 / 2 ^ 13) = ρ.getD 16 0 * E2V.eqAtF ((ρ.drop 9).take 7) 0 := by
  have e : ρ.drop 9 = (ρ.drop 9).take 7 ++ [ρ.getD 16 0] := by
    apply List.ext_getElem (by simp [hρ])
    intro i h1 h2
    rcases Nat.lt_or_ge i 7 with hi | hi
    · rw [List.getElem_append_left (by simp [hρ]; omega), List.getElem_take]
    · have : i = 7 := by simp [hρ] at h1; omega
      subst this
      rw [List.getElem_append_right (by simp [hρ])]
      simp [List.getD_eq_getElem?_getD, hρ]
  have hl : ((ρ.drop 9).take 7).length = 7 := by simp [hρ]
  conv_lhs => rw [e, show 2 ^ 20 / 2 ^ 13 = 2 ^ ((ρ.drop 9).take 7).length by rw [hl]; norm_num]
  rw [eqAtF_top, eqAtF_zero2]
  ring

/-- `eqEvalF` of equal-length lists as a product over the coordinates. -/
theorem eqEvalF_prod (l r : List FE2) (h : l.length = r.length) :
    E2V.eqEvalF l r = ((List.range l.length).map fun k => 1 + l.getD k 0 + r.getD k 0).prod := by
  unfold E2V.eqEvalF
  rw [← List.prod_eq_foldl]
  congr 1
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
  simp at h1
  simp [List.getD_eq_getElem?_getD, h1.1, h1.2]

/-- **`msEvalF` at `|σ'| = 13`, base `2^20`** as the top factor times the split low-digit sum. -/
theorem msEvalF_low (ρ μ σ' : List FE2) (hσ : σ'.length = 13) (u : ℕ) :
    E2V.msEvalF ρ μ σ' (2 ^ 20) u = E2V.eqAtF (ρ.drop 9) (2 ^ 20 / 2 ^ 13) *
      ((E2V.msTailF (σ'.drop 4) (ρ.take 9) (u / 16)).v00 *
          ((List.range (u % 16)).map fun d => E2V.eqAtF (σ'.take 4) d * μ.getD ((d + 1) % 16) 0).sum +
        (E2V.msTailF (σ'.drop 4) (ρ.take 9) (u / 16)).v01 *
          (((List.range 15).drop (u % 16)).map fun d => E2V.eqAtF (σ'.take 4) d * μ.getD ((d + 1) % 16) 0).sum +
        (E2V.msTailF (σ'.drop 4) (ρ.take 9) (u / 16)).v10 *
          (E2V.eqAtF (σ'.take 4) 15 * μ.getD ((15 + 1) % 16) 0)) := by
  unfold E2V.msEvalF
  dsimp only
  rw [hσ, show 13 - 4 = 9 from rfl, sumF_eq_sum]
  congr 1
  rw [← msLow_split _ (fun d => E2V.eqAtF (σ'.take 4) d * μ.getD ((d + 1) % 16) 0) (Nat.mod_lt _ (by norm_num))]

theorem getD_map_val (l : List C2) {d : ℕ} (hd : d < l.length) :
    (l.getD d default).val M = (l.map (C2.val M)).getD d 0 := by
  simp [List.getD_eq_getElem?_getD, hd]

set_option maxHeartbeats 1000000 in
/-- **The kernels' values** (`kernU`): `K̃_ch(σ) = msEvalF ρ μ σ 0 t`, `K̃_ks(σ') = kksF` on `cont`'s two intervals
`[1, B − 1]`, `[K + 1, K + 31]` at base `2^20`, `Ĩ_ks(σ') = ikEvalP` at base `2^20`, `e' = eTailF 13 20 σ`
(`|ρ| = 17`, `|μ| = 16`, `|σ| = 20`, `mb` the bits of `t < 2^20`, `lt` its low digit's prefix table). -/
theorem hs_kernU {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (rho mu σ mb lt : List C2) (t : ℕ)
    (hρ : rho.length = 17) (hμ : mu.length = 16) (hσ : σ.length = 20) (hmb : mb.map (C2.val M) = bitsF t 20)
    (ht : t < 2 ^ 20)
    (hlt : lt.map (C2.val M) = (List.range 17).map fun k => ((eqKernelF ((mb.take 4).map (C2.val M))).take k).sum)
    (B K : ℕ) (hB : B - 1 < 2 ^ 13) (hK : K + 31 < 2 ^ 13) :
    Hs c M (kernU z one rho mu σ mb lt B K) (fun k =>
      k.kch.val M = E2V.msEvalF (rho.map (C2.val M)) (mu.map (C2.val M)) (σ.map (C2.val M)) 0 t ∧
      k.kks.val M = Lvm.E2U.kksF [(1, B - 1), (K + 1, K + 31)] (rho.map (C2.val M)) (mu.map (C2.val M))
        ((σ.map (C2.val M)).take 13) (2 ^ 20) ∧
      k.iks.val M = E2V.ikEvalP (rho.map (C2.val M)) (mu.map (C2.val M)) ((σ.map (C2.val M)).take 13) (2 ^ 20) ∧
      k.e'.val M = Lvm.E2U.eTailF 13 20 (σ.map (C2.val M))) := by
  unfold kernU
  rw [g2Ms_take]
  refine hs_bind (hs_g2Ms hz ho (rho.take (σ.length - 4)) mu σ mb lt t (by omega) (by simp [hρ, hσ]) hμ
    (by rw [hmb, hσ]) (by rw [hσ]; exact ht) hlt) fun ms hms => ?_
  refine hs_bind (hs_g2One _) fun r16 hr16 => hs_bind (hs_g2Mul _ _ _) fun kch hkch => ?_
  refine hs_bind (hs_g2Eq0 hz _ _) fun cTop hcTop => hs_bind (hs_g2EqTab hz [one] (σ.take 4)) fun e4 he4 => ?_
  refine hs_bind (hs_mapB_getDU _ (fun d v => v.val M = (e4.getD d default).val M *
      (mu.getD ((d + 1) % 16) default).val M) (fun d => hs_mono (hs_g2Mul _ _ _) fun v hv => by rw [hv, hz, add_zero])
      _) fun A ⟨hAl, hA⟩ => ?_
  refine hs_bind (hs_mapB_getDU _ (fun k q => q.1.val M = 1 + ((σ.getD (4 + k) default).val M +
      (rho.getD k default).val M + (σ.getD (4 + k) default).val M * (rho.getD k default).val M) ∧
      q.2.1.val M = (σ.getD (4 + k) default).val M * (rho.getD k default).val M ∧
      q.2.2.1.val M = (rho.getD k default).val M + (σ.getD (4 + k) default).val M * (rho.getD k default).val M ∧
      q.2.2.2.val M = (σ.getD (4 + k) default).val M + (σ.getD (4 + k) default).val M * (rho.getD k default).val M)
      (fun k => hs_msCoef hz _ _) _) fun cs ⟨hcsl, hcs⟩ => ?_
  rw [List.length_range] at hcsl
  -- the automaton's points: `σ'_{4…12}`, `ρ_{<9}`
  set as := ((σ.map (C2.val M)).take 13).drop 4 with has
  set rs := (rho.map (C2.val M)).take 9 with hrs
  have hasl : as.length = 9 := by simp [has, hσ]
  have hrsl : rs.length = 9 := by simp [hrs, hρ]
  have hc : ∀ i (hi : i < cs.length), (cs[i]).1.val M = 1 + (as.getD i 0 + rs.getD i 0 + as.getD i 0 * rs.getD i 0) ∧
      (cs[i]).2.1.val M = as.getD i 0 * rs.getD i 0 ∧
      (cs[i]).2.2.1.val M = rs.getD i 0 + as.getD i 0 * rs.getD i 0 ∧
      (cs[i]).2.2.2.val M = as.getD i 0 + as.getD i 0 * rs.getD i 0 := by
    intro i hi
    have h := hcs i (by simp; omega)
    simp only [List.getElem_range] at h
    have ea : as.getD i 0 = (σ.getD (4 + i) default).val M := by
      rw [getD_map_val σ (by omega), has, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        List.getElem?_take]
      rw [if_pos (by omega)]
    have er : rs.getD i 0 = (rho.getD i default).val M := by
      rw [getD_map_val rho (by omega), hrs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
        if_pos (by omega)]
    rw [ea, er, ← List.getD_eq_getElem cs default hi]
    exact h
  have hcB : ∀ u, u < 2 ^ 13 → u / 16 < 2 ^ cs.length := fun u hu => by rw [hcsl]; omega
  refine hs_bind (hs_msConstU hz ho cs as rs A (B - 1) (by omega) (by omega) hc (hcB _ hB)) fun m1 hm1 => ?_
  refine hs_bind (hs_msConstU hz ho cs as rs A (K + 31) (by omega) (by omega) hc (hcB _ hK)) fun m2 hm2 => ?_
  refine hs_bind (hs_msConstU hz ho cs as rs A K (by omega) (by omega) hc (hcB _ (by omega))) fun m3 hm3 => ?_
  refine hs_bind (hs_g2Sum _ _) fun ms3 hms3 => hs_bind (hs_g2Mul _ _ _) fun kks hkks => ?_
  refine hs_bind (hs_g2Dot z _) fun dg hdg => ?_
  refine hs_bind (hs_mapB_getDU _ (fun k v => v.val M = 1 + ((rho.getD k default).val M +
      (σ.getD (4 + k) default).val M)) (fun k => hs_bind (hs_g2Add _ _) fun s hs =>
        hs_mono (hs_g2One _) fun v hv => by rw [hv, hs]) _) fun fs ⟨hfsl, hfs⟩ => ?_
  refine hs_bind (hs_g2Prod hz dg fs) fun ik0 hik0 => hs_bind (hs_g2Mul _ _ _) fun iks hiks => ?_
  refine hs_bind (hs_g2Eq0 hz one _) fun e' he' => hs_pure ?_
  -- the shared values: `eq(σ_{<4}, ·)`, the `A_d`, the top factor
  have hσ' : ((σ.map (C2.val M)).take 13).length = 13 := by simp [hσ]
  have he4' : ∀ d < 16, (e4.getD d default).val M = E2V.eqAtF (((σ.map (C2.val M)).take 13).take 4) d := by
    intro d hd
    have e : e4.map (C2.val M) = eqKernelF ((σ.take 4).map (C2.val M)) := by
      rw [he4, List.map_cons, List.map_nil, ho]; rfl
    have he4l : e4.length = 16 := by
      have := congrArg List.length e
      simp only [List.length_map, eqKernelF_length, List.length_take, hσ] at this
      simpa using this
    rw [getD_map_val e4 (by omega), e, eqKernelF_getD, if_pos (by simp [hσ]; omega), List.take_take, List.map_take]
    rfl
  have hAv : ∀ d < 16, (A.getD d default).val M =
      E2V.eqAtF (((σ.map (C2.val M)).take 13).take 4) d * (mu.map (C2.val M)).getD ((d + 1) % 16) 0 := by
    intro d hd
    have h := hA d (by simpa using hd)
    simp only [List.getElem_range] at h
    rw [h, he4' d hd, getD_map_val mu (by rw [hμ]; omega)]
  have hcT : cTop.val M = E2V.eqAtF ((rho.map (C2.val M)).drop 9) (2 ^ 20 / 2 ^ 13) := by
    rw [hcTop, cTop_eq _ (by simp [hρ]), getD_map_val rho (by omega), List.map_take, List.map_drop]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hkch, hms, hr16, hz, add_zero, msEvalF_top (rho.map (C2.val M)) (mu.map (C2.val M)) (σ.map (C2.val M))
      (by simp [hρ]) (by simp [hσ]),
      show σ.length - 4 = 16 by omega, List.map_take, getD_map_val rho (by omega)]
    ring
  · unfold Lvm.E2U.kksF
    simp only [List.map_cons, List.map_nil]
    rw [sumF_eq_sum]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [msEvalF_low _ _ _ hσ', msEvalF_low _ _ _ hσ', msEvalF_low _ _ _ hσ', msEvalF_low _ _ _ hσ',
      show 1 - 1 = 0 from rfl, Nat.add_sub_cancel, Nat.zero_div, Nat.zero_mod, (msTailF_zero _ _).1,
      (msTailF_zero _ _).2]
    have hlo : ∀ u, u < 16 → ((List.range u).map fun d => (A.getD d default).val M).sum =
        ((List.range u).map fun d => E2V.eqAtF (((σ.map (C2.val M)).take 13).take 4) d *
          (mu.map (C2.val M)).getD ((d + 1) % 16) 0).sum := fun u hu =>
      congrArg _ (List.map_congr_left fun d hd => hAv d (by have := List.mem_range.mp hd; omega))
    have hhi : ∀ u, (((List.range 15).drop u).map fun d => (A.getD d default).val M).sum =
        (((List.range 15).drop u).map fun d => E2V.eqAtF (((σ.map (C2.val M)).take 13).take 4) d *
          (mu.map (C2.val M)).getD ((d + 1) % 16) 0).sum := fun u =>
      congrArg _ (List.map_congr_left fun d hd => hAv d (by
        have := List.mem_range.mp (List.mem_of_mem_drop hd); omega))
    rw [hkks, hms3]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hm1, hm2, hm3, hcT, hz, add_zero, hlo _ (Nat.mod_lt _ (by norm_num)),
      hlo _ (Nat.mod_lt _ (by norm_num)), hlo _ (Nat.mod_lt _ (by norm_num)), hhi, hhi, hhi, hAv 15 (by norm_num)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.range_zero,
      List.map_nil, mul_zero, zero_mul, sub_zero]
    simp only [CharTwo.sub_eq_add]
    ring
  · rw [hiks, hik0, hdg, hz, zero_add, add_zero, hcT]
    unfold E2V.ikEvalP
    rw [hσ', sumF_eq_sum, eqEvalF_prod _ _ (by simp [hρ, hσ])]
    congr 2
    · rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
      have := List.mem_range.mp hd
      simp only [Function.comp_apply]
      rw [he4' d this, getD_map_val mu (by omega)]
    · have hfv : fs.map (C2.val M) = (List.range 9).map fun k =>
          1 + ((rho.map (C2.val M)).getD k 0 + (σ.map (C2.val M)).getD (4 + k) 0) := by
        apply List.ext_getElem (by simp [hfsl])
        intro i h1 h2
        have hi9 : i < 9 := by simpa [hfsl] using h1
        have h := hfs i (by simpa [hfsl] using h1)
        simp only [List.getElem_range] at h
        simp only [List.getElem_map, List.getElem_range]
        rw [← getD_map_val rho (by omega), ← getD_map_val σ (by omega), ← h, ← List.getD_eq_getElem fs default (by simpa [hfsl] using h1)]
      rw [hfv, List.length_take, List.length_map, hρ, show min (13 - 4) 17 = 9 from rfl]
      refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
      have := List.mem_range.mp hk
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, show 13 - 4 = 9 from rfl,
        if_pos this, if_pos (show 4 + k < 13 by omega)]
      ring
  · rw [he', ho, one_mul, eqAtF_zero2]
    unfold Lvm.E2U.eTailF
    rw [prodF_eq, List.take_of_length_le (by simp [hσ] : (σ.map (C2.val M)).length ≤ 20), List.map_take,
      List.map_drop, List.take_of_length_le (by simp [hσ])]
    exact congrArg List.prod (List.map_congr_left fun x _ => by rw [CharTwo.sub_eq_add])

/-! ## The target block (`preWU`) -/

set_option maxHeartbeats 1000000 in
/-- **`preWU`'s values** (`hs_preW2` at `P = 16` with `20` bits of `t`: the threshold sum's top factor `1 + ρ₁₆`):
the target is `targetF` at `P = 16`, `eZ` is `eq(a, ·)`. -/
theorem hs_preWU (cv : ℕ → C2) (mb sb : List C2) (t : ℕ) (hmb : mb.map (C2.val M) = bitsF t 20)
    (ht : t < 2 ^ 20) (hsb : sb.length = 256) :
    Hs c M (preWU 16 cv mb sb) (fun G => G.z.val M = 0 ∧ G.one.val M = 1 ∧
      G.om.map (C2.val M) = wPos.map (omegaF M 16 cv) ∧ G.eZ.map (C2.val M) = eqKernelF (cvA M 16 cv) ∧
      G.lt.map (C2.val M) = (List.range 17).map (fun k => ((eqKernelF ((mb.take 4).map (C2.val M))).take k).sum) ∧
      G.target.val M = targetF M 16 cv (sb.map (C2.val M)) t) := by
  unfold preWU
  refine hs_bind (hs_g2Zero _) fun z hz => hs_bind (hs_g2One z) fun one ho => ?_
  rw [hz, add_zero] at ho
  refine hs_bind (hs_g2EqTab hz [one] _) fun eZ heZ => ?_
  have heZ' : eZ.map (C2.val M) = eqKernelF (cvA M 16 cv) := by
    rw [heZ, List.map_cons, List.map_nil, ho, cvA, List.map_map]; rfl
  have heZl : eZ.length = 64 := by
    have := congrArg List.length heZ'; rw [List.length_map, eqKernelF_length, cvA] at this; simpa using this
  refine hs_bind (hs_mapB' _ (omegaF M 16 cv) wPos fun j hj => hs_mono (hs_g2Omega hz (by simp) (wPos_lt hj))
    fun r hr => ?_) fun om hom => ?_
  · rw [hr, omegaF, cvB, List.map_map]
    congr 1
    funext s
    rw [getD_val eZ (by rw [heZl]; omega), heZ']
  refine hs_bind (hs_g2Eq0 hz one _) fun e0 he0 => hs_bind (hs_g2Mul _ _ _) fun io0 hio0 => ?_
  refine hs_bind (hs_g2LtTab hz ho (mb.take 4)) fun lt hlt => ?_
  have hmbl : mb.length = 20 := by simpa using congrArg List.length hmb
  rw [g2Thr_take, hmbl]
  refine hs_bind (hs_g2Thr hz ho _ _ mb lt t (by simp) (by rw [hmb]; simp) (by simpa using ht) hlt)
    fun thr0 hthr0 => ?_
  refine hs_bind (hs_g2One _) fun r1 hr1 => hs_bind (hs_g2Mul _ _ _) fun thr hthr => ?_
  refine hs_bind (hs_g2Sum z _) fun c43 hc43 => hs_bind (hs_g2Dot c43 _) fun pd hpd => ?_
  refine hs_bind (hs_g2Add _ _) fun ti hti => hs_bind (hs_g2Mul _ _ _) fun t1 ht1 =>
    hs_bind (hs_g2Mul _ _ _) fun tgt htgt => hs_pure ⟨hz, ho, hom, heZ', hlt, ?_⟩
  have g := fun i (hi : i < 261) => getD_omega hom hi
  have hmu0 : (((List.range 16).map (fun i => cv (1 + i))).getD 0 default).val M = (cvMu M cv).getD 0 0 := by
    rw [getD_val _ (by simp), cvMu, List.map_map]; rfl
  have hc : c43.val M = c43F M 16 cv := by
    rw [hc43, hz, zero_add]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [g 0 (by norm_num), g 1 (by norm_num), g 2 (by norm_num), g 259 (by norm_num), g 260 (by norm_num),
      show wPos.getD 259 0 = 264 from by simpa [wIx] using wPos_ix 256 le_rfl, wPos_small.1, wPos_small.2.1,
      wPos_small.2.2, wPos_last, c43F]
    ring
  have hp : pd.val M = c43F M 16 cv +
      ((List.range 256).map fun p => omegaF M 16 cv (8 + p) * (sb.map (C2.val M)).getD p 0).sum := by
    rw [hpd, hc, List.map_map]
    refine congrArg (fun x => c43F M 16 cv + x) ?_
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hp' := List.mem_range.mp hp
    simp only [Function.comp_apply]
    rw [g (wIx p) (by simp [wIx]; omega), wPos_ix p (by omega), getD_val sb (by omega)]
  have hi0 : io0.val M = io0F M 16 cv := by
    rw [hio0, he0, ho, hz, one_mul, add_zero, hmu0, io0F, cvRho, List.map_map]; rfl
  have hth : thr.val M = E2V.thrEvalF (cvRho M 16 cv) (cvMu M cv) t := by
    have eρ : ((List.range (16 + 1)).map fun i => cv (18 + i)).map (C2.val M) = cvRho M 16 cv := by
      rw [cvRho, List.map_map]; rfl
    have eμ : ((List.range 16).map fun i => cv (1 + i)).map (C2.val M) = cvMu M cv := by
      rw [cvMu, List.map_map]; rfl
    rw [hthr, hr1, hthr0, hz, add_zero, thrEvalF_top (cvRho M 16 cv) _ (by simp [cvRho]) ht,
      show 20 - 4 = 16 from rfl, List.map_take, eρ, eμ, getD_map_val _ (by simp), eρ]
    ring
  rw [htgt, ht1, hti, hth, hp, hc, hi0, targetF]
  ring

/-! ## The slot weights of `Y` and `M` (`slotWeightsU`, `slotWU`) -/

/-- The slot weight of a block of `nl` lanes at `τ`, column `z`: `Σ_{l<nl} eq(τ, l)·ω(64 l + z)`, `ω(64 l + z)` the
lane form of `B` on `eq(a, ·)` rotated by `z`. -/
def slotWv (Bv eZv τv : List FE2) (nl zz : ℕ) : FE2 :=
  ((List.range nl).map fun l => E2V.eqAtF τv l *
    Lvm.Q1.laneFormF Bv (fun s => eZv.getD ((zz + s) % 64) 0) l).sum

/-! ### The convolution (`slotWeightsU`): its regrouping, its loop, its copies -/

section Conv
open Finset (range)


theorem convOffs_nodup : convOffs.Nodup := by decide

theorem rho_lt64U : ∀ m < 25, Lvm.Q1.rho m < 64 := by decide

theorem mem_convOffs1 {m : ℕ} (hm : m < 25) : Lvm.Q1.rho m ∈ convOffs :=
  List.mem_eraseDups.2 (List.mem_append_left _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))

theorem mem_convOffs2 {m : ℕ} (hm : m < 25) : (Lvm.Q1.rho m + 1) % 64 ∈ convOffs :=
  List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))

theorem convOffs_lt {o : ℕ} (ho : o ∈ convOffs) : o < 64 := by
  obtain ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ := List.mem_append.1 (List.mem_eraseDups.1 ho) |>.imp List.mem_map.1 List.mem_map.1
  · exact rho_lt64U m (List.mem_range.1 hm)
  · exact Nat.mod_lt _ (by norm_num)

theorem sum_map_rangeU {β : Type} [AddCommMonoid β] (f : ℕ → β) : ∀ n, ((List.range n).map f).sum = ∑ m ∈ range n, f m
  | 0 => by simp
  | n + 1 => by rw [List.sum_range_succ, sum_map_rangeU f n, Finset.sum_range_succ]

theorem sum_filter_rangeU {β : Type} [AddCommMonoid β] (p : ℕ → Bool) (f : ℕ → β) : ∀ n,
    (((List.range n).filter p).map f).sum = ∑ m ∈ range n, if p m then f m else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, sum_filter_rangeU p f n,
      Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem col5U {β : Type} [AddCommMonoid β] (G : ℕ → β) {x : ℕ} (hx : x < 5) :
    ∑ y ∈ range 5, G (x + 5 * y) = ∑ m ∈ range 25, if m % 5 = x then G m else 0 := by
  interval_cases x <;> simp [Finset.sum_range_succ]

/-- `E_x = Σ_{l<nl, l ≡ x (5)} eq(τ, l)`. -/
def convE (τv : List FE2) (nl x : ℕ) : FE2 :=
  (((List.range nl).filter fun l => l % 5 = x).map fun l => E2V.eqAtF τv l).sum

/-- Lane `m`'s coefficient at `ρ_m`. -/
def convU1 (Bv τv : List FE2) (nl m : ℕ) : FE2 :=
  Bv.getD (keccakPi m) 0 * (if m < nl then E2V.eqAtF τv m + convE τv nl ((m + 4) % 5) else convE τv nl ((m + 4) % 5))

/-- Lane `m`'s coefficient at `ρ_m + 1`. -/
def convU2 (Bv τv : List FE2) (nl m : ℕ) : FE2 := Bv.getD (keccakPi m) 0 * convE τv nl ((m + 1) % 5)

/-- `C_o`. -/
def convC (Bv τv : List FE2) (nl o : ℕ) : FE2 :=
  (((List.range 25).filter fun m => Lvm.Q1.rho m = o).map (convU1 Bv τv nl)).sum +
    (((List.range 25).filter fun m => (Lvm.Q1.rho m + 1) % 64 = o).map (convU2 Bv τv nl)).sum

theorem sum_ite_mulRU (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → FE2) (X : FE2) :
    ∑ l ∈ s, (if p l then f l * X else 0) = (∑ l ∈ s, if p l then f l else 0) * X := by
  rw [Finset.sum_mul]; simp only [ite_mul, zero_mul]

/-- **The regrouped convolution** is the slot weight. -/
theorem conv_eqU (Bv eZv τv : List FE2) {nl : ℕ} (hnl : nl ≤ 25) (zz : ℕ) :
    (convOffs.map fun o => convC Bv τv nl o * eZv.getD ((zz + o) % 64) 0).sum = slotWv Bv eZv τv nl zz := by
  have hR : ∀ s, eZv.getD ((zz + s) % 64) 0 = (fun s => eZv.getD ((zz + s) % 64) 0) s := fun _ => rfl
  generalize (fun s => eZv.getD ((zz + s) % 64) 0) = R at hR
  have hE : ∀ x, convE τv nl x = ∑ l ∈ range nl, if l % 5 = x then E2V.eqAtF τv l else 0 := fun x => by
    rw [convE, sum_filter_rangeU]; simp
  -- the left side, lane by lane
  have hL : (convOffs.map fun o => convC Bv τv nl o * eZv.getD ((zz + o) % 64) 0).sum =
      ∑ m ∈ range 25, (convU1 Bv τv nl m * R (Lvm.Q1.rho m) + convU2 Bv τv nl m * R ((Lvm.Q1.rho m + 1) % 64)) := by
    rw [← List.sum_toFinset _ convOffs_nodup]
    simp only [hR, convC, sum_filter_rangeU, decide_eq_true_eq, add_mul, Finset.sum_mul, Finset.sum_add_distrib, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := convOffs.toFinset)]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun m hm => ?_) (Finset.sum_congr rfl fun m hm => ?_)
    · rw [Finset.sum_ite_eq, ite_eq_left (List.mem_toFinset.2 (mem_convOffs1 (Finset.mem_range.1 hm)))]
    · rw [Finset.sum_ite_eq, ite_eq_left (List.mem_toFinset.2 (mem_convOffs2 (Finset.mem_range.1 hm)))]
  rw [hL, slotWv, sum_map_rangeU]
  simp only [Lvm.Q1.laneFormF, sumF_eq_sum, sum_map_rangeU, hR]
  have c1 : ∀ x, ∑ y ∈ range 5, Bv.getD (keccakPi ((x % 5 + 1) % 5 + 5 * y)) 0 * R (Q1.rho ((x % 5 + 1) % 5 + 5 * y)) =
      ∑ m ∈ range 25, if m % 5 = (x % 5 + 1) % 5 then Bv.getD (keccakPi m) 0 * R (Q1.rho m) else 0 := fun x =>
    col5U (fun m => Bv.getD (keccakPi m) 0 * R (Q1.rho m)) (Nat.mod_lt _ (by norm_num))
  have c2 : ∀ x, ∑ y ∈ range 5, Bv.getD (keccakPi ((x % 5 + 4) % 5 + 5 * y)) 0 *
      R ((Q1.rho ((x % 5 + 4) % 5 + 5 * y) + 1) % 64) =
      ∑ m ∈ range 25, if m % 5 = (x % 5 + 4) % 5 then Bv.getD (keccakPi m) 0 * R ((Q1.rho m + 1) % 64) else 0 :=
    fun x => col5U (fun m => Bv.getD (keccakPi m) 0 * R ((Q1.rho m + 1) % 64)) (Nat.mod_lt _ (by norm_num))
  have hu1 : ∀ m, convU1 Bv τv nl m * R (Q1.rho m) = (if m < nl then E2V.eqAtF τv m * (Bv.getD (keccakPi m) 0 *
      R (Q1.rho m)) else 0) + ∑ l ∈ range nl, (if l % 5 = (m + 4) % 5 then E2V.eqAtF τv l *
        (Bv.getD (keccakPi m) 0 * R (Q1.rho m)) else 0) := fun m => by
    rw [convU1, hE, sum_ite_mulRU]
    split_ifs <;> ring
  have hu2 : ∀ m, convU2 Bv τv nl m * R ((Q1.rho m + 1) % 64) = ∑ l ∈ range nl, (if l % 5 = (m + 1) % 5 then
      E2V.eqAtF τv l * (Bv.getD (keccakPi m) 0 * R ((Q1.rho m + 1) % 64)) else 0) := fun m => by
    rw [convU2, hE, sum_ite_mulRU]
    ring
  have hcut : ∑ m ∈ range 25, (if m < nl then E2V.eqAtF τv m * (Bv.getD (keccakPi m) 0 * R (Q1.rho m)) else 0) =
      ∑ m ∈ range nl, E2V.eqAtF τv m * (Bv.getD (keccakPi m) 0 * R (Q1.rho m)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [c1, c2, hu1, hu2, Finset.sum_add_distrib, hcut, mul_add, Finset.mul_sum, mul_ite, mul_zero, add_assoc]
  congr 1
  rw [Finset.sum_comm, Finset.sum_comm (s := range 25) (t := range nl)]
  congr 1 <;> refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_ <;>
    split_ifs <;> first | rfl | (exfalso; omega)

/-! ## The loop -/

section Loop
open Lvm.Q1

theorem length_flatMap2U (g : ℕ → List Ins) (hg : ∀ i, (g i).length = 2) : ∀ N,
    ((List.range N).flatMap g).length = 2 * N
  | 0 => rfl
  | N + 1 => by rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap2U g hg N]; simp [hg]; omega

theorem seg_flatMap2U (g : ℕ → List Ins) (hg : ∀ i, (g i).length = 2) : ∀ N, ∀ k < N,
    Seg ((List.range N).flatMap g) (2 * k) (g k)
  | 0, k, hk => absurd hk (Nat.not_lt_zero _)
  | N + 1, k, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · intro i hi
      rw [List.getD_append _ _ _ _ (by rw [length_flatMap2U g hg]; rw [hg] at hi; omega)]
      exact seg_flatMap2U g hg N k hk i hi
    · have := seg_append ((List.range k).flatMap g) (g k) []
      rwa [List.append_nil, length_flatMap2U g hg] at this

/-- **A chain of twin products** `acc_k = a_k·b_k + acc_{k−1}` (`acc_{−1} = d₀`). -/
theorem chain2_valU {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) (a b : ℕ → S2) (d0 : S2)
    {N : ℕ} (hseg : ∀ k < N, Seg ins (2 * k) (mul2I (a k) (b k) (if k = 0 then d0 else locS2 (2 * (k - 1)))))
    (hlen : 2 * N ≤ ins.length) : ∀ k < N,
      twinVal V (2 * k) = ((List.range (k + 1)).map fun i => (a i).val xv V * (b i).val xv V).sum + d0.val xv V
  | 0, h0 => by
    rw [mul2I_val hF (hseg 0 h0) (by omega)]
    simp
  | k + 1, hk => by
    rw [mul2I_val hF (hseg (k + 1) hk) (by omega), ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel, locS2_val,
      chain2_valU hF a b d0 hseg hlen k (by omega), List.sum_range_succ (n := k + 1)]
    ring

end Loop

section Loop2
open Lvm.Q1

/-- `convIns` is the chain of its terms. -/
theorem convIns_seg (z0 : C2) (C : List C2) (b : ℕ) {i : ℕ} (hi : i < convOffs.length) :
    Seg (convIns z0 C b) (2 * i) (mul2I (c2Ext (C.getD i default))
      (.ext ⟨.K, b + 2 * convOffs.getD i 0, [2]⟩, .ext ⟨.K, b + 2 * convOffs.getD i 0 + 1, [2]⟩)
      (if i = 0 then c2Ext z0 else locS2 (2 * (i - 1)))) :=
  seg_flatMap2U _ (fun _ => rfl) _ i hi

theorem convIns_length (z0 : C2) (C : List C2) (b : ℕ) : (convIns z0 C b).length = 2 * convOffs.length :=
  length_flatMap2U _ (fun _ => rfl) _

theorem convIns_op (z0 : C2) (C : List C2) (b : ℕ) {i j : ℕ} (hi : i < convOffs.length) (hj : j < 2) :
    ((convIns z0 C b).getD (2 * i + j) default).op ≠ .assert0 := by
  rw [convIns_seg z0 C b hi j (by simpa [mul2I, e2I] using hj)]
  interval_cases j <;> simp [mul2I, e2I]

theorem convIns_ok (z0 : C2) (C : List C2) (b : ℕ) : SLok (convIns z0 C b) = true := by
  unfold SLok
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range, convIns_length] at hk
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 2 ∧ k = 2 * i + j := ⟨k / 2, k % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  have hi : i < convOffs.length := by omega
  rw [convIns_seg z0 C b hi j (by simpa [mul2I, e2I] using hj)]
  by_cases h0 : i = 0
  · subst h0
    interval_cases j <;> simp [Ins.locOk, mul2I, e2I, s2Args, c2Ext]
  · have h1 := convIns_op z0 C b (i := i - 1) (j := 0) (by omega) (by norm_num)
    have h2 := convIns_op z0 C b (i := i - 1) (j := 1) (by omega) (by norm_num)
    rw [Nat.add_zero] at h1
    simp only [List.getD_eq_getElem?_getD] at h1 h2
    interval_cases j <;> simp [Ins.locOk, mul2I, e2I, s2Args, c2Ext, locS2, h0, h1, h2] <;> omega

theorem cp_fstU (l : List C2) : ∀ p : Ptr, (mapB (fun e => g2Lin 0 0 e e) l p).1 =
    (List.range l.length).map fun t => (⟨kc (p.k + 2 * t), kc (p.k + 2 * t + 1)⟩ : C2) := by
  induction l with
  | nil => intro p; rfl
  | cons a l ih =>
    intro p
    show (⟨kc p.k, kc (p.k + 1)⟩ : C2) :: (mapB (fun e => g2Lin 0 0 e e) l (p.adv _)).1 = _
    rw [ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [g2Lin, gE2lin, gE2, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
    omega

end Loop2

section Loop3
open Lvm.Q1

theorem iterXv_fixedU (M : Mem) (o : LoopOut) (jf : Nat) (τ : Ty) (b : Nat) :
    iterXv M o jf (.ext ⟨τ, b, []⟩) = M.rd τ b := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, Addr.at]
  rfl

theorem c2Ext_valU (o : LoopOut) (jf : ℕ) (V : List FE) (x : C2) : (c2Ext x).val (iterXv M o jf) V = x.val M := by
  simp only [c2Ext, S2.val, Src.val, Cell.addr]
  rw [iterXv_fixedU, iterXv_fixedU]
  rfl

theorem convOffs_length : convOffs.length = 40 := by decide

/-- **The convolution loop** (`convIns` on `[6]`): iteration `z`'s last twin pair is `z₀ + Σ_i C_i·eZ2[o_i + z]`,
`eZ2[t]` the `K` cells `b + 2t`, `b + 2t + 1`. -/
theorem hs_convLoop (z0 : C2) (C : List C2) (b : ℕ) :
    Hs c M (VF.loopF [6] (tplOf (convIns z0 C b))) (fun lo => ∀ zz < 64,
      (lo.cell2 (2 * convOffs.length - 2) zz).val M = ((List.range convOffs.length).map fun i =>
        (C.getD i default).val M * (⟨(M.rd .K (b + 2 * convOffs.getD i 0 + 2 * zz)).c₀,
          (M.rd .K (b + 2 * convOffs.getD i 0 + 1 + 2 * zz)).c₀⟩ : FE2)).sum + z0.val M) := by
  intro p hp
  rw [VF.loopF_eq] at hp ⊢
  intro zz hzz
  have hF := fix_of_loop (convIns_ok z0 C b) hp (jf := zz) (by simpa using hzz)
  have hch := chain2_valU hF (fun i => c2Ext (C.getD i default))
    (fun i => (.ext ⟨.K, b + 2 * convOffs.getD i 0, [2]⟩, .ext ⟨.K, b + 2 * convOffs.getD i 0 + 1, [2]⟩))
    (c2Ext z0) (N := convOffs.length) (fun k hk => convIns_seg z0 C b hk) (by rw [convIns_length])
    (convOffs.length - 1) (by rw [convOffs_length]; norm_num)
  have hl := convIns_length z0 C b
  rw [convOffs_length, show 40 - 1 + 1 = 40 from rfl] at hch
  rw [convOffs_length] at hl ⊢
  rw [cell2_val, ← iterV_getD M _ (n := (convIns z0 C b).length) (by rw [hl]; norm_num),
    ← iterV_getD M _ (n := (convIns z0 C b).length) (by rw [hl]; norm_num)]
  unfold twinVal at hch
  rw [show 2 * (40 - 1) = 2 * 40 - 2 from rfl] at hch
  rw [hch, c2Ext_valU]
  refine congrArg (· + z0.val M) (congrArg List.sum (List.map_congr_left fun i _ => ?_))
  rw [c2Ext_valU]
  have ho : (loop [6] (tplOf (convIns z0 C b)) p).1.dims = [6] := rfl
  simp only [S2.val, Src.val]
  rw [iterXv_ext1 M _ ho (by simpa using hzz), iterXv_ext1 M _ ho (by simpa using hzz)]

/-- **The doubled copy**: `mapB (g2Lin 0 0 e e)` writes twin pair `t` at the `K` cells `b + 2t`, `b + 2t + 1`
from the first one's `b`, with `l`'s values. -/
theorem hs_cpU (l : List C2) : Hs c M (mapB (fun e => g2Lin 0 0 e e) l) (fun cp => ∀ t < l.length,
    (⟨(M.rd .K ((cp.getD 0 default).re.n + 2 * t)).c₀, (M.rd .K ((cp.getD 0 default).re.n + 2 * t + 1)).c₀⟩ : FE2) =
      (l.getD t default).val M) := by
  intro p hp
  have hv := hs_mapB_getDU (fun e => g2Lin 0 0 e e) (fun a r => r.val M = a.val M)
    (fun a => hs_mono (hs_g2Lin 0 0 a a) fun r hr => by rw [hr, show FE2.ofK 0 = 0 from rfl]; ring) l p hp
  rw [cp_fstU] at hv ⊢
  intro t ht
  have h1 := hv.2 t ht
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, List.getElem_range] at h1
  rw [List.getD_eq_getElem _ _ ht, ← h1]
  rcases l with _ | ⟨a, l⟩
  · exact absurd ht (Nat.not_lt_zero _)
  · simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero, Nat.mul_zero,
      Nat.add_zero]
    rfl

end Loop3

section Main

theorem keccakPi_ltU {m : ℕ} (hm : m < 25) : keccakPi m < 25 := by unfold keccakPi; omega

theorem sum_map_getDU (l : List ℕ) (g : ℕ → FE2) :
    (l.map g).sum = ((List.range l.length).map fun i => g (l.getD i 0)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (by simpa using h1)]

theorem eZ2_getDU (eZ : List C2) (heZ : eZ.length = 64) {o zz : ℕ} (ho : o < 64) (hzz : zz < 64) :
    (eZ ++ eZ).getD (o + zz) default = eZ.getD ((zz + o) % 64) default := by
  by_cases h : o + zz < 64
  · rw [List.getD_append _ _ _ _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  · rw [List.getD_append_right _ _ _ _ (by omega), heZ, show (zz + o) % 64 = o + zz - 64 by omega]

/-- The `eq` table from `[o2]` is `eqKernelF`, entry for entry (`Lvm.E2Q.eqTab_getD`'s twin). -/
theorem eqTabU_getD {o2 : C2} (ho : o2.val M = 1) {pt t : List C2}
    (ht : t.map (C2.val M) = (pt.map (C2.val M)).foldl eqStep2 ([o2].map (C2.val M))) {l : ℕ}
    (hl : l < 2 ^ pt.length) : (t.getD l default).val M = E2V.eqAtF (pt.map (C2.val M)) l := by
  have hk : t.map (C2.val M) = E2V.eqKernelF (pt.map (C2.val M)) := by
    rw [ht, List.map_cons, List.map_nil, ho, eqKernelF_eq]
  have hlen : t.length = 2 ^ pt.length := by
    rw [← List.length_map (f := C2.val M), hk, E2V.eqKernelF_length, List.length_map]
  rw [c2_getD t (by rw [hlen]; exact hl), hk, E2V.eqKernelF_getD, List.length_map, ite_eq_left hl]

end Main

end Conv

/-- **The convolution's values** (`slotWeightsU`): `W_z = Σ_{l<nl} eq(τ, l)·ω(64 l + z)`. -/
theorem hs_slotWeightsU {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (B eZ τ : List C2) (nl : ℕ)
    (hB : B.length = 25) (heZ : eZ.length = 64) (hτ : τ.length = 5) (hnl : nl ≤ 25) :
    Hs c M (slotWeightsU z one B eZ τ nl) (fun W => W.length = 64 ∧ ∀ zz < 64,
      (W.getD zz default).val M = slotWv (B.map (C2.val M)) (eZ.map (C2.val M)) (τ.map (C2.val M)) nl zz) := by
  unfold slotWeightsU
  refine hs_bind (hs_g2EqTab hz [one] τ) fun et het => ?_
  have hetv : ∀ l < 25, (et.getD l default).val M = E2V.eqAtF (τ.map (C2.val M)) l := fun l hl =>
    eqTabU_getD ho het (by rw [hτ]; omega)
  refine hs_bind (hs_mapB_getDU _ (fun x r => r.val M = convE (τ.map (C2.val M)) nl x) (fun x =>
    hs_mono (hs_g2Sum z _) fun r hr => by
      rw [hr, hz, zero_add, convE, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun l hl => hetv l (by
        have := List.mem_range.1 (List.mem_filter.1 hl).1; omega))) _) fun E ⟨hEl, hE⟩ => ?_
  have hE' : ∀ x < 5, (E.getD x default).val M = convE (τ.map (C2.val M)) nl x := fun x hx => by
    have := hE x (by simpa using hx); simpa using this
  have hBv : ∀ m < 25, (B.getD (keccakPi m) default).val M = (B.map (C2.val M)).getD (keccakPi m) 0 := fun m hm =>
    c2_getD B (by rw [hB]; exact keccakPi_ltU hm)
  have hc1 : ∀ m, Hs c M (if m < nl then g2Add (et.getD m default) (E.getD ((m + 4) % 5) default)
      else pure (E.getD ((m + 4) % 5) default)) (fun c1 => m < 25 → c1.val M =
        if m < nl then E2V.eqAtF (τ.map (C2.val M)) m + convE (τ.map (C2.val M)) nl ((m + 4) % 5)
        else convE (τ.map (C2.val M)) nl ((m + 4) % 5)) := fun m => by
    by_cases hm : m < nl
    · rw [ite_eq_left hm]
      exact hs_mono (hs_g2Add _ _) fun r hr hm25 => by
        rw [hr, hetv m hm25, hE' _ (Nat.mod_lt _ (by norm_num)), ite_eq_left hm]
    · rw [ite_eq_right hm]
      exact hs_pure fun _ => by rw [hE' _ (Nat.mod_lt _ (by norm_num)), ite_eq_right hm]
  refine hs_bind (hs_mapB_getDU _ (fun m (u : C2 × C2) => m < 25 →
    u.1.val M = convU1 (B.map (C2.val M)) (τ.map (C2.val M)) nl m ∧
    u.2.val M = convU2 (B.map (C2.val M)) (τ.map (C2.val M)) nl m) (fun m =>
      hs_bind (hc1 m) fun c1 h1 => hs_bind (hs_g2Mul _ _ _) fun u1 hu1 => hs_bind (hs_g2Mul _ _ _) fun u2 hu2 =>
        hs_pure fun hm => ⟨by rw [hu1, hz, add_zero, h1 hm, hBv m hm, convU1], by
          rw [hu2, hz, add_zero, hBv m hm, hE' _ (Nat.mod_lt _ (by norm_num)), convU2]⟩) _) fun us ⟨_, hus⟩ => ?_
  have hus' : ∀ m < 25, (us.getD m default).1.val M = convU1 (B.map (C2.val M)) (τ.map (C2.val M)) nl m ∧
      (us.getD m default).2.val M = convU2 (B.map (C2.val M)) (τ.map (C2.val M)) nl m := fun m hm => by
    have := hus m (by simpa using hm)
    simp only [List.getElem_range] at this
    exact this hm
  refine hs_bind (hs_mapB_getDU _ (fun o r => r.val M = convC (B.map (C2.val M)) (τ.map (C2.val M)) nl o) (fun o =>
    hs_mono (hs_g2Sum z _) fun r hr => by
      rw [hr, hz, zero_add, List.map_append, List.sum_append, convC, List.map_map, List.map_map]
      exact congrArg₂ (· + ·)
        (congrArg List.sum (List.map_congr_left fun m hm =>
          (hus' m (List.mem_range.1 (List.mem_filter.1 hm).1)).1))
        (congrArg List.sum (List.map_congr_left fun m hm =>
          (hus' m (List.mem_range.1 (List.mem_filter.1 hm).1)).2))) _) fun C ⟨_, hC⟩ => ?_
  refine hs_bind (hs_cpU (eZ ++ eZ)) fun cp hcp => hs_bind (hs_convLoop z C _) fun lo hlo => hs_pure ⟨by simp,
    fun zz hzz => ?_⟩
  rw [List.getD_eq_getElem _ _ (by simpa using hzz), List.getElem_map, List.getElem_range, hlo zz hzz, hz, add_zero,
    ← conv_eqU _ _ _ hnl, sum_map_getDU convOffs]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' := List.mem_range.1 hi
  have hoi : convOffs.getD i 0 < 64 :=
    convOffs_lt (by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi')
  have hCi := hC i hi'
  rw [← List.getD_eq_getElem _ 0 hi'] at hCi
  rw [hCi, show (cp.getD 0 default).re.n + 2 * convOffs.getD i 0 + 2 * zz =
      (cp.getD 0 default).re.n + 2 * (convOffs.getD i 0 + zz) by ring,
    show (cp.getD 0 default).re.n + 2 * convOffs.getD i 0 + 1 + 2 * zz =
      (cp.getD 0 default).re.n + 2 * (convOffs.getD i 0 + zz) + 1 by ring,
    hcp _ (by rw [List.length_append, heZ]; omega), eZ2_getDU eZ heZ hoi hzz,
    c2_getD eZ (by rw [heZ]; exact Nat.mod_lt _ (by norm_num))]

/-- **The slot check of `Y`/`M`** (`slotWU`): with the gate on, the slot sumcheck's final claim is
`Σ_z W_z(τ)·slice_z`. -/
theorem slotWU_sound (qs nl : ℕ) (B eZ τ : List C2) {z one : C2} (final : C2) {gate : Cell}
    (hz : z.val M = 0) (ho : one.val M = 1) (hg : gate.val M = 1) (hB : B.length = 25) (heZ : eZ.length = 64)
    (hτ : τ.length = 5) (hnl : nl ≤ 25) :
    HsA c M (slotWU qs nl B eZ τ z one final gate) (fun _ => final.val M =
      ((List.range 64).map fun zz => slotWv (B.map (C2.val M)) (eZ.map (C2.val M)) (τ.map (C2.val M)) nl zz *
        (ld2 (qs + 2 * zz)).val M).sum) := by
  unfold slotWU
  refine hsA_bind (hsA_of_hs (hs_slotWeightsU hz ho B eZ τ nl hB heZ hτ hnl)) fun W hW' => ?_
  obtain ⟨hWl, hW⟩ := hW'
  refine hsA_bind (hsA_of_hs (hs_g2Dot final _)) fun e he => hsA_mono (hsA_g2Assert e gate hg) fun _ hE => ?_
  rw [he] at hE
  have hs : ((List.range 64).map ((fun e : C2 × C2 => e.1.val M * e.2.val M) ∘
      fun zz => (W.getD zz default, (slices2 qs).getD zz default))).sum =
      ((List.range 64).map fun zz => slotWv (B.map (C2.val M)) (eZ.map (C2.val M)) (τ.map (C2.val M)) nl zz *
        (ld2 (qs + 2 * zz)).val M).sum := by
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    simp only [Function.comp_apply]
    rw [hW zz hzz']
    simp [List.getD_eq_getElem?_getD, hzz', slices2]
  rw [List.map_map, hs] at hE
  linear_combination hE - (((List.range 64).map fun zz => slotWv (B.map (C2.val M)) (eZ.map (C2.val M))
    (τ.map (C2.val M)) nl zz * (ld2 (qs + 2 * zz)).val M).sum) * fe2_two

/-- **V's slot weight of a block of `nl ≤ 32` lanes** (`yWG`, `mWG`): `slotWF 5 W τ z = Σ_{o<nl} eq(τ, o)·f(64 o + z)`. -/
theorem slotWF_blk (f : ℕ → FE2) (nl : ℕ) (hnl : nl ≤ 32) (τ : List FE2) (zz : ℕ) :
    E2V.slotWF 5 (fun o z => if o < nl then f (64 * o + z) else 0) τ zz =
      ((List.range nl).map fun o => E2V.eqAtF τ o * f (64 * o + zz)).sum := by
  unfold E2V.slotWF
  rw [sumF_eq_sum, show 2 ^ 5 = nl + (32 - nl) by omega, List.range_add, List.map_append, List.sum_append]
  have h0 : ((List.map (fun x => nl + x) (List.range (32 - nl))).map fun o =>
      E2V.eqAtF τ o * if o < nl then f (64 * o + zz) else 0).sum = 0 := by
    rw [List.map_map]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      simp
  rw [h0, add_zero]
  exact congrArg List.sum (List.map_congr_left fun o ho => by beta_reduce; rw [if_pos (List.mem_range.mp ho)])

/-! ## The wire gadget at S2GU (`wireGU`) -/

set_option maxHeartbeats 2000000 in
/-- **The S2GU wire gadget is sound** (gate on; `P = 16`, `w = 20`): its points are the stream's challenges; the wire
sumcheck from `targetF` ends at `K̃_ch·g_D + e'·(K̃_ks·g_Y + Ĩ_ks·g_M)` (V's final check); the slot sumchecks of
`D`, `Y`, `M` end at their slot weights against the slices. `mb`'s cells hold `t`'s bits (`t < 2^20`). -/
theorem wireGU_sound (qw : ℕ) (cv : ℕ → C2) (mb sb : List Cell) (B K : ℕ) (zk gate : Cell) (t : ℕ)
    (hzk : zk.val M = 0) (hg : gate.val M = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => kC2 b zk).map (C2.val M) = bitsF t 20) (ht : t < 2 ^ 20)
    (hB : B - 1 < 2 ^ 13) (hK : K + 31 < 2 ^ 13) :
    HsA c M (wireGU 16 20 qw cv mb sb B K zk gate) (fun o =>
      o.sigma = (sc2Ans 20 qw).map ld2 ∧ o.tauD = (sc2Ans 2 (wireLanesU 20 qw).slotD).map ld2 ∧
      o.tauY = (sc2Ans 5 (wireLanesU 20 qw).slotY).map ld2 ∧ o.tauM = (sc2Ans 5 (wireLanesU 20 qw).slotM).map ld2 ∧
      scFold2 (fun k => (ld2 k).val M) 20 qw (targetF M 16 cv ((sb.map fun b => kC2 b zk).map (C2.val M)) t) =
        E2V.msEvalF (cvRho M 16 cv) (cvMu M cv) (o.sigma.map (C2.val M)) 0 t * (ld2 (wireLanesU 20 qw).g3).val M +
        Lvm.E2U.eTailF 13 20 (o.sigma.map (C2.val M)) *
          (Lvm.E2U.kksF [(1, B - 1), (K + 1, K + 31)] (cvRho M 16 cv) (cvMu M cv)
              ((o.sigma.map (C2.val M)).take 13) (2 ^ 20) * (ld2 ((wireLanesU 20 qw).g3 + 2)).val M +
            E2V.ikEvalP (cvRho M 16 cv) (cvMu M cv) ((o.sigma.map (C2.val M)).take 13) (2 ^ 20) *
              (ld2 ((wireLanesU 20 qw).g3 + 4)).val M) ∧
      scFold2 (fun k => (ld2 k).val M) 2 (wireLanesU 20 qw).slotD ((ld2 (wireLanesU 20 qw).g3).val M) =
        ((List.range 64).map fun zz => ((List.range 4).map fun ob =>
          (eqKernelF (o.tauD.map (C2.val M))).getD ob 0 * omegaF M 16 cv (8 + 64 * ob + zz)).sum *
            (ld2 ((wireLanesU 20 qw).slicesD + 2 * zz)).val M).sum ∧
      scFold2 (fun k => (ld2 k).val M) 5 (wireLanesU 20 qw).slotY ((ld2 ((wireLanesU 20 qw).g3 + 2)).val M) =
        ((List.range 64).map fun zz => slotWv (cvB M 16 cv) (eqKernelF (cvA M 16 cv)) (o.tauY.map (C2.val M)) 25 zz *
          (ld2 ((wireLanesU 20 qw).slicesY + 2 * zz)).val M).sum ∧
      scFold2 (fun k => (ld2 k).val M) 5 (wireLanesU 20 qw).slotM ((ld2 ((wireLanesU 20 qw).g3 + 4)).val M) =
        ((List.range 64).map fun zz => slotWv (cvB M 16 cv) (eqKernelF (cvA M 16 cv)) (o.tauM.map (C2.val M)) 17 zz *
          (ld2 ((wireLanesU 20 qw).slicesM + 2 * zz)).val M).sum) := by
  unfold wireGU
  refine hsA_bind (hsA_of_hs (hs_preWU cv _ _ t hmb ht (by simp [hsb]))) fun G hG => ?_
  obtain ⟨hz, ho, hom, heZ, hlt, htg⟩ := hG
  have heZl : G.eZ.length = 64 := by
    have := congrArg List.length heZ; rw [List.length_map, eqKernelF_length, cvA] at this; simpa using this
  refine hsA_bind (hsA_of_hs (hs_sc2 20 qw G.target)) fun sc ⟨hs1, hs2⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_kernU hz ho _ _ sc.1 _ G.lt t (by simp) (by simp) (by rw [hs1]; simp [sc2Ans])
    hmb ht hlt B K hB hK)) fun k ⟨hkch, hkks, hiks, he'⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t1 ht1 => hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t2 ht2 =>
    hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t3 ht3 => hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun fin hfin => ?_
  refine hsA_bind (hsA_g2Assert fin gate hg) fun _ hF => ?_
  refine hsA_bind (hsA_of_hs (hs_sc2 2 _ _)) fun sd ⟨hd1, hd2⟩ => ?_
  refine hsA_bind (slotW2_sound _ hom sd.1 sd.2 hz ho hg (by rw [hd1]; simp [sc2Ans])) fun _ hsD => ?_
  refine hsA_bind (hsA_of_hs (hs_sc2 5 _ _)) fun sy ⟨hy1, hy2⟩ => ?_
  refine hsA_bind (slotWU_sound _ 25 _ G.eZ sy.1 sy.2 hz ho hg (by simp) heZl (by rw [hy1]; simp [sc2Ans])
    (by norm_num)) fun _ hsY => ?_
  refine hsA_bind (hsA_of_hs (hs_sc2 5 _ _)) fun sm ⟨hm1, hm2⟩ => ?_
  refine hsA_bind (slotWU_sound _ 17 _ G.eZ sm.1 sm.2 hz ho hg (by simp) heZl (by rw [hm1]; simp [sc2Ans])
    (by norm_num)) fun _ hsM => hsA_pure ⟨hs1, hd1, hy1, hm1, ?_, ?_, ?_, ?_⟩
  · have e1 : (List.map (C2.val M) ((List.range (16 + 1)).map fun i => cv (18 + i))) = cvRho M 16 cv := by
      rw [cvRho, List.map_map]; rfl
    have e2 : (List.map (C2.val M) ((List.range 16).map fun i => cv (1 + i))) = cvMu M cv := by
      rw [cvMu, List.map_map]; rfl
    rw [e1, e2] at hkch hkks hiks
    rw [← htg, ← hs2, ← hkch, ← hkks, ← hiks, ← he']
    rw [hfin, ht3, ht2, ht1, hz, add_zero] at hF
    linear_combination hF - (k.kch.val M * (ld2 (wireLanesU 20 qw).g3).val M + k.e'.val M *
      (k.kks.val M * (ld2 ((wireLanesU 20 qw).g3 + 2)).val M + k.iks.val M * (ld2 ((wireLanesU 20 qw).g3 + 4)).val M))
        * fe2_two
  · rw [← hd2, hsD]
  · rw [← hy2, hsY, heZ]
    simp only [cvB, List.map_map]
    rfl
  · rw [← hm2, hsM, heZ]
    simp only [cvB, List.map_map]
    rfl

end Lvm.Q2
