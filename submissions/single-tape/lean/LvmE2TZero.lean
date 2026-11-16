-- New for lvm2 E2-FT (stage S2GT, E2F-T): the zerocheck at `E2` with the swapped coordinate split
-- (`zeroProgT`): `τ` by the zero test, `ω`'s degree-2 escape, the equality-mode rounds, the nine values.
import LvmE2TProg
import LvmE2TSum
import LvmE2VZero

/-!
# The zerocheck at `E2` (S2GT)

The relation's three coordinates (`LvmE2TWiring.relT`) are a table `deltaZT` on 22 bits (slot `x` low, coordinate
`k` in bits 20–21; `k = 3` is `0`).

* `τ` (`e2Samples gTau 20`): E2F-V's `zeroSpecE2` on `deltaZT`, `n = 22`: from `ZeroOnF δ [] 22` (the relation at
  every slot) to `ZeroOnF δ τ 22` (the three folded coordinates `f_k = Σ_x eq(τ, x)·rel_k(x)` vanish).
* `ω` (`e2Sample gOmega`): **the degree-2-in-`ω` escape** (`omega_escape`): if some `f_k ≠ 0`, the polynomial
  `f₀ + f₁W + f₂W²` is nonzero of degree `≤ 2`, so an accepted `ω` is a root with probability `≤ errG gOmega 2`.
* The rounds (`eqSumcheckGSpec`) on `Σ_x eq(τ, x)·zeroGT ω (bits x)`, `zeroGT ω pt = zeroFinalT ω` of the nine
  columns' extensions at `pt` (`zeroGT_bits`: on the cube it is `Σ_k ω^k·rel_k`), degree 2 per coordinate.
* The nine values and the final check: doom of "the values are the columns' extensions at `r_x`" (`zeroSpecTT`).
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Polynomial Finset
open scoped ENNReal NNReal

/-! ## The columns and the table -/

/-- The nine columns at slot `x`: `A_j = M_{4j}`, `B_j = M_{1+4j}`, `C_j = M_{2+4j} + M_{3+4j}` (`j < 3`), in `E2`. -/
def colT (Q : Program) (lay : Lay) (z : ℕ → FK) (j x : ℕ) : E2 :=
  if j < 3 then FE2.toE2 (matZT Q lay (4 * j) z x)
  else if j < 6 then FE2.toE2 (matZT Q lay (1 + 4 * (j - 3)) z x)
  else FE2.toE2 (matZT Q lay (2 + 4 * (j - 6)) z x + matZT Q lay (3 + 4 * (j - 6)) z x)

/-- **The relation's coordinates as a table on 22 bits**: `rel_k(x)` at `x + 2^20·k`, `k < 3`. -/
def deltaZT (Q : Program) (lay : Lay) (z : ℕ → FK) (v : ℕ) : E2 :=
  if v / 2 ^ xVars < 3 then FE2.toE2 (relT Q lay z (v % 2 ^ xVars) (v / 2 ^ xVars)) else 0

/-- A column's extension at a point (`r_x`: 20 coordinates). The range is `2^|pt|`, never a literal: the kernel can
then never fall back to evaluating the `2^20`-element range in a defeq check (GOLF patterns). -/
def mleX (pt : List E2) (f : ℕ → E2) : E2 := ∑ w ∈ range (2 ^ pt.length), E2V.eqAtF pt w * f w

/-- The nine columns' extensions at `pt`. -/
def vals9 (Q : Program) (lay : Lay) (z : ℕ → FK) (pt : List E2) : List E2 :=
  (List.range 9).map fun j ↦ mleX pt (colT Q lay z j)

/-- **The zerocheck's summand**: `zeroFinalT ω` of the nine columns' extensions. -/
def zeroGT (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E2) (pt : List E2) : E2 :=
  zeroFinalT ω (vals9 Q lay z pt)

/-! ## Algebra -/

theorem mulY3_toE2 (a b : ℕ → FE2) (k : ℕ) :
    FE2.toE2 (mulY3 a b k) = mulY3 (fun j ↦ FE2.toE2 (a j)) (fun j ↦ FE2.toE2 (b j)) k := by
  rcases k with _ | _ | _ <;> simp [mulY3, FE2.toE2_add, FE2.fe2_mul_eq]

theorem mulY3_congr {R : Type} [Add R] [Mul R] {a a' b b' : ℕ → R} (ha : ∀ j < 3, a j = a' j)
    (hb : ∀ j < 3, b j = b' j) (k : ℕ) : mulY3 a b k = mulY3 a' b' k := by
  rcases k with _ | _ | _ <;>
    simp only [mulY3, ha 0 (by norm_num), ha 1 (by norm_num), ha 2 (by norm_num), hb 0 (by norm_num),
      hb 1 (by norm_num), hb 2 (by norm_num)]

theorem polyLEF_mulY3 {F : Type} [Field F] {a b : ℕ → F → F} (ha : ∀ j, PolyLEF 1 (a j))
    (hb : ∀ j, PolyLEF 1 (b j)) (k : ℕ) : PolyLEF 2 fun x ↦ mulY3 (fun j ↦ a j x) (fun j ↦ b j x) k := by
  have m : ∀ i j, PolyLEF 2 fun x ↦ a i x * b j x := fun i j ↦ PolyLEF.mul (ha i) (hb j)
  rcases k with _ | _ | _
  · exact PolyLEF.add (m 0 0) (PolyLEF.add (m 1 2) (m 2 1))
  · exact PolyLEF.add (PolyLEF.add (PolyLEF.add (m 0 1) (m 1 0)) (PolyLEF.add (m 1 2) (m 2 1))) (m 2 2)
  · exact PolyLEF.add (PolyLEF.add (PolyLEF.add (m 0 2) (m 1 1)) (m 2 0)) (m 2 2)

theorem zeroFinalT_eq (ω : E2) (v : List E2) :
    zeroFinalT ω v = ∑ k ∈ range 3, ω ^ k *
      (mulY3 (fun j ↦ v.getD j 0) (fun j ↦ v.getD (3 + j) 0) k + v.getD (6 + k) 0) := by
  rw [zeroFinalT, ← sumF_eq_sum, sumF_map_range]

theorem vals9_getD (Q : Program) (lay : Lay) (z : ℕ → FK) (pt : List E2) {j : ℕ} (hj : j < 9) :
    (vals9 Q lay z pt).getD j 0 = mleX pt (colT Q lay z j) := by
  rw [vals9, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

/-- `zeroGT` with its nine extensions spelled out. -/
theorem zeroGT_eq (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E2) (pt : List E2) :
    zeroGT Q lay z ω pt = ∑ k ∈ range 3, ω ^ k *
      (mulY3 (fun j ↦ mleX pt (colT Q lay z j)) (fun j ↦ mleX pt (colT Q lay z (3 + j))) k +
        mleX pt (colT Q lay z (6 + k))) := by
  rw [zeroGT, zeroFinalT_eq]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk3 := Finset.mem_range.mp hk
  rw [mulY3_congr (a' := fun j ↦ mleX pt (colT Q lay z j)) (b' := fun j ↦ mleX pt (colT Q lay z (3 + j)))
    (fun j hj ↦ vals9_getD Q lay z pt (by omega)) (fun j hj ↦ vals9_getD Q lay z pt (by omega)),
    vals9_getD Q lay z pt (by omega)]

theorem polyLEF_mleX (pre post : List E2) (f : ℕ → E2) : PolyLEF 1 fun x ↦ mleX (pre ++ x :: post) f :=
  (polyLEF_mle pre post (2 ^ (pre.length + post.length + 1)) f).congr fun x ↦ by
    rw [mleX, List.length_append, List.length_cons, Nat.add_assoc]

/-- **The summand has degree 2 in each coordinate.** -/
theorem polyLEF_zeroGT (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E2) (pre post : List E2) :
    PolyLEF 2 fun x ↦ zeroGT Q lay z ω (pre ++ x :: post) := by
  simp only [zeroGT_eq]
  refine PolyLEF.sum _ fun k _ ↦ PolyLEF.const_mul (PolyLEF.add ?_ ((polyLEF_mleX pre post _).mono (by norm_num))) _
  exact polyLEF_mulY3 (a := fun j x ↦ mleX (pre ++ x :: post) (colT Q lay z j))
    (b := fun j x ↦ mleX (pre ++ x :: post) (colT Q lay z (3 + j)))
    (fun j ↦ polyLEF_mleX pre post _) (fun j ↦ polyLEF_mleX pre post _) k

/-! ## On the cube -/

theorem mleX_bits {u : ℕ} (hu : u < 2 ^ xVars) (f : ℕ → E2) : mleX (bitsF u xVars) f = f u := by
  rw [mleX, bitsF_length]
  exact sum_eqAtF_bitsF hu f

/-- **On the cube, the summand is the batched relation**: `zeroGT ω (bits u) = Σ_k ω^k·rel_k(u)`. -/
theorem zeroGT_bits (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E2) {u : ℕ} (hu : u < 2 ^ xVars) :
    zeroGT Q lay z ω (bitsF u xVars) =
      ∑ k ∈ range 3, ω ^ k * deltaZT Q lay z (u + 2 ^ xVars * k) := by
  rw [zeroGT_eq]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk3 := Finset.mem_range.mp hk
  have h1 : (u + 2 ^ xVars * k) / 2 ^ xVars = k := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add]
  have h2 : (u + 2 ^ xVars * k) % 2 ^ xVars = u := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  rw [deltaZT, h1, if_pos hk3, h2, relT, FE2.toE2_add, FE2.toE2_add, mulY3_toE2,
    mulY3_congr (a' := fun j ↦ FE2.toE2 (matZT Q lay (4 * j) z u))
      (b' := fun j ↦ FE2.toE2 (matZT Q lay (1 + 4 * j) z u))
      (fun j hj ↦ by rw [mleX_bits hu, colT, if_pos hj])
      (fun j hj ↦ by rw [mleX_bits hu, colT, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]) k,
    mleX_bits hu, colT, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left, FE2.toE2_add]

/-- **The zerocheck's start**: the equality cube sum of the summand is `Σ_k ω^k·f_k`, `f_k` the folded
coordinates. -/
theorem zeroGT_cube (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E2) {τ : List E2} (hτ : τ.length = xVars) :
    eqCubeSumF τ xVars (zeroGT Q lay z ω) [] =
      ∑ k ∈ range 3, ω ^ k * foldTF (deltaZT Q lay z) τ k := by
  rw [eqCubeSumF_nil]
  simp only [foldTF, hτ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [zeroGT_bits Q lay z ω (Finset.mem_range.mp hu), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

theorem foldTF_three (Q : Program) (lay : Lay) (z : ℕ → FK) {τ : List E2} (hτ : τ.length = xVars) :
    foldTF (deltaZT Q lay z) τ 3 = 0 := by
  refine Finset.sum_eq_zero fun w hw ↦ ?_
  rw [hτ] at hw
  have h1 : (w + 2 ^ xVars * 3) / 2 ^ xVars = 3 := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (Finset.mem_range.mp hw), zero_add]
  rw [hτ, deltaZT, h1, if_neg (by norm_num), mul_zero]

/-! ## `ω`'s escape -/

/-- **`ω`'s escape** (degree 2 in `ω`): if one of three values is nonzero, an accepted `ω` makes
`f₀ + ωf₁ + ω²f₂` vanish with probability at most `errG g 2`. -/
theorem omega_escape {g : ℕ} (hg : g ≤ 64) (f : ℕ → E2) (hne : ∃ k < 3, f k ≠ 0) :
    avgE (fun c ↦ indE (powOK g c ∧ ∑ k ∈ range 3, e2OfE c ^ k * f k = 0)) ≤ errG g 2 := by
  set p : E2[X] := C (f 0) + C (f 1) * X + C (f 2) * X ^ 2 with hp
  have hc : ∀ k < 3, p.coeff k = f k := by
    intro k hk
    interval_cases k <;> simp [hp, coeff_X, coeff_X_pow, coeff_C]
  have hp0 : p ≠ 0 := by
    obtain ⟨k, hk, hfk⟩ := hne
    intro h
    exact hfk (by rw [← hc k hk, h, coeff_zero])
  have hdeg : p.natDegree ≤ 2 := by
    rw [hp]
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
    · exact (natDegree_C _).trans_le (by norm_num)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  refine (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨h.1, ?_⟩).trans (sampleG_escape hg hp0 (q := 0) hdeg (by simp))
  rw [eval_zero, ← h.2, hp]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-! ## The phase -/

section Phase

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **The separator keeps doom**; lead `L₀·0 + T`. -/
noncomputable def sepSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (A : β → Prop) :
    Spec e2Sep (Doomed C A) (fun _ h ↦ Doomed C A h) εmax ((L₀ : ℝ≥0∞) * 0 + T) T :=
  (doomSample (εmax := εmax) (T := T) hst hcard A (fun _ ↦ A) 0
      (fun q hq ↦ avgE_le_of_le fun c ↦ (indE_of_not hq).le)).bind' fun _ ↦
    Spec.ret (Post := fun _ h ↦ Doomed C A h) ()

variable (Q : Program) (lay : Lay) (zq : β → ℕ → FK) (R : β → Prop)

/-- **The zerocheck at `E2`**: from doom of the relation's table on the cube to doom of "the nine values are the
columns' extensions at `r_x`"; lead `0`; groups `τ_i` (`errG gTau 1`), `ω` (`errG gOmega 2`), rounds
(`errG gZero 2`), each with follower `0`. -/
noncomputable def zeroSpecTT (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (hτ : (L₀ : ℝ≥0∞) * errG gTau 1 + 0 ≤ εmax) (hω : (L₀ : ℝ≥0∞) * errG gOmega 2 + 0 ≤ εmax)
    (hz : (L₀ : ℝ≥0∞) * errG gZero 2 + 0 ≤ εmax) (hT : T ≤ εmax) :
    Spec zeroProgT (Doomed C (fun q ↦ ZeroOnF (deltaZT Q lay (zq q)) [] (xVars + 2) ∧ R q))
      (fun r h ↦ r.1.length = xVars ∧ r.2.length = 9 ∧
        Doomed C (fun q ↦ r.2 = vals9 Q lay (zq q) r.1 ∧ R q) h) εmax 0 T := by
  unfold zeroProgT
  refine ((sepSpec (T := 0) hst hcard _).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind'
    fun _ ↦ ?_
  refine (zeroSpecE2 (T := 0) hst hcard (g := gTau) (by norm_num) (fun q ↦ deltaZT Q lay (zq q)) R
    (n := xVars + 2) (m := xVars - 1) (by norm_num) hτ).bind' fun τ ↦ ?_
  exact if hτl : τ.length = xVars then
    ((doomE2SampleSpec (T := 0) hst hcard (fun q ↦ ZeroOnF (deltaZT Q lay (zq q)) τ (xVars + 2) ∧ R q)
        (fun ω q ↦ ∑ k ∈ range 3, ω ^ k * foldTF (deltaZT Q lay (zq q)) τ k = 0 ∧ R q) (errG gOmega 2)
        (fun q hq ↦ by
          by_cases hR : R q
          · have hne : ∃ k < 3, foldTF (deltaZT Q lay (zq q)) τ k ≠ 0 := by
              by_contra hall
              push Not at hall
              refine hq ⟨fun v hv ↦ ?_, hR⟩
              rw [hτl, show xVars + 2 - xVars = 2 by omega] at hv
              by_cases hv3 : v < 3
              · exact hall v hv3
              · rw [show v = 3 by omega]; exact foldTF_three Q lay (zq q) hτl
            exact (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨h.1, h.2.1⟩).trans
              (omega_escape (by norm_num) _ hne)
          · exact avgE_le_of_le fun c ↦ (indE_of_not fun h ↦ hR h.2.2).le.trans zero_le) hω).mono
      (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ω ↦
    ((eqSumcheckGSpec (T := 0) hst hcard R (Fm := fun q acc ↦ eqCubeSumF τ xVars (zeroGT Q lay (zq q) ω) acc)
        (eqCubeSumF_eqFamily τ xVars 2 hτl _ fun q pre post ↦ polyLEF_zeroGT Q lay (zq q) ω pre post)
        (count := 3) (by norm_num) (by norm_num) (g := gZero) (by norm_num) hz τ [] 0 (by simp)).mono
      (fun _ hp ↦ Doomed.mono hp fun q hq ↦ ⟨by rw [← zeroGT_cube Q lay (zq q) ω hτl]; exact hq.1.symm, hq.2⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl zero_le).bind' fun rf ↦
    if hrf : rf.1.length = xVars then
      ((e2ReadsSpec hst (fun q ↦ rf.2 = eqCubeSumF τ xVars (zeroGT Q lay (zq q) ω) ([] ++ rf.1) ∧ R q)
          hT 8).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl zero_le le_rfl).bind' fun v ↦
        (Spec.require (Pre := fun h ↦ v.length = 9 ∧ Doomed C (fun q ↦
            rf.2 = eqCubeSumF τ xVars (zeroGT Q lay (zq q) ω) ([] ++ rf.1) ∧ R q) h)
          (Post := fun _ h ↦ v.length = 9 ∧ Doomed C (fun q ↦ v = vals9 Q lay (zq q) rf.1 ∧ R q) h)
          fun _ hp hc ↦ ⟨hp.1, Doomed.mono hp.2 fun q hq ↦ ⟨by
            rw [List.nil_append, eqCubeSumF_full _ _ _ hrf hτl, hc, zeroGT, hq.1], hq.2⟩⟩).bind' fun _ ↦
          (Spec.ret (Post := fun r h ↦ r.1.length = xVars ∧ r.2.length = 9 ∧
              Doomed C (fun q ↦ r.2 = vals9 Q lay (zq q) r.1 ∧ R q) h) (rf.1, v)).mono
            (fun _ hp ↦ ⟨hrf, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hrf (hp.1.trans (by simp [hτl]))) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hτl (hp.1.trans (by norm_num))) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Phase

end Lvm.E2T
