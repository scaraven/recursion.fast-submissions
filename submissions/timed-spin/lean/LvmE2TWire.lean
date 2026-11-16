-- New for lvm2 E2-FT (stage S2GT, E2F-T): the wiring at `E2` (`wireProgT`): `γ` over the nine values (degree 8),
-- 21 plain rounds on the twelve matrices' batch times `z̃`, the matrix and region values, the final check.
import LvmE2TZero
import LvmE2TRegion
import LvmE2TAcc
import LvmTypedSpecXP

/-!
# The wiring at `E2` (S2GT)

* **The entry form** (`colT_sum`, `vals9_batch`): `Σ_k γ^k·vals9_k(r_x) = Σ_{e ∈ entsT} γ^{kT(e.o)}·c_e·eq(r_x, x_e)·z(y_e)`,
  `kT(m + 4j)` the value index of slot `m + 4j` (`A_j ↦ j`, `B_j ↦ 3 + j`, `C_j ↦ 6 + j`).
* **The family** (`wireGT`): `wireMT γ r_x pt · z̃(pt)` with `wireMT γ r_x pt = Σ_e γ^{kT(e.o)}·c_e·eq(r_x ++ pt, x_e + 2^20 y_e)`,
  degree 2 in each of `y`'s coordinates; its cube sum is the batch (`wire_nilT`).
* **`γ`'s escape** (`gamma_escape`): a wrong nine-tuple batched by `γ` meets the true one at a root of a nonzero
  polynomial of degree `≤ 8`.
* **`wireSpecTT`**: from doom of "the nine values are true" to doom of "the twelve matrix values and the region
  values are true".
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Polynomial Finset
open scoped ENNReal NNReal

/-! ## The entries at `E2` -/

/-- **Every entry at `E2` lies on the cube** (a checked layout): `o' < 12`, `x < 2^20`, `y < 2^21`. -/
theorem entsT_fit (Q : Program) (lay : Lay) (hlay : lay.Ok Q) :
    ∀ e ∈ entsT Q lay, e.o < 12 ∧ e.x < 2 ^ xVars ∧ e.y < 2 ^ yVars := by
  intro e he
  refine ⟨entsT_o Q lay e he, ?_⟩
  obtain ⟨e₀, he₀, hs⟩ := List.mem_flatMap.mp he
  obtain ⟨j, -, hje⟩ := List.mem_filterMap.mp hs
  have hf := entsX_fit Q lay hlay e₀ he₀
  split at hje
  · exact absurd hje (by simp)
  · rw [Option.some.injEq] at hje
    rw [← hje]
    exact ⟨hf.2.1, hf.2.2⟩

/-- The value index of slot `o' = m + 4j`: `A_j ↦ j`, `B_j ↦ 3 + j`, `C_j` (`D`, `W`) `↦ 6 + j`. -/
def kT (o : ℕ) : ℕ := (if o % 4 = 0 then 0 else if o % 4 = 1 then 3 else 6) + o / 4

/-- Slot `o` contributes to value `k`. -/
def inO (k o : ℕ) : Prop :=
  (k < 3 ∧ o = 4 * k) ∨ (3 ≤ k ∧ k < 6 ∧ o = 1 + 4 * (k - 3)) ∨
    (6 ≤ k ∧ k < 9 ∧ (o = 2 + 4 * (k - 6) ∨ o = 3 + 4 * (k - 6)))

instance (k o : ℕ) : Decidable (inO k o) := by unfold inO; infer_instance

theorem inO_iff {k o : ℕ} (ho : o < 12) : inO k o ↔ k = kT o := by
  unfold inO kT
  split_ifs <;> omega

theorem kT_lt {o : ℕ} (ho : o < 12) : kT o < 9 := by
  unfold kT
  split_ifs <;> omega

theorem sum_inO (γ : E2) {o : ℕ} (ho : o < 12) :
    ∑ k ∈ range 9, (if inO k o then γ ^ k else 0) = γ ^ kT o := by
  rw [Finset.sum_congr rfl fun k _ ↦ if_congr (inO_iff ho) rfl rfl, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr (kT_lt ho))]

/-- `toE2` of a filtered fold is the indicator sum. -/
theorem toE2_foldr_filter (l : List EntT) (p : EntT → Bool) (g : EntT → FE2) :
    FE2.toE2 ((l.filter p).foldr (fun e acc ↦ g e + acc) 0) =
      (l.map fun e ↦ if p e then FE2.toE2 (g e) else 0).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    by_cases hp : p e
    · simp [List.filter_cons, hp, FE2.toE2_add, ih]
    · simp [List.filter_cons, hp, ih]

/-- **A column at a slot as an entry sum.** -/
theorem colT_sum (Q : Program) (lay : Lay) (z : ℕ → FK) {k : ℕ} (hk : k < 9) (x : ℕ) :
    colT Q lay z k x = ((entsT Q lay).map fun e ↦
      if inO k e.o ∧ e.x = x then FE2.toE2 e.c * zwT z e.y else 0).sum := by
  have hm : ∀ o, FE2.toE2 (matZT Q lay o z x) = ((entsT Q lay).map fun e ↦
      if e.o = o ∧ e.x = x then FE2.toE2 e.c * zwT z e.y else 0).sum := fun o ↦ by
    unfold matZT
    rw [toE2_foldr_filter]
    refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
    simp only [Bool.and_eq_true, beq_iff_eq, FE2.fe2_mul_eq, zwT, kE2]
  unfold colT
  split_ifs with h3 h6
  · rw [hm]
    refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
    simp only [inO]
    congr 1
    apply propext; omega
  · rw [hm]
    refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
    simp only [inO]
    congr 1
    apply propext; omega
  · rw [FE2.toE2_add, hm, hm, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
    by_cases h2 : e.o = 2 + 4 * (k - 6) ∧ e.x = x
    · have h3' : ¬ (e.o = 3 + 4 * (k - 6) ∧ e.x = x) := fun h ↦ by omega
      have hi : inO k e.o ∧ e.x = x := ⟨by unfold inO; omega, h2.2⟩
      rw [if_pos h2, if_neg h3', if_pos hi, add_zero]
    · by_cases h3'' : e.o = 3 + 4 * (k - 6) ∧ e.x = x
      · have hi : inO k e.o ∧ e.x = x := ⟨by unfold inO; omega, h3''.2⟩
        rw [if_neg h2, if_pos h3'', if_pos hi, zero_add]
      · have hi : ¬ (inO k e.o ∧ e.x = x) := fun h ↦ by unfold inO at h; omega
        rw [if_neg h2, if_neg h3'', if_neg hi, add_zero]

/-- **Collapsing a slot sum**: a weighted sum over the slots of per-slot entry sums is the entry sum, every entry's
slot being below `N`. -/
theorem sum_slot_collapse (l : List EntT) (N : ℕ) (hl : ∀ e ∈ l, e.x < N) (P : EntT → Prop) [DecidablePred P]
    (w : ℕ → E2) (f : EntT → E2) :
    ∑ x ∈ range N, w x * (l.map fun e ↦ if P e ∧ e.x = x then f e else 0).sum =
      (l.map fun e ↦ if P e then w e.x * f e else 0).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := hl e (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib,
      ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')]
    congr 1
    by_cases hP : P e
    · simp only [hP, true_and, if_true]
      rw [Finset.sum_eq_single e.x (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero])
        (fun h ↦ absurd (Finset.mem_range.mpr he) h), if_pos rfl]
    · simp [hP]

/-- **A column's extension at `r_x` as an entry sum** (the entries' slots are on the cube). -/
theorem mleX_colT (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) {k : ℕ} (hk : k < 9)
    {rx : List E2} (hrx : rx.length = xVars) :
    mleX rx (colT Q lay z k) = ((entsT Q lay).map fun e ↦
      if inO k e.o then E2V.eqAtF rx e.x * (FE2.toE2 e.c * zwT z e.y) else 0).sum := by
  have hb : ∀ e ∈ entsT Q lay, e.x < 2 ^ rx.length := fun e he ↦ hrx ▸ (entsT_fit Q lay hlay e he).2.1
  rw [mleX, ← sum_slot_collapse _ _ hb (fun e ↦ inO k e.o) _ _]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [colT_sum Q lay z hk x]

/-- **Collapsing the value index**: `Σ_k γ^k·(entries of value k)` is the entry sum at `γ^{kT}`. -/
theorem sum_k_collapse (l : List EntT) (hl : ∀ e ∈ l, e.o < 12) (γ : E2) (a : EntT → E2) :
    ∑ k ∈ range 9, γ ^ k * (l.map fun e ↦ if inO k e.o then a e else 0).sum =
      (l.map fun e ↦ γ ^ kT e.o * a e).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib,
      ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')]
    congr 1
    rw [← sum_inO γ (hl e (List.mem_cons_self ..)), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> simp

/-- **Collapsing a position sum**: `Σ_{u<N} (entries at position u)` is the entry sum. -/
theorem sum_pos_collapse {α : Type} (l : List α) (pos : α → ℕ) (N : ℕ) (hl : ∀ e ∈ l, pos e < N)
    (f : α → E2) : ∑ u ∈ range N, (l.map fun e ↦ if pos e = u then f e else 0).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib,
      ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hl e (List.mem_cons_self ..)))]

/-- **The nine values batched by `γ`, as an entry sum.** -/
theorem vals9_batch (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E2) {rx : List E2}
    (hrx : rx.length = xVars) :
    wBatchT γ (vals9 Q lay z rx) = ((entsT Q lay).map fun e ↦
      γ ^ kT e.o * (E2V.eqAtF rx e.x * (FE2.toE2 e.c * zwT z e.y))).sum := by
  have hb : wBatchT γ (vals9 Q lay z rx) = ∑ k ∈ range 9, γ ^ k * mleX rx (colT Q lay z k) := by
    rw [wBatchT, ← sumF_eq_sum, sumF_map_range]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [vals9_getD Q lay z rx (Finset.mem_range.mp hk)]
  rw [hb, Finset.sum_congr rfl fun k hk ↦ by rw [mleX_colT Q lay hlay z (Finset.mem_range.mp hk) hrx]]
  exact sum_k_collapse _ (fun e he ↦ (entsT_fit Q lay hlay e he).1) γ _

/-! ## The family -/

/-- **The twelve matrices batched by `γ`** at `(r_x, pt)`, as an entry sum. -/
def wireMT (Q : Program) (lay : Lay) (γ : E2) (rx pt : List E2) : E2 :=
  ((entsT Q lay).map fun e ↦ γ ^ kT e.o * (FE2.toE2 e.c * E2V.eqAtF (rx ++ pt) (e.x + 2 ^ xVars * e.y))).sum

/-- **The wiring's summand**: the batched matrices times `z̃`. -/
def wireGT (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E2) (rx pt : List E2) : E2 :=
  wireMT Q lay γ rx pt * mleYT pt (zwT z)

/-- **An `E2` extension sum over any range is affine in each coordinate** (stated with `E2`'s own sum, proved at a
symbolic `N`: the generic lemma's sum carries the field's instance path, which must never be compared with
`E2`'s at a literal range — the kernel would evaluate the range). -/
theorem polyLEF_sumE2 (N : ℕ) (pre post : List E2) (f : ℕ → E2) :
    PolyLEF 1 fun x ↦ ∑ w ∈ range N, E2V.eqAtF (pre ++ x :: post) w * f w :=
  polyLEF_mle pre post N f

/-- `sum_eqAtF_bitsF` with `E2`'s own sum, at a symbolic `m`. -/
theorem sum_eqAtF_bitsE2 {m z : ℕ} (hz : z < 2 ^ m) (G : ℕ → E2) :
    ∑ w ∈ range (2 ^ m), E2V.eqAtF (bitsF z m : List E2) w * G w = G z :=
  sum_eqAtF_bitsF hz G

/-- `PolyLEF.mul` stated with `E2`'s own product, on abstract factors (the field's instance path meets `E2`'s only
here, where nothing can be evaluated). -/
theorem polyLEF_mulE2 {f g : E2 → E2} (hf : PolyLEF 1 f) (hg : PolyLEF 1 g) : PolyLEF 2 fun x ↦ f x * g x :=
  PolyLEF.mul hf hg

theorem polyLEF_wireMT (Q : Program) (lay : Lay) (γ : E2) (rx pre post : List E2) :
    PolyLEF 1 fun x ↦ wireMT Q lay γ rx (pre ++ x :: post) := by
  refine polyLEF_listSum 1 _ _ fun e _ ↦ PolyLEF.const_mul (PolyLEF.const_mul ?_ _) _
  have := polyLEF_eqAtF (rx ++ pre) post (e.x + 2 ^ xVars * e.y)
  simpa only [List.append_assoc] using this

theorem polyLEF_mleYT (pre post : List E2) (f : ℕ → E2) : PolyLEF 1 fun x ↦ mleYT (pre ++ x :: post) f :=
  (polyLEF_sumE2 (2 ^ (pre.length + post.length + 1)) pre post f).congr fun x ↦ by
    rw [mleYT, List.length_append, List.length_cons, Nat.add_assoc]

/-- **The summand has degree 2 in each of `y`'s coordinates.** -/
theorem polyLEF_wireGT (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E2) (rx pre post : List E2) :
    PolyLEF 2 fun x ↦ wireGT Q lay z γ rx (pre ++ x :: post) :=
  polyLEF_mulE2 (polyLEF_wireMT Q lay γ rx pre post) (polyLEF_mleYT pre post (zwT z))

/-- `wire_nilT` at a symbolic number `n = yVars` of `y`'s coordinates (no literal range meets a defeq check). -/
theorem wire_nil_gen (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E2) {rx : List E2}
    (hrx : rx.length = xVars) (n : ℕ) (hn : yVars = n) :
    tCubeSumF n (wireGT Q lay z γ rx) [] = wBatchT γ (vals9 Q lay z rx) := by
  have hfit := entsT_fit Q lay hlay
  have hy : ∀ e ∈ entsT Q lay, e.y < 2 ^ n := fun e he ↦ hn ▸ (hfit e he).2.2
  rw [tCubeSumF_nil, vals9_batch Q lay hlay z γ hrx]
  have hpt : ∀ u < 2 ^ n, ∀ e ∈ entsT Q lay,
      E2V.eqAtF (rx ++ bitsF u n) (e.x + 2 ^ xVars * e.y) =
        E2V.eqAtF rx e.x * (if e.y = u then 1 else 0) := fun u hu e he ↦ by
    have hx := (hfit e he).2.1
    rw [eqAtF_append, eqAtF_mod rx, hrx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add,
      eqAtF_bitsF_lt hu (hy e he)]
  have hmle : ∀ u < 2 ^ n, mleYT (bitsF u n) (zwT z) = zwT z u := fun u hu ↦ by
    rw [mleYT, bitsF_length]
    exact sum_eqAtF_bitsE2 hu _
  have hu : ∀ u ∈ range (2 ^ n), wireGT Q lay z γ rx (bitsF u n) =
      ((entsT Q lay).map fun e ↦ if e.y = u then
        γ ^ kT e.o * (E2V.eqAtF rx e.x * (FE2.toE2 e.c * zwT z e.y)) else 0).sum := fun u hu ↦ by
    have hu' := Finset.mem_range.mp hu
    rw [wireGT, wireMT, hmle u hu', ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    rw [hpt u hu' e he]
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [Finset.sum_congr rfl hu]
  exact sum_pos_collapse (entsT Q lay) EntT.y (2 ^ n) hy _

/-- **The wiring's start is the batch of the nine true values** (`r_x` of 20 coordinates). -/
theorem wire_nilT (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E2) {rx : List E2}
    (hrx : rx.length = xVars) :
    tCubeSumF yVars (wireGT Q lay z γ rx) [] = wBatchT γ (vals9 Q lay z rx) :=
  wire_nil_gen Q lay hlay z γ hrx yVars rfl

/-! ## `γ`'s escape -/

theorem wBatchT_eq (γ : E2) (v : List E2) : wBatchT γ v = ∑ k ∈ range 9, γ ^ k * v.getD k 0 := by
  rw [wBatchT, ← sumF_eq_sum, sumF_map_range]

/-- **`γ`'s escape** (degree 8): two different nine-tuples batched by an accepted `γ` agree with probability at
most `errG g 8`. -/
theorem gamma_escape {g : ℕ} (hg : g ≤ 64) {v w : List E2} (hv : v.length = 9) (hw : w.length = 9)
    (hne : v ≠ w) :
    avgE (fun c ↦ indE (powOK g c ∧ wBatchT (e2OfE c) v = wBatchT (e2OfE c) w)) ≤ errG g 8 := by
  set p : E2[X] := ∑ k ∈ range 9, C (v.getD k 0 - w.getD k 0) * X ^ k with hp
  obtain ⟨k, hk, hvk⟩ : ∃ k < 9, v.getD k 0 ≠ w.getD k 0 := by
    by_contra hall
    push Not at hall
    refine hne (List.ext_getElem (hv.trans hw.symm) fun i hi _ ↦ ?_)
    have := hall i (by omega)
    rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at this
  have hp0 : p ≠ 0 := by
    intro h
    have hc := congrArg (coeff · k) h
    simp only [hp, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_zero] at hc
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)] at hc
    exact hvk (sub_eq_zero.mp hc)
  have hdeg : p.natDegree ≤ 8 := by
    rw [hp]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  refine (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨h.1, ?_⟩).trans (sampleG_escape hg hp0 (q := 0) hdeg (by simp))
  rw [eval_zero, hp, eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have h2 := h.2
  rw [wBatchT_eq, wBatchT_eq] at h2
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
  exact (Finset.sum_congr rfl fun i _ ↦ by ring).trans h2

/-! ## The final check -/

theorem wGT_eq (γ : E2) (vs : List E2) : wGT γ vs = ∑ o ∈ range 12, γ ^ kT o * vs.getD o 0 := by
  simp only [wGT, ← sumF_eq_sum, sumF_map_range, Finset.sum_range_succ, Finset.sum_range_zero, kT]
  norm_num
  ring

/-- **The batched matrices at `(r_x, r_y)` are the twelve matrix values batched** (`wGT`), when they are true. -/
theorem wireMT_vs (Q : Program) (lay : Lay) (γ : E2) (rx ry vs : List E2) (hvs : vs.length = 12)
    (hV : ∀ o < 12, vs.getD o 0 = matMleT Q lay o (rx ++ ry)) : wireMT Q lay γ rx ry = wGT γ vs := by
  have hall : ∀ o < 2 ^ selBitsT, γ ^ kT o * vs.getD o 0 = γ ^ kT o * matMleT Q lay o (rx ++ ry) := by
    intro o ho
    by_cases h12 : o < 12
    · rw [hV o h12]
    · rw [List.getD_eq_default _ _ (by omega), matMleT_eq_sum,
        List.filter_eq_nil_iff.mpr fun e he ↦ by have := entsT_o Q lay e he; simp only [beq_iff_eq]; omega]
      simp
  rw [wGT_eq, show ∑ o ∈ range 12, γ ^ kT o * vs.getD o 0 = ∑ o ∈ range (2 ^ selBitsT), γ ^ kT o * vs.getD o 0
    by rw [show 2 ^ selBitsT = 12 + 4 by rfl, Finset.sum_range_add, left_eq_add]
       exact Finset.sum_eq_zero fun x _ ↦ by rw [List.getD_eq_default _ _ (by omega), mul_zero],
    Finset.sum_congr rfl fun o ho ↦ hall o (Finset.mem_range.mp ho)]
  simp only [matMleT_eq_sum]
  rw [sum_sel_filterT (fun o ↦ γ ^ kT o) _ _ fun e he ↦ by have := entsT_o Q lay e he; simp [selBitsT]; omega]
  rfl

theorem sumF_four (rv : List E2) (h : rv.length = 4) :
    sumF rv = rv.getD 0 0 + rv.getD 1 0 + rv.getD 2 0 + rv.getD 3 0 := by
  match rv, h with
  | [a, b, c, d], _ => simp [sumF_eq_sum, add_assoc]

/-! ## The phase -/

section Phase

variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (R : Column L.nuMain × Column L.nuRec → Prop)

/-- A candidate's words. -/
abbrev zT (q : Column L.nuMain × Column L.nuRec) : ℕ → FK := Ti.zOf L pub q.1 q.2

/-- The twelve matrix values are the matrices' extensions at `r_x ++ r_y`. -/
def VsTrueT (rxy vs : List E2) : Prop := ∀ o < 12, vs.getD o 0 = matMleT Ti.Q Ti.lay o rxy

/-- The four region values (committed, `S_flat`, `σ′`, `KS`) are true at `r_y`. -/
def RegsT (ry rv : List E2) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  rv.getD 0 0 = regSumT Ti (· == .com) (zwT (zT Ti L pub q)) ry ∧
    rv.getD 1 0 = regSumT Ti (· == .sflat) (zwT (zT Ti L pub q)) ry ∧
    rv.getD 2 0 = regSumT Ti (· == .sigma) (zwT (zT Ti L pub q)) ry ∧
    rv.getD 3 0 = regSumT Ti (· == .ks) (zwT (zT Ti L pub q)) ry

/-- The committed, `σ′` and `KS` region values are true at `r_y` (`RegsT` without `S_flat`'s, which the relayout
consumes). -/
def Regs3T (ry rv : List E2) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  rv.getD 0 0 = regSumT Ti (· == .com) (zwT (zT Ti L pub q)) ry ∧
    rv.getD 2 0 = regSumT Ti (· == .sigma) (zwT (zT Ti L pub q)) ry ∧
    rv.getD 3 0 = regSumT Ti (· == .ks) (zwT (zT Ti L pub q)) ry

variable {L₀ : ℕ} {εmax T : ℝ≥0∞} {C : List Ev → Set (Column L.nuMain × Column L.nuRec)}

/-- **The wiring at `E2`** (`γ`, 21 plain rounds, the twelve matrix and four region values, the final check):
from doom of "the nine values are true at `r_x`" to doom of "the matrix values and the region values are true";
lead `0`; groups `γ` (`errG gGamma 8`) and the rounds (`errG gWire 2`). -/
noncomputable def wireSpecTT (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (hTi : Ti.Ok)
    (hγ : (L₀ : ℝ≥0∞) * errG gGamma 8 + 0 ≤ εmax) (hw : (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax) (hT : T ≤ εmax)
    (rx v : List E2) :
    Spec (wireProgT Ti pub v)
      (fun h ↦ rx.length = xVars ∧ v.length = 9 ∧
        Doomed C (fun q ↦ v = vals9 Ti.Q Ti.lay (zT Ti L pub q) rx ∧ R q) h)
      (fun w h ↦ w.1.length = yVars ∧ w.2.1.length = 12 ∧ w.2.2.length = 4 ∧
        Doomed C (fun q ↦ VsTrueT Ti (rx ++ w.1) w.2.1 ∧ RegsT Ti L pub w.1 w.2.2 q ∧ R q) h) εmax 0 T := by
  exact if hz : rx.length = xVars ∧ v.length = 9 then by
    unfold wireProgT
    refine ((doomE2SampleSpec (T := 0) hst hcard (fun q ↦ v = vals9 Ti.Q Ti.lay (zT Ti L pub q) rx ∧ R q)
      (fun γ q ↦ wBatchT γ v = tCubeSumF yVars (wireGT Ti.Q Ti.lay (zT Ti L pub q) γ rx) [] ∧ R q)
      (errG gGamma 8) (fun q hq ↦ by
        by_cases hR : R q
        · have hne : v ≠ vals9 Ti.Q Ti.lay (zT Ti L pub q) rx := fun h ↦ hq ⟨h, hR⟩
          refine (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨h.1, ?_⟩).trans
            (gamma_escape (by norm_num) hz.2 (by simp [vals9]) hne)
          rw [h.2.1, wire_nilT Ti.Q Ti.lay hTi.1 _ _ hz.1]
        · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
            ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)) hγ).mono
      (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun γ ↦ ?_
    refine (sumcheckGSpec (T := 0) hst hcard R
      (Fm := fun q acc ↦ tCubeSumF yVars (wireGT Ti.Q Ti.lay (zT Ti L pub q) γ rx) acc)
      (tCubeSumF_plainFamily yVars 2 _ fun q pre post ↦ polyLEF_wireGT _ _ _ γ rx pre post)
      (count := 3) (by norm_num) (by norm_num) (g := gWire) (by norm_num) hw yVars [] _ (by simp)).bind'
      fun rf ↦ ?_
    exact if hry : rf.1.length = yVars then
      ((e2ReadsSpec hst (fun q ↦ rf.2 = tCubeSumF yVars (wireGT Ti.Q Ti.lay (zT Ti L pub q) γ rx) ([] ++ rf.1) ∧
          R q) zero_le 11).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun vs ↦
      if hvs : vs.length = 12 then
        ((e2ReadsSpec hst (fun q ↦ rf.2 = tCubeSumF yVars (wireGT Ti.Q Ti.lay (zT Ti L pub q) γ rx) ([] ++ rf.1) ∧
            R q) hT 3).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun rv ↦
        if hrv : rv.length = 4 then
          (Spec.require (Pre := fun h ↦ rv.length = 3 + 1 ∧ Doomed C (fun q ↦
              rf.2 = tCubeSumF yVars (wireGT Ti.Q Ti.lay (zT Ti L pub q) γ rx) ([] ++ rf.1) ∧ R q) h)
            (Post := fun _ h ↦ Doomed C (fun q ↦ VsTrueT Ti (rx ++ rf.1) vs ∧ RegsT Ti L pub rf.1 rv q ∧ R q) h)
            fun _ hp hc ↦ Doomed.mono hp.2 fun q ⟨hV, ⟨h0, h1, h2, h3⟩, hR⟩ ↦ ⟨by
              rw [List.nil_append, tCubeSumF_full _ _ hry, wireGT, wireMT_vs Ti.Q Ti.lay γ rx rf.1 vs hvs hV,
                mleZ_zOfT Ti L pub hTi q.1 q.2 hry, hc, sumF_four rv hrv, h0, h1, h2, h3], hR⟩).bind' fun _ ↦
            (Spec.ret (Post := fun w h ↦ w.1.length = yVars ∧ w.2.1.length = 12 ∧ w.2.2.length = 4 ∧
                Doomed C (fun q ↦ VsTrueT Ti (rx ++ w.1) w.2.1 ∧ RegsT Ti L pub w.1 w.2.2 q ∧ R q) h)
              (rf.1, vs, rv)).mono (fun _ hp ↦ ⟨hry, hvs, hrv, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hp ↦ hrv hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
      else Spec.dead.mono (fun _ hp ↦ hvs hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ hp ↦ hry hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hz ⟨hp.1, hp.2.1⟩) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **The relayout at `E2`** (19 plain rounds, `v_R`, the final check): from doom of the region values at `r_y`
to doom of `C_rec`'s extension at the point with the other three region values, the rest carried; lead `0`,
follower `Tf`. -/
noncomputable def relaySpecTT (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (hTi : Ti.Ok) (hmaps : Ti.MapsFit L)
    (hrec : L.nuRec = relayRounds) (hw : (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax) {Tf : ℝ≥0∞} (hTf : Tf ≤ εmax)
    (A : Column L.nuMain × Column L.nuRec → Prop) (ry rv : List E2) :
    Spec (relayProgT Ti ry (rv.getD 1 0))
      (Doomed C (fun q ↦ RegsT Ti L pub ry rv q ∧ A q))
      (fun r h ↦ r.1.length = relayRounds ∧ Doomed C (fun q ↦
        r.2 = (∑ w ∈ range (2 ^ L.nuRec), E2V.eqAtF r.1 w * recT q.2 w) ∧ Regs3T Ti L pub ry rv q ∧ A q) h)
      εmax 0 Tf := by
  unfold relayProgT
  refine ((sumcheckGSpec (T := 0) hst hcard (fun q ↦ Regs3T Ti L pub ry rv q ∧ A q)
    (Fm := fun q acc ↦ tCubeSumF L.nuRec (relayGTT Ti ry L.nuRec (recT q.2)) acc)
    (tCubeSumF_plainFamily L.nuRec 2 _ fun q pre post ↦ polyLEF_relayGTT Ti ry L.nuRec (recT q.2) pre post)
    (count := 3) (by norm_num) (by norm_num) (g := gWire) (by norm_num) hw relayRounds [] _
    (by simp [hrec])).mono
    (fun _ hp ↦ Doomed.mono hp fun q hq ↦ ⟨⟨hq.2.1.1, by rw [hq.1, relay_trueT Ti L pub hTi hmaps q.1 q.2 ry],
      hq.2.1.2⟩, hq.2.2⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun rf ↦ ?_
  exact if hrr : rf.1.length = relayRounds then
    ((e2ReadSpec hst (fun q ↦ rf.2 = tCubeSumF L.nuRec (relayGTT Ti ry L.nuRec (recT q.2)) ([] ++ rf.1) ∧
        Regs3T Ti L pub ry rv q ∧ A q) hTf).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
      fun vR ↦
      (Spec.require (Pre := Doomed C (fun q ↦
            rf.2 = tCubeSumF L.nuRec (relayGTT Ti ry L.nuRec (recT q.2)) ([] ++ rf.1) ∧ Regs3T Ti L pub ry rv q ∧ A q))
          (Post := fun _ h ↦ Doomed C (fun q ↦
            vR = (∑ w ∈ range (2 ^ L.nuRec), E2V.eqAtF rf.1 w * recT q.2 w) ∧ Regs3T Ti L pub ry rv q ∧ A q) h)
          fun _ hp hc ↦ Doomed.mono hp fun q hq ↦ ⟨by
            rw [List.nil_append, tCubeSumF_full _ _ (hrr.trans hrec.symm), relayGTT, hc, hq.1], hq.2⟩).bind'
        fun _ ↦
        (Spec.ret (Post := fun r h ↦ r.1.length = relayRounds ∧ Doomed C (fun q ↦
            r.2 = (∑ w ∈ range (2 ^ L.nuRec), E2V.eqAtF r.1 w * recT q.2 w) ∧ Regs3T Ti L pub ry rv q ∧ A q) h)
          (rf.1, vR)).mono (fun _ hp ↦ ⟨hrr, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hrr hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Phase

end Lvm.E2T
