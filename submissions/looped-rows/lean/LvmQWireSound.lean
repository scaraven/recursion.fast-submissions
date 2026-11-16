-- New for lvm2 (T-Q): the wire gadget's closed forms (`LvmQEqWire`) against V_S's `FE` evaluators
-- (T-V's `msEvalF`, `thrEvalF`, through `FE.toExt3` and T-K's `msEvalA_bitsE`, `thrEvalA_bitsE`).
import LvmVEqWire
import LvmQSigDefs
import LvmQWire
import LvmQEqKeccakTape

-- ===== merged from `LvmQEqWire` (GOLF module merge: `LvmQEqWire.lean` is now a stub importing `LvmQWireSound`) =====
section
-- New for lvm2 (T-Q): Q_arith_eq of the S2 wiring gadget's blocks (`LvmQWire`), part 1: the
-- closed forms the rows compute. The proofs follow v1's template gadget specs (`LvmQKeccakTB`,
-- `LvmQKeccakParts*`); the `F`-side bridges (T-V's `dWire`, T-K's `msEvalA_bitsE`) are part 2.

/-!
# The wiring gadget's closed forms (`LvmQEqWire`)

Every gadget of `preW`, `postW`, `slotW` has a spec stating the value its result source takes in any
row assignment that satisfies the template (`THold`), as an `FE` closed form:

* `thrStepC`, `thrTailC`, `ltC`, `thrC`: `gThrStep`, `gThrTail`, `gLtTab`, `gThr` (`thrEvalA`'s rows);
* `msStepC`, `msTailC`, `msC`: `gMsStepA`, `gMsTail`, `gMs` (`msEvalA`'s rows);
* `gOmega_spec`: `ω_j = laneForm B (eq(a, (j mod 64 + ·) mod 64)) (j / 64)`, and `lt_pos`: that is
  entry `j` of `keccakLinearTranspose (prodW (eq a) B)` (the claim's weights, `Rep.weights`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {xv : Src → FE} {V : Nat → FE}

/-! ## Peeling -/

theorem pr_bind {α β : Type} {n : Nat} (m : TB α) (f : α → TB β) (h : THold xv V n ((m >>= f) n).2) :
    THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 :=
  (thold_bind m f).mp h

theorem pr_fst {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) :
    ((m >>= f) n).1 = (f (m n).1 (n + (m n).2.length)).1 := by rw [tb_bind]

/-! ## `thrEvalA`'s rows -/

/-- One bit of the threshold automaton, as the rows compute it: `(q₁ + (r + b r) d, q₂ + (b + b r) d)`,
`d = q₁ + q₂`. -/
def thrStepC (r b : FE) (q : FE × FE) : FE × FE :=
  ((r + b * r) * (q.1 + q.2) + q.1, (b + b * r) * (q.1 + q.2) + q.2)

/-- `thrTailA` as the rows compute it. -/
def thrTailC : List FE → List FE → FE × FE
  | r :: ρ, b :: tb => thrStepC r b (thrTailC ρ tb)
  | _, _ => (1, 0)

theorem gThrStep_spec {z r b : Src} (hz : z.valF xv V = 0) {q : Src × Src} {n : Nat}
    (h : THold xv V n (gThrStep z r b q n).2) :
    ((gThrStep z r b q n).1.1.valF xv V, (gThrStep z r b q n).1.2.valF xv V) =
      thrStepC (r.valF xv V) (b.valF xv V) (q.1.valF xv V, q.2.valF xv V) := by
  unfold gThrStep at h ⊢
  obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h4, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h5, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h6, -⟩ := pr_bind _ _ h; rw [pr_fst]
  simp only [tb_pure]
  rw [gMul_spec h6, gAdd_spec h5, gMul_spec h4, gAdd_spec h3, gMul_spec h2, gAdd_spec h1, hz, add_zero]
  rfl

theorem gThrTail_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) :
    ∀ (ρ tb : List Src) (n : Nat), THold xv V n (gThrTail z one ρ tb n).2 →
      ((gThrTail z one ρ tb n).1.1.valF xv V, (gThrTail z one ρ tb n).1.2.valF xv V) =
        thrTailC (vals xv V ρ) (vals xv V tb)
  | r :: ρ, b :: tb, n, h => by
    simp only [gThrTail] at h ⊢
    obtain ⟨h1, h2⟩ := pr_bind _ _ h
    rw [pr_fst, gThrStep_spec hz h2, gThrTail_spec hz ho ρ tb n h1]
    rfl
  | [], _, n, _ => by simp only [gThrTail, tb_pure, ho, hz]; rfl
  | _ :: _, [], n, _ => by simp only [gThrTail, tb_pure, ho, hz]; rfl

/-- `Σ_{j<e} eq(tb4, j)` (T-K's `ltE`, over `FE`). -/
def ltC (tb4 : List FE) (e : Nat) : FE := ((List.range e).map (eqAt tb4)).sum

theorem gLtTab_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) (tb4 : List Src)
    (h4 : tb4.length = 4) {n : Nat} (h : THold xv V n (gLtTab z one tb4 n).2) :
    vals xv V (gLtTab z one tb4 n).1 = (List.range 17).map (ltC (vals xv V tb4)) := by
  unfold gLtTab at h ⊢
  obtain ⟨h1, h2⟩ := pr_bind _ _ h
  rw [pr_fst]
  have e1 := gk_eqTab_one hz ho tb4 n h1
  have hl : (gEqTab z [one] tb4 n).1.length = 16 := by
    have := congrArg List.length e1
    rw [List.length_map, eqKernel_length, List.length_map, h4] at this; simpa using this
  refine forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = ltC (vals xv V tb4) k) _ (fun k hk m hm => ?_) _ h2)
  have hk' := List.mem_range.mp hk
  have hE : eqKernel (vals xv V tb4) = (List.range 16).map (eqAt (vals xv V tb4)) := by
    have hl' : (eqKernel (vals xv V tb4)).length = 16 := by
      rw [eqKernel_length, List.length_map, h4]; rfl
    conv_lhs => rw [← gk_range_map_getD (eqKernel (vals xv V tb4)), hl']
    rfl
  rw [gSum_spec _ _ _ hm, hz, zero_add, List.map_take, show List.map (Src.valF xv V) (gEqTab z [one] tb4 n).1 = _ from e1, hE, gk_take_range_map _ (by omega : k ≤ 16)]
  rfl

/-- `thrEvalA ρ μ tb` as the rows compute it. -/
def thrC (ρ μ tb : List FE) : FE :=
  ((thrTailC ρ (tb.drop 4)).1 + (thrTailC ρ (tb.drop 4)).2) *
      ((List.range 16).map fun d => μ.getD d 0 * ltC (tb.take 4) d).sum +
    μ.sum * (thrTailC ρ (tb.drop 4)).1

theorem gThr_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) {ρ μ tb lt : List Src}
    (hμ : μ.length = 16) (hlt : vals xv V lt = (List.range 17).map (ltC (vals xv V (tb.take 4)))) {n : Nat}
    (h : THold xv V n (gThr z one ρ μ tb lt n).2) :
    (gThr z one ρ μ tb lt n).1.valF xv V = thrC (vals xv V ρ) (vals xv V μ) (vals xv V tb) := by
  unfold gThr at h ⊢
  obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
  have e1 := gThrTail_spec hz ho ρ (tb.drop 4) n h1
  generalize gThrTail z one ρ (tb.drop 4) n = R at h e1 ⊢
  obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h4, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h5, h⟩ := pr_bind _ _ h; rw [pr_fst]
  rw [gMul_spec h, gMul_spec h5, gAdd_spec h4, gDot_spec _ _ _ h3, gSum_spec _ _ _ h2, hz]
  have eq1 := congrArg Prod.fst e1
  have eq2 := congrArg Prod.snd e1
  simp only at eq1 eq2
  have hl : lt.length = 17 := by
    have := congrArg List.length hlt; simpa using this
  have hL : ((List.range 16).map fun d => (μ.getD d default, lt.getD d default)).map
      (fun cd => cd.1.valF xv V * cd.2.valF xv V) =
      (List.range 16).map fun d => (μ.map (Src.valF xv V)).getD d 0 *
        ltC ((tb.map (Src.valF xv V)).take 4) d := by
    rw [List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have hd' := List.mem_range.mp hd
    simp only [Function.comp_apply]
    rw [getD_vals _ (by omega), getD_vals _ (by omega), hlt, ← List.map_take]
    simp [List.getD_eq_getElem?_getD, hd', show d < 17 by omega]
  rw [eq1, eq2, hL]
  simp only [thrC, vals, List.map_drop, zero_add, add_zero]

/-! ## `eq(ρ, 0)` -/

theorem gEq0_spec {z : Src} (hz : z.valF xv V = 0) :
    ∀ (acc : Src) (ρ : List Src) (n : Nat), THold xv V n (gEq0 z acc ρ n).2 →
      (gEq0 z acc ρ n).1.valF xv V = acc.valF xv V * ((vals xv V ρ).map (1 + ·)).prod
  | acc, [], n, _ => by simp [gEq0, tb_pure]
  | acc, r :: rs, n, h => by
    simp only [gEq0] at h ⊢
    obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h2, h3⟩ := pr_bind _ _ h; rw [pr_fst]
    rw [gEq0_spec hz _ rs _ h3, gMul_spec h2, gOne_spec h1, hz]
    simp only [vals, List.map_cons, List.prod_cons, add_zero]
    ring

/-! ## The weights `ω` -/

/-- **Entry `j` of the transposed product weights** is a lane form at slice `j mod 64`. -/
theorem lt_pos (A : ℕ → FE) (B : List FE) {j : ℕ} (hj : j < 1600) :
    (keccakLinearTranspose (prodW A B)).getD j 0 = laneForm B (fun s => A ((j % 64 + s) % 64)) (j / 64) := by
  have h := lane_dot A (fun z => if z = j % 64 then 1 else 0) B (l := j / 64) (by omega)
  rw [sumE_range] at h
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    show j % 64 < 64 from Nat.mod_lt _ (by omega), if_true] at h
  rw [show 64 * (j / 64) + j % 64 = j by omega] at h
  rw [h]
  congr 1
  funext s
  unfold rotSum
  rw [sumE_range]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    show j % 64 < 64 from Nat.mod_lt _ (by omega), if_true]

theorem gOmega_spec {z : Src} (hz : z.valF xv V = 0) {B eZ : List Src} (hB : 25 ≤ B.length) {j : Nat}
    (hj : j < 1600) {n : Nat} (h : THold xv V n (gOmega z B eZ j n).2) :
    (gOmega z B eZ j n).1.valF xv V =
      laneForm (vals xv V B) (fun s => (eZ.getD ((j % 64 + s) % 64) default).valF xv V) (j / 64) :=
  gLaneForm_spec hz hB _ (by omega) n h

/-! ## `msEvalA`'s rows -/

/-- Four `FE` entries `(c, s) = 00, 01, 10, 11`. -/
abbrev Q4F := FE × FE × FE × FE

/-- `msStep a r t q` as the rows compute it. -/
def msStepTC (al be ga de : FE) (t : Bool) (q : Q4F) : Q4F :=
  if t then (al * q.1 + be * q.1, al * q.1 + be * q.2.1, ga * q.1 + de * q.2.2.1, ga * q.2.1 + de * q.2.2.1)
  else (al * q.1 + be * q.2.1, al * q.2.1 + be * q.2.1, ga * q.2.1 + de * q.2.2.1, ga * q.2.1 + de * q.2.2.2)

/-- `f₀ + b·(f₁ + f₀)` entrywise. -/
def mixC (b : FE) (f1 f0 : Q4F) : Q4F :=
  (b * (f1.1 + f0.1) + f0.1, b * (f1.2.1 + f0.2.1) + f0.2.1, b * (f1.2.2.1 + f0.2.2.1) + f0.2.2.1,
    b * (f1.2.2.2 + f0.2.2.2) + f0.2.2.2)

/-- `msStepA a r b q` as the rows compute it. -/
def msStepC (a r b : FE) (q : Q4F) : Q4F :=
  mixC b (msStepTC (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) true q)
    (msStepTC (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) false q)

/-- `msTailA` as the rows compute it. -/
def msTailC : List FE → List FE → List FE → Q4F
  | a :: σ, r :: ρ, b :: tb => msStepC a r b (msTailC σ ρ tb)
  | _, _, _ => (1, 0, 0, 0)

/-- `msEvalA ρ μ σ tb 1` as the rows compute it. -/
def msC (ρ μ σ tb : List FE) : FE :=
  ((msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).2.1 +
      (msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).1) *
    ((List.range 15).map fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * ltC (tb.take 4) (d + 1)).sum +
  (eqAt (σ.take 4) 15 * μ.getD 0 0 * (msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).2.2.1 +
    ((List.range 15).map fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0).sum *
      (msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).1)

/-- The values of a `Q4` of sources. -/
def q4v (q : Q4) : Q4F := (q.1.valF xv V, q.2.1.valF xv V, q.2.2.1.valF xv V, q.2.2.2.valF xv V)

theorem gDot2_spec {z a b c d : Src} (hz : z.valF xv V = 0) {n : Nat}
    (h : THold xv V n (gDot z [(a, b), (c, d)] n).2) :
    (gDot z [(a, b), (c, d)] n).1.valF xv V = a.valF xv V * b.valF xv V + c.valF xv V * d.valF xv V := by
  rw [gDot_spec _ _ _ h, hz]; simp

theorem gMsStep_spec {z al be ga de : Src} (hz : z.valF xv V = 0) (t : Bool) (q : Q4) {n : Nat}
    (h : THold xv V n (gMsStep z al be ga de t q n).2) :
    q4v (xv := xv) (V := V) (gMsStep z al be ga de t q n).1 =
      msStepTC (al.valF xv V) (be.valF xv V) (ga.valF xv V) (de.valF xv V) t (q4v (xv := xv) (V := V) q) := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  cases t
  · simp only [gMsStep, Bool.false_eq_true, ite_false] at h ⊢
    obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h4, -⟩ := pr_bind _ _ h; rw [pr_fst]
    simp only [tb_pure, q4v, msStepTC, Bool.false_eq_true, ite_false]
    rw [gDot2_spec hz h1, gDot2_spec hz h2, gDot2_spec hz h3, gDot2_spec hz h4]
  · simp only [gMsStep, ite_true] at h ⊢
    obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h4, -⟩ := pr_bind _ _ h; rw [pr_fst]
    simp only [tb_pure, q4v, msStepTC, ite_true]
    rw [gDot2_spec hz h1, gDot2_spec hz h2, gDot2_spec hz h3, gDot2_spec hz h4]

theorem gMix_spec {b f1 f0 : Src} {n : Nat} (h : THold xv V n (gMix b f1 f0 n).2) :
    (gMix b f1 f0 n).1.valF xv V = b.valF xv V * (f1.valF xv V + f0.valF xv V) + f0.valF xv V := by
  unfold gMix at h ⊢
  obtain ⟨h1, h2⟩ := pr_bind _ _ h; rw [pr_fst, gMul_spec h2, gAdd_spec h1]

theorem gMsStepA_spec {z a r b : Src} (hz : z.valF xv V = 0) (q : Q4) {n : Nat}
    (h : THold xv V n (gMsStepA z a r b q n).2) :
    q4v (xv := xv) (V := V) (gMsStepA z a r b q n).1 =
      msStepC (a.valF xv V) (r.valF xv V) (b.valF xv V) (q4v (xv := xv) (V := V) q) := by
  unfold gMsStepA at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e1 := gMul_spec h1; rw [hz, add_zero] at e1
  generalize (gMul a r z n).1 = ar at h e1 ⊢; generalize n + (gMul a r z n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e2 := gAdd_spec h2
  generalize (gAdd a r n1).1 = sr at h e2 ⊢; generalize n1 + (gAdd a r n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e3 := gAdd_spec h3
  generalize (gAdd sr ar n2).1 = al0 at h e3 ⊢; generalize n2 + (gAdd sr ar n2).2.length = n3 at h ⊢
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e4 := gOne_spec h4
  generalize (gOne al0 n3).1 = al at h e4 ⊢; generalize n3 + (gOne al0 n3).2.length = n4 at h ⊢
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e5 := gAdd_spec h5
  generalize (gAdd r ar n4).1 = ga at h e5 ⊢; generalize n4 + (gAdd r ar n4).2.length = n5 at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e6 := gAdd_spec h6
  generalize (gAdd a ar n5).1 = de at h e6 ⊢; generalize n5 + (gAdd a ar n5).2.length = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e7 := gMsStep_spec hz true q h7
  generalize (gMsStep z al ar ga de true q n6).1 = f1 at h e7 ⊢
  generalize n6 + (gMsStep z al ar ga de true q n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e8 := gMsStep_spec hz false q h8
  generalize (gMsStep z al ar ga de false q n7).1 = f0 at h e8 ⊢
  generalize n7 + (gMsStep z al ar ga de false q n7).2.length = n8 at h ⊢
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e9 := gMix_spec h9
  generalize (gMix b f1.1 f0.1 n8).1 = m1 at h e9 ⊢; generalize n8 + (gMix b f1.1 f0.1 n8).2.length = n9 at h ⊢
  obtain ⟨h10, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e10 := gMix_spec h10
  generalize (gMix b f1.2.1 f0.2.1 n9).1 = m2 at h e10 ⊢
  generalize n9 + (gMix b f1.2.1 f0.2.1 n9).2.length = n10 at h ⊢
  obtain ⟨h11, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e11 := gMix_spec h11
  generalize (gMix b f1.2.2.1 f0.2.2.1 n10).1 = m3 at h e11 ⊢
  generalize n10 + (gMix b f1.2.2.1 f0.2.2.1 n10).2.length = n11 at h ⊢
  obtain ⟨h12, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e12 := gMix_spec h12
  generalize (gMix b f1.2.2.2 f0.2.2.2 n11).1 = m4 at e12 ⊢
  have a1 := congrArg Prod.fst e7
  have a2 := congrArg (fun x => x.2.1) e7
  have a3 := congrArg (fun x => x.2.2.1) e7
  have a4 := congrArg (fun x => x.2.2.2) e7
  have b1 := congrArg Prod.fst e8
  have b2 := congrArg (fun x => x.2.1) e8
  have b3 := congrArg (fun x => x.2.2.1) e8
  have b4 := congrArg (fun x => x.2.2.2) e8
  simp only [q4v] at a1 a2 a3 a4 b1 b2 b3 b4
  simp only [tb_pure, q4v]
  rw [e9, e10, e11, e12, a1, a2, a3, a4, b1, b2, b3, b4, e4, e3, e2, e5, e6, e1]
  rfl

theorem gMsTail_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) :
    ∀ (σ ρ tb : List Src) (n : Nat), THold xv V n (gMsTail z one σ ρ tb n).2 →
      q4v (xv := xv) (V := V) (gMsTail z one σ ρ tb n).1 = msTailC (vals xv V σ) (vals xv V ρ) (vals xv V tb)
  | a :: σ, r :: ρ, b :: tb, n, h => by
    simp only [gMsTail] at h ⊢
    obtain ⟨h1, h2⟩ := pr_bind _ _ h
    rw [pr_fst, gMsStepA_spec hz _ h2, gMsTail_spec hz ho σ ρ tb n h1]
    rfl
  | [], _, _, n, _ => by simp only [gMsTail, tb_pure, q4v, ho, hz]; rfl
  | _ :: _, [], _, n, _ => by simp only [gMsTail, tb_pure, q4v, ho, hz]; rfl
  | _ :: _, _ :: _, [], n, _ => by simp only [gMsTail, tb_pure, q4v, ho, hz]; rfl

theorem gnoA_dot2 (z a b c d : Src) (n : Nat) : GNoA (gDot z [(a, b), (c, d)] n).2 := gnoA_gDot _ _ _

theorem gnoA_gMsStep (z al be ga de : Src) (t : Bool) (q : Q4) (n : Nat) : GNoA (gMsStep z al be ga de t q n).2 := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  cases t <;> simp only [gMsStep, Bool.false_eq_true, ite_false, ite_true] <;>
    exact gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _)
      (gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _) (gnoA_pure _ _))))

theorem gnoA_gMix (b f1 f0 : Src) (n : Nat) : GNoA (gMix b f1 f0 n).2 :=
  gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_mul _ _ _ _)

theorem gnoA_gMsStepA (z a r b : Src) (q : Q4) (n : Nat) : GNoA (gMsStepA z a r b q n).2 := by
  unfold gMsStepA
  exact gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI]))
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_one _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI]))
    (gnoA_bind _ _ _ (gnoA_gMsStep _ _ _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_gMsStep _ _ _ _ _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _) (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _) (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _) (gnoA_pure _ _))))))))))))

theorem gnoA_gMsTail (z one : Src) : ∀ (σ ρ tb : List Src) (n : Nat), GNoA (gMsTail z one σ ρ tb n).2
  | a :: σ, r :: ρ, b :: tb, n => by
    simp only [gMsTail]
    exact gnoA_bind _ _ _ (gnoA_gMsTail z one σ ρ tb n) (gnoA_gMsStepA _ _ _ _ _ _)
  | [], _, _, n => gnoA_pure _ _
  | _ :: _, [], _, n => gnoA_pure _ _
  | _ :: _, _ :: _, [], n => gnoA_pure _ _

theorem gnoA_gMs (z one : Src) (ρ μ σ tb lt : List Src) (n : Nat) : GNoA (gMs z one ρ μ σ tb lt n).2 := by
  unfold gMs
  exact gnoA_bind _ _ _ (gnoA_gMsTail _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_gEqTab _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_mul _ _ _ _) _ _) (gnoA_bind _ _ _ (gnoA_gSum _ _ _)
    (gnoA_bind _ _ _ (gnoA_gDot _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_mul _ _ _ _))))))))

theorem gMs_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) {ρ μ σ tb lt : List Src}
    (hσ : 4 ≤ σ.length) (hμ : μ.length = 16)
    (hlt : vals xv V lt = (List.range 17).map (ltC (vals xv V (tb.take 4)))) {n : Nat}
    (h : THold xv V n (gMs z one ρ μ σ tb lt n).2) :
    (gMs z one ρ μ σ tb lt n).1.valF xv V = msC (vals xv V ρ) (vals xv V μ) (vals xv V σ) (vals xv V tb) := by
  unfold gMs at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e1 := gMsTail_spec hz ho (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) n h1
  generalize (gMsTail z one (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) n).1 = q at h e1 ⊢
  generalize n + (gMsTail z one (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e2 := gk_eqTab_one hz ho (σ.take 4) n1 h2
  have hl4 : (gEqTab z [one] (σ.take 4) n1).1.length = 16 := by
    have := congrArg List.length e2
    rw [List.length_map, eqKernel_length, List.length_map, List.length_take, min_eq_left hσ] at this
    simpa using this
  generalize (gEqTab z [one] (σ.take 4) n1).1 = e4 at h e2 hl4 ⊢
  generalize n1 + (gEqTab z [one] (σ.take 4) n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e3 : vals xv V (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).1 = (List.range 16).map fun d =>
        eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 :=
    forall₂_map_eq (mapTB_spec_mem (P := fun d v => v = eqAt (vals xv V (σ.take 4)) d *
      (vals xv V μ).getD ((d + 1) % 16) 0) _ (fun d hd m hm => by
        have hd' := List.mem_range.mp hd
        rw [gMul_spec hm, hz, add_zero, getD_vals _ (by omega), getD_vals _ (by omega), e2]
        rfl) _ h3)
  have hA16 : (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).1.length = 16 := by rw [mapTB_length]; rfl
  generalize (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).1 = A at h e3 hA16 ⊢
  generalize n2 + (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).2.length = n3 at h ⊢
  have hAd : ∀ d < 16, (A.getD d default).valF xv V =
      eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 := by
    intro d hd
    rw [getD_vals _ (by omega), e3]; simp [List.getD_eq_getElem?_getD, hd]
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e4' := gSum_spec _ _ _ h4
  generalize (gSum z (A.take 15) n3).1 = sA at h e4' ⊢; generalize n3 + (gSum z (A.take 15) n3).2.length = n4 at h ⊢
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e5 := gDot_spec _ _ _ h5
  generalize (gDot z ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)) n4).1 = L at h e5 ⊢
  generalize n4 + (gDot z ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)) n4).2.length = n5
    at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e6 := gMul_spec h6
  generalize (gMul sA q.1 z n5).1 = x1 at h e6 ⊢; generalize n5 + (gMul sA q.1 z n5).2.length = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e7 := gMul_spec h7
  generalize (gMul (A.getD 15 default) q.2.2.1 x1 n6).1 = x2 at h e7 ⊢
  generalize n6 + (gMul (A.getD 15 default) q.2.2.1 x1 n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e8 := gAdd_spec h8
  generalize (gAdd q.2.1 q.1 n7).1 = d at h e8 ⊢; generalize n7 + (gAdd q.2.1 q.1 n7).2.length = n8 at h ⊢
  rw [gMul_spec h, e8, e7, e6, e5, e4', hz, hAd 15 (by omega)]
  have q1 := congrArg Prod.fst e1
  have q2 := congrArg (fun x => x.2.1) e1
  have q3 := congrArg (fun x => x.2.2.1) e1
  simp only [q4v] at q1 q2 q3
  rw [q1, q2, q3]
  have hlt' : ∀ d < 15, (lt.getD (d + 1) default).valF xv V = ltC (vals xv V (tb.take 4)) (d + 1) := by
    intro d hd
    have hl : lt.length = 17 := by have := congrArg List.length hlt; simpa using this
    rw [getD_vals _ (by omega), hlt]; simp [List.getD_eq_getElem?_getD, show d + 1 < 17 by omega]
  have hS1 : ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)).map
      (fun cd => cd.1.valF xv V * cd.2.valF xv V) = (List.range 15).map fun d =>
        eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 * ltC (vals xv V (tb.take 4)) (d + 1) := by
    rw [List.map_map]
    exact List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [hAd d (by omega), hlt' d hd']
  have hS2 : (A.take 15).map (Src.valF xv V) = (List.range 15).map fun d =>
      eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 := by
    rw [List.map_take, show A.map (Src.valF xv V) = vals xv V A from rfl, e3, gk_take_range_map _ (by omega)]
  rw [hS1, hS2]
  simp only [msC, vals, List.map_drop, List.map_take, List.length_map, zero_add, add_zero]

/-! ## The blocks' assertions -/

theorem gnoA_gThrStep (z r b : Src) (q : Src × Src) (n : Nat) : GNoA (gThrStep z r b q n).2 := by
  unfold gThrStep
  exact gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_pure _ _))))))

/-- **The final check block** (`postW`): `g_D` is the stream scalar at lane `qg`; its assertion is
`b·(msC … · g_D + final) = 0`. -/
theorem postW_spec {P qg : Nat} {cv : Nat → Src} {mb σ lt : List Src} {z one final b : Src}
    (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) (hσ : 4 ≤ σ.length)
    (hlt : vals xv V lt = (List.range 17).map (ltC (vals xv V (mb.take 4)))) {n : Nat}
    (h : THold xv V n (postW P qg cv mb σ lt z one final b n).2) :
    (postW P qg cv mb σ lt z one final b n).1.valF xv V = lv xv [] qg ∧
    (TAssert xv V (postW P qg cv mb σ lt z one final b n).2 ↔
      b.valF xv V * (msC ((List.range (P + 1)).map fun i => (cv (18 + i)).valF xv V)
        ((List.range 16).map fun i => (cv (1 + i)).valF xv V) (vals xv V σ) (vals xv V mb) * lv xv [] qg +
        final.valF xv V) = 0) := by
  have hfst : (postW P qg cv mb σ lt z one final b n).1 = (gLoad qg [] n).1 := by
    simp only [postW, tb_bind, tb_pure]
  refine ⟨by rw [hfst]; unfold postW at h; exact gLoad_lv (tb_peel _ _ h).1, ?_⟩
  unfold postW at h ⊢
  obtain ⟨h1, h, -⟩ := tb_peel _ _ h
  rw [tassert_bind_noA _ _ (gnoA_load _ _ _)]
  have eg := gLoad_lv h1
  generalize (gLoad qg [] n).1 = g at h eg ⊢; generalize n + (gLoad qg [] n).2.length = n1 at h ⊢
  obtain ⟨h2, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gMs _ _ _ _ _ _ _ _)]
  have em := gMs_spec hz ho hσ (by simp) hlt h2
  generalize (gMs z one _ _ σ mb lt n1).1 = ms at h em ⊢
  generalize n1 + (gMs z one _ _ σ mb lt n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mul _ _ _ _)]
  have ee := gMul_spec h3
  generalize (gMul ms g final n2).1 = ee' at h ee ⊢
  generalize n2 + (gMul ms g final n2).2.length = n3 at h ⊢
  rw [tassert_bind, gAssert_iff, ee, em, eg]
  simp only [vals, List.map_map, Function.comp_def]
  exact ⟨fun h => h.1, fun h => ⟨h, tassert_noA (gnoA_pure _ _)⟩⟩

/-- **The slot check block** (`slotW`): the 64 slices are the stream scalars at lanes `qs + 3z`, and
its assertion is `b·(Σ_z (Σ_{o<4} eq(τ, o)·ω_{wIx(64 o + z)})·slice_z + final) = 0`. -/
theorem slotW_spec {qs : Nat} {om τ : List Src} {z one final b : Src} (hz : z.valF xv V = 0)
    (ho : one.valF xv V = 1) (hτ : τ.length = 2) {n : Nat}
    (h : THold xv V n (slotW qs om τ z one final b n).2) :
    TAssert xv V (slotW qs om τ z one final b n).2 ↔
      b.valF xv V * (final.valF xv V + ((List.range 64).map fun zz =>
        ((List.range 4).map fun o => eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum *
          lv xv [] (qs + 3 * zz)).sum) = 0 := by
  unfold slotW at h ⊢
  obtain ⟨h1, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mapTB (fun _ _ => gnoA_load _ _ _) _ _)]
  have esl : vals xv V (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).1 =
      (List.range 64).map fun k => lv xv [] (qs + 3 * k) :=
    forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = lv xv [] (qs + 3 * k)) _ (fun k _ m hm => gLoad_lv hm) _ h1)
  have hsl : (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).1.length = 64 := by rw [mapTB_length]; rfl
  generalize (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).1 = sl at h esl hsl ⊢
  generalize n + (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).2.length = n1 at h ⊢
  obtain ⟨h2, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]
  have et := gk_eqTab_one hz ho τ n1 h2
  have hl4 : (gEqTab z [one] τ n1).1.length = 4 := by
    have := congrArg List.length et
    rw [List.length_map, eqKernel_length, List.length_map, hτ] at this; simpa using this
  generalize (gEqTab z [one] τ n1).1 = e4 at h et hl4 ⊢
  generalize n1 + (gEqTab z [one] τ n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mapTB (fun _ _ => gnoA_gDot _ _ _) _ _)]
  have eW : vals xv V (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).1 =
      (List.range 64).map fun zz => ((List.range 4).map fun o =>
        eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum :=
    forall₂_map_eq (mapTB_spec_mem (P := fun zz v => v = ((List.range 4).map fun o =>
        eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum) _ (fun zz _ m hm => by
      rw [gDot_spec _ _ _ hm, hz, zero_add, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun o ho' => ?_)
      have ho'' := List.mem_range.mp ho'
      simp only [Function.comp_apply]
      rw [getD_vals _ (by omega), et]; rfl) _ h3)
  have hW : (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).1.length = 64 := by
    rw [mapTB_length]; rfl
  generalize (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).1 = W at h eW hW ⊢
  generalize n2 + (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).2.length = n3 at h ⊢
  obtain ⟨h4, -, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gDot _ _ _), gAssert_iff, gDot_spec _ _ _ h4]
  rw [List.map_map]
  have hs : ((List.range 64).map ((fun cd => cd.1.valF xv V * cd.2.valF xv V) ∘ fun zz =>
      (W.getD zz default, sl.getD zz default))) = (List.range 64).map fun zz =>
        ((List.range 4).map fun o => eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum *
          lv xv [] (qs + 3 * zz) := by
    refine List.map_congr_left fun zz hzz => ?_
    have hzz' := List.mem_range.mp hzz
    simp only [Function.comp_apply]
    rw [getD_vals _ (by omega), getD_vals _ (by omega), eW, esl]
    simp [List.getD_eq_getElem?_getD, hzz']
  rw [hs]

/-! ## The target block -/

theorem fx_gSum : ∀ (acc : Src) (cs : List Src) (n : Nat), Fx acc → Fx (gSum acc cs n).1
  | _, [], _, h => h
  | acc, c :: cs, n, _ => by
    simp only [gSum, tb_bind]
    exact fx_gSum _ cs _ (fx_emit _ _)

/-- `ω_j` from the claim's lane weights `B` and slice point `a` (`laneForm` at slice `j mod 64`). -/
def wOm (A B : List FE) (j : Nat) : FE := laneForm B (fun s => (eqKernel A).getD ((j % 64 + s) % 64) 0) (j / 64)

/-- `⟨ω, c43⟩` on `wOm`. -/
def wC43 (A B : List FE) : FE := wOm A B 0 + wOm A B 1 + wOm A B 6 + wOm A B 264 + wOm A B 1087

/-- **The wiring target as the rows compute it**: `ι(0)·padDot + (c43·(thr + ι(0)) + value)` with
`padDot = c43 + Σ_{p<256} ω_{8+p}·s_p`, `ι(0) = Π(1 + ρ_k)·μ_0`, `thr = thrC ρ μ bits(m)`. -/
def wTgt (value : FE) (μ ρ A B mb sb : List FE) : FE :=
  (ρ.map (1 + ·)).prod * μ.getD 0 0 *
      (wC43 A B + ((List.range 256).map fun p => wOm A B (8 + p) * sb.getD p 0).sum) +
    (wC43 A B * (thrC ρ μ mb + (ρ.map (1 + ·)).prod * μ.getD 0 0) + value)

theorem wPos_length : wPos.length = 261 := by simp [wPos]

theorem wPos_ix_all : ∀ p < 257, wPos.getD (3 + p) 0 = 8 + p := by
  intro p hp
  have h3 : 3 + p - [0, 1, 6].length = p := by simp
  rw [wPos, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), h3,
    List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hp]
  simp [Nat.add_comm]

theorem wPos_getD_ix {p : Nat} (hp : p ≤ 256) : wPos.getD (wIx p) 0 = 8 + p := wPos_ix_all p (by omega)

theorem wPos_lt_all : wPos.all (· < 1600) = true := by decide +kernel

theorem wPos_lt : ∀ j ∈ wPos, j < 1600 := by
  intro j hj; have := List.all_eq_true.mp wPos_lt_all j hj; simpa using this

theorem wPos_c43 : wPos.getD 0 0 = 0 ∧ wPos.getD 1 0 = 1 ∧ wPos.getD 2 0 = 6 ∧ wPos.getD 259 0 = 264 ∧
    wPos.getD 260 0 = 1087 := by decide +kernel

theorem wPos_map_getD (f : Nat → FE) {k : Nat} (hk : k < 261) : (wPos.map f).getD k 0 = f (wPos.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simp [wPos_length]; omega), List.getElem_map,
    List.getD_eq_getElem _ _ (by rw [wPos_length]; omega)]

/-- **The target block** (`preW`): zero, one, `ω` on `wPos`, the `lt` table of `m`'s low bits and the
target. -/
theorem preW_spec {P : Nat} {cv : Nat → Src} {mb sb : List Src} {b : Src} (hmb : 4 ≤ mb.length)
    (hsb : sb.length = 256) {n : Nat} (h : THold xv V n (preW P cv mb sb b n).2) :
    (preW P cv mb sb b n).1.z.valF xv V = 0 ∧ Fx (preW P cv mb sb b n).1.z ∧
    (preW P cv mb sb b n).1.one.valF xv V = 1 ∧ Fx (preW P cv mb sb b n).1.one ∧
    vals xv V (preW P cv mb sb b n).1.om = wPos.map (wOm ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
      ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V)) ∧
    (∀ x ∈ (preW P cv mb sb b n).1.om, Fx x) ∧
    vals xv V (preW P cv mb sb b n).1.lt = (List.range 17).map (ltC (vals xv V (mb.take 4))) ∧
    (∀ x ∈ (preW P cv mb sb b n).1.lt, Fx x) ∧
    (preW P cv mb sb b n).1.target.valF xv V =
      wTgt ((cv 0).valF xv V) ((List.range 16).map fun i => (cv (1 + i)).valF xv V)
        ((List.range (P + 1)).map fun i => (cv (18 + i)).valF xv V)
        ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
        ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V) (vals xv V mb) (vals xv V sb) ∧
    Fx (preW P cv mb sb b n).1.target := by
  unfold preW at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ez := gZero_spec h1; have fz : Fx (gZero b n).1 := fx_emit _ _
  generalize (gZero b n).1 = z at h ez fz ⊢; generalize n + (gZero b n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eo := gOne_spec h2; have fo : Fx (gOne z n1).1 := fx_emit _ _
  rw [ez, add_zero] at eo
  generalize (gOne z n1).1 = one at h eo fo ⊢; generalize n1 + (gOne z n1).2.length = n2 at h ⊢
  -- `eq(a)`
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eZ := gk_eqTab_one ez eo ((List.range 6).map fun i => cv (44 + P + i)) n2 h3
  have hZ : (gEqTab z [one] ((List.range 6).map fun i => cv (44 + P + i)) n2).1.length = 64 := by
    have := congrArg List.length eZ
    rw [List.length_map, eqKernel_length, List.length_map] at this; simpa using this
  generalize (gEqTab z [one] ((List.range 6).map fun i => cv (44 + P + i)) n2).1 = eZs at h eZ hZ ⊢
  generalize n2 + (gEqTab z [one] _ n2).2.length = n3 at h ⊢
  simp only [vals, List.map_map, Function.comp_def] at eZ
  -- `ω`
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eom : vals xv V (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1 =
      wPos.map (wOm ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
        ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V)) :=
    forall₂_map_eq (mapTB_spec_mem (P := fun j v => v = wOm _ _ j) _ (fun j hj m hm => by
      rw [gOmega_spec ez (by simp) (wPos_lt j hj) hm, wOm]
      simp only [vals, List.map_map, Function.comp_def]
      congr 1
      funext s
      rw [getD_vals _ (by rw [hZ]; exact Nat.mod_lt _ (by omega))]
      simp only [vals]; rw [eZ]) _ h4)
  have fom : ∀ x ∈ (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1, Fx x :=
    fx_mapTB (fun _ _ => by
      unfold gOmega gLaneForm
      simp only [tb_bind]
      exact fx_gDot _ _ _ (fx_gDot _ _ _ (fx_emit _ _))) _ _
  have hom : (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1.length = 261 := by
    rw [mapTB_length, wPos_length]
  generalize (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1 = om at h eom fom hom ⊢
  generalize n3 + (mapTB (gOmega z _ eZs) wPos n3).2.length = n4 at h ⊢
  have hOm : ∀ k < 261, (om.getD k default).valF xv V = (wPos.map (wOm ((List.range 6).map fun i =>
      (cv (44 + P + i)).valF xv V) ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V))).getD k 0 := by
    intro k hk; rw [getD_vals _ (by omega), eom]
  -- `ι(0)`
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e0 := gEq0_spec ez one ((List.range (P + 1)).map fun i => cv (18 + i)) n4 h5
  rw [eo, one_mul] at e0
  generalize (gEq0 z one ((List.range (P + 1)).map fun i => cv (18 + i)) n4).1 = q0 at h e0 ⊢
  generalize n4 + (gEq0 z one _ n4).2.length = n5 at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ei := gMul_spec h6; rw [ez, add_zero] at ei
  generalize (gMul q0 _ z n5).1 = io0 at h ei ⊢; generalize n5 + (gMul q0 _ z n5).2.length = n6 at h ⊢
  -- `lt`, `thr`
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have elt := gLtTab_spec ez eo (mb.take 4) (by rw [List.length_take]; omega) h7
  have flt : ∀ x ∈ (gLtTab z one (mb.take 4) n6).1, Fx x := by
    unfold gLtTab; simp only [tb_bind]
    exact fx_mapTB (fun _ _ => fx_gSum _ _ _ fz) _ _
  generalize (gLtTab z one (mb.take 4) n6).1 = lt at h elt flt ⊢
  generalize n6 + (gLtTab z one (mb.take 4) n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eth := gThr_spec ez eo (by simp) elt h8
  generalize (gThr z one _ _ mb lt n7).1 = thr at h eth ⊢
  generalize n7 + (gThr z one _ _ mb lt n7).2.length = n8 at h ⊢
  -- `c43`, `padDot`
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ec := gSum_spec _ _ _ h9
  generalize (gSum z _ n8).1 = c43 at h ec ⊢; generalize n8 + (gSum z _ n8).2.length = n9 at h ⊢
  obtain ⟨h10, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have epd := gDot_spec _ _ _ h10
  generalize (gDot c43 _ n9).1 = pd at h epd ⊢; generalize n9 + (gDot c43 _ n9).2.length = n10 at h ⊢
  -- the target
  obtain ⟨h11, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e11 := gAdd_spec h11
  generalize (gAdd thr io0 n10).1 = ti at h e11 ⊢; generalize n10 + (gAdd thr io0 n10).2.length = n11 at h ⊢
  obtain ⟨h12, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e12 := gMul_spec h12
  generalize (gMul c43 ti _ n11).1 = t1 at h e12 ⊢; generalize n11 + (gMul c43 ti _ n11).2.length = n12 at h ⊢
  obtain ⟨h13, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e13 := gMul_spec h13
  have ft : Fx (gMul io0 pd t1 n12).1 := fx_emit _ _
  generalize (gMul io0 pd t1 n12).1 = tgt at e13 ft ⊢
  simp only [tb_pure]
  refine ⟨ez, fz, eo, fo, eom, fom, elt, flt, ?_, ft⟩
  rw [e13, e12, e11, epd, ec, eth, ei, e0, ez]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  have hpd : ((List.range 256).map fun p => (om.getD (wIx p) default, sb.getD p default)).map
      (fun cd => cd.1.valF xv V * cd.2.valF xv V) = (List.range 256).map fun p =>
        wOm ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
          ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V) (8 + p) * (vals xv V sb).getD p 0 := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have hp' := List.mem_range.mp hp
    simp only [Function.comp_apply]
    rw [hOm _ (by simp [wIx]; omega), getD_vals _ (by omega), wPos_map_getD _ (by simp [wIx]; omega),
      wPos_getD_ix (by omega)]
  rw [hpd, hOm 0 (by omega), hOm 1 (by omega), hOm 2 (by omega), hOm 259 (by omega), hOm 260 (by omega),
    wPos_map_getD _ (by omega), wPos_map_getD _ (by omega), wPos_map_getD _ (by omega),
    wPos_map_getD _ (by omega), wPos_map_getD _ (by omega), wPos_c43.1, wPos_c43.2.1, wPos_c43.2.2.1,
    wPos_c43.2.2.2.1, wPos_c43.2.2.2.2]
  simp only [wTgt, wC43, vals, List.map_map, Function.comp_def]
  rw [getD_vals _ (by simp), List.getD_eq_getElem?_getD]
  simp only [vals, List.getElem?_map, List.getElem?_range (show 0 < 16 by omega), Option.map_some,
    Option.getD_some, Nat.add_zero]
  have hμ0 : (List.map (fun x => Src.valF xv V (cv (1 + x))) (List.range 16)).getD 0 0 = Src.valF xv V (cv 1) := by
    simp
  rw [hμ0]
  ring

end Lvm.Q1
end
-- ===== end of `LvmQEqWire` =====

/-!
# The wire gadget against V_S (`LvmQWireSound`)

The rows compute T-K's circuit twins: `q4E (msStepC …) = msStepA …`, `p2E (thrTailC …) = thrTailA …`,
`toExt3 (msC …) = msEvalA … 1`, `toExt3 (thrC …) = thrEvalA …`. With the bits of `m` in the cells
(`toExt3` of them is `bitsE m w`), T-K's `*_bitsE` and T-V's `toExt3_*F` give
**`msC_eq_msEvalF`** and **`thrC_eq_thrEvalF`**: the circuit's values are V_S's.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM Lvm.VEq Lvm.VEq.Wr

local notation "tE" => FE.toExt3

/-! ## `msEvalA` -/

/-- Four `FE` entries as T-K's automaton vector over `E`. -/
def q4E (q : Q4F) : Lvm.WK.MS4 := ⟨tE q.1, tE q.2.1, tE q.2.2.1, tE q.2.2.2⟩

theorem q4E_msStepC (a r b : FE) (q : Q4F) :
    q4E (msStepC a r b q) = Lvm.WK.msStepA (tE a) (tE r) (tE b) (q4E q) := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  unfold q4E msStepC mixC msStepTC Lvm.WK.msStepA Lvm.WK.msStep
  simp only [Lvm.WK.nextS, Lvm.WK.eqBit, Lvm.WK.MS4.get, Bool.not_true, Bool.not_false, ite_true,
    Bool.false_eq_true, ite_false, Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false]
  simp only [M3.tE_add, M3.tE_mul, M3.tE_one, Lvm.WK.MS4.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem q4E_msTailC : ∀ (σ ρ tb : List FE),
    q4E (msTailC σ ρ tb) = Lvm.WK.msTailA (σ.map tE) (ρ.map tE) (tb.map tE)
  | a :: σ, r :: ρ, b :: tb => by
    rw [msTailC, q4E_msStepC, q4E_msTailC σ ρ tb]; rfl
  | [], _, _ => by
    show (⟨tE 1, tE 0, tE 0, tE 0⟩ : Lvm.WK.MS4) = ⟨1, 0, 0, 0⟩
    rw [M3.tE_one, M3.tE_zero]
  | _ :: _, [], _ => by
    show (⟨tE 1, tE 0, tE 0, tE 0⟩ : Lvm.WK.MS4) = ⟨1, 0, 0, 0⟩
    rw [M3.tE_one, M3.tE_zero]
  | _ :: _, _ :: _, [] => by
    show (⟨tE 1, tE 0, tE 0, tE 0⟩ : Lvm.WK.MS4) = ⟨1, 0, 0, 0⟩
    rw [M3.tE_one, M3.tE_zero]

theorem tE_listSum : ∀ (l : List FE), tE l.sum = (l.map tE).sum
  | [] => M3.tE_zero
  | x :: l => by rw [List.sum_cons, M3.tE_add, tE_listSum l, List.map_cons, List.sum_cons]

theorem tE_eqAt (A : List FE) {i : Nat} (hi : i < 2 ^ A.length) :
    tE (eqAt A i) = LeanVM.Protocol.KeccakGkr.eqAt (A.map tE) i := getD_eqKernel A hi

theorem tE_ltC {tb4 : List FE} (h4 : tb4.length = 4) {e : Nat} (he : e ≤ 16) :
    tE (ltC tb4 e) = Lvm.WK.ltE (tb4.map tE) e := by
  rw [ltC, tE_listSum, Lvm.WK.ltE, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply]
  exact tE_eqAt _ (by rw [h4]; have := List.mem_range.mp hj; (clear * - he this; omega))

theorem tE_getD (l : List FE) (i : Nat) : tE (l.getD i 0) = (l.map tE).getD i 0 := (getD_map_toExt3 l i).symm

/-- **The rows' `msEvalA`**: `toExt3 (msC ρ μ σ tb) = msEvalA ρ μ σ tb 1` (`|σ| = |tb| ≥ 4`). -/
theorem tE_msC {ρ μ σ tb : List FE} (hσ : 4 ≤ σ.length) (htb : 4 ≤ tb.length) :
    tE (msC ρ μ σ tb) = Lvm.WK.msEvalA (ρ.map tE) (μ.map tE) (σ.map tE) (tb.map tE) 1 := by
  have h4 : (σ.take 4).length = 4 := by rw [List.length_take]; (clear * - hσ; omega)
  have ht4 : (tb.take 4).length = 4 := by rw [List.length_take]; (clear * - htb; omega)
  have hq := q4E_msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)
  have h00 := congrArg Lvm.WK.MS4.v00 hq
  have h01 := congrArg Lvm.WK.MS4.v01 hq
  have h10 := congrArg Lvm.WK.MS4.v10 hq
  simp only [q4E] at h00 h01 h10
  unfold Lvm.WK.msEvalA
  rw [List.length_map, ← List.map_drop, ← List.map_take, ← List.map_drop]
  dsimp only
  rw [← h00, ← h01, ← h10, one_mul,
    LeanVM.Protocol.KeccakGkr.sumE_eq_sum, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, ← List.map_take, ← List.map_take]
  unfold msC
  simp only [M3.tE_add, M3.tE_mul, tE_listSum, List.map_map]
  have hA : ∀ d < 16, tE (eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0) =
      LeanVM.Protocol.KeccakGkr.eqAt ((σ.take 4).map tE) d * (μ.map tE).getD ((d + 1) % 16) 0 := by
    intro d hd; rw [M3.tE_mul, tE_eqAt _ (by rw [h4]; omega), tE_getD]
  rw [tE_eqAt _ (by rw [h4]; (clear * -; omega)), tE_getD, show (15 + 1) % 16 = 0 from rfl]
  have s1 : (List.range 15).map (tE ∘ fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * ltC (tb.take 4) (d + 1)) =
      (List.range 15).map fun d => LeanVM.Protocol.KeccakGkr.eqAt ((σ.take 4).map tE) d *
        (μ.map tE).getD ((d + 1) % 16) 0 * Lvm.WK.ltE ((tb.take 4).map tE) (d + 1) :=
    List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [M3.tE_mul, hA d (by (clear * - hd'; omega)), tE_ltC ht4 (by (clear * - hd'; omega))]
  have s2 : (List.range 15).map (tE ∘ fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0) =
      (List.range 15).map fun d => LeanVM.Protocol.KeccakGkr.eqAt ((σ.take 4).map tE) d *
        (μ.map tE).getD ((d + 1) % 16) 0 :=
    List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [hA d (by (clear * - hd'; omega))]
  rw [s1, s2]
  ring

/-! ## `thrEvalA` -/

theorem p2E_thrStepC (r b : FE) (q : FE × FE) :
    p2E (thrStepC r b q) =
      (tE b * ((1 + tE r) * (p2E q).1 + tE r * (p2E q).1) + (1 + tE b) * ((1 + tE r) * (p2E q).1 + tE r * (p2E q).2),
        tE b * ((1 + tE r) * (p2E q).1 + tE r * (p2E q).2) + (1 + tE b) * ((1 + tE r) * (p2E q).2 + tE r * (p2E q).2)) := by
  obtain ⟨q1, q2⟩ := q
  simp only [p2E, thrStepC, M3.tE_add, M3.tE_mul, Prod.mk.injEq]
  constructor
  · linear_combination (-(tE b * tE q1 + tE b * tE r * tE q1)) * (CharTwo.two_eq_zero (R := LeanVM.Parameters.E))
  · linear_combination (-(tE r * tE q2 + tE b * tE r * tE q2)) * (CharTwo.two_eq_zero (R := LeanVM.Parameters.E))

theorem p2E_thrTailC : ∀ (ρ tb : List FE), p2E (thrTailC ρ tb) = Lvm.WK.thrTailA (ρ.map tE) (tb.map tE)
  | r :: ρ, b :: tb => by
    rw [thrTailC, p2E_thrStepC, p2E_thrTailC ρ tb]
    simp only [List.map_cons, Lvm.WK.thrTailA, Lvm.WK.nextS, Bool.false_and, Bool.true_and, Bool.false_or,
      Bool.true_or, ite_true, Bool.false_eq_true, ite_false]
  | [], _ => by show (tE 1, tE 0) = (1, 0); rw [M3.tE_one, M3.tE_zero]
  | _ :: _, [] => by show (tE 1, tE 0) = (1, 0); rw [M3.tE_one, M3.tE_zero]

/-- **The rows' `thrEvalA`**. -/
theorem tE_thrC {ρ μ tb : List FE} (hμ : μ.length = 16) (htb : 4 ≤ tb.length) :
    tE (thrC ρ μ tb) = Lvm.WK.thrEvalA (ρ.map tE) (μ.map tE) (tb.map tE) := by
  have ht4 : (tb.take 4).length = 4 := by rw [List.length_take]; (clear * - htb; omega)
  have hq := p2E_thrTailC ρ (tb.drop 4)
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [p2E] at h1 h2
  unfold Lvm.WK.thrEvalA
  rw [← List.map_drop]
  dsimp only
  rw [← h1, ← h2, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, LeanVM.Protocol.KeccakGkr.sumE_eq_sum,
    ← List.map_take]
  unfold thrC
  simp only [M3.tE_add, M3.tE_mul, tE_listSum, List.map_map]
  have s1 : (List.range 16).map (tE ∘ fun d => μ.getD d 0 * ltC (tb.take 4) d) =
      (List.range 16).map fun d => (μ.map tE).getD d 0 * Lvm.WK.ltE ((tb.take 4).map tE) d :=
    List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [M3.tE_mul, tE_getD, tE_ltC ht4 (by (clear * - hd'; omega))]
  have s2 : μ.map tE = (List.range 16).map fun d => (μ.map tE).getD d 0 := by
    apply List.ext_getElem (by simp [hμ])
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD, show i < μ.length by simpa using h1]
  have s3 : (μ.map tE).sum = ((List.range 16).map fun d => (μ.map tE).getD d 0).sum := congrArg List.sum s2
  rw [s1, s3]
  ring

/-! ## The bits of `m` and V_S's evaluators -/

/-- Bit `j` of `t` as an `FE` (`0` or `1`; the borrow chain's cells, HAR's `bitE`). -/
def bitF (t j : Nat) : FE := if t.testBit j then 1 else 0

theorem bitsF_E : ∀ (t w : Nat), ((List.range w).map (bitF t)).map tE = LeanVM.Protocol.KeccakGkr.bitsE t w
  | _, 0 => rfl
  | t, w + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, LeanVM.Protocol.KeccakGkr.bitsE]
    congr 1
    · simp only [bitF, Nat.testBit_zero]
      split_ifs with h1 h2 h2
      · exact M3.tE_one
      · simp at h1; omega
      · simp at h1; omega
      · exact M3.tE_zero
    · rw [← bitsF_E (t / 2) w, List.map_map, List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, bitF, Nat.testBit_succ]

theorem bitsF_length (t w : Nat) : ((List.range w).map (bitF t)).length = w := by simp

/-- **`K̃_ch(σ)` in the circuit is V_S's**: the rows' `msC` on the bits of `m` is `msEvalF ρ μ σ 0 m`
(`|σ| = |ρ| + 4`, `m < 2^|σ|`). -/
theorem msC_eq_msEvalF {ρ μ σ : List FE} {m : Nat} (hσ : σ.length = ρ.length + 4) (hm : m < 2 ^ σ.length) :
    msC ρ μ σ ((List.range σ.length).map (bitF m)) = msEvalF ρ μ σ 0 m := by
  apply FE.toExt3_injective
  rw [tE_msC (by (clear * - hσ; omega)) (by simp; (clear * - hσ; omega)), toExt3_msEvalF, bitsF_E,
    ← Lvm.WK.msEvalA_bitsE _ _ _ 0 m (by simp; (clear * - hσ; omega)) (by simp; (clear * - hσ; omega)) (by simpa using hm)]
  congr 1
  · simp
  · rw [List.length_map, hσ, Nat.add_sub_cancel, List.drop_eq_nil_of_le (by simp)]; rfl

/-- **`Σ_{i ≤ m} ι(i)` in the circuit is V_S's** (`m < 2^(|ρ| + 4)`). -/
theorem thrC_eq_thrEvalF {ρ μ : List FE} {m : Nat} (hμ : μ.length = 16) (hm : m < 2 ^ (ρ.length + 4)) :
    thrC ρ μ ((List.range (ρ.length + 4)).map (bitF m)) = thrEvalF ρ μ m := by
  apply FE.toExt3_injective
  rw [tE_thrC hμ (by simp), toExt3_thrEvalF, bitsF_E]
  have := Lvm.WK.thrEvalA_bitsE (ρ.map tE) (μ.map tE) m (by simpa using hm)
  rwa [List.length_map] at this

/-! ## The wiring target -/

theorem eqAtF_zero : ∀ (ρ : List FE), eqAtF ρ 0 = (ρ.map (1 + ·)).prod
  | [] => rfl
  | r :: ρ => by
    rw [eqAtF, eqAtF_zero ρ, List.map_cons, List.prod_cons]
    simp

/-- `ω_j` of a represented (non-first) claim is `wOm` of its carried `a`, `B`. -/
theorem wOm_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) {j : Nat} (hj : j < 1600) :
    wOm (repA P cv) (repB P cv) j = C.weights.getD j 0 := by
  rw [hR.weights, if_neg (by decide), lt_pos _ _ hj, wOm]
  rfl

theorem c43_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) :
    wC43 (repA P cv) (repB P cv) = c43DotF C.weights.toArray := by
  simp only [wC43, c43DotF, array_getD_toArray', wOm_rep hR (by norm_num : (0 : Nat) < 1600),
    wOm_rep hR (by norm_num : (1 : Nat) < 1600), wOm_rep hR (by norm_num : (6 : Nat) < 1600),
    wOm_rep hR (by norm_num : (264 : Nat) < 1600), wOm_rep hR (by norm_num : (1087 : Nat) < 1600)]

/-- The bits of a digest's four lanes as `FE` (`0`/`1`), bit `p` of lane `p / 64`. -/
def digBitsF (d : List FK) : List FE :=
  (List.range 256).map fun q => if (d.getD (q / 64) 0).val.toNat.testBit (q % 64) then 1 else 0

theorem padDot_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) (d : List FK) :
    wC43 (repA P cv) (repB P cv) + ((List.range 256).map fun q =>
      wOm (repA P cv) (repB P cv) (8 + q) * (digBitsF d).getD q 0).sum = padDotF C.weights.toArray d := by
  rw [padDotF, c43_rep hR, sumE_eq_sum]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  have hq' := List.mem_range.mp hq
  rw [wOm_rep hR (by (clear * - hq'; omega)), array_getD_toArray']
  simp only [digBitsF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq', Option.map_some,
    Option.getD_some]
  split_ifs <;> simp

/-- **The rows' target is V_S's `wireTargetF`**, for a represented claim with `|ρ| = P + 1`, `m`'s bits and
`s`'s bits. -/
theorem wTgt_eq {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) (s : List FK) {n : Nat}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ (P + 5)) :
    wTgt (cv 0) ((List.range 16).map fun i => cv (1 + i)) ((List.range (P + 1)).map fun i => cv (18 + i))
      (repA P cv) (repB P cv) ((List.range (P + 5)).map (bitF (n - 1))) (digBitsF s) =
      wireTargetF s n C := by
  have hpt : C.point.length = P + 1 := by rw [← hR.point]; simp
  have hmu : C.mu.length = 16 := by rw [← hR.mu]; simp
  unfold wTgt wireTargetF
  rw [show ((List.range (P + 1)).map fun i => cv (18 + i)) = C.point from hR.point,
    show ((List.range 16).map fun i => cv (1 + i)) = C.mu from hR.mu, hR.value,
    show P + 5 = C.point.length + 4 by (clear * - hpt; omega), thrC_eq_thrEvalF hmu (by rw [hpt, show P + 1 + 4 = P + 5 by (clear * -; omega)]; (clear * - hn hN; omega)),
    padDot_rep hR, c43_rep hR]
  simp only [Lvm.iotaF, Nat.zero_div, Nat.zero_mod, eqAtF_zero]
  ring

/-! ## The bits of the child's `s` (S2's `sSpec` class) -/

/-- **The `BITS` outputs of `s`'s lanes** (`sSpec`): bit `z` of the stream lane `hd + 9 + l` at
`sb + 64 l + z`. -/
def SBitsS (v : Nat → FK) (hd sb : Nat) : Prop :=
  ∀ l < 4, ∀ z < 64, Lvm.QSig.Out1 v (hd + 9 + l) (.bit z) (sb + 64 * l + z)

theorem bitWord (w : UInt64) {z : Nat} (hz : z < 64) :
    (Lvm.Bits.BOut.bit z).word w = if w.toNat.testBit z then 1 else 0 := by
  simp only [Lvm.Bits.BOut.word]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hz' : z.toUInt64.toNat % 64 = z := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [hz', show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split_ifs with h <;> simp [Nat.testBit, Nat.shiftRight_eq_div_pow] at h ⊢ <;> omega

/-- **The `s` bit cells hold `digBitsF` of `s`'s lanes.** -/
theorem sbits_vals {v : Nat → FK} {hd sb : Nat} (h : SBitsS v hd sb) :
    ((List.range 256).map fun q => FE.ofK (v (sb + q))) = digBitsF ((List.range 4).map fun l => v (hd + 9 + l)) := by
  unfold digBitsF
  refine List.map_congr_left fun q hq => ?_
  have hq' := List.mem_range.mp hq
  have h1 := h (q / 64) (by (clear * - hq'; omega)) (q % 64) (Nat.mod_lt _ (by (clear * -; omega)))
  rw [show sb + 64 * (q / 64) + q % 64 = sb + q by (clear * -; omega)] at h1
  unfold Lvm.QSig.Out1 at h1
  rw [h1, bitWord _ (Nat.mod_lt _ (by (clear * -; omega)))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show q / 64 < 4 by (clear * - hq'; omega)),
    Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- **`dRange` needs no circuit**: Q_sig's `ChildOk` already asserts `1 ≤ n' ∧ n' ≤ 2^ln` on the child's header
lane `n'` (`LvmQSigDefs.ChildOk`, `ln = logN` in `cfg20`/`cfg8`), so V_S's range `require` keeps the flag. -/
theorem dRange_run (pp : Params) (pub : Pub) (sig : ByteArray) (s : RS) (h1 : 1 ≤ pub.n)
    (h2 : pub.n ≤ 2 ^ pp.logN) : dRange pp pub sig s = ((), s) := by
  unfold dRange
  rw [require_run]
  simp [h1, h2]

/-! ## The gadget -/

section gadget

open Lvm.Loop Lvm.Loop.Build Lvm.Har

theorem log2_cover (w : Nat) (hw : 1 ≤ w) : w ≤ 2 ^ Nat.log2 (2 * w - 1) := by
  have h := Nat.lt_log2_self (n := 2 * w - 1)
  rw [Nat.pow_succ] at h
  omega

theorem tassert_one {ins : List Ins} {M : Mem} {p : Ptr} :
    SegsAssert M p (loop [] (tplOf ins) p).2 ↔ TAssert (iterXv M ⟨p, [], tplOf ins⟩ 0) (iterF M ⟨p, [], tplOf ins⟩ 0) ins := by
  rw [segsAssert_loop_iff]
  exact ⟨fun h => h 0 (by simp), fun h jf hjf => by rw [show jf = 0 by simpa using hjf]; exact h⟩

/-- **The wire gadget's cells and assertions**, in the stream's values (`v = feAt Σ`): the wiring
challenges are `F`'s sumcheck challenges from the rows' target, `g_D` and the slices are the stream's
scalars, the slot challenges are the slot sumcheck's from `g_D`, the ring switch's cells are
`ringG_spec`'s; with the gate `1`, the assertions hold iff the two checks do (the final check with
the rows' `msC`, the slot check with the rows' `ω`). -/
theorem wire_core {c : Ctx} {M : Mem} {p : Ptr} {P qw zE : Nat} {cv : Nat → Cell} {mb sb : List Cell}
    {b : Cell} {sig : ByteArray} {T : Nat} (hq : 5 ≤ qw) (hS : Streamed M sig T)
    (hT : wireEnd P qw + 2 ≤ T) (hmb : mb.length = P + 5) (hsb : sb.length = 256) (hzE : M.e zE = 0)
    (h : SegsHold c M p (wireGadget P qw cv mb sb b zE p).2) :
    let tgt := wTgt ((cv 0).val M) ((List.range 16).map fun i => (cv (1 + i)).val M)
      ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) ((List.range 6).map fun i => (cv (44 + P + i)).val M)
      ((List.range 25).map fun l => (cv (19 + P + l)).val M) (vs M mb) (vs M sb)
    let sc := scSpec (feAt sig) 3 (8 * qw - 40) tgt (List.replicate (P + 5) none)
    let g := feAt sig (8 * (qw + 15 * (P + 5)))
    let sl := scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40) g (List.replicate 2 none)
    vs M (wireGadget P qw cv mb sb b zE p).1.sigma = sc.1 ∧
    (wireGadget P qw cv mb sb b zE p).1.gD.val M = g ∧
    vs M (wireGadget P qw cv mb sb b zE p).1.tau = sl.1 ∧
    vs M (wireGadget P qw cv mb sb b zE p).1.ring.cs = ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225)) ∧
    (wireGadget P qw cv mb sb b zE p).1.ring.target.val M =
      polyEval ((slAt sig (qw + 15 * (P + 5) + 33)).map (phiMap · (chsAt sig (qw + 15 * (P + 5) + 225)))) gen ∧
    (b.val M = 1 → SegsAssert M p (wireGadget P qw cv mb sb b zE p).2 →
      msC ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) ((List.range 16).map fun i => (cv (1 + i)).val M)
          sc.1 (vs M mb) * g + sc.2 = 0 ∧
      sl.2 + ((List.range 64).map fun zz => ((List.range 4).map fun o => eqAt sl.1 o *
          wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M) ((List.range 25).map fun l => (cv (19 + P + l)).val M)
            (8 + 64 * o + zz)).sum * (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0).sum = 0) := by
  intro tgt sc g sl
  have hTe : wireEnd P qw = qw + 15 * (P + 5) + 225 + 54 := rfl
  simp only [wireGadget, hold_bind, assert_bind, gk_bind_fst_eq, gk_pure_apply_eq] at h ⊢
  obtain ⟨hPre, hSc, hPost, hSl, hSlot, hRing, -⟩ := h
  -- the target block
  set G := preW P (fun j => gkS (cv j)) (mb.map gkS) (sb.map gkS) (gkS b) 0 with hG
  have hpre0 := thold_of_loop hPre (jf := 0) (by simp)
  rw [gk_loop_fst] at hpre0
  obtain ⟨ez, fz, eo, fo, eom, fom, elt, flt, etg, ftg⟩ :=
    preW_spec (P := P) (cv := fun j => gkS (cv j)) (mb := mb.map gkS) (sb := sb.map gkS) (b := gkS b)
      (by simp [hmb]) (by simp [hsb]) hpre0
  have hvs : ∀ l : List Cell, vals (iterXv M ⟨p, [], tplOf G.2⟩ 0) (iterF M ⟨p, [], tplOf G.2⟩ 0) (l.map gkS) = vs M l :=
    fun l => by simp only [vals, List.map_map, vs]; exact List.map_congr_left fun x _ => gkS_valF M _ 0 _ x
  simp only [gkS_valF, hvs] at etg eom
  have htg : (G.1.target.gkCell ⟨p, [], tplOf G.2⟩).val M = tgt := by rw [gkCell_val M _ ftg, etg]
  simp only [gk_loop_fst] at hSc hPost hSl hSlot hRing ⊢
  generalize p.adv (loop [] (tplOf G.2) p).2 = p1 at hSc hPost hSl hSlot hRing ⊢
  -- the wiring sumcheck
  obtain ⟨hc1, hv1⟩ := gk_sc_lists (D := Nat.log2 (2 * (P + 5) - 1)) (R := P + 5) (log2_cover _ (by (clear * -; omega)))
    (by (clear * -; omega)) hq hS (by simp only [roundLanes]; (clear * - hT hTe; omega)) hSc
  rw [htg] at hc1 hv1
  set pre : LoopOut := ⟨p, [], tplOf G.2⟩ with hpre
  set scO := (scGadget (Nat.log2 (2 * (P + 5) - 1)) 2 qw .plain (G.1.target.gkCell pre) p1).1 with hscO
  generalize p1.adv (scGadget (Nat.log2 (2 * (P + 5) - 1)) 2 qw .plain (G.1.target.gkCell pre) p1).2 = p2
    at hPost hSl hSlot hRing ⊢
  -- the final check block
  set H := postW P (qw + 15 * (P + 5)) (fun j => gkS (cv j)) (mb.map gkS)
    (((List.range (P + 5)).map fun i => scO.cell 2 i).map gkS) (G.1.lt.map (Src.gkOut pre)) (G.1.z.gkOut pre)
    (G.1.one.gkOut pre) (gkS (scO.cell 5 (P + 5 - 1))) (gkS b) 0 with hH
  have hpost0 := thold_of_loop hPost (jf := 0) (by simp)
  rw [gk_loop_fst] at hpost0
  set post : LoopOut := ⟨p2, [], tplOf H.2⟩ with hpost
  have hpv : ∀ (o : LoopOut), vals (iterXv M o 0) (iterF M o 0) ((mb.map gkS).take 4) = (vs M mb).take 4 :=
    fun o => by
      simp only [vals, List.map_take, List.map_map, vs]
      rw [List.map_congr_left (l := mb) (f := Src.valF (iterXv M o 0) (iterF M o 0) ∘ gkS) (g := Cell.val M)
        fun x _ => gkS_valF M o 0 _ x]
  have hltP : vals (iterXv M post 0) (iterF M post 0) (G.1.lt.map (Src.gkOut pre)) =
      (List.range 17).map (ltC (vals (iterXv M post 0) (iterF M post 0) ((mb.map gkS).take 4))) := by
    have e : vals (iterXv M post 0) (iterF M post 0) (G.1.lt.map (Src.gkOut pre)) =
        vals (iterXv M pre 0) (iterF M pre 0) G.1.lt := by
      simp only [vals, List.map_map]
      exact List.map_congr_left fun x hx => gkOut_val M pre post 0 _ (flt x hx)
    rw [e, elt, hpv, hpv]
  have hzP : (G.1.z.gkOut pre).valF (iterXv M post 0) (iterF M post 0) = 0 := by rw [gkOut_val M pre post 0 _ fz, ez]
  have hoP : (G.1.one.gkOut pre).valF (iterXv M post 0) (iterF M post 0) = 1 := by rw [gkOut_val M pre post 0 _ fo, eo]
  obtain ⟨egD, hApost⟩ := postW_spec hzP hoP (by simp) hltP hpost0
  have hfxH : Fx H.1 := by
    show Fx (postW _ _ _ _ _ _ _ _ _ _ 0).1
    simp only [postW, tb_bind, tb_pure]
    exact fx_emit _ _
  have hgv : (H.1.gkCell post).val M = g := by
    rw [gkCell_val M _ hfxH, egD, gk_lv_fix hS post 0 _ (by simp only [wireEnd] at hT; (clear * - hT hmb hTe; omega))]
  generalize p2.adv (loop [] (tplOf H.2) p2).2 = p3 at hSl hSlot hRing ⊢
  -- the slot sumcheck
  obtain ⟨hc2, hv2⟩ := gk_sc_lists (D := 1) (R := 2) (by norm_num) (by norm_num) (by (clear * - hq hTe; omega)) hS
    (by simp only [roundLanes, wireEnd] at hT ⊢; (clear * - hT hmb hTe; omega)) hSl
  rw [hgv] at hc2 hv2
  set slO := (scGadget 1 2 (qw + 15 * (P + 5) + 3) .plain (H.1.gkCell post) p3).1 with hslO
  generalize p3.adv (scGadget 1 2 (qw + 15 * (P + 5) + 3) .plain (H.1.gkCell post) p3).2 = p4 at hSlot hRing ⊢
  -- the slot check block
  set Sb := slotW (qw + 15 * (P + 5) + 33) (G.1.om.map (Src.gkOut pre))
    (((List.range 2).map fun i => slO.cell 2 i).map gkS) (G.1.z.gkOut pre) (G.1.one.gkOut pre)
    (gkS (slO.cell 5 1)) (gkS b) 0 with hSb
  have hslot0 := thold_of_loop hSlot (jf := 0) (by simp)
  rw [gk_loop_fst] at hslot0
  set slb : LoopOut := ⟨p4, [], tplOf Sb.2⟩ with hslb
  have hzS : (G.1.z.gkOut pre).valF (iterXv M slb 0) (iterF M slb 0) = 0 := by rw [gkOut_val M pre slb 0 _ fz, ez]
  have hoS : (G.1.one.gkOut pre).valF (iterXv M slb 0) (iterF M slb 0) = 1 := by rw [gkOut_val M pre slb 0 _ fo, eo]
  have hAslot := slotW_spec hzS hoS (by simp) hslot0
  generalize p4.adv (loop [] (tplOf Sb.2) p4).2 = p5 at hRing ⊢
  -- the ring switch
  obtain ⟨hcs, htgt⟩ := ringG_spec hS (by simp only [wireEnd] at hT; (clear * - hT hmb hTe; omega)) (by simp only [wireEnd] at hT; (clear * - hT hmb hTe; omega))
    hzE hRing
  refine ⟨by rw [vs, List.map_map]; exact hc1.symm, hgv, by rw [vs, List.map_map]; exact hc2.symm, hcs, htgt, ?_⟩
  rintro hb ⟨-, -, hAP, -, hAS, -, -⟩
  have hbv : (gkS b).valF (iterXv M post 0) (iterF M post 0) = 1 := by rw [gkS_valF, hb]
  have hbv' : (gkS b).valF (iterXv M slb 0) (iterF M slb 0) = 1 := by rw [gkS_valF, hb]
  constructor
  · have e := hApost.mp (tassert_one.mp hAP)
    rw [hbv, one_mul, gk_lv_fix hS post 0 _ (by simp only [wireEnd] at hT; (clear * - hT hmb hTe; omega)), gkS_valF, ← hv1] at e
    have e1 : ((List.range (P + 1)).map fun i => (gkS (cv (18 + i))).valF (iterXv M post 0) (iterF M post 0)) =
        (List.range (P + 1)).map fun i => (cv (18 + i)).val M := List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have e2 : ((List.range 16).map fun i => (gkS (cv (1 + i))).valF (iterXv M post 0) (iterF M post 0)) =
        (List.range 16).map fun i => (cv (1 + i)).val M := List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have e3 : vals (iterXv M post 0) (iterF M post 0) (((List.range (P + 5)).map fun i => scO.cell 2 i).map gkS) = sc.1 := by
      rw [hc1]; simp only [vals, List.map_map]; exact List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have e4 : vals (iterXv M post 0) (iterF M post 0) (mb.map gkS) = vs M mb := by
      simp only [vals, List.map_map, vs]; exact List.map_congr_left fun x _ => gkS_valF M _ 0 _ _
    rw [e1, e2, e3, e4] at e
    exact e
  · have e := hAslot.mp (tassert_one.mp hAS)
    rw [hbv', one_mul, gkS_valF, ← hv2] at e
    have hτ : vals (iterXv M slb 0) (iterF M slb 0) (((List.range 2).map fun i => slO.cell 2 i).map gkS) = sl.1 := by
      rw [hc2]; simp only [vals, List.map_map]; exact List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have homL : G.1.om.length = 261 := by
      have := congrArg List.length eom; simp only [vals, List.length_map, wPos_length] at this; exact this
    have hom : ∀ o < 4, ∀ zz < 64, ((G.1.om.map (Src.gkOut pre)).getD (wIx (64 * o + zz)) default).valF
        (iterXv M slb 0) (iterF M slb 0) = wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M)
          ((List.range 25).map fun l => (cv (19 + P + l)).val M) (8 + 64 * o + zz) := by
      intro o ho zz hzz
      have hk : wIx (64 * o + zz) < G.1.om.length := by rw [homL]; simp only [wIx]; (clear * - ho hzz; omega)
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
        gkOut_val M pre slb 0 _ (fom _ (List.getElem_mem hk)), ← List.getD_eq_getElem _ default hk,
        getD_vals _ hk, eom, wPos_map_getD _ (by simp only [wIx]; (clear * - ho hzz; omega)), wPos_getD_ix (by (clear * - ho hzz; omega))]
      rw [show 8 + (64 * o + zz) = 8 + 64 * o + zz by (clear * -; omega)]
    rw [hτ] at e
    have hs : ((List.range 64).map fun zz => ((List.range 4).map fun o => eqAt sl.1 o *
        ((G.1.om.map (Src.gkOut pre)).getD (wIx (64 * o + zz)) default).valF (iterXv M slb 0) (iterF M slb 0)).sum *
          lv (iterXv M slb 0) [] (qw + 15 * (P + 5) + 33 + 3 * zz)) =
        (List.range 64).map fun zz => ((List.range 4).map fun o => eqAt sl.1 o *
          wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M) ((List.range 25).map fun l => (cv (19 + P + l)).val M)
            (8 + 64 * o + zz)).sum * (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0 := by
      refine List.map_congr_left fun zz hzz => ?_
      have hzz' := List.mem_range.mp hzz
      rw [gk_lv_fix hS slb 0 _ (by simp only [wireEnd] at hT; (clear * - hT hmb hTe hzz'; omega))]
      have h1 := congrArg List.sum (List.map_congr_left (l := List.range 4) fun o ho =>
        congrArg (eqAt sl.1 o * ·) (hom o (List.mem_range.mp ho) zz hzz'))
      have h2 : feAt sig (8 * (qw + 15 * (P + 5) + 33 + 3 * zz)) = (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0 := by
        simp only [slAt, kBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hzz',
          Option.map_some, Option.getD_some]
      rw [h1, h2]
    rw [hs] at e
    have hsl : sl = scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40) g (List.replicate 2 none) := rfl
    rw [hsl]
    exact e

/-- `F`'s ring switch on a view (`ringSwitch_run`, HAR's, restated below the v1 phase cut). -/
theorem ringSwitch_runW (sig : ByteArray) (point sv : List FE) (st : RS) :
    ringSwitch point sv sig st =
      ((polyEval (sv.map (phiMap · (sampAt (feAt sig) (st.ent + st.msg) ringStages))) gen,
        fun r' => ringWeight point r' (ringCoefficients (sampAt (feAt sig) (st.ent + st.msg) ringStages))),
        ⟨st.ent + st.msg + 72 * ringStages, 0, st.ok⟩) := by
  rw [show ringSwitch point sv = (samples ringStages >>= fun challenges =>
    pure (polyEval (sv.map (phiMap · challenges)) gen,
      fun rPrime => ringWeight point rPrime (ringCoefficients challenges))) from rfl,
    bind_run, show ringStages = 5 + 1 from rfl, gk_samples_run sig 5 st _ rfl, pure_run]

theorem sampAt_chs (sig : ByteArray) {q : Nat} (hq : 5 ≤ q) :
    sampAt (feAt sig) (8 * q - 40) ringStages = chsAt sig q := by
  simp only [sampAt, chsAt]
  exact List.map_congr_left fun i _ => congrArg _ (by omega)

/-- **T-V's `dWire` on a view, replayed by the wire gadget** (`logN = P + 5`): from the wire's position
`8 qw − 40` (the tape's end), with the input claim represented by the cells `cv`, `m`'s bits in `mb` and
`s`'s bits in `sb`, `F`'s wiring point, `g_D`, slot point and ring switch are the gadget's cells, `F`'s
position after is the gadget's last lane, and with the gate `1` the gadget's assertions keep `F`'s flag. -/
theorem wire_spec {c : Ctx} {M : Mem} {p : Ptr} {P qw zE : Nat} {cv : Nat → Cell} {mb sb : List Cell}
    {b : Cell} {sig : ByteArray} {T : Nat} (hq : 5 ≤ qw) (hS : Streamed M sig T)
    (hT : wireEnd P qw + 2 ≤ T) (hzE : M.e zE = 0)
    (h : SegsHold c M p (wireGadget P qw cv mb sb b zE p).2)
    (pp : Params) (hlog : pp.logN = P + 5) (pub : Pub) (hn : 1 ≤ pub.n) (hN : pub.n ≤ 2 ^ (P + 5))
    {claim : KeccakClaim} (hR : Rep P (fun j => (cv j).val M) claim false)
    (hmb : vs M mb = (List.range (P + 5)).map (bitF (pub.n - 1))) (hsb : vs M sb = digBitsF pub.s)
    (s : RS) (hs : s.ent + s.msg = 8 * qw - 40) :
    (dWire pp pub claim sig s).1.sc.1 = vs M (wireGadget P qw cv mb sb b zE p).1.sigma ∧
    (dWire pp pub claim sig s).1.g = [(wireGadget P qw cv mb sb b zE p).1.gD.val M] ∧
    (dWire pp pub claim sig s).1.sl.1 = vs M (wireGadget P qw cv mb sb b zE p).1.tau ∧
    (dWire pp pub claim sig s).1.sc.2 =
      (scSpec (feAt sig) 3 (8 * qw - 40) (wireTargetF pub.s pub.n claim) (List.replicate (P + 5) none)).2 ∧
    (dWire pp pub claim sig s).1.sl.2 = (scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40)
      (feAt sig (8 * (qw + 15 * (P + 5)))) [none, none]).2 ∧
    (dWire pp pub claim sig s).1.sv = slAt sig (qw + 15 * (P + 5) + 33) ∧
    (dWire pp pub claim sig s).1.ring.1 = (wireGadget P qw cv mb sb b zE p).1.ring.target.val M ∧
    (dWire pp pub claim sig s).1.ring.2 = (fun r' => ringWeight
      ((dWire pp pub claim sig s).1.sc.1 ++ (dWire pp pub claim sig s).1.sl.1 ++ selectorPoint (dSel pp) (dSelBits pp))
      r' (vs M (wireGadget P qw cv mb sb b zE p).1.ring.cs)) ∧
    (dWire pp pub claim sig s).2.ent = 8 * wireEnd P qw - 40 ∧ (dWire pp pub claim sig s).2.msg = 0 ∧
    (b.val M = 1 → SegsAssert M p (wireGadget P qw cv mb sb b zE p).2 → (dWire pp pub claim sig s).2.ok = s.ok) := by
  have hmbL : mb.length = P + 5 := by have := congrArg List.length hmb; simpa [vs] using this
  have hsbL : sb.length = 256 := by have := congrArg List.length hsb; simpa [vs, digBitsF] using this
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := wire_core hq hS hT hmbL hsbL hzE h
  have htgt : wTgt ((cv 0).val M) ((List.range 16).map fun i => (cv (1 + i)).val M)
      ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) ((List.range 6).map fun i => (cv (44 + P + i)).val M)
      ((List.range 25).map fun l => (cv (19 + P + l)).val M) (vs M mb) (vs M sb) = wireTargetF pub.s pub.n claim := by
    rw [hmb, hsb]; exact wTgt_eq hR pub.s hn hN
  rw [htgt] at e1 e6
  have hst1 : scState 3 s (List.replicate (P + 5) none) = ⟨8 * qw - 40 + (P + 5) * roundLen 3, 0, s.ok⟩ := by
    rw [show P + 5 = (P + 4) + 1 from rfl, List.replicate_succ]
    show (⟨s.ent + s.msg + _, 0, s.ok⟩ : RS) = _
    rw [hs, List.length_cons, List.length_replicate]
  have hrl : roundLen 3 = 120 := rfl
  unfold dWire
  rw [hlog, bind_run, sumcheck_run sig 3 (by norm_num), hs, hst1, bind_run, readEs_run, bind_run, require_run,
    bind_run, sumcheck_run sig 3 (by norm_num), bind_run, readEs_run, bind_run, require_run, bind_run,
    ringSwitch_runW, pure_run]
  simp only [scState, List.length_cons, List.length_nil, hrl]
  have hg : scalarsAt (feAt sig) (8 * qw - 40 + (P + 5) * 120 + 0 + 40) 1 = [feAt sig (8 * (qw + 15 * (P + 5)))] := by
    simp only [scalarsAt, List.range_one, List.map_cons, List.map_nil]
    exact congrArg (fun x => [feAt sig x]) (by (clear * - hq; omega))
  have hp1 : 8 * qw - 40 + (P + 5) * 120 + (0 + 24 * 1) = 8 * (qw + 15 * (P + 5) + 3) - 40 := by (clear * - hq hmbL; omega)
  have hsv : scalarsAt (feAt sig) (8 * (qw + 15 * (P + 5) + 3) - 40 + (0 + 1 + 1) * 120 + 0 + 40) kBits =
      slAt sig (qw + 15 * (P + 5) + 33) := by
    simp only [scalarsAt, slAt]
    exact List.map_congr_left fun k _ => congrArg _ (by (clear * - hq hmbL; omega))
  have hpr : 8 * (qw + 15 * (P + 5) + 3) - 40 + (0 + 1 + 1) * 120 + (0 + 24 * kBits) =
      8 * (qw + 15 * (P + 5) + 225) - 40 := by simp only [kBits]; (clear * - hq hmbL; omega)
  have hend : 8 * (qw + 15 * (P + 5) + 225) - 40 + 72 * ringStages = 8 * wireEnd P qw - 40 := by
    simp only [ringStages, wireEnd]; (clear * - hq hmbL hpr; omega)
  rw [hg, hp1, hsv, hpr, sampAt_chs sig (by (clear * - hq hmbL; omega)), hend]
  simp only [List.getD_cons_zero]
  refine ⟨e1.symm, by rw [e2], e3.symm, trivial, trivial, trivial, e5.symm, by rw [e4], trivial, trivial, fun hb hA => ?_⟩
  obtain ⟨c1, c2⟩ := e6 hb hA
  have hσL : (scSpec (feAt sig) 3 (8 * qw - 40) (wireTargetF pub.s pub.n claim) (List.replicate (P + 5) none)).1.length =
      claim.point.length + 4 := by
    rw [gk_scSpec_length, List.length_replicate, ← hR.point]; simp
  have hptv : ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) = claim.point := hR.point
  have hmuv : ((List.range 16).map fun i => (cv (1 + i)).val M) = claim.mu := hR.mu
  have hm := msC_eq_msEvalF (μ := claim.mu) (m := pub.n - 1) hσL
    (by rw [gk_scSpec_length, List.length_replicate]; (clear * - hn hN; omega))
  rw [gk_scSpec_length, List.length_replicate] at hm
  rw [hptv, hmuv, hmb, hm, gk_add_eq_zero] at c1
  have hd : dot (slotWF claim.weights.toArray (scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40)
      (feAt sig (8 * (qw + 15 * (P + 5)))) [none, none]).1) (slAt sig (qw + 15 * (P + 5) + 33)) =
      ((List.range 64).map fun zz => ((List.range 4).map fun o => eqAt (scSpec (feAt sig) 3
        (8 * (qw + 15 * (P + 5) + 3) - 40) (feAt sig (8 * (qw + 15 * (P + 5)))) [none, none]).1 o *
          wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M) ((List.range 25).map fun l => (cv (19 + P + l)).val M)
            (8 + 64 * o + zz)).sum * (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0).sum := by
    rw [gk_dot_eq_sum (n := 64) (by simp [slotWF]) (by simp [slAt, kBits])]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    congr 1
    simp only [slotWF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hzz', Option.map_some,
      Option.getD_some, sumE_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
    have ho' := List.mem_range.mp ho
    rw [array_getD_toArray', ← wOm_rep hR (by (clear * - hzz' ho'; omega))]
    rfl
  rw [show (List.replicate 2 none : List (Option FE)) = [none, none] from rfl, ← hd, gk_add_eq_zero] at c2
  rw [(gk_fe_beq _ _).mpr c2, (gk_fe_beq _ _).mpr c1.symm]
  simp

end gadget

end Lvm.Q1
