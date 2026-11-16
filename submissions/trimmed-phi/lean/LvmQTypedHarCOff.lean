/- `LvmQTypedHarCOff` (GOLF2 off-path move, group 42 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQWireSound, LvmQShapeH, LvmQAsmHarP47, LvmQAsmHarTails, LvmQTypedHarC,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQWireSound
import LvmQShapeH
import LvmQAsmHarP47
import LvmQAsmHarTails
import LvmQTypedHarC
import LvmE2QHarPosOff
import LvmE2QNodeChkGOff
import LvmFinPosOff
import LvmQAccSoundOff
import LvmQAsmArith2Off
import LvmQAsmHar47Off
import LvmQEqKeccakTapeOff
import LvmQTypedHarZOff
import LvmVEqWireOff
import LvmChainTablePad
import LvmMlListLemmas
import LvmQAsmHar47

-- ===== from `LvmQWireSound` =====

section
section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {xv : Src → FE} {V : Nat → FE}

theorem pr_bind {α β : Type} {n : Nat} (m : TB α) (f : α → TB β) (h : THold xv V n ((m >>= f) n).2) :
    THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 :=
  (thold_bind m f).mp h

theorem pr_fst {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) :
    ((m >>= f) n).1 = (f (m n).1 (n + (m n).2.length)).1 := by rw [tb_bind]

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
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm DM Lvm.VEq Lvm.VEq.Wr
local notation "tE" => FE.toExt3

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

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm DM Lvm.VEq Lvm.VEq.Wr
local notation "tE" => FE.toExt3

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

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm DM Lvm.VEq Lvm.VEq.Wr
local notation "tE" => FE.toExt3

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

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm DM Lvm.VEq Lvm.VEq.Wr
local notation "tE" => FE.toExt3
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
end

-- ===== from `LvmQShapeH` =====

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm DM Lvm.VEq Lvm.VEq.Wr Lvm.Loop Lvm.Loop.Build Lvm.Har

/-- `ringSwitchC` on a view. -/
theorem ringSwitchC_runW (sig : ByteArray) (sv : List FE) (st : RS) :
    Lvm.Shape.ringSwitchC sv sig st =
      ((polyEval (sv.map (phiMap · (sampAt (feAt sig) (st.ent + st.msg) ringStages))) gen,
        ringCoefficients (sampAt (feAt sig) (st.ent + st.msg) ringStages)),
        ⟨st.ent + st.msg + 72 * ringStages, 0, st.ok⟩) := by
  rw [show Lvm.Shape.ringSwitchC sv = (samples ringStages >>= fun challenges =>
    pure (polyEval (sv.map (phiMap · challenges)) gen, ringCoefficients challenges)) from rfl,
    bind_run, show ringStages = 5 + 1 from rfl, gk_samples_run sig 5 st _ rfl, pure_run]

/-- **`dWireC`'s coefficients** are read at the wire's challenge lanes. -/
theorem dWireC_snd {P qw : Nat} (hq : 5 ≤ qw) (pp : Params) (hlog : pp.logN = P + 5) (pub : Pub)
    (claim : KeccakClaim) (sig : ByteArray) (s : RS) (hs : s.ent + s.msg = 8 * qw - 40) :
    (Lvm.Shape.dWireC pp pub claim sig s).1.2 = ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225)) := by
  have hst1 : scState 3 s (List.replicate (P + 5) none) = ⟨8 * qw - 40 + (P + 5) * roundLen 3, 0, s.ok⟩ := by
    rw [show P + 5 = (P + 4) + 1 from rfl, List.replicate_succ]
    show (⟨s.ent + s.msg + _, 0, s.ok⟩ : RS) = _
    rw [hs, List.length_cons, List.length_replicate]
  have hrl : roundLen 3 = 120 := rfl
  unfold Lvm.Shape.dWireC
  rw [hlog, bind_run, sumcheck_run sig 3 (by norm_num), hs, hst1, bind_run, readEs_run, bind_run, require_run,
    bind_run, sumcheck_run sig 3 (by norm_num), bind_run, readEs_run, bind_run, require_run, bind_run,
    ringSwitchC_runW, pure_run]
  simp only [scState, List.length_cons, List.length_nil, hrl]
  have hp1 : 8 * qw - 40 + (P + 5) * 120 + (0 + 24 * 1) = 8 * (qw + 15 * (P + 5) + 3) - 40 := by (clear * - hq; omega)
  have hpr : 8 * (qw + 15 * (P + 5) + 3) - 40 + (0 + 1 + 1) * 120 + (0 + 24 * kBits) =
      8 * (qw + 15 * (P + 5) + 225) - 40 := by simp only [kBits]; (clear * - hq; omega)
  rw [hp1, hpr, sampAt_chs sig (by (clear * - hq; omega))]

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm DM

/-- `wirePh` is `wirePhC`'s first component. -/
theorem wirePh_runC (pp : Params) (pub : Pub) (claim : KeccakClaim) (sig : ByteArray) (s : RS) :
    wirePh pp pub claim sig s = ((wirePhC pp pub claim sig s).1.1, (wirePhC pp pub claim sig s).2) := by
  have br : ∀ {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS),
      (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := fun _ _ _ _ => rfl
  have pr : ∀ {α : Type} (a : α) (sig : ByteArray) (s : RS), (pure a : DM α) sig s = (a, s) := fun _ _ _ => rfl
  unfold wirePh wirePhC
  rw [Lvm.Shape.dWire_eqC, br, br, br, pr]

/-- **The wire phase with its coefficients** (`wirePhC`) from `wirePh`'s phase fact: the coefficients are read
at the wire's challenge lanes. -/
theorem wireC_phase {pp : Params} {pub : Pub} {claim : KeccakClaim} {sig : ByteArray} {P5 P6 : Nat} {wo : WireOut}
    {P qw : Nat} (hW : PhaseAt (wirePh pp pub claim) sig P5 P6 wo) (hq : 5 ≤ qw) (hlog : pp.logN = P + 5)
    (hn1 : 1 ≤ pub.n) (hnN : pub.n ≤ 2 ^ pp.logN) (hP5 : 8 * qw - 40 = P5) :
    PhaseAt (wirePhC pp pub claim) sig P5 P6 (wo, ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225))) := by
  intro s hs hok
  have hw := hW s hs hok
  rw [wirePh_runC] at hw
  have br : ∀ {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS),
      (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := fun _ _ _ _ => rfl
  have hc : (wirePhC pp pub claim sig s).1.2 = ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225)) := by
    unfold wirePhC
    rw [br, Lvm.Q1.dRange_run pp pub sig s hn1 hnN]
    dsimp only
    exact Lvm.Q1.dWireC_snd hq pp hlog pub claim sig s (by simp only [pos] at hs; (clear * - hP5 hs; omega))
  generalize wirePhC pp pub claim sig s = X at hw hc ⊢
  obtain ⟨⟨a, b⟩, st⟩ := X
  obtain ⟨h1, h2, h3⟩ := hw
  exact ⟨by rw [show a = wo from h1, show b = _ from hc], h2, h3⟩

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.QShape
open Lvm Lvm.Shape Lvm.Har

theorem zF_sel (l : ℕ) (hl : l < 4) :
    zF ((selectorPoint l 2).getD 0 0) ((selectorPoint l 2).getD 1 0) = zStarF l := by
  have h4 : (4 : FE) = 0 := by
    rw [show (4 : FE) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
  rw [zF_eq]
  interval_cases l <;>
    simp [selectorPoint, List.range_succ, Har.eOfNat_zero, Har.eOfNat_one, CharTwo.add_self_eq_zero] <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, h4]

/-- **`D`'s point claims**: the cells' tail is `V_S`'s `tailDF`. -/
theorem tailD_pt (r : List FE) (hr : r.length = 20) (l : ℕ) (hl : l < 4) :
    tailD (r ++ selectorPoint l 2) = tailDF r l := by
  have g : ∀ i < 20, (r ++ selectorPoint l 2).getD i 0 = r.getD i 0 := fun i hi ↦ getD_append_lo (by (clear * - hr hi; omega))
  have g2 : ∀ j < 2, (r ++ selectorPoint l 2).getD (20 + j) 0 = (selectorPoint l 2).getD j 0 := fun j _ ↦ by
    rw [show 20 + j = r.length + j by (clear * - hr; omega), getD_append_hi]
  rw [tailD, kappaD, g 18 (by norm_num), g 19 (by norm_num), show 20 = 20 + 0 from rfl, g2 0 (by norm_num),
    show 21 = 20 + 1 from rfl, g2 1 (by norm_num), zF_sel l hl, tailDF, CharTwo.sub_eq_add, CharTwo.sub_eq_add,
    CharTwo.sub_eq_add]

/-- **`D`'s boundary claims** (`m < 2^18`): no tail. -/
theorem tailD_bnd (m : ℕ) (hm : m < 2 ^ 18) (l : ℕ) :
    tailD (selectorPoint m 20 ++ selectorPoint l 2) = 0 := by
  have g : ∀ i < 20, (selectorPoint m 20 ++ selectorPoint l 2).getD i 0 = eOfNat ((m >>> i) % 2) := fun i hi ↦ by
    rw [getD_append_lo (by rw [selectorPoint_length']; omega), selectorPoint_getD' hi]
  rw [tailD, kappaD, g 18 (by norm_num), g 19 (by norm_num), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    show m / 2 ^ 18 % 2 = 0 by (clear * - hm; omega), show m / 2 ^ 19 % 2 = 0 by (clear * - hm; omega)]
  simp [Har.eOfNat_zero, CharTwo.add_self_eq_zero]

/-- **The tape's ring claim** (`pt` zero above `D`: its `ν − 22` block bits): the cells' tail is `V_S`'s
`ringTailN`. -/
theorem tailR_eq (pt cs : List FE) (hpt : pt.length = CMain.nu20)
    (h0 : pt.drop 22 = List.replicate (CMain.nu20 - 22) 0) :
    tailR pt cs = ringTailN pt cs := by
  rw [ringTailN_eq', ringTailF_sum, tailR]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  have hpow : ∀ i, (0 : FE) ^ 2 ^ i = 0 := fun i ↦ zero_pow (by positivity)
  have hl : (pt.map (· ^ 2 ^ k)).length = CMain.nu20 := by rw [List.length_map, hpt]
  have hd : (pt.map (· ^ 2 ^ k)).drop 22 = List.replicate (CMain.nu20 - 22) 0 := by
    rw [← List.map_drop, h0, List.map_replicate, hpow]
  have g : ∀ i < CMain.nu20, (pt.map (· ^ 2 ^ k)).getD i 0 = (pt.getD i 0) ^ 2 ^ k := fun i hi ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show i < pt.length by (clear * - hpt hl hi; omega))]
  rw [tailPtF, hd, kappaD, g 18 (by decide), g 19 (by decide), ← g 20 (by decide), ← g 21 (by decide)]
  have e2 : ((pt.map (· ^ 2 ^ k)).drop 20).take 2 = [(pt.map (· ^ 2 ^ k)).getD 20 0, (pt.map (· ^ 2 ^ k)).getD 21 0] := by
    have hl2 : (((pt.map (· ^ 2 ^ k)).drop 20).take 2).length = 2 := by
      simp only [List.length_take, List.length_drop, hl]; decide
    refine List.ext_getElem (by rw [hl2]; rfl) fun i h1 h2 ↦ ?_
    have hi : i < 2 := by simpa using h2
    interval_cases i <;> simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 21 < (pt.map (· ^ 2 ^ k)).length by
      rw [hl]; decide), List.getElem?_eq_getElem (show 20 < (pt.map (· ^ 2 ^ k)).length by rw [hl]; decide)]
  rw [e2, show CMain.nu20 - 22 = 1 from rfl, ← selectorPoint_zero]
  simp [zF, selectorPoint, List.range_succ, eqEval, Har.eOfNat_zero, CharTwo.sub_eq_add]

end Lvm.QShape
end

-- ===== from `LvmQAsmHarP47` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- The `E` constant `k'` from any cell `x` (`x + 1·x + k'`). -/
theorem constE_val' {c : Ctx} {M : Mem} {k' : FK} {x : Cell} {p : Ptr}
    (h : SegsHold c M p (const .E k' x p).2) : (const .E k' x p).1.val M = FE.ofK k' := by
  have e := lin_spec (c := c) (M := M) (p := p) (τ := .E) (k := 1) (k' := k') (a := x) (b := x) h
  show (lin .E 1 k' x x p).1.val M = _
  rw [e, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

/-- A claim is determined by the cells representing it. -/
theorem rep_unique {P : Nat} {cv : Nat → FE} {C1 C2 : KeccakClaim} {f : Bool} (h1 : Rep P cv C1 f)
    (h2 : Rep P cv C2 f) : C1 = C2 := by
  obtain ⟨v1, m1, p1, w1⟩ := C1
  obtain ⟨v2, m2, p2, w2⟩ := C2
  have e1 := h1.value.symm.trans h2.value
  have e2 := h1.mu.symm.trans h2.mu
  have e3 := h1.point.symm.trans h2.point
  have e4 := h1.weights.trans h2.weights.symm
  simp only at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-- **The tape phase as a `PhaseAt` fact** (from `dTape_spec`): the result at the canonical state, tied to the
gadget's cells. -/
theorem tape_phase {c : Ctx} {M : Mem} {pT : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : Lvm.Q1.tapeEnd P qs + 2 ≤ T) (hh : SegsHold c M pT (tapeGadget P qs inst out b pT).2)
    (ha : SegsAssert M pT (tapeGadget P qs inst out b pT).2) (hb : b.val M = 1) {P4 P5 : Nat}
    (hinst : ((List.range (P + 5)).map fun i => (inst i).val M) = sampAt (feAt sig) P4 (P + 5))
    (hout : ((List.range 25).map fun l => (out l).val M) = scalarsAt (feAt sig) (P4 + 72 * (P + 5) + 40) 25)
    (hqs : 8 * qs - 40 = P4 + 72 * (P + 5) + 600) (hP5 : 8 * Lvm.Q1.tapeEnd P qs - 40 = P5) :
    PhaseAt (dTape (P + 5)) sig P4 P5 (dTape (P + 5) sig ⟨P4, 0, true⟩).1 ∧
    (dTape (P + 5) sig ⟨P4, 0, true⟩).1.r = (List.range (P + 5)).map (fun i => (inst i).val M) ∧
    (dTape (P + 5) sig ⟨P4, 0, true⟩).1.v = (List.range 25).map (fun l => (out l).val M) ∧
    Rep P (fun j => ((tapeGadget P qs inst out b pT).1.cv j).val M) (dTape (P + 5) sig ⟨P4, 0, true⟩).1.claim false := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := dTape_spec hP hq hS hT hh ⟨P4, 0, true⟩ (P0 := P4) (by simp) hinst hout hqs
  refine ⟨fun s hs hok => ?_, a1, a2, a4⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := dTape_spec hP hq hS hT hh s (P0 := P4) hs hinst hout hqs
  refine ⟨?_, (b7 hb).mpr ⟨hok, ha⟩, by simp only [pos]; rw [b5, b6]; omega⟩
  have hcl := rep_unique b4 a4
  generalize (dTape (P + 5) sig s).1 = X at b1 b2 b3 hcl
  generalize (dTape (P + 5) sig ⟨P4, 0, true⟩).1 = Y at a1 a2 a3 hcl
  obtain ⟨xr, xv, xl, xc⟩ := X
  obtain ⟨yr, yv, yl, yc⟩ := Y
  simp only at b1 b2 b3 a1 a2 a3 hcl ⊢
  rw [b1, b2, b3, a1, a2, a3, hcl]

/-- **The wire phase as a `PhaseAt` fact** (from `dRange_run`, `wire_spec`). -/
theorem wire_phase {c : Ctx} {M : Mem} {pW : Ptr} {P qw zE : Nat} {cv : Nat → Cell} {mb sb : List Cell}
    {b : Cell} {sig : ByteArray} {T : Nat} (hq : 5 ≤ qw) (hS : Streamed M sig T)
    (hT : Lvm.Q1.wireEnd P qw + 2 ≤ T) (hzE : M.e zE = 0)
    (hh : SegsHold c M pW (wireGadget P qw cv mb sb b zE pW).2)
    (ha : SegsAssert M pW (wireGadget P qw cv mb sb b zE pW).2) (hb : b.val M = 1)
    (pp : Params) (hlog : pp.logN = P + 5) (pub : Pub) (hn : 1 ≤ pub.n) (hN : pub.n ≤ 2 ^ (P + 5))
    {claim : KeccakClaim} (hR : Rep P (fun j => (cv j).val M) claim false)
    (hmb : vs M mb = (List.range (P + 5)).map (bitF (pub.n - 1))) (hsb : vs M sb = digBitsF pub.s)
    {P5 P6 : Nat} (hP5 : 8 * qw - 40 = P5) (hP6 : 8 * Lvm.Q1.wireEnd P qw - 40 = P6) :
    PhaseAt (wirePh pp pub claim) sig P5 P6 (wirePh pp pub claim sig ⟨P5, 0, true⟩).1 ∧
    (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sc.1 = vs M (wireGadget P qw cv mb sb b zE pW).1.sigma ∧
    (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sl.1 = vs M (wireGadget P qw cv mb sb b zE pW).1.tau ∧
    (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.ring =
      ((wireGadget P qw cv mb sb b zE pW).1.ring.target.val M, fun r' => ringWeight
        ((wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sc.1 ++ (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sl.1 ++
          selectorPoint (dSel pp) (dSelBits pp)) r' (vs M (wireGadget P qw cv mb sb b zE pW).1.ring.cs)) := by
  have hNl : pub.n ≤ 2 ^ pp.logN := by rw [hlog]; exact hN
  have hw : ∀ s : RS, wirePh pp pub claim sig s = dWire pp pub claim sig s := by
    intro s
    show (dRange pp pub >>= fun _ => dWire pp pub claim) sig s = _
    rw [bind_run', dRange_run pp pub sig s hn hNl]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ :=
    wire_spec hq hS hT hzE hh pp hlog pub hn hN hR hmb hsb ⟨P5, 0, true⟩ (by simp [hP5])
  rw [hw]
  refine ⟨fun s hs hok => ?_, a1, a3, Prod.ext a7 a8⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ :=
    wire_spec hq hS hT hzE hh pp hlog pub hn hN hR hmb hsb s (by simp only [pos] at hs; (clear * - hP5 hs; omega))
  rw [hw]
  refine ⟨?_, by rw [b11 hb ha]; exact hok, by simp only [pos]; rw [b9, b10]; omega⟩
  generalize (dWire pp pub claim sig s).1 = X at b1 b2 b3 b4 b5 b6 b7 b8
  generalize (dWire pp pub claim sig ⟨P5, 0, true⟩).1 = Y at a1 a2 a3 a4 a5 a6 a7 a8
  obtain ⟨⟨xσ, xf⟩, xg, ⟨xτ, xf'⟩, xsv, ⟨xt, xw⟩⟩ := X
  obtain ⟨⟨yσ, yf⟩, yg, ⟨yτ, yf'⟩, ysv, ⟨yt, yw⟩⟩ := Y
  simp only at b1 b2 b3 b4 b5 b6 b7 b8 a1 a2 a3 a4 a5 a6 a7 a8 ⊢
  subst b1 b2 b3 b4 b5 b6 b7 a1 a2 a3 a4 a5 a6 a7
  rw [b8, a8]

/-- The positions of phases 4–7 the wiring assumes (`P4 … P8`: the tape, the wire, `KS`, the `KS` link, the
openings). -/
structure P47Pos (p : Params) (P4 P5 P6 P7 P8 : Nat) : Prop where
  tp0 : P4 + 40 = 8 * aLane p 0
  tp1 : P4 + 72 * p.logN + 40 = 8 * aLane p 1
  tp2 : 8 * aLane p 2 - 40 = P4 + 72 * p.logN + 600
  tp5 : Lvm.Q1.tapeEnd (p.logN - 5) (aLane p 2) = aLane p 3
  w5 : 8 * aLane p 3 - 40 = P5
  w6 : 8 * Lvm.Q1.wireEnd (p.logN - 5) (aLane p 3) - 40 = P6
  ks0 : P6 + 40 = 8 * aLane p 4
  ks1 : kV p.ksLog P6 + 40 = 8 * aLane p 5
  ks2 : kG p.ksLog P6 = 8 * aLane p 6 - 40
  ks7 : 8 * gkrEnd (p.ksLog - 4) (aLane p 6) - 40 + 72 * ringStages = P7
  l7 : P7 + 40 = 8 * aLane p 7
  l8 : ksP2 p P7 + 96 = P8

/-- What phases 4–5 hand to the claims: the tape's result and the wire's, tied to the cells. -/
structure TW (C : QCfg) (M : Mem) (o : P47Out) (pub : Pub) (tp : TapeRes) (wo : WireOut) : Prop where
  r : tp.r = vs M o.r
  v : tp.v = vs M o.v
  rep : Rep (C.p.logN - 5) (fun j => (o.tape.cv j).val M) tp.claim false
  sc : wo.sc.1 = vs M o.wire.sigma
  sl : wo.sl.1 = vs M o.wire.tau
  ring : wo.ring = (o.wire.ring.target.val M,
    fun r' => ringWeight (wo.sc.1 ++ wo.sl.1 ++ selectorPoint (dSel C.p) (dSelBits C.p)) r' (vs M o.wire.ring.cs))
  mb : vs M o.mb = selectorPoint (pub.n - 1) C.p.logN

/-- **Phases 4–7 from `phases47`'s rows and assertions** (gate on): each phase from its start position yields
values tied to the cells (`TW` for the tape and the wire), keeps `ok`, reaches the next start; the `KS` link's
check holds. Hypotheses beyond v1's `KS` ones: Q_sig's bits of `n'` (`hnb`) and `ChildOk`'s range (`hn1`,
`hnN`), the `s'` bit class (`hsb`) and `s`'s header lanes (`hsl`). -/
theorem p47_at (C : QCfg) {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T : Nat}
    {bf : BusIn → BusOut} {tb : Pub → List TableSpec} {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {tfv : Pub → List FE → List FE} {tfs : Pub → List (List FE × List FE) → List FE}
    {tpc : Pub → List (List FE × List FE) → Bool} (pub : Pub) {P4 P5 P6 P7 P8 : Nat}
    (hpos : P47Pos C.p P4 P5 P6 P7 P8)
    (hn : 5 ≤ C.p.logN) (hk : 4 ≤ C.p.ksLog)
    (hlay : layOk (C.p.logN - 5) = true) (hlayk : layOk (C.p.ksLog - 4) = true)
    (hq : 5 ≤ aLane C.p 2) (hqw : 5 ≤ aLane C.p 3) (hqk : 5 ≤ aLane C.p 6)
    (hS : Streamed M sig T) (hT : Lvm.Q1.wireEnd (C.p.logN - 5) (aLane C.p 3) + 2 ≤ T)
    (hTk : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) ≤ T)
    (hTr : aLane C.p 0 + 9 * C.p.logN + 2 < T) (hTv : aLane C.p 1 + 3 * 25 + 2 < T)
    (hTrk : aLane C.p 4 + 9 * C.p.ksLog + 2 < T) (hTvk : aLane C.p 5 + 3 * 25 + 2 < T)
    (hD : C.p.logN ≤ 2 ^ clog2 C.p.logN) (hDk : C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog)
    (hTlk : ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T)
    (hB : 1 ≤ spongeBlocks C.p) (hB2 : spongeBlocks C.p ≤ 2 ^ C.p.ksLog) (hK : ksSplit C.p + 431 ≤ 2 ^ C.p.ksLog)
    (hokE : ∀ sh : LoopOut, SLok (ksBlockE C.p (aLane C.p 7) sh (kc (pbB C))) = true)
    (hnb : ∀ j < C.p.logN, (kc ((sigIn C).bn + 2 + j)).val M = bitE pub.n j) (hn1 : 1 ≤ pub.n)
    (hnN : pub.n ≤ 2 ^ C.p.logN) (hsb : Lvm.Q1.SBitsS M.k (sigIn C).hd (bsB C))
    (hsl : pub.s = (List.range 4).map fun l => M.k ((sigIn C).hd + 9 + l))
    (hg : (kc (pbB C)).val M = 1) (h : Lvm.QSig.Ok c M (phases47 C) ptr)
    (o : P47Out) (ho : (phases47 C ptr).1 = o) (m : M3) (hm : m = M3.ofParts C.p bf tb tcl tfv tfs tpc) :
    ∃ tp wo, PhaseAt (tapePh C.p) sig P4 P5 tp ∧ PhaseAt (wirePh C.p pub tp.claim) sig P5 P6 wo ∧
      PhaseAt (wirePhC C.p pub tp.claim) sig P5 P6 (wo, vs M o.wire.ring.cs) ∧
      TW C M o pub tp wo ∧
    PhaseAt (ksPh C.p) sig P6 P7 (vs M o.rk, vs M o.vk, o.kko.vals M,
      ringAt (feAt sig) (8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40) (o.kko.vals M).slicePoint (o.kko.vals M).slices) ∧
    PhaseAt (ksLinkPh C.p m (vs M o.rk) pub) sig P7 P8 (m.ksLink (ksLinkView C.p m (feAt sig) P7 (vs M o.rk) pub)) ∧
    (m.ksLink (ksLinkView C.p m (feAt sig) P7 (vs M o.rk) pub)).1 = true := by
  subst hm
  obtain ⟨hh, ha⟩ := h
  have hO : (phases47 C ptr).1 = o := ho
  simp only [phases47, bind_apply, pure_apply] at hO
  simp only [phases47] at hh ha
  rw [hold_bind] at hh; obtain ⟨hhR, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhV, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhT, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhZ, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhO, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhB, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhW, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhRk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhVk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhLk, -⟩ := hh
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haT, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haW, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haGk, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haLk, -⟩ := ha
  subst hO
  obtain ⟨e0, e1, e2, e5, w5, w6, k0, k1, k2, k7, l7, l8⟩ := hpos
  have hlog5 : C.p.logN - 5 + 5 = C.p.logN := by (clear * - hn; omega)
  -- the tape
  have hinst : ((List.range (C.p.logN - 5 + 5)).map fun i =>
      ((loadEs (clog2 C.p.logN) (aLane C.p 0) 9 ptr).1.cell 0 i).val M) = sampAt (feAt sig) P4 (C.p.logN - 5 + 5) := by
    rw [hlog5]; unfold sampAt
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [loadEs_val hhR hS (by (clear * - hD hlog5 hi'; omega)) (by (clear * - hTr e0 e1 hlog5 hi'; omega))]
    congr 1; (clear * - e0; omega)
  have hout : ((List.range 25).map fun l =>
      ((loadEs 5 (aLane C.p 1) 3 (ptr.adv (loadEs (clog2 C.p.logN) (aLane C.p 0) 9 ptr).2)).1.cell 0 l).val M) =
      scalarsAt (feAt sig) (P4 + 72 * (C.p.logN - 5 + 5) + 40) 25 := by
    rw [hlog5]; unfold scalarsAt
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [loadEs_val hhV hS (by norm_num; (clear * - hl'; omega)) (by (clear * - hTv hl'; omega))]
    congr 1; (clear * - e0 e1; omega)
  have T1 := tape_phase (P4 := P4) (P5 := P5) hlay hq hS
    (by rw [e5]; simp only [Lvm.Q1.wireEnd] at hT; (clear * - hn hT e5 hlog5; omega))
    hhT haT hg hinst hout (by rw [hlog5]; omega) (by rw [e5]; exact w5)
  rw [hlog5] at T1
  obtain ⟨T1a, T1r, T1v, T1c⟩ := T1
  -- the constants and the borrow chain
  have hz0 := constE_val' hhZ
  have ho1 := constE_val' hhO
  rw [Lvm.Loop.QRing.const_out] at hz0 ho1
  simp only [Cell.val, Mem.rd, Ptr.at, ofK_one, ofK_zero] at hz0 ho1
  have hmb := borrow_vs (ho := by rw [Lvm.Loop.QRing.const_out]; exact ho1) hnb hn1 hhB
  -- the wire
  have hsbv : vs M (sbCells C) = digBitsF pub.s := by
    rw [hsl, ← Lvm.Q1.sbits_vals hsb]; simp only [vs, sbCells, List.map_map]; rfl
  have W1 := wire_phase hqw hS hT (by rw [Lvm.Loop.QRing.const_out]; exact hz0) hhW haW hg C.p
    hlog5.symm pub hn1 (by rw [hlog5]; exact hnN) T1c (by rw [hmb, hlog5]; rfl) hsbv w5 w6
  obtain ⟨W1a, W1s, W1t, W1r⟩ := W1
  -- roll 7 (CR-Q): `dWireC`'s coefficients are the wire gadget's
  have hmbL := congrArg List.length hmb
  simp only [vs, List.length_map, List.length_range] at hmbL
  have hsbL := congrArg List.length hsbv
  simp only [vs, List.length_map, digBitsF, List.length_range] at hsbL
  have WC := Lvm.Q1.wire_core hqw hS hT (by rw [hmbL]; (clear * - hlog5; omega)) hsbL
    (by rw [Lvm.Loop.QRing.const_out]; exact hz0) hhW
  have WCc := WC.2.2.2.1
  have KK := kblock_sound hk hlayk hqk hS hTk hTrk hTvk hDk hhRk hhVk hhGk haGk hg P6 k0 k1 k2
  refine ⟨_, _, T1a, W1a, by rw [WCc]; exact wireC_phase W1a hqw hlog5.symm hn1 hnN w5, ⟨?_, ?_, T1c, W1s, W1t, W1r, ?_⟩, ?_, ?_, ?_⟩
  · rw [T1r]; simp only [vs, List.map_map]; rfl
  · rw [T1v]; simp only [vs, List.map_map]; rfl
  · rw [hmb, selectorPoint_bits]
  · intro s hs hok
    rw [ksPh_run C.p (by (clear * - hk; omega)) sig s, hs]
    obtain ⟨f1, f2, f3, f4, f5⟩ := KK s.ok
    refine ⟨?_, ?_, ?_⟩
    · simp only [vs, List.map_map]
      rw [f4, f3, f1, f2]
      rfl
    · exact f5 hok
    · simp only [pos, Nat.add_zero]; (clear * - k7 l7 f4; omega)
  · intro s hs hok
    rw [ksLinkPh_run C.p _ _ pub sig s (by (clear * - hk; omega)), hs]
    exact ⟨rfl, hok, by simp only [pos]; exact l8⟩
  · exact ksLink_sound C.p (clog2 C.p.ksLog) _ pub (kc (pbB C)) (by (clear * - hk; omega)) hk hDk l7 hB hB2 hK hokE hS hTlk hg
      hhLk haLk

end Lvm.Har
end

-- ===== from `LvmQAsmHarTails` =====

section
section
set_option autoImplicit false
namespace Lvm.Har
open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.Q1 Lvm.Replay

/-- The gate: `PUB` lane 0 holds the flag. -/
theorem gate_val {M : Mem} (C : QCfg) (h : M.k (pbB C) = 1) : (kc (pbB C)).val M = 1 := by
  simp [h, ofK_one]

/-- **Q_arith's segments split** into phases 4–7 and the rest. -/
theorem qarith_split (C : QCfg) {c : Ctx} {M : Mem} {p : Ptr} (h : Lvm.QSig.Ok c M (qarith C) p) :
    Lvm.QSig.Ok c M (phases47 C) p ∧
      Lvm.QSig.Ok c M (qarithRest C (phases47 C p).1) (p.adv (phases47 C p).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [show qarith C = (phases47 C >>= qarithRest C) from rfl, hold_bind] at h1
  rw [show qarith C = (phases47 C >>= qarithRest C) from rfl, assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.M3 Lvm.QAsm

theorem sumcheckTabs_shape : ∀ (l : List Tab),
    (sumcheckTabs l).map Tab.shape = (l.map Tab.shape).filter TShape.sc
  | [] => rfl
  | t :: l => by
    have ih := sumcheckTabs_shape l
    unfold sumcheckTabs at ih ⊢
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    have e : TShape.sc t.shape = (!t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty) := rfl
    rw [e]
    split <;> simp [ih]

theorem shapeTab_shape (σ : Shape) (τ : Nat) (fx fx' : FCol → Nat → FK) (fe fe' : FCol → List FE → FE)
    (pl : Var → Bool × Nat) : (shapeTab σ τ fx fe pl).shape = (shapeTab σ τ fx' fe' pl).shape := by
  simp only [Tab.shape, shapeTab, List.map_map]
  congr 1
  refine List.map_congr_left fun u _ => ?_
  cases u <;> rfl

theorem inArr_shape (a a' : InArr) (hτ : a.τ = a'.τ) (hb : a.base = a'.base) (hs : a.stride = a'.stride)
    (hv : a.val = a'.val) (hf : a.fin = a'.fin) (hp : a.pub.isSome = a'.pub.isSome) (hty : a.ty = a'.ty) :
    a.tab.shape = a'.tab.shape := by
  rcases a with ⟨ty, τ, base, stride, val, fin, pub⟩
  rcases a' with ⟨ty', τ', base', stride', val', fin', pub'⟩
  simp only at hτ hb hs hv hf hp hty
  subst hτ hb hs hv hf hty
  simp only [Tab.shape, InArr.tab, InArr.vcols, List.map_append, List.map_cons, List.map_nil]
  congr 2
  cases pub <;> cases pub' <;> simp_all [List.map_map, colKind]

theorem lvmTabsC_shape (G G' : PG) (pl : Nat → Var → Bool × Nat) (gs : List Grp) (as as' : List InArr)
    (aux : List Tab) (ha : as.map (·.tab.shape) = as'.map (·.tab.shape)) :
    (lvmTabsC G pl gs as aux).map Tab.shape = (lvmTabsC G' pl gs as' aux).map Tab.shape := by
  unfold lvmTabsC
  rw [List.map_append, List.map_append, List.map_append, List.map_append, List.map_map, List.map_map,
    List.map_map, List.map_map]
  have hg : (List.range gs.length).map (Tab.shape ∘ fun i => shapeTab (gs.getD i default).σ (gs.getD i default).τ
      (grpFix G.C.Q (gs.getD i default)) (grpEvalG G (gs.getD i default)) (pl i)) =
      (List.range gs.length).map (Tab.shape ∘ fun i => shapeTab (gs.getD i default).σ (gs.getD i default).τ
      (grpFix G'.C.Q (gs.getD i default)) (grpEvalG G' (gs.getD i default)) (pl i)) :=
    List.map_congr_left fun i _ => shapeTab_shape _ _ _ _ _ _ _
  have ha' : as.map (Tab.shape ∘ InArr.tab) = as'.map (Tab.shape ∘ InArr.tab) := ha
  rw [hg, ha']

/-- **The node program's table shapes depend only on the configuration and the placement record.** -/
theorem tabs_shape (C : QCfg) (G G' : PG) (D : QData) (P P' : Pub) :
    (tabs C G D P).map Tab.shape = (tabs C G' D P').map Tab.shape := by
  unfold tabs
  apply lvmTabsC_shape
  unfold arrs
  simp only [List.map_append]
  congr 1

end Lvm.Har
end
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- A `Replays` fact and the gadget's `Ok` give a `PhaseAt` fact, the value read off `R`. -/
theorem phaseAt_of {α β : Type} {c : Ctx} {M : Mem} {sig : ByteArray} {F : DM α} {g : BM β} {ptr : Ptr}
    {P P' : Nat} {R : α → β → Prop} {v : α} (h : Replays c M sig F g ptr P P' R)
    (hok : Lvm.QSig.Ok c M g ptr) (hv : ∀ a, R a (g ptr).1 → a = v) : PhaseAt F sig P P' v :=
  fun s hs hsok => by
    obtain ⟨h1, h2, h3⟩ := h hok s hs hsok
    exact ⟨hv _ h3, h1, h2⟩

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

theorem real_eq (p : Params) (ts : Pub → List M3.Tab) :
    M3.real p ts = M3.ofParts p (fun i => M3.busFinalR (M3.sumcheckTabs (ts i.pub)) i)
      (fun pub => (M3.sumcheckTabs (ts pub)).map M3.nativeTable)
      (fun pub => M3.tableClaimsR (M3.sumcheckTabs (ts pub)))
      (fun pub => M3.fixValsR (M3.sumcheckTabs (ts pub)) p.pubTab)
      (fun pub => M3.fixSentR (M3.sumcheckTabs (ts pub)) p.pubTab)
      (fun pub => M3.pubCheckR p.pubTab pub) := rfl

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- **The tape's claims as cells are T-V's `tapeClaims`** on the phases' values (`TW`), the header lanes
`h'` the stream's (`pub_h`). -/
theorem tapeClaimsC_val (C : QCfg) {M : Mem} {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) {oP : P47Out}
    {tp : TapeRes} {wo : WireOut} {pub : Pub} (htw : TW C M oP pub tp wo) (hvl : oP.v.length = 25)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) :
    (tapeClaimsC C.p z o oP).map (CClaim.val M) = (tapeClaims C.p tp wo pub).map (.main, ·) := by
  obtain ⟨hr, hv, -, hsc, hsl, hring, hmb⟩ := htw
  have e4 : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [tapeClaimsC, tapeClaims, dLanes, e4, hh, List.map_cons, List.map_nil, List.zipIdx_cons,
    List.zipIdx_nil, List.cons_append, List.nil_append, CClaim.val, vs_append, selC_vs hz ho, hr, hv, hmb,
    hring, hsc, hsl, vs_getD M oP.v (show 0 < oP.v.length by (clear * - hvl; omega)), vs_getD M oP.v (show 1 < oP.v.length by (clear * - hvl; omega)),
    vs_getD M oP.v (show 2 < oP.v.length by (clear * - hvl; omega)), vs_getD M oP.v (show 3 < oP.v.length by (clear * - hvl; omega))]
  rfl

/-- A claim whose tail is `0` by its form (no `D` point claim, no ring claim on `⟨CMain.nu20, 0⟩`). -/
def noDR (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk _ => blk != ⟨22, 0⟩
  | .ring blk _ _ => blk != ⟨CMain.nu20, 0⟩
  | .sum _ _ => true

theorem tailC_noDR {M : Mem} (cc : CClaim) (h : noDR cc = true) : Lvm.QShape.tailC M cc = 0 := by
  rcases cc with ⟨com, cw, v⟩
  cases cw <;> simp_all [noDR, Lvm.QShape.tailC]

theorem list_eq_of_proj (l₁ l₂ : List (Com × BlockClaim × FE))
    (h1 : l₁.map (fun e => (e.1, e.2.1)) = l₂.map (fun e => (e.1, e.2.1))) (h2 : l₁.map (·.2.2) = l₂.map (·.2.2)) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h1
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h1 h2
      obtain ⟨a1, a2, a3⟩ := a
      obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at h1 h2
      rw [h1.1.1, h1.1.2, h2.1, ih l' h1.2 h2.2]

theorem claimsT_proj {M : Mem} (cs : List CClaim) : (claimsT M cs).map (fun e => (e.1, e.2.1)) = cs.map (CClaim.val M) := by
  rw [claimsT, List.map_map]; rfl

theorem zeroTails_tails (l : List (Com × BlockClaim)) :
    (Lvm.Shape.zeroTails l).map (·.2.2) = List.replicate l.length 0 := by
  rw [List.eq_replicate_iff]
  simp only [Lvm.Shape.zeroTails, List.map_map, List.length_map, true_and]
  intro b hb
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hb
  rfl

theorem map_tailC_zero {M : Mem} (l : List CClaim) (h : l.all noDR = true) :
    l.map (Lvm.QShape.tailC M) = List.replicate l.length 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun t ht => ?_⟩
  obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp ht
  exact tailC_noDR cc (List.all_eq_true.mp h cc hcc)

/-- **The tape's tails as cells are `V_S`'s** (`tapeTails`) when the child is small. -/
theorem tapeTails_eq (C : QCfg) {M : Mem} {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) {oP : P47Out}
    {tp : TapeRes} {wo : WireOut} {pub : Pub} (htw : TW C M oP pub tp wo) (hrl : oP.r.length = 20)
    (hστ : (oP.wire.sigma ++ oP.wire.tau).length = 22) (hh : pub.h.length = 4)
    (hsm : Lvm.Shape.smallP C.p pub = true) (hD : Lvm.dBlock C.p = ⟨22, 0⟩) (hds : dSel C.p = 0)
    (hn1 : 1 ≤ pub.n) :
    (tapeClaimsC C.p z o oP).map (Lvm.QShape.tailC M) =
      Lvm.Shape.tapeTails C.p tp wo (vs M oP.wire.ring.cs) pub := by
  obtain ⟨hr, -, -, hsc, hsl, -, hmb⟩ := htw
  simp only [Lvm.Shape.smallP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsm
  obtain ⟨⟨hlog, hnu⟩, hsmall⟩ := hsm
  have hdb : dSelBits C.p = 1 := by simp [dSelBits, hlog, hnu]; rfl
  have e4 : List.range 4 = [0, 1, 2, 3] := rfl
  have hvr : (vs M oP.r).length = 20 := by simp [vs, hrl]
  have hph : pub.h.map (fun _ => (0 : FE)) = [0, 0, 0, 0] := by
    rw [List.map_const', hh]; rfl
  have tD : ∀ l < 4, Lvm.QShape.tailC M ⟨.main, .point (Lvm.dBlock C.p) (oP.r ++ selC z o l 2), oP.v.getD l default⟩ =
      Lvm.Shape.tailDF tp.r l := fun l hl => by
    simp only [Lvm.QShape.tailC, hD, if_true, vs_append, selC_vs hz ho, hr]
    exact Lvm.QShape.tailD_pt _ hvr l hl
  have tB : ∀ l < 4, Lvm.QShape.tailC M ⟨.main, .point (Lvm.dBlock C.p) (oP.mb ++ selC z o l 2), kc (hLane l)⟩ = 0 :=
    fun l _ => by
      simp only [Lvm.QShape.tailC, hD, if_true, vs_append, selC_vs hz ho, hmb, hlog]
      exact Lvm.QShape.tailD_bnd _ (by simp [CMain.smallLogN20] at hsmall; (clear * - hn1 hsmall; omega)) l
  have tR : Lvm.QShape.tailC M ⟨.main, .ring ⟨C.p.nuMain, 0⟩ (oP.wire.sigma ++ oP.wire.tau ++
      selC z o (dSel C.p) (dSelBits C.p)) oP.wire.ring.cs, oP.wire.ring.target⟩ =
      Lvm.Shape.ringTailN (Lvm.Shape.wirePt C.p wo) (vs M oP.wire.ring.cs) := by
    simp only [Lvm.QShape.tailC, hnu, if_true, vs_append, selC_vs hz ho, Lvm.Shape.wirePt, hsc, hsl]
    have hl : (vs M oP.wire.sigma ++ vs M oP.wire.tau).length = 22 := by
      simpa [vs] using hστ
    rw [hds, hdb]
    refine Lvm.QShape.tailR_eq _ _ (by
      show _ = 23; simp only [List.length_append, Lvm.QShape.selectorPoint_length'] at hl ⊢; (clear * - hl; omega)) ?_
    rw [List.drop_left' hl]
    show selectorPoint 0 1 = List.replicate 1 0
    simp [selectorPoint, eOfNat_zero]
  simp only [tapeClaimsC, Lvm.Shape.tapeTails, dLanes, e4, hph, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.singleton_append]
  rw [tD 0 (by norm_num), tD 1 (by norm_num), tD 2 (by norm_num), tD 3 (by norm_num), tR, tB 0 (by norm_num),
    tB 1 (by norm_num), tB 2 (by norm_num), tB 3 (by norm_num)]

end Lvm.Har
end

-- ===== from `LvmQTypedHarC` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)
section
variable {c : Ctx} {M : Mem}

/-- **`eqConstG`'s value** is `eqAtF` of its cells at the constant. -/
theorem eqConstG_valC {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (r : List Cell) (b : Nat) (p : Ptr), SegsHold c M p (eqConstG z o r b p).2 →
      (eqConstG z o r b p).1.val M = eqAtF (vs M r) b
  | [], _, _, _ => by simp [eqConstG, pure, vs, eqAtF, ho]
  | x :: r, b, p, h => by
    simp only [eqConstG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    have ih := eqConstG_valC hz ho r (b / 2) p h.1
    simp only [vs, List.map_cons, eqAtF] at ih ⊢
    by_cases hb : b % 2 = 1
    · simp only [hb, if_true] at h ⊢
      rw [mulAdd_spec h.2, ih, hz, add_zero, mul_comm]
    · simp only [hb, if_false, neg1, addK, bind_apply] at h ⊢
      rw [segsHold_append] at h
      rw [mulAdd_spec h.2.2, lin_spec h.2.1, ih, hz, add_zero, ofK_zero, zero_mul, add_zero, ofK_one,
        mul_comm, add_comm]

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)
section
variable {c : Ctx} {M : Mem}

/-- `regClaimG`'s parts (selector cell, block, point cells) by value. -/
theorem regParts_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (ry : List Cell) :
    ∀ (rs : List TReg) (p : Ptr),
      SegsHold c M p (seqAll (rs.map fun R => do
        let s ← regSelG z o ry R
        pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) p).2 →
      (seqAll (rs.map fun R => do
        let s ← regSelG z o ry R
        pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) p).1.map
          (fun x => (x.1.val M, x.2.1, vs M x.2.2)) =
        rs.map fun R => (TypedV.hiW (vs M ry) R.log R.base, (⟨R.log, R.off⟩ : Placement), (vs M ry).take R.log)
  | [], _, _ => rfl
  | R :: rs, p, h => by
    simp only [List.map_cons, seqAll, bind_apply, pure_apply, List.append_nil] at h ⊢
    rw [segsHold_append] at h
    rw [regParts_val hz ho ry rs _ h.2]
    rw [List.cons.injEq]
    refine ⟨?_, rfl⟩
    rw [regSelG, eqConstG_valC hz ho _ _ _ h.1, TypedV.hiW]
    simp [vs, List.map_drop, List.map_take]

/-- The region claim's weight, term by term. -/
theorem affW_eq (N : TNat) (s : Lvm.Typed.YSrc) (ry : List FE) (X : List FE) :
    TypedV.affW N s ry X = sumE ((N.regsOf s).map fun g =>
      TypedV.hiW ry g.log g.base * (⟨g.log, g.dst⟩ : Placement).eqAbove X * eqEval (ry.take g.log) (X.take g.log)) := by
  simp only [TypedV.affW, sumE, List.foldl_map]
  congr 1
  funext acc g
  rw [eqAbove_eqAtF]
  ring

/-- **`regClaimG`'s claim is V_S's region claim**, on regions that are V_S's. -/
theorem regClaimG_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (com : Com) (nu : Nat) (N : TNat)
    (s : Lvm.Typed.YSrc) (rs : List TReg) (hrs : (N.regsOf s).map nTrip = rs.map tTrip) (ry : List Cell) (v : Cell)
    (p : Ptr) (h : SegsHold c M p (regClaimG z o com nu rs ry v p).2) :
    (regClaimG z o com nu rs ry v p).1.val M = (com, ⟨⟨nu, 0⟩, TypedV.affW N s (vs M ry), v.val M⟩) := by
  simp only [regClaimG, bind_apply, pure_apply, List.append_nil] at h ⊢
  have hp := regParts_val hz ho ry rs p h
  simp only [CClaim.val, sumClaim]
  refine congrArg (Prod.mk com) ?_
  congr 1
  funext X
  rw [affW_eq, List.map_map]
  generalize (seqAll (rs.map fun R => do
    let s ← regSelG z o ry R
    pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) p).1 = parts at hp
  have e1 : parts.map ((fun cbz : FE × Placement × List FE => cbz.1 * cbz.2.1.eqAbove X *
      eqEval cbz.2.2 (X.take cbz.2.1.variableCount)) ∘ fun x => (x.1.val M, x.2.1, vs M x.2.2)) =
      (parts.map fun x => (x.1.val M, x.2.1, vs M x.2.2)).map (fun cbz => cbz.1 * cbz.2.1.eqAbove X *
        eqEval cbz.2.2 (X.take cbz.2.1.variableCount)) := by rw [List.map_map]
  rw [e1, hp, List.map_map]
  congr 1
  clear hp e1 parts h
  generalize N.regsOf s = gs at hrs ⊢
  induction gs generalizing rs with
  | nil => cases rs with
    | nil => rfl
    | cons _ _ => simp at hrs
  | cons g gs ih =>
    cases rs with
    | nil => simp at hrs
    | cons R rs =>
      simp only [List.map_cons, List.cons.injEq, nTrip, tTrip, Prod.mk.injEq] at hrs ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hrs
      refine ⟨?_, ih rs h4⟩
      simp only [Function.comp_apply, h1, h2, h3]
/-- The claims of one commitment, by value (`CClaim.val` keeps the commitment). -/
theorem filter_val (l : List CClaim) (com : Com) :
    (l.filter (·.com == com)).map (CClaim.val M) = (l.map (CClaim.val M)).filter (·.1 == com) := by
  rw [List.filter_map]; rfl

/-- **The circuit's typed claims are V_S's** (M′ `S2GM`: all on `C_main`): first the relayout's point claim on the
stream block (`⟨19, sOff⟩`), `σ′`'s region claim and the mini-bus's `C_rec` table claims (none at `S2GM`, by the
guard's `claimsOkB`); then the committed regions', `KS`'s and the mini-bus's `C_main` table claims. -/
theorem typedClaimsC_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {Td : TData} {N : TNat}
    (htd : TdOk Td N) (nu sOff : Nat) (t : TypedC) (st : List Lvm.M3.Tab) (hst : Td.mbS = st.map Lvm.M3.Tab.shape)
    (p : Ptr) (h : SegsHold c M p (typedClaimsC z o Td nu sOff t p).2) :
    (typedClaimsC z o Td nu sOff t p).1.1.map (CClaim.val M) =
      (.main, BlockClaim.point ⟨19, sOff⟩ (vs M t.rr) (t.vR.val M)) ::
        (.main, ⟨⟨nu, 0⟩, TypedV.affW N .sigma (vs M t.ry), (t.rv.getD 2 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))).filter (·.1 == .crec) ∧
    (typedClaimsC z o Td nu sOff t p).1.2.map (CClaim.val M) =
      (.main, ⟨⟨nu, 0⟩, TypedV.affW N .com (vs M t.ry), (t.rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨nu, 0⟩, TypedV.affW N .ks (vs M t.ry), (t.rv.getD 3 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))).filter (·.1 == .main) ∧
    (∀ cc ∈ (typedClaimsC z o Td nu sOff t p).1.2, cc.com = .main) := by
  simp only [typedClaimsC, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  have e1 := regClaimG_val hz ho .main nu N .sigma Td.sig htd.sig t.ry (t.rv.getD 2 z) p h.1
  have e2 := regClaimG_val hz ho .main nu N .com Td.com htd.com t.ry (t.rv.getD 0 z) _ h.2.1
  have e3 := regClaimG_val hz ho .main nu N .ks Td.ks htd.ks t.ry (t.rv.getD 3 z) _ h.2.2
  have hv := tabClaims_val hz st t.tab
  rw [← hst] at hv
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_cons, List.map_cons, e1, filter_val, hv]; rfl
  · rw [List.map_cons, List.map_cons, e2, e3, filter_val, hv]
  · intro cc hcc
    simp only [List.mem_cons, List.mem_filter, beq_iff_eq] at hcc
    rcases hcc with rfl | rfl | ⟨-, h⟩
    · simp [regClaimG, bind_apply, pure_apply]
    · simp [regClaimG, bind_apply, pure_apply]
    · exact h

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)

theorem map_pair_eq {α β γ : Type} : ∀ (l₁ l₂ : List (α × β × γ)), l₁.map (·.2.1) = l₂.map (·.2.1) →
    l₁.map (·.2.2) = l₂.map (·.2.2) → l₁.map (·.2) = l₂.map (·.2)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l₁, b :: l₂, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
    exact ⟨Prod.ext h1.1 h2.1, map_pair_eq l₁ l₂ h1.2 h2.2⟩

/-- **`dOpenT` reads only the claims' commitments and claims, and `C_main`'s tails in the small shape** (M′ `S2GM`:
it requires every claim on `C_main` and opens `C_main` alone). -/
theorem dOpenT_congr (p : Params) (s : Bool) (l₁ l₂ : List (Com × BlockClaim × FE))
    (hp : l₁.map (fun e => (e.1, e.2.1)) = l₂.map (fun e => (e.1, e.2.1)))
    (ht : s = true → (l₁.filter (·.1 == .main)).map (·.2.2) = (l₂.filter (·.1 == .main)).map (·.2.2)) :
    TypedV.dOpenT p s l₁ = TypedV.dOpenT p s l₂ := by
  have ha : l₁.all (·.1 == .main) = l₂.all (·.1 == .main) := by
    have e := congrArg (fun l : List (Com × BlockClaim) => l.all (·.1 == Com.main)) hp
    simpa only [List.all_map, Function.comp_def] using e
  have ef : ∀ l : List (Com × BlockClaim × FE), (l.filter (·.1 == .main)).map (·.2.1) =
      ((l.map fun e => (e.1, e.2.1)).filter (·.1 == .main)).map (·.2) := fun l => by
    rw [List.filter_map, List.map_map]; rfl
  have hm : (l₁.filter (·.1 == .main)).map (·.2.1) = (l₂.filter (·.1 == .main)).map (·.2.1) := by
    rw [ef, ef, hp]
  unfold TypedV.dOpenT
  rw [ha]
  cases s with
  | false =>
    simp only [Bool.false_eq_true, if_false, List.map_map]
    have em : ∀ l : List (Com × BlockClaim × FE), (l.filter (·.1 == .main)).map ((·.1.onStack) ∘ (·.2)) =
        ((l.filter (·.1 == .main)).map (·.2.1)).map (·.onStack) := fun l => by rw [List.map_map]; rfl
    rw [em l₁, em l₂, hm]
  | true =>
    simp only [if_true]
    rw [map_pair_eq _ _ hm (ht rfl)]

/-- The shape bit at `P20` is roll 7's `smallP`. -/
theorem smallT_P20 (pub : Pub) : TypedV.smallT P20 pub = Shape.smallP P20 pub := rfl

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)
section
variable {M : Mem}

/-- `noDRB` is roll 7's `noDR`. -/
theorem noDRB_eq (cc : CClaim) : noDRB cc = noDR cc := rfl

theorem filter_all {α : Type} {l : List α} {f : α → Bool} (h : ∀ x ∈ l, f x = true) : l.filter f = l :=
  List.filter_eq_self.mpr h

/-- **V_S's openings on its claim list are its openings on the circuit's claims** (with their tails; M′ `S2GM`: all
on `C_main`): the typed claims (`[A, B, C, D]`, tail `0`) and the mini-bus's table claims `tabs` (tail `0`) on V_S's
side; the circuit's first claims `tc₁` (`A`, `B` and the `C_rec` table claims, of which there are none since `tc₁`
is on `C_main`) and `tc₂` (`C`, `D`, the `C_main` table claims); the rest equal on both sides (in the small shape
with their tails). -/
theorem openClaims_eq (p : Params) (s : Bool) (A B Cc D : BlockClaim) (tabs : List (Com × BlockClaim))
    (tc₁ tc₂ rest : List CClaim) (restV : List (Com × BlockClaim × FE))
    (h1 : tc₁.map (CClaim.val M) = (.main, A) :: (.main, B) :: tabs.filter (·.1 == .crec))
    (h2 : tc₂.map (CClaim.val M) = (.main, Cc) :: (.main, D) :: tabs.filter (·.1 == .main))
    (hc1 : ∀ cc ∈ tc₁, cc.com = .main) (hnd1 : tc₁.all noDRB = true) (hnd2 : tc₂.all noDRB = true)
    (hr : rest.map (CClaim.val M) = restV.map fun e => (e.1, e.2.1))
    (ht : s = true → claimsT M rest = restV) :
    TypedV.dOpenT p s ([(.main, A, 0), (.main, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
        (Shape.zeroTails ([] ++ tabs) ++ restV)) =
      TypedV.dOpenT p s (claimsT M (tc₁ ++ tc₂ ++ rest)) := by
  -- no table claim is on `C_rec`: `tc₁`'s are on `C_main`
  have hT1 : tabs.filter (·.1 == .crec) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro e he
    have he' : e ∈ tc₁.map (CClaim.val M) := by
      rw [h1]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)
    obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he'
    have h := (List.mem_filter.mp he).2
    have h' : (CClaim.val M cc).1 = .main := hc1 cc hcc
    rw [h'] at h
    exact absurd h (by decide)
  have hT2 : tabs.filter (·.1 == .main) = tabs := by
    refine filter_all fun e he => ?_
    have hn := List.filter_eq_nil_iff.mp hT1 e he
    revert hn
    rcases e with ⟨c', b'⟩
    cases c' <;> simp
  rw [hT1] at h1
  rw [hT2] at h2
  have hl1 := congrArg List.length h1
  have hl2 := congrArg List.length h2
  simp only [List.length_map, List.length_cons, List.length_nil] at hl1 hl2
  have hP : (claimsT M (tc₁ ++ tc₂ ++ rest)).map (fun e => (e.1, e.2.1)) =
      [(.main, A), (.main, B), (.main, Cc), (.main, D)] ++ (tabs ++ restV.map fun e => (e.1, e.2.1)) := by
    rw [claimsT_proj, List.map_append, List.map_append, h1, h2, hr]
    simp
  have hV : ([(.main, A, 0), (.main, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
      (Shape.zeroTails ([] ++ tabs) ++ restV) : List (Com × BlockClaim × FE)).map (fun e => (e.1, e.2.1)) =
      [(.main, A), (.main, B), (.main, Cc), (.main, D)] ++ (tabs ++ restV.map fun e => (e.1, e.2.1)) := by
    rw [List.map_append, List.map_append, Shape.map_zeroTails, List.nil_append]; rfl
  refine dOpenT_congr p s _ _ (hV.trans hP.symm) fun hs => ?_
  have hR := ht hs
  have ec : ∀ l : List CClaim, (∀ cc ∈ l, cc.com = .main) → (claimsT M l).filter (·.1 == .main) = claimsT M l :=
    fun l hl => filter_all fun e he => by
      obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he
      simp [hl cc hcc]
  have hall : ∀ e ∈ tabs, e.1 = .main := fun e he => by
    have := List.filter_eq_self.mp hT2 e he
    simpa using this
  have hc2 : ∀ cc ∈ tc₂, cc.com = .main := fun cc hcc => by
    have he : CClaim.val M cc ∈ tc₂.map (CClaim.val M) := List.mem_map_of_mem hcc
    rw [h2] at he
    show (CClaim.val M cc).1 = .main
    simp only [List.mem_cons] at he
    rcases he with he | he | he
    · rw [he]
    · rw [he]
    · exact hall _ he
  have hl1' : tc₁.length = 2 := by simpa using hl1
  have hl2' : tc₂.length = 2 + tabs.length := by omega
  have et1 : (claimsT M tc₁).map (·.2.2) = List.replicate 2 0 := by
    rw [claimsT, List.map_map, show (2 : Nat) = tc₁.length from hl1'.symm]
    exact map_tailC_zero tc₁ (by simpa [noDRB_eq] using hnd1)
  have et2 : (claimsT M tc₂).map (·.2.2) = List.replicate (2 + tabs.length) 0 := by
    rw [claimsT, List.map_map, ← hl2']
    exact map_tailC_zero tc₂ (by simpa [noDRB_eq] using hnd2)
  have ez : ((Shape.zeroTails ([] ++ tabs)).filter (·.1 == .main)).map (·.2.2) =
      List.replicate (tabs.filter (·.1 == .main)).length 0 := by
    rw [List.nil_append, Shape.zeroTails, List.filter_map, List.map_map, List.eq_replicate_iff]
    refine ⟨by simp [Function.comp_def], fun b hb => ?_⟩
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hb
    rfl
  rw [hT2] at ez
  have eR : ((claimsT M (tc₁ ++ tc₂ ++ rest)).filter (·.1 == .main)).map (·.2.2) =
      List.replicate (4 + tabs.length) 0 ++ (restV.filter (·.1 == .main)).map (·.2.2) := by
    rw [show claimsT M (tc₁ ++ tc₂ ++ rest) = claimsT M tc₁ ++ claimsT M tc₂ ++ claimsT M rest by
      simp [claimsT], hR, List.filter_append, List.filter_append, ec tc₁ hc1, ec tc₂ hc2, List.map_append,
      List.map_append, et1, et2, ← List.replicate_add]
    congr 2; omega
  have eL : (([(.main, A, 0), (.main, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
      (Shape.zeroTails ([] ++ tabs) ++ restV) : List (Com × BlockClaim × FE)).filter (·.1 == .main)).map (·.2.2) =
      [0, 0, 0, 0] ++ (List.replicate tabs.length 0 ++ (restV.filter (·.1 == .main)).map (·.2.2)) := by
    rw [List.filter_append, List.map_append, List.filter_append, List.map_append, ez]
    rfl
  rw [eL, eR, List.replicate_add, List.append_assoc]
  rfl

theorem zipProj (L : List BlockClaim) (T : List FE) (h : T.length = L.length) :
    ((L.zip T).map fun e => (Com.main, e.1, e.2)).map (fun e => (e.1, e.2.1)) = L.map (Com.main, ·) := by
  induction L generalizing T with
  | nil => rfl
  | cons a L ih => cases T with
    | nil => simp at h
    | cons b T => simp only [List.zip_cons_cons, List.map_cons]; rw [ih T (by simpa using h)]

theorem Shape.zeroTails_tails' (l : List (Com × BlockClaim)) :
    (Shape.zeroTails l).map (·.2.2) = List.replicate l.length 0 := zeroTails_tails l

/-- **V_S's openings on its whole claim list are the circuit's** (`openClaims_eq` with V_S's list written out: the typed
claims `typedClaimsN`, then `dClaimsZ` with no bus claims; the circuit's list `qarithB`'s `cs`). -/
theorem openClaimsT_eq (p : Params) (s : Bool) (N : TNat) (m : M3) (pub : Pub) (z : Cell) (hz : z.val M = 0)
    (ry rv rr : List Cell) (vR : Cell) (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut)
    (wcs rk vks : List FE) (ksC : List BlockClaim) (kL : List (Com × BlockClaim))
    (tc₁ tc₂ tapeC kC ksOut clK : List CClaim) (hrec : p.nuRec = 19)
    (h1 : tc₁.map (CClaim.val M) =
      (.main, BlockClaim.point ⟨19, (layout0 p).s⟩ (vs M rr) (vR.val M)) ::
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .sigma (vs M ry), (rv.getD 2 z).val M⟩) ::
          (m.tableClaims pub evals).filter (·.1 == .crec))
    (h2 : tc₂.map (CClaim.val M) =
      (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .com (vs M ry), (rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .ks (vs M ry), (rv.getD 3 z).val M⟩) ::
          (m.tableClaims pub evals).filter (·.1 == .main))
    (hc1 : ∀ cc ∈ tc₁, cc.com = .main) (hnd1 : tc₁.all noDRB = true) (hnd2 : tc₂.all noDRB = true)
    (htape : tapeC.map (CClaim.val M) = (tapeClaims p tp wo pub).map (.main, ·))
    (hks : kC.map (CClaim.val M) = ksC.map (.main, ·)) (hko : ksOut.map (CClaim.val M) = m.ksOutputClaims rk vks)
    (hkl : clK.map (CClaim.val M) = kL)
    (htt : s = true → tapeC.map (Lvm.QShape.tailC M) = Shape.tapeTails p tp wo wcs pub)
    (hnd : (kC ++ ksOut ++ clK).all noDRB = true) :
    TypedV.dOpenT p s (TypedV.typedClaimsN N p (vs M ry) (vs M rv) (vs M rr) (vR.val M) ++
        Shape.dClaimsZ m p pub [] evals tp wo wcs rk vks ksC kL) =
      TypedV.dOpenT p s (claimsT M (tc₁ ++ tc₂ ++ (tapeC ++ kC) ++ ksOut ++ clK)) := by
  have gv : ∀ i, (vs M rv).getD i 0 = (rv.getD i z).val M := fun i => Lvm.QAcc.getD_vals rv z hz i
  have eN : TypedV.typedClaimsN N p (vs M ry) (vs M rv) (vs M rr) (vR.val M) =
      [(.main, BlockClaim.point ⟨19, (layout0 p).s⟩ (vs M rr) (vR.val M), 0),
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .sigma (vs M ry), (rv.getD 2 z).val M⟩, 0),
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .com (vs M ry), (rv.getD 0 z).val M⟩, 0),
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .ks (vs M ry), (rv.getD 3 z).val M⟩, 0)] := by
    simp only [TypedV.typedClaimsN, hrec, gv]
  have eZ : Shape.dClaimsZ m p pub [] evals tp wo wcs rk vks ksC kL = Shape.zeroTails ([] ++ m.tableClaims pub evals) ++
      ((((tapeClaims p tp wo pub).zip (Shape.tapeTails p tp wo wcs pub)).map fun e => (Com.main, e.1, e.2)) ++
        Shape.zeroTails (ksC.map (.main, ·)) ++ Shape.zeroTails (m.ksOutputClaims rk vks ++ kL)) := by
    simp only [Shape.dClaimsZ, List.append_assoc]
  rw [eN, eZ, show tc₁ ++ tc₂ ++ (tapeC ++ kC) ++ ksOut ++ clK = tc₁ ++ tc₂ ++ ((tapeC ++ kC) ++ ksOut ++ clK) by
    simp only [List.append_assoc]]
  have hlt := Shape.length_tapeTails p tp wo wcs pub
  have hP : ((((tapeClaims p tp wo pub).zip (Shape.tapeTails p tp wo wcs pub)).map fun e => (Com.main, e.1, e.2)) ++
      Shape.zeroTails (ksC.map (.main, ·)) ++ Shape.zeroTails (m.ksOutputClaims rk vks ++ kL)).map
        (fun e => (e.1, e.2.1)) = ((tapeC ++ kC) ++ ksOut ++ clK).map (CClaim.val M) := by
    simp only [List.map_append, Shape.map_zeroTails, zipProj _ _ hlt, htape, hks, hko, hkl, List.append_assoc]
  refine openClaims_eq p s _ _ _ _ _ tc₁ tc₂ _ _ h1 h2 hc1 hnd1 hnd2 hP.symm fun hs => ?_
  refine list_eq_of_proj _ _ (by rw [claimsT_proj, hP]) ?_
  have hnd' : (kC ++ ksOut ++ clK).map (Lvm.QShape.tailC M) = List.replicate (kC ++ ksOut ++ clK).length 0 :=
    map_tailC_zero _ (by simpa [noDRB_eq] using hnd)
  have hl1 := congrArg List.length hks
  have hl2 := congrArg List.length hko
  have hl3 := congrArg List.length hkl
  simp only [List.length_map] at hl1 hl2 hl3
  simp only [claimsT, List.map_map, List.map_append, List.append_assoc, Shape.zeroTails_tails',
    ← htt hs]
  simp only [List.map_append, List.length_append, ← List.append_assoc] at hnd'
  have e1 : ∀ l : List CClaim, l.map ((fun x : Com × BlockClaim × FE => x.2.2) ∘
      fun cc => (cc.com, (CClaim.val M cc).2, Lvm.QShape.tailC M cc)) = l.map (Lvm.QShape.tailC M) := fun l => rfl
  have hl0 := congrArg List.length htape
  simp only [List.length_map] at hl0
  rw [e1, e1, e1, e1, show ((fun x : Com × BlockClaim × FE => x.2.2) ∘ fun e : BlockClaim × FE => (Com.main, e.1, e.2)) =
    Prod.snd from rfl, List.map_snd_zip (by rw [List.length_map]; omega)]
  congr 1
  rw [← List.append_assoc, hnd']
  simp only [List.length_map, List.length_append, List.replicate_add, List.append_assoc, hl1, hl2, hl3]

end
end Lvm.Har
end
