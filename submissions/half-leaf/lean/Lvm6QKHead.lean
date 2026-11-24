-- New for lvm6 (WP CB). The head of the tree batch in the node circuit: FORMAT6 §6.2 rows 1–7 (`δ`,
-- `ρ`, `D⁰ D¹`, `u`, `o₄ … o₂₄`, `r_seg`, `r_lane`, `c_st`) and leanVM's first claim (value, `μ`,
-- the lane table its weights are made of), with the HAR on `treeProg`'s prefix.
import Lvm6QKRound

/-!
# The tree batch's head (generator and HAR)

* **`treeHeadProg κ`**: `treeProg κ`'s reads up to the layers (§6.2 rows 1–7), returning the raw
  values; `treeProg_head`: `treeProg κ` is `treeHeadProg κ` followed by the rest (`treeRest`).
* **`headItems κ`**: its FORMAT6 items; `treeItems_head`: `treeItems κ = headItems κ ++ …`.
* **`treeHeadG κ a`**: the gadget. Lanes from `a` (`hA1 … hA6`, FORMAT6 §4's geometry). It computes
  `o_m = (1+u)·D⁰_m + u·D¹_m` (8 products), the `eq` table of `r_lane` (62), the first claim's
  value `c_st + r_seg·Σ_{ℓ<25} eq(r_lane, ℓ)·o_ℓ` (26) and `μ = eq((u, ρ₀, ρ₁, ρ₂), ·)` (30):
  126 `E2` products.
* **`treeHead_runs`**: the gadget's cells represent `treeHeadProg κ`'s values and leanVM's first
  claim `firstClaimSF Shape.v1 (u :: ρ) [r_seg] r_lane (oLow u D ++ o') c_st` (value and `μ`; its
  point and weights are functions of represented cells).
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd)

variable {c : Ctx} {M : Mem}

/-! ## The program's head -/

/-- The raw values of §6.2 rows 1–7: `δ`, `ρ`, `D⁰ D¹`, `u`, `o₄ … o₂₄`, `r_seg :: r_lane`, `c_st`. -/
abbrev HeadV : Type := List K × List E2 × List E2 × E2 × List E2 × List E2 × E2

/-- **`treeProg`'s reads up to the layers.** -/
def treeHeadProg (κ : ℕ) : VerifierProgram HeadV :=
  kReads 4 >>= fun δ ↦ gPoint gRho (κ - 2) >>= fun ρ ↦ e2Reads 8 >>= fun dd ↦ e2Sample gU >>= fun u ↦
  e2Reads 21 >>= fun o' ↦ gPoint gSeg 5 >>= fun sl ↦ e2Read >>= fun cst ↦ pure (δ, ρ, dd, u, o', sl, cst)

/-- The rest of `treeProg` after its head. -/
def treeRest (κ : ℕ) (v : HeadV) : VerifierProgram Lvm6.K.TreeOut :=
  layers6 (κ - 4 + 4) (List.range 12)
    (firstClaimSF Shape.v1 (v.2.2.2.1 :: v.2.1) (v.2.2.2.2.2.1.take 1) (v.2.2.2.2.2.1.drop 1)
      (oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1) v.2.2.2.2.2.2) >>= fun claim ↦
  sumcheckE2 gC2 v.2.2.2.2.2.2 3 (List.replicate 6 none) >>= fun om ↦
  e2Read >>= fun cout ↦
  VerifierProgram.require (midWt 8 (v.2.2.2.2.2.1.headD 0) (v.2.2.2.2.2.1.drop 1) om.1 * cout = om.2) >>=
    fun _ ↦
  treeEnd6 (κ - 4) claim >>= fun en ↦
  pure ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1,
    ⟨v.2.2.2.2.2.1, v.2.2.2.2.2.2, claim, om.1, cout⟩, en⟩

/-- **`treeProg κ` is its head followed by the rest.** -/
theorem treeProg_head (κ : ℕ) : treeProg κ = treeHeadProg κ >>= treeRest κ := by
  simp only [treeProg, treeHeadProg, treeRest, kHead6, bind_assoc, pure_bind]

/-- The items of the head. -/
def headItems (κ : ℕ) : List Item :=
  [.K 4] ++ ([.G 5, .D (κ - 2)] ++ ([.E 8] ++ ([.G 1] ++ ([.E 21] ++ ([.G 3, .D 5] ++ [.E 1])))))

theorem treeItems_head (κ : ℕ) : ∃ rest, treeItems κ = headItems κ ++ rest := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [treeItems, Shape.treePart, Shape.keccakCore, headItems, List.cons_append,
    List.nil_append, List.append_assoc, show κ - 1 - 1 = κ - 2 by omega]
  rfl

/-! ## Lanes -/

/-- After `δ`. -/
def hA1 (a : ℕ) : ℕ := a + 4
/-- After `ρ` (`D(κ−2)`). -/
def hA2 (κ a : ℕ) : ℕ := hA1 a + 10 + 9 * (κ - 2)
/-- After `D⁰ D¹`. -/
def hA3 (κ a : ℕ) : ℕ := hA2 κ a + 16
/-- After `u`. -/
def hA4 (κ a : ℕ) : ℕ := hA3 κ a + 10
/-- After `o₄ … o₂₄`. -/
def hA5 (κ a : ℕ) : ℕ := hA4 κ a + 42
/-- After `r_seg, r_lane`. -/
def hA6 (κ a : ℕ) : ℕ := hA5 κ a + 10 + 45

/-- The values the head reads, from the stream. -/
def headVals (M : Mem) (κ a : ℕ) : HeadV :=
  (words M a 4, ev2 M (ld2 (hA1 a + 1)) :: draws M (hA1 a + 10) (κ - 2), scal M (hA2 κ a) 8,
    ev2 M (ld2 (hA3 κ a + 1)), scal M (hA4 κ a) 21,
    ev2 M (ld2 (hA5 κ a + 1)) :: draws M (hA5 κ a + 10) 5, ev2 M (ld2 (hA6 κ a)))

theorem runs_e2Reads' (M : Mem) (n a : ℕ) :
    Runs M (layItems [.E n] a) (e2Reads n) (· = scal M a n) := by
  simpa [layItems] using runs_e2Reads M n a

theorem runs_kReads' (M : Mem) (n a : ℕ) :
    Runs M (layItems [.K n] a) (kReads n) (· = words M a n) := by
  simpa [layItems] using runs_kReads M n a

theorem runs_e2Read' (M : Mem) (a : ℕ) : Runs M (layItems [.E 1] a) e2Read (· = ev2 M (ld2 a)) := by
  simpa [layItems] using runs_e2Read M a

theorem runs_e2Sample' (M : Mem) {g : ℕ} (hg : g ≤ 64) (a : ℕ) :
    Runs M (layItems [.G g] a) (e2Sample g) (· = ev2 M (ld2 (a + 1))) := by
  simpa [layItems] using runs_e2Sample M hg a

/-- **The head runs on the stream** to `headVals`. -/
theorem runs_treeHead (M : Mem) (κ a : ℕ) :
    Runs M (layItems (headItems κ) a) (treeHeadProg κ) (· = headVals M κ a) := by
  unfold headItems treeHeadProg
  simp only [layItems_append]
  refine runs_bind (runs_kReads' M 4 a) fun δ hδ ↦ runs_bind (runs_gPoint M (by norm_num) _ _)
    fun ρ hρ ↦ runs_bind (runs_e2Reads' M 8 _) fun dd hdd ↦ runs_bind (runs_e2Sample' M
      (by norm_num) _) fun u hu ↦ runs_bind (runs_e2Reads' M 21 _) fun o' ho ↦
    runs_bind (runs_gPoint M (by norm_num) _ _) fun sl hsl ↦ ?_
  rw [show ∀ x, layItems [V.Item.E 1] x = layItems [V.Item.E 1] x ++ [] from fun _ ↦ (List.append_nil _).symm]
  refine runs_bind (runs_e2Read' M _) fun cst hcst ↦ runs_pure ?_
  rw [hδ, hρ, hdd, hu, ho, hsl, hcst]
  rfl

/-! ## The gadget -/

/-- **What the head gadget hands on.** -/
structure HeadC where
  δ : List Cell
  ρ : List C2
  dd : List C2
  u : C2
  o : List C2
  sl : List C2
  cst : C2
  lanes : List C2
  mu : List C2
  value : C2

/-- `o_m = (1+u)·D⁰_m + u·D¹_m`. -/
def oLowG (z u u1 : C2) (dd : List C2) (m : ℕ) : BM C2 :=
  g2Mul u (dd.getD (4 + m) default) z >>= fun t ↦ g2Mul u1 (dd.getD m default) t

/-- The cells of `D⁰ D¹`. -/
def ddL (κ a : ℕ) : List C2 := (List.range 8).map fun i ↦ ld2 (hA2 κ a + 2 * i)

/-- **The head gadget** for `2^κ` rows, lanes from `a`. -/
def treeHeadG (κ a : ℕ) : BM HeadC :=
  let δ := (List.range 4).map fun i ↦ kc (a + i)
  let ρ := ld2 (hA1 a + 1) :: (List.range (κ - 2)).map fun i ↦ ld2 (hA1 a + 10 + 9 * i)
  let dd := ddL κ a
  let u := ld2 (hA3 κ a + 1)
  let o' := (List.range 21).map fun i ↦ ld2 (hA4 κ a + 2 * i)
  let sl := ld2 (hA5 κ a + 1) :: (List.range 5).map fun i ↦ ld2 (hA5 κ a + 10 + 9 * i)
  let cst := ld2 (hA6 κ a)
  g2Zero cst >>= fun z ↦ g2One z >>= fun one ↦ g2One u >>= fun u1 ↦
  mapB (oLowG z u u1 dd) (List.range 4) >>= fun ol ↦
  g2EqTab z [one] (sl.drop 1) >>= fun lanes ↦
  g2Dot z ((lanes.take 25).zip (ol ++ o')) >>= fun dot ↦
  g2Mul (sl.headD default) dot cst >>= fun value ↦
  g2EqTab z [one] ((u :: ρ).take 4) >>= fun mu ↦
  pure ⟨δ, ρ, dd, u, ol ++ o', sl, cst, lanes, mu, value⟩

/-! ## Algebra -/

theorem foldl_add_eq_sum : ∀ (l : List E2) (s : E2), l.foldl (· + ·) s = s + l.sum
  | [], s => by simp
  | x :: l, s => by rw [List.foldl_cons, foldl_add_eq_sum l, List.sum_cons, add_assoc]

/-- The table fold through `toE2` is `eqKernelF`'s. -/
theorem map_toE2_eqFold : ∀ (pt tab : List FE2),
    (pt.foldl eqStep2 tab).map FE2.toE2 =
      (pt.map FE2.toE2).foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) (tab.map FE2.toE2)
  | [], tab => rfl
  | r :: rs, tab => by
    rw [List.foldl_cons, map_toE2_eqFold rs, List.map_cons, List.foldl_cons]
    congr 1
    simp only [eqStep2, List.map_append, List.map_map]
    congr 1 <;> exact List.map_congr_left fun x _ ↦ by
      simp [Function.comp_apply, FE2.fe2_mul_eq, FE2.toE2_add, FE2.toE2_one]

theorem eqTab_ev2 {one : C2} {tab : List C2} (hone : one.val M = 1) (pt : List C2)
    (h : tab.map (C2.val M) = (pt.map (C2.val M)).foldl eqStep2 ([one].map (C2.val M))) :
    tab.map (ev2 M) = eqKernelF (pt.map (ev2 M)) := by
  have : tab.map (ev2 M) = (tab.map (C2.val M)).map FE2.toE2 := by simp [ev2, List.map_map]
  rw [this, h, map_toE2_eqFold, eqKernelF, List.map_map]
  simp [hone, Function.comp_def]
  rfl

/-- **The head gadget's cells represent the head's values and leanVM's first claim.** -/
def HeadRep (M : Mem) (o : HeadC) (v : HeadV) : Prop :=
  o.δ.map (kv M) = v.1 ∧ o.ρ.map (ev2 M) = v.2.1 ∧ o.dd.map (ev2 M) = v.2.2.1 ∧ ev2 M o.u = v.2.2.2.1 ∧
    o.o.map (ev2 M) = oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1 ∧ o.sl.map (ev2 M) = v.2.2.2.2.2.1 ∧
    ev2 M o.cst = v.2.2.2.2.2.2 ∧ o.lanes.map (ev2 M) = eqKernelF (v.2.2.2.2.2.1.drop 1) ∧
    o.mu.map (ev2 M) = (firstClaimSF Shape.v1 (v.2.2.2.1 :: v.2.1) (v.2.2.2.2.2.1.take 1)
      (v.2.2.2.2.2.1.drop 1) (oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1) v.2.2.2.2.2.2).mu ∧
    ev2 M o.value = (firstClaimSF Shape.v1 (v.2.2.2.1 :: v.2.1) (v.2.2.2.2.2.1.take 1)
      (v.2.2.2.2.2.1.drop 1) (oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1) v.2.2.2.2.2.2).value

theorem zip_map_mul (f : C2 → E2) : ∀ (xs ys : List C2),
    ((xs.zip ys).map fun e ↦ f e.1 * f e.2) = List.zipWith (· * ·) (xs.map f) (ys.map f)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp [zip_map_mul f xs ys]

theorem ev2_sum (l : List FE2) : FE2.toE2 l.sum = (l.map FE2.toE2).sum := by
  exact map_list_sum FE2.ringEquivE2 l

/-- **The head gadget re-executes the head of `treeProg`**, and its cells carry leanVM's first claim. -/
theorem treeHead_runs (κ a : ℕ) :
    Hs c M (treeHeadG κ a) fun o ↦ Runs M (layItems (headItems κ) a) (treeHeadProg κ) (HeadRep M o) := by
  unfold treeHeadG
  refine hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2One z) fun one hone ↦
    hs_bind (hs_g2One _) fun u1 hu1 ↦ ?_
  rw [hz, add_zero] at hone
  refine hs_bind (hs_mapB _ (fun m ↦ u1.val M * ((ddL κ a).getD m default).val M +
      (ld2 (hA3 κ a + 1)).val M * ((ddL κ a).getD (4 + m) default).val M)
    (fun m ↦ hs_bind (hs_g2Mul _ _ _) fun t ht ↦ hs_mono (hs_g2Mul _ _ _) fun r hr ↦ by
      rw [hr, ht, hz, add_zero]) _) fun ol hol ↦ ?_
  refine hs_bind (hs_g2EqTab hz [one] _) fun lanes hlanes ↦ hs_bind (hs_g2Dot _ _) fun dot hdot ↦
    hs_bind (hs_g2Mul _ _ _) fun value hvalue ↦ hs_bind (hs_g2EqTab hz [one] _) fun mu hmu ↦
      hs_pure (runs_mono (runs_treeHead M κ a) fun v hv ↦ ?_)
  subst hv
  have hlan := eqTab_ev2 hone _ hlanes
  have hol' : ol.map (ev2 M) = oLow (ev2 M (ld2 (hA3 κ a + 1))) (scal M (hA2 κ a) 8) := by
    have : ol.map (ev2 M) = (ol.map (C2.val M)).map FE2.toE2 := by simp [ev2, List.map_map]
    rw [this, hol]
    simp only [oLow, scal, ddL, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.getD_cons_succ, List.getD_cons_zero, List.cons.injEq, and_true,
      List.cons_append]
    simp only [ev2, hu1, FE2.toE2_add, FE2.fe2_mul_eq, FE2.toE2_one]
    norm_num
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp [words, kv, lk, List.map_map]; rfl
  · simp [draws, List.map_map]; rfl
  · simp [scal, List.map_map]; rfl
  · rw [List.map_append, hol']
    simp [scal, List.map_map]; rfl
  · simp [draws, List.map_map]; rfl
  · rw [hlan, List.map_drop]
    simp [draws, List.map_map]; rfl
  · rw [eqTab_ev2 hone _ hmu, List.map_take]
    simp [firstClaimSF, headVals, draws, List.map_map]; rfl
  · rw [ev2, hvalue, FE2.toE2_add, FE2.fe2_mul_eq, hdot, hz, zero_add, ev2_sum, List.map_map]
    simp only [firstClaimSF, dotF]
    rw [foldl_add_eq_sum, zero_add]
    have hseg : Shape.v1.segments - 1 = 1 := by decide
    have hm : (FE2.toE2 ∘ fun e : C2 × C2 ↦ C2.val M e.1 * C2.val M e.2) =
        fun e ↦ ev2 M e.1 * ev2 M e.2 := by
      funext e; simp [ev2, FE2.fe2_mul_eq]
    have hd : (List.drop 1 (ld2 (hA5 κ a + 1) :: List.map (fun i ↦ ld2 (hA5 κ a + 10 + 9 * i))
        (List.range 5))).map (ev2 M) = draws M (hA5 κ a + 10) 5 := by
      simp [draws, List.map_map]
    have ho : (List.map (fun i ↦ ld2 (hA4 κ a + 2 * i)) (List.range 21)).map (ev2 M) =
        scal M (hA4 κ a) 21 := by simp [scal, List.map_map]
    rw [hm, zip_map_mul, List.map_take, hlan, hd, List.map_append, hol', ho, hseg]
    simp only [headVals, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      eqKernelF, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.getD_cons_succ, List.getD_cons_zero, one_mul, List.headD_cons]
    rw [add_comm]
    rfl

end Lvm6.QK
