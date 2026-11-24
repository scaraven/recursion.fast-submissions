-- New for lvm6 (WP CB). CB-3: the node circuit re-executes the child's sponge link (season 1's
-- `ksLinkProgE2`) on the v6 stream. Season 1's gadget `ksLinkG2` with a third continuation interval
-- (the second WOTS key leaf, `σ_leaf`'s walk): versioned statement `LinkHarStmt2` over `rowsBK2`.
import Lvm6QKHead

/-!
# The sponge link (CB-3, generator and HAR)

* **`rowsBK2 B K₁ K₂`**: the continuation rows `[1, B) ∪ [K₁+1, K₁+32) ∪ [K₂+1, K₂+32)` (the trace
  blocks, `σ′`'s key leaf, `σ_leaf`'s key leaf; CB's row map: `K₁ = split + 399`, `K₂ = split + 864`).
  **`LinkHarStmt2`** is `LinkHarStmt` over these rows (versioned: season 1's `rowsBK` has two intervals).
* **`ksLinkG6`**: `ksLinkG2` from the lanes of `layItems (linkItems hk) a` (first answer `a + 1`; season 1's
  spacing is FORMAT6's) with `Sc = pre(B−1) + pre(K₁+31) + pre(K₁) + pre(K₂+31) + pre(K₂)`.
* **`linkHar`**: `LinkHarStmt2 ksLinkG6`.
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K
open Lvm6 (Item rep rnd)
open Finset

/-- The continuation rows of the v6 sponge block (three intervals). -/
def rowsBK2 (B K₁ K₂ : ℕ) : List ℕ := rowsBK B K₁ ++ (List.range 31).map (K₂ + 1 + ·)

/-- **CB-3, versioned** (statement): `G hk xl B K₁ K₂ a gate` re-executes `ksLinkProgE2` over `rowsBK2`. -/
def LinkHarStmt2 (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cell → BM LinkOutC) : Prop :=
  ∀ (hk xl B K₁ K₂ : ℕ), B - 1 < 2 ^ hk → K₁ + 31 < 2 ^ hk → K₂ + 31 < 2 ^ hk → ∀ (a : ℕ) (gate : Cell),
    Har gate (G hk xl B K₁ K₂ a gate) (ksLinkProgE2 hk xl (rowsBK2 B K₁ K₂)) (layItems (linkItems hk) a)
      LinkRep

section Gen

variable {F : Type} [Field F] [CharP F 2]

theorem contShiftF_pre2 (B K₁ K₂ : ℕ) (rho rho' : List F) :
    contShiftF (rowsBK2 B K₁ K₂) rho rho' = contShiftF (rowsBK B K₁) rho rho' +
      preSumF rho rho' (K₂ + 31) + preSumF rho rho' K₂ := by
  have h2 : preSumF rho rho' (K₂ + 31) = preSumF rho rho' K₂ +
      ∑ i ∈ range 31, (eqAtF rho (K₂ + 1 + i) * eqAtF rho' (K₂ + 1 + i - 1)) := by
    unfold preSumF
    rw [sum_range_add]
    congr 1
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [show K₂ + 1 + k - 1 = K₂ + k by omega, show K₂ + k + 1 = K₂ + 1 + k by omega]; ring
  rw [contShiftF, sumF_eq_sum, rowsBK2, List.map_append, List.sum_append, ← sumF_eq_sum, ← contShiftF,
    List.map_map, lsum_range, h2]
  simp only [Function.comp_apply]
  linear_combination (-preSumF rho rho' K₂) * CharTwo.two_eq_zero (R := F)

end Gen

/-! ## `toE2` through the verifier's forms -/

theorem toE2_foldl_add : ∀ (l : List FE2) (s : FE2),
    FE2.toE2 (l.foldl (· + ·) s) = (l.map FE2.toE2).foldl (· + ·) (FE2.toE2 s)
  | [], _ => rfl
  | x :: l, s => by simp only [List.foldl_cons, List.map_cons, toE2_foldl_add l, FE2.toE2_add]

theorem toE2_foldl_mul : ∀ (l : List FE2) (s : FE2),
    FE2.toE2 (l.foldl (· * ·) s) = (l.map FE2.toE2).foldl (· * ·) (FE2.toE2 s)
  | [], _ => rfl
  | x :: l, s => by simp only [List.foldl_cons, List.map_cons, toE2_foldl_mul l, FE2.fe2_mul_eq]

theorem toE2_eqAtF : ∀ (l : List FE2) (w : ℕ), FE2.toE2 (eqAtF l w) = eqAtF (l.map FE2.toE2) w
  | [], _ => FE2.toE2_one
  | r :: rs, w => by
    simp only [E2V.eqAtF, List.map_cons, FE2.fe2_mul_eq, toE2_eqAtF rs]
    by_cases h : w % 2 = 1 <;> simp [h, FE2.toE2_add, FE2.toE2_one]

theorem toE2_contShiftF (rows : List ℕ) (a b : List FE2) :
    FE2.toE2 (contShiftF rows a b) = contShiftF rows (a.map FE2.toE2) (b.map FE2.toE2) := by
  simp only [contShiftF, sumF, toE2_foldl_add, FE2.toE2_zero, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp [FE2.fe2_mul_eq, toE2_eqAtF]

theorem map_toE2_zipWith : ∀ (a b : List FE2),
    (List.zipWith (fun x z ↦ 1 + x + z) a b).map FE2.toE2 =
      List.zipWith (fun x z ↦ 1 + x + z) (a.map FE2.toE2) (b.map FE2.toE2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, z :: b => by simp [map_toE2_zipWith a b, FE2.toE2_add, FE2.toE2_one]

theorem toE2_eqEvalF (a b : List FE2) :
    FE2.toE2 (eqEvalF a b) = eqEvalF (a.map FE2.toE2) (b.map FE2.toE2) := by
  simp only [eqEvalF, toE2_foldl_mul, map_toE2_zipWith, FE2.toE2_one]

theorem toE2_selXF (xl : ℕ) (pt : List FE2) :
    FE2.toE2 (selXF xl pt) = selXF xl (pt.map FE2.toE2) := by
  simp only [selXF, prodF, toE2_foldl_mul, FE2.toE2_one, List.map_drop]

/-! ## Layouts -/

theorem layEnd_repG (g : ℕ) : ∀ (n a : ℕ), layEnd (rep n [.G g]) a = a + 10 * n
  | 0, a => rfl
  | n + 1, a => by
    rw [show rep (n + 1) [V.Item.G g] = [V.Item.G g] ++ rep n [V.Item.G g] from rfl, layEnd_append,
      layEnd_repG g n]
    simp only [layEnd]; ring

theorem layEnd_repR (g : ℕ) : ∀ (n a : ℕ), layEnd (rep n (rnd 2 g)) a = a + 14 * n
  | 0, a => rfl
  | n + 1, a => by
    rw [rep_succ, layEnd_append, layEnd_repR g n]
    simp only [rnd, layEnd]; ring

/-! ## The gadget -/

/-- **The sponge link gadget** (season 1's `ksLinkG2` from lane `a`, three intervals). -/
def ksLinkG6 (hk xl B K₁ K₂ a : ℕ) (gate : Cell) : BM LinkOutC :=
  let qa := a + 1
  let kchal := (List.range (hk + 5)).map fun i ↦ ld2 (qa + 10 * i)
  let rho := kchal.take hk
  let vals := (List.range 4).map fun k ↦ ld2 (ksLinkQV hk qa + 2 * k)
  g2Zero (ld2 qa) >>= fun z ↦ g2One z >>= fun one ↦
  sc2 hk (ksLinkQ1 hk qa) z >>= fun sh ↦
  g2PreRec z rho sh.1 (B - 1) (z, z, one) >>= fun p1 ↦
  g2PreRec z rho sh.1 (K₁ + 31) (z, z, one) >>= fun p2 ↦
  g2PreRec z rho sh.1 K₁ (z, z, one) >>= fun p3 ↦
  g2PreRec z rho sh.1 (K₂ + 31) (z, z, one) >>= fun p4 ↦
  g2PreRec z rho sh.1 K₂ (z, z, one) >>= fun p5 ↦
  g2Add p1.1 p2.1 >>= fun s12 ↦ g2Add s12 p3.1 >>= fun s3 ↦ g2Add s3 p4.1 >>= fun s4 ↦
  g2Add s4 p5.1 >>= fun cs ↦
  g2EqEval z one rho sh.1 >>= fun ee ↦
  g2Prod z one (sh.1.drop xl) >>= fun sel ↦
  g2Add (vals.getD 1 default) (vals.getD 2 default) >>= fun im ↦
  g2Mul sel (vals.getD 3 default) im >>= fun inner ↦
  g2Mul ee inner z >>= fun t1 ↦
  g2Mul cs (vals.getD 0 default) t1 >>= fun rhs ↦
  g2Add sh.2 rhs >>= fun e ↦
  g2Assert e gate >>= fun _ ↦
  pure ⟨kchal, sh.1, sh.2, vals⟩

variable {c : Ctx} {M : Mem}

theorem hs_and' {α : Type} {m : BM α} {P Q : α → Prop} (hP : Hs c M m P) (hQ : Hs c M m Q) :
    Hs c M m fun a ↦ P a ∧ Q a := fun p h ↦ ⟨hP p h, hQ p h⟩

/-- **CB-3: the link gadget re-executes the sponge link.** -/
theorem linkHar : LinkHarStmt2 ksLinkG6 := by
  intro hk xl B K₁ K₂ hB hK₁ hK₂ a gate c M hg
  unfold ksLinkG6
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ hsA_bind (hsA_of_hs (hs_g2One z)) fun one ho ↦ ?_
  rw [hz, add_zero] at ho
  refine hsA_bind (hsA_of_hs (hs_and' (sc2_runs (c := c) gC2 (by norm_num) hk (ksLinkQ1 hk (a + 1)) z)
    (hs_sc2 hk (ksLinkQ1 hk (a + 1)) z))) fun sh hsh ↦ ?_
  obtain ⟨hrun, hs1, hs2⟩ := hsh
  have hlr : ((((List.range (hk + 5)).map fun i ↦ ld2 (a + 1 + 10 * i)).take hk).map (C2.val M)).length
      = hk := by simp
  have hl' : (sh.1.map (C2.val M)).length = hk := by rw [hs1]; simp [sc2Ans]
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ (B - 1))) fun p1 hp1 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ (K₁ + 31))) fun p2 hp2 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ K₁)) fun p3 hp3 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ (K₂ + 31))) fun p4 hp4 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2PreRec hz ho _ _ K₂)) fun p5 hp5 ↦ ?_
  rw [preCFF_eq _ _ _ (by rw [hlr, hl']) (by rw [hlr]; exact hB)] at hp1
  rw [preCFF_eq _ _ _ (by rw [hlr, hl']) (by rw [hlr]; exact hK₁)] at hp2
  rw [preCFF_eq _ _ _ (by rw [hlr, hl']) (by rw [hlr]; omega)] at hp3
  rw [preCFF_eq _ _ _ (by rw [hlr, hl']) (by rw [hlr]; exact hK₂)] at hp4
  rw [preCFF_eq _ _ _ (by rw [hlr, hl']) (by rw [hlr]; omega)] at hp5
  simp only [Prod.mk.injEq] at hp1 hp2 hp3 hp4 hp5
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s12 h12 ↦ hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s3 h3 ↦
    hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s4 h4 ↦ hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun cs hcs ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2EqEval hz one _ _ (by simp [hs1, sc2Ans]))) fun ee hee ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Prod hz one _)) fun sel hsel ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun im him ↦ hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun inner hin ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t1 ht1 ↦ hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun rhs hrhs ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun e he ↦ hsA_bind (hsA_g2Assert e gate hg) fun _ hE ↦
    hsA_pure ?_
  -- the check in `FE2`
  set rho := ((List.range (hk + 5)).map fun i ↦ ld2 (a + 1 + 10 * i)).take hk with hrho
  set vals := (List.range 4).map fun k ↦ ld2 (ksLinkQV hk (a + 1) + 2 * k) with hvals
  have hfin : sh.2.val M = contShiftF (rowsBK2 B K₁ K₂) (rho.map (C2.val M)) (sh.1.map (C2.val M)) *
      (vals.getD 0 default).val M + eqEvalF (rho.map (C2.val M)) (sh.1.map (C2.val M)) *
        ((vals.getD 1 default).val M + (vals.getD 2 default).val M +
          selXF xl (sh.1.map (C2.val M)) * (vals.getD 3 default).val M) := by
    have hE' : sh.2.val M = rhs.val M := by
      rw [he] at hE
      linear_combination hE - (rhs.val M) * CharTwo.two_eq_zero (R := FE2)
    have hsel' : sel.val M = selXF xl (sh.1.map (C2.val M)) := by
      rw [hsel, ho, one_mul, selXF, prodF_eq, List.map_drop]
    rw [hE', hrhs, ht1, hin, him, hsel', hee, ho, one_mul, hz, add_zero, hcs, h4, h3, h12,
      contShiftF_pre2, contShiftF_pre, ← hp1.1, ← hp2.1, ← hp3.1, ← hp4.1, ← hp5.1]
    ring
  -- the run
  intro hpw evs hev
  have hlay : layItems (linkItems hk) a = layItems (rep (hk + 5) [.G 1]) a ++
      (layItems (rep hk (rnd 2 2)) (ksLinkQ1 hk (a + 1)) ++ layItems [.E 4] (ksLinkQV hk (a + 1))) := by
    rw [linkItems, layItems_append, layItems_append, layEnd_append, layEnd_repG, layEnd_repR]
    simp only [List.append_assoc, ksLinkQ1, ksLinkQV, roundLanes2]
    congr 2 <;> ring_nf
  rw [hlay] at hpw hev
  have hz2 : ev2 M z = 0 := by simp [ev2, hz]
  rw [hz2] at hrun
  refine runs_bind (runs_e2Samples M (by norm_num) (hk + 5) a) (fun kc hkc ↦ runs_bind hrun
    fun ks hks ↦ runs_bind (runs_e2Reads' M 4 _) fun vs hvs ↦
      runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ?_) hpw evs hev
  · rw [hkc, hks.1, hks.2, hvs]
    have hfin' := congrArg FE2.toE2 hfin
    simp only [FE2.toE2_add, FE2.fe2_mul_eq, toE2_contShiftF, toE2_eqEvalF, toE2_selXF,
      List.map_map] at hfin'
    have hk' : (gdraws M a (hk + 5)).take hk = rho.map (ev2 M) := by
      simp [gdraws, hrho, List.map_take, List.map_map]; rfl
    rw [hk']
    convert hfin' using 3 <;> first | rfl | exact Or.inl rfl |
      simp [scal, hvals, ev2, Function.comp_def, List.getD_eq_getElem?_getD]
  · exact ⟨by rw [hkc]; simp [gdraws, List.map_map], hks.1.symm, hks.2.symm,
      by rw [hvs]; simp [scal, hvals, List.map_map]⟩

end Lvm6.QK
