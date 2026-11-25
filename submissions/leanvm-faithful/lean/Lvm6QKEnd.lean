-- New for lvm6 (WP CB-E). The two Keccak input ends in the node circuit (FORMAT6 §6.2 row 10,
-- §6.3): gadgets on a represented claim with `lt` weights, and their HARs `treeEnd_har :
-- TreeEndHarStmt treeEndG`, `spEnd_har : SpEndHarStmt spEndG` (statements frozen in `Lvm6QKClaim`).
import Lvm6QKEndAlg

/-!
# The input ends (generators and HARs, CB-E)

The claim reaching an end has weights `Lᵀ(batchWF pos β)` (`WRep.lt`), kept as the cells of `pos`
and `β`. Its gadget never writes the 1,600 weights:

* `wDataG`: `eq(pos₀…₅, ·)` (64 cells) and the 25 lane weights `laneWB pos β`, so the weights are
  `Lᵀ(prodWG A B)` (`batchW_eq`); `laneFormG`: one lane form (11 products).
* tree only: `cwG` (`C^P`, `C^L`: four weight entries each, `lt_posF`) and `vG` (`value'`,
  `treeV'`), then 11 plain rounds (`sc2 11`);
* sponge: 10 plain rounds from the claim's value;
* `mleG`: `μ̃(ϱ_low)` (`multilinearEvalF`, one product a pair);
* `rotTabsG`: the rotated sums of the slices against `A` for `uHi`, `uLo` (4,096 products) and
  `uS` (64 additions, `rot_s`);
* `treeTotG` / `spTotG`: the check sum (`treeSum` / `spSum`): the slot point's `eq` table, the
  lane forms, three (two) inner products and the coefficients;
* the check `μ̃·Σ + final = 0` asserted under the gate; the end hands on the opening's
  challenges, the slice point and the 64 slice cells.

Products: tree ≈ 5.1 k, sponge ≈ 4.8 k (4,096 of them the rotated sums).
-/

set_option autoImplicit false

namespace Lvm6.QK.En

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack Lvm.Q1
open Lvm6 (Item rep rnd)
open Finset

variable {c : Ctx} {M : Mem}

/-! ## The kit in `E2` values -/

theorem ev2_of_zero {z : C2} (hz : z.val M = 0) : ev2 M z = 0 := by simp [ev2, hz]

theorem ev2_getDz {z : C2} (hz : ev2 M z = 0) (l : List C2) (i : ℕ) :
    ev2 M (l.getD i z) = (l.map (ev2 M)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hz]

theorem ev2_headDz {z : C2} (hz : ev2 M z = 0) (l : List C2) :
    ev2 M (l.headD z) = (l.map (ev2 M)).headD 0 := by
  cases l <;> simp [hz]

theorem getD_range_map {β : Type} (f : ℕ → β) (d : β) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem ev2_dot_range (n : ℕ) (f g : ℕ → C2) :
    (((List.range n).map fun i ↦ (f i, g i)).map fun e ↦ ev2 M e.1 * ev2 M e.2).sum =
      ∑ i ∈ range n, ev2 M (f i) * ev2 M (g i) := by
  rw [List.map_map]
  exact lsum_range' _ n

theorem hsE_mul (a b d : C2) : Hs c M (g2Mul a b d) fun r ↦ ev2 M r = ev2 M a * ev2 M b + ev2 M d :=
  hs_mono (hs_g2Mul a b d) fun _ h ↦ ev2_mul h

theorem hsE_add (a b : C2) : Hs c M (g2Add a b) fun r ↦ ev2 M r = ev2 M a + ev2 M b :=
  hs_mono (hs_g2Add a b) fun _ h ↦ ev2_add h

theorem hsE_one (a : C2) : Hs c M (g2One a) fun r ↦ ev2 M r = 1 + ev2 M a :=
  hs_mono (hs_g2One a) fun _ h ↦ by simp [ev2, h, FE2.toE2_add, FE2.toE2_one]

theorem hsE_sum (s : C2) (cs : List C2) :
    Hs c M (g2Sum s cs) fun r ↦ ev2 M r = ev2 M s + (cs.map (ev2 M)).sum :=
  hs_mono (hs_g2Sum s cs) fun r h ↦ by
    rw [ev2, h, FE2.toE2_add, ev2_sum, List.map_map]
    rfl

theorem hsE_dot (acc : C2) (l : List (C2 × C2)) :
    Hs c M (g2Dot acc l) fun r ↦ ev2 M r = ev2 M acc + (l.map fun e ↦ ev2 M e.1 * ev2 M e.2).sum :=
  hs_mono (hs_g2Dot acc l) fun r h ↦ by
    have hm : (FE2.toE2 ∘ fun e : C2 × C2 ↦ C2.val M e.1 * C2.val M e.2) =
        fun e ↦ ev2 M e.1 * ev2 M e.2 := by
      funext e; simp [ev2, FE2.fe2_mul_eq]
    rw [ev2, h, FE2.toE2_add, ev2_sum, List.map_map, hm]
    rfl

theorem hsE_mapB {α : Type} (f : α → BM C2) (g : α → E2) : ∀ (l : List α),
    (∀ a ∈ l, Hs c M (f a) fun r ↦ ev2 M r = g a) →
      Hs c M (mapB f l) fun rs ↦ rs.map (ev2 M) = l.map g
  | [], _ => hs_pure rfl
  | a :: l, hf => hs_bind (hf a (by simp)) fun r hr ↦
      hs_bind (hsE_mapB f g l fun b hb ↦ hf b (by simp [hb])) fun rs hrs ↦
        hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

theorem hsE_eqTab {z one : C2} (hz0 : z.val M = 0) (hone : one.val M = 1) (pt : List C2) :
    Hs c M (g2EqTab z [one] pt) fun t ↦ t.map (ev2 M) = eqKernelF (pt.map (ev2 M)) :=
  hs_mono (hs_g2EqTab hz0 [one] pt) fun _ h ↦ eqTab_ev2 hone pt h

/-- The check of an end from its asserted cell `e = m·t + f`. -/
theorem chk_of_assert {m t f e : C2} (he : e.val M = m.val M * t.val M + f.val M)
    (hE : e.val M = 0) : ev2 M m * ev2 M t = ev2 M f := by
  have h0 : m.val M * t.val M = f.val M := by
    rw [he] at hE
    linear_combination hE - f.val M * CharTwo.two_eq_zero (R := FE2)
  simp only [ev2, ← FE2.fe2_mul_eq, h0]

theorem layEnd_repR' (g : ℕ) : ∀ (n a : ℕ), layEnd (rep n (rnd 2 g)) a = a + 14 * n
  | 0, a => rfl
  | n + 1, a => by
    rw [rep_succ, layEnd_append, layEnd_repR' g n]
    simp only [rnd, layEnd]; ring

/-! ## Gadgets -/

/-- **One lane form** from the lane weight cells `Bc` and a shift table `Rf` (11 products). -/
def laneFormG (z : C2) (Bc : List C2) (Rf : ℕ → C2) (l : ℕ) : BM C2 :=
  g2Dot z ((lanePairs l).map fun p ↦ (Bc.getD p.1 z, Rf p.2))

/-- One lane weight of the batch (2 products). -/
def laneWG (β : C2) (tb : List C2) (z : C2) (l : ℕ) : BM C2 :=
  g2Mul β (tb.getD (Lvm.keccakAlong (64 * l) 3 / 64) z) (tb.getD (Lvm.keccakAlong (64 * l) 4 / 64) z) >>=
    fun t ↦ g2Mul β t (tb.getD l z)

/-- `eq(pos₀…₅, ·)` and the 25 lane weights. -/
def wDataG (z one : C2) (pos : List C2) (β : C2) : BM (List C2 × List C2) :=
  g2EqTab z [one] (pos.take 6) >>= fun ta ↦ g2EqTab z [one] (pos.drop 6) >>= fun tb ↦
    mapB (laneWG β tb z) (List.range 25) >>= fun bc ↦ pure (ta, bc)

/-- Weight entry `j` (`lt_posF`). -/
def entG (z : C2) (ta bc : List C2) (j : ℕ) : BM C2 :=
  laneFormG z bc (fun k ↦ ta.getD ((j % 64 + k) % 64) z) (j / 64)

/-- `C^t = Σ_{j ∈ bits} W_j`. -/
def cwG (z : C2) (ta bc : List C2) (bits : List ℕ) : BM C2 :=
  mapB (entG z ta bc) bits >>= fun es ↦ g2Sum z es

/-- `value' = value + (1 + r'_seg)·Σμ·((1 + r_top)·C^P + r_top·C^L)` (`treeV'`). -/
def vG (κ : ℕ) (z : C2) (claim : ClaimC) (cwp cwl : C2) : BM C2 :=
  g2Sum z claim.mu >>= fun msum ↦ g2Add cwp cwl >>= fun d ↦
  g2Mul (claim.point.getD (κ - 4 - 1) z) d cwp >>= fun inner ↦
  g2One (claim.point.getD (κ - 4) z) >>= fun rseg1 ↦ g2Mul rseg1 msum z >>= fun t ↦
  g2Mul t inner claim.value

/-- One fold of `multilinearEvalF`: adjacent pairs `(a, b)` to `a + (a + b)·r`. -/
def foldPairsG (r : C2) : List C2 → BM (List C2)
  | a :: b :: rest => g2Add b a >>= fun d ↦ g2Mul d r a >>= fun x ↦
    foldPairsG r rest >>= fun xs ↦ pure (x :: xs)
  | _ => pure []

/-- `multilinearEvalF`'s folds (the value is the head). -/
def mleG : List C2 → List C2 → BM (List C2)
  | cur, [] => pure cur
  | cur, r :: rs => foldPairsG r cur >>= fun nx ↦ mleG nx rs

/-- **The three rotated sums of the slices** (`uHi`, `uLo`, `uS`) against the table `ta`. -/
def rotTabsG (z : C2) (sl ta : List C2) : BM (List C2 × List C2 × List C2) :=
  mapB (fun t ↦ g2Dot z ((List.range 56).map fun i ↦ (sl.getD i z, ta.getD ((i + 8 + t) % 64) z)))
    (List.range 64) >>= fun rh ↦
  mapB (fun t ↦ g2Dot z ((List.range 8).map fun i ↦ (sl.getD (56 + i) z, ta.getD ((i + t) % 64) z)))
    (List.range 64) >>= fun rl ↦
  mapB (fun t ↦ g2Add (rh.getD ((t + 56) % 64) z) (rl.getD ((t + 56) % 64) z)) (List.range 64) >>=
    fun rs ↦ pure (rh, rl, rs)

/-- **The tree end's check sum** (`treeSum`). -/
def treeTotG (z one : C2) (ta bc sl : List C2) (rseg rtop : C2) (ϱ : List C2) : BM C2 :=
  rotTabsG z sl ta >>= fun R ↦
  g2EqTab z [one] (ϱ.drop 5) >>= fun te ↦
  mapB (fun o ↦ laneFormG z bc (fun k ↦ R.1.getD (k % 64) z) o >>= fun a ↦
    laneFormG z bc (fun k ↦ R.2.1.getD (k % 64) z) (o + 1) >>= fun b ↦ g2Add a b)
    (List.range 8) >>= fun X ↦
  mapB (laneFormG z bc fun k ↦ R.2.2.getD (k % 64) z) (List.range 25) >>= fun LS ↦
  g2Dot z ((List.range 8).map fun o ↦ (te.getD o z, X.getD o z)) >>= fun T1 ↦
  g2Dot z ((List.range 4).map fun o ↦ (te.getD o z, X.getD o z)) >>= fun T2 ↦
  g2Dot z ((List.range 25).map fun l ↦ (te.getD (8 + l) z, LS.getD l z)) >>= fun T3 ↦
  g2One rseg >>= fun rseg1 ↦ g2One rtop >>= fun rtop1 ↦ g2One (ϱ.getD 4 z) >>= fun ϱtop1 ↦
  g2Mul rseg1 rtop1 z >>= fun p1 ↦ g2Mul p1 ϱtop1 z >>= fun cP ↦
  g2Mul rseg1 rtop z >>= fun l1 ↦ g2Mul l1 (ϱ.getD 4 z) z >>= fun cL ↦
  g2Add rtop ϱtop1 >>= fun mm ↦ g2Mul rseg mm z >>= fun cM ↦
  g2Mul cP T1 z >>= fun a1 ↦ g2Mul cL T2 a1 >>= fun a2 ↦ g2Mul cM T3 a2

/-- **The sponge end's check sum** (`spSum`). -/
def spTotG (z one : C2) (ta bc sl : List C2) (rseg : C2) (ϱ : List C2) : BM C2 :=
  rotTabsG z sl ta >>= fun R ↦
  g2EqTab z [one] (ϱ.drop 4) >>= fun te ↦
  mapB (laneFormG z bc fun k ↦ R.2.2.getD (k % 64) z) (List.range 25) >>= fun LS ↦
  g2Dot z ((List.range 25).map fun l ↦ (te.getD l z, LS.getD l z)) >>= fun S0 ↦
  g2Dot z ((List.range 25).map fun l ↦ (te.getD (25 + l) z, LS.getD l z)) >>= fun S1 ↦
  g2One rseg >>= fun rseg1 ↦ g2Mul rseg1 S0 z >>= fun a ↦ g2Mul rseg S1 a

/-- The 64 slice cells after `R` rounds from lane `q`. -/
def slC (R q : ℕ) : List C2 := (List.range 64).map fun i ↦ ld2 (q + 14 * R + 2 * i)

/-! ## Their values -/

theorem hs_laneFormG {z : C2} (hz : ev2 M z = 0) (Bc : List C2) (Rf : ℕ → C2) (R : ℕ → E2)
    (hR : ∀ k, ev2 M (Rf k) = R k) (l : ℕ) :
    Hs c M (laneFormG z Bc Rf l) fun r ↦ ev2 M r = laneFormF (Bc.map (ev2 M)) R l :=
  hs_mono (hsE_dot _ _) fun r h ↦ by
    rw [h, hz, zero_add, laneForm_pairs, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun p _ ↦ by
      simp only [Function.comp_apply, ev2_getDz hz, hR])

theorem hs_wDataG {z one : C2} (hz0 : z.val M = 0) (hone : one.val M = 1) (pos : List C2) (β : C2) :
    Hs c M (wDataG z one pos β) fun o ↦ o.1.map (ev2 M) = eqKernelF ((pos.map (ev2 M)).take 6) ∧
      o.2.map (ev2 M) = laneWB (pos.map (ev2 M)) (ev2 M β) := by
  have hz := ev2_of_zero hz0
  unfold wDataG
  refine hs_bind (hsE_eqTab hz0 hone _) fun ta hta ↦ hs_bind (hsE_eqTab hz0 hone _) fun tb htb ↦
    hs_bind (hsE_mapB (laneWG β tb z) (fun l ↦ (eqKernelF ((pos.map (ev2 M)).drop 6)).getD l 0 +
      ev2 M β * ((eqKernelF ((pos.map (ev2 M)).drop 6)).getD (Lvm.keccakAlong (64 * l) 4 / 64) 0 +
        ev2 M β * (eqKernelF ((pos.map (ev2 M)).drop 6)).getD (Lvm.keccakAlong (64 * l) 3 / 64) 0))
      (List.range 25) fun l _ ↦ ?_) fun bc hbc ↦ hs_pure ⟨by rw [hta, List.map_take], hbc⟩
  rw [List.map_drop] at htb
  unfold laneWG
  refine hs_bind (hsE_mul _ _ _) fun t ht ↦ hs_mono (hsE_mul _ _ _) fun r hr ↦ ?_
  simp only [hr, ht, ev2_getDz hz, htb]
  ring

theorem hs_cwG {z : C2} (hz : ev2 M z = 0) (ta bc : List C2) (a B : List E2)
    (hta : ta.map (ev2 M) = eqKernelF a) (hbc : bc.map (ev2 M) = B) (bits : List ℕ)
    (hb : ∀ j ∈ bits, j < 1600) :
    Hs c M (cwG z ta bc bits) fun r ↦ ev2 M r = cW (linearTransposeF (prodWG (eqAtG a) B)) bits := by
  unfold cwG
  refine hs_bind (hsE_mapB _ (fun j ↦ (linearTransposeF (prodWG (eqAtG a) B)).getD j 0) bits
      fun j hj ↦ hs_mono (hs_laneFormG hz bc _ (fun k ↦ eqAtG a ((j % 64 + k) % 64))
        (fun k ↦ by rw [ev2_getDz hz, hta]; rfl) (j / 64))
        fun r hr ↦ by rw [hr, hbc, lt_posF _ _ (hb j hj)])
    fun es hes ↦ hs_mono (hsE_sum z es) fun r hr ↦ ?_
  rw [hr, hz, zero_add, hes, cW]

theorem hs_vG (κ : ℕ) {z : C2} (hz : ev2 M z = 0) (claim : ClaimC) (cl : KClaim E2)
    (hv : ev2 M claim.value = cl.value) (hmu : claim.mu.map (ev2 M) = cl.mu)
    (hpoint : claim.point.map (ev2 M) = cl.point) (cwp cwl : C2)
    (hp : ev2 M cwp = cW cl.weights cPbits) (hl : ev2 M cwl = cW cl.weights cLbits) :
    Hs c M (vG κ z claim cwp cwl) fun r ↦ ev2 M r = treeV' (κ - 4) cl := by
  unfold vG
  refine hs_bind (hsE_sum z claim.mu) fun msum hmsum ↦ hs_bind (hsE_add _ _) fun d hd ↦
    hs_bind (hsE_mul _ _ _) fun inner hinner ↦ hs_bind (hsE_one _) fun r1 hr1 ↦
    hs_bind (hsE_mul _ _ _) fun t ht ↦ hs_mono (hsE_mul _ _ _) fun r hr ↦ ?_
  simp only [hr, ht, hinner, hr1, hd, hmsum, hz, hmu, hp, hl, hv, ev2_getDz hz, hpoint, treeV']
  ring

theorem hs_foldPairsG (r : C2) : ∀ l : List C2,
    Hs c M (foldPairsG r l) fun o ↦ o.map (ev2 M) = foldPairsF (ev2 M r) (l.map (ev2 M))
  | [] => hs_pure rfl
  | [_] => hs_pure rfl
  | a :: b :: rest => hs_bind (hsE_add b a) fun d hd ↦ hs_bind (hsE_mul d r a) fun x hx ↦
      hs_bind (hs_foldPairsG r rest) fun xs hxs ↦ hs_pure (by
        rw [List.map_cons, hxs, hx, hd]
        exact congrArg₂ List.cons (by ring) rfl)

theorem hs_mleG : ∀ (cur pt : List C2), Hs c M (mleG cur pt) fun o ↦
    o.map (ev2 M) = (pt.map (ev2 M)).foldl (fun cur r ↦ foldPairsF r cur) (cur.map (ev2 M))
  | cur, [] => hs_pure rfl
  | cur, r :: rs => hs_bind (hs_foldPairsG r cur) fun nx hnx ↦ hs_mono (hs_mleG nx rs) fun o ho ↦ by
      rw [ho, hnx, List.map_cons, List.foldl_cons]

theorem hs_mle {z : C2} (hz : ev2 M z = 0) (mu pt : List C2) :
    Hs c M (mleG mu pt) fun o ↦
      ev2 M (o.headD z) = multilinearEvalF (mu.map (ev2 M)) (pt.map (ev2 M)) :=
  hs_mono (hs_mleG mu pt) fun o ho ↦ by rw [ev2_headDz hz, ho, multilinearEvalF]

theorem hs_rotTabsG {z : C2} (hz : ev2 M z = 0) (sl ta : List C2) (A : ℕ → E2)
    (hA : ∀ k, ev2 M (ta.getD k z) = A k) :
    Hs c M (rotTabsG z sl ta) fun R ↦
      R.1.map (ev2 M) = (List.range 64).map (rotSumG (uHi (sl.map (ev2 M))) A) ∧
      R.2.1.map (ev2 M) = (List.range 64).map (rotSumG (uLo (sl.map (ev2 M))) A) ∧
      R.2.2.map (ev2 M) = (List.range 64).map (rotSumG (uS (sl.map (ev2 M))) A) := by
  unfold rotTabsG
  refine hs_bind (hsE_mapB _ (rotSumG (uHi (sl.map (ev2 M))) A) _ fun t _ ↦
      hs_mono (hsE_dot _ _) fun r hr ↦ by
        rw [hr, hz, zero_add, ev2_dot_range, rot_hi]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hA, ev2_getDz hz]) fun rh hrh ↦
    hs_bind (hsE_mapB _ (rotSumG (uLo (sl.map (ev2 M))) A) _ fun t _ ↦
      hs_mono (hsE_dot _ _) fun r hr ↦ by
        rw [hr, hz, zero_add, ev2_dot_range, rot_lo]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hA, ev2_getDz hz]) fun rl hrl ↦
    hs_bind (hsE_mapB _ (rotSumG (uS (sl.map (ev2 M))) A) _ fun t _ ↦
      hs_mono (hsE_add _ _) fun r hr ↦ by
        rw [hr, rot_s, ev2_getDz hz, ev2_getDz hz, hrh, hrl,
          getD_range_map _ _ (Nat.mod_lt (t + 56) (by norm_num : (64 : ℕ) > 0)),
          getD_range_map _ _ (Nat.mod_lt (t + 56) (by norm_num : (64 : ℕ) > 0))]) fun rs hrs ↦
    hs_pure ⟨hrh, hrl, hrs⟩

theorem hs_treeTotG {z one : C2} (hz0 : z.val M = 0) (hone : one.val M = 1) (ta bc sl : List C2)
    (a B : List E2) (hta : ta.map (ev2 M) = eqKernelF a) (hbc : bc.map (ev2 M) = B)
    (rseg rtop : C2) (ϱ : List C2) (hϱ : ϱ.length = 11) :
    Hs c M (treeTotG z one ta bc sl rseg rtop ϱ) fun r ↦ ev2 M r =
      ∑ x ∈ range 64, treeWt (ev2 M rseg) (ev2 M rtop) ((ϱ.map (ev2 M)).getD 4 0)
        (linearTransposeF (prodWG (eqAtG a) B)) ((ϱ.map (ev2 M)).drop 5) x *
          (sl.map (ev2 M)).getD x 0 := by
  have hz := ev2_of_zero hz0
  have hA : ∀ k, ev2 M (ta.getD k z) = eqAtG a k := fun k ↦ by rw [ev2_getDz hz, hta]; rfl
  have hRf : ∀ (Rc : List C2) (u : ℕ → E2),
      Rc.map (ev2 M) = (List.range 64).map (rotSumG u (eqAtG a)) →
        ∀ k, ev2 M (Rc.getD (k % 64) z) = rotSumG u (eqAtG a) k := fun Rc u h k ↦ by
    rw [ev2_getDz hz, h, getD_range_map _ _ (Nat.mod_lt k (by norm_num : (64 : ℕ) > 0)), rotSum_mod']
  have hϱs : ((ϱ.map (ev2 M)).drop 5).length = 6 := by simp [hϱ]
  unfold treeTotG
  refine hs_bind (hs_rotTabsG hz sl ta _ hA) fun R hR ↦ ?_
  obtain ⟨h1, h2, h3⟩ := hR
  refine hs_bind (hsE_eqTab hz0 hone _) fun te hte ↦ ?_
  rw [List.map_drop] at hte
  refine hs_bind (hsE_mapB _ (XF (eqAtG a) B (sl.map (ev2 M))) _ fun o _ ↦
      hs_bind (hs_laneFormG hz bc _ _ (hRf _ _ h1) o) fun x hx ↦
      hs_bind (hs_laneFormG hz bc _ _ (hRf _ _ h2) (o + 1)) fun y hy ↦
      hs_mono (hsE_add x y) fun r hr ↦ by rw [hr, hx, hy, hbc, XF]) fun X hX ↦ ?_
  refine hs_bind (hsE_mapB _ (laneFormF B (rotSumG (uS (sl.map (ev2 M))) (eqAtG a))) _ fun l _ ↦
      hs_mono (hs_laneFormG hz bc _ _ (hRf _ _ h3) l) fun r hr ↦ by rw [hr, hbc]) fun LS hLS ↦ ?_
  refine hs_bind (hsE_dot _ _) fun T1 hT1 ↦ hs_bind (hsE_dot _ _) fun T2 hT2 ↦
    hs_bind (hsE_dot _ _) fun T3 hT3 ↦ hs_bind (hsE_one _) fun rseg1 hrseg1 ↦
    hs_bind (hsE_one _) fun rtop1 hrtop1 ↦ hs_bind (hsE_one _) fun ϱtop1 hϱtop1 ↦
    hs_bind (hsE_mul _ _ _) fun p1 hp1 ↦ hs_bind (hsE_mul _ _ _) fun cP hcP ↦
    hs_bind (hsE_mul _ _ _) fun l1 hl1 ↦ hs_bind (hsE_mul _ _ _) fun cL hcL ↦
    hs_bind (hsE_add _ _) fun mm hmm ↦ hs_bind (hsE_mul _ _ _) fun cM hcM ↦
    hs_bind (hsE_mul _ _ _) fun a1 ha1 ↦ hs_bind (hsE_mul _ _ _) fun a2 ha2 ↦
    hs_mono (hsE_mul _ _ _) fun r hr ↦ ?_
  have hT1' : ev2 M T1 = ∑ o ∈ range 8, (eqKernelF ((ϱ.map (ev2 M)).drop 5)).getD o 0 *
      XF (eqAtG a) B (sl.map (ev2 M)) o := by
    rw [hT1, hz, zero_add, ev2_dot_range]
    exact Finset.sum_congr rfl fun o ho ↦ by
      rw [ev2_getDz hz, ev2_getDz hz, hte, hX, getD_range_map _ _ (Finset.mem_range.mp ho)]
  have hT2' : ev2 M T2 = ∑ o ∈ range 4, (eqKernelF ((ϱ.map (ev2 M)).drop 5)).getD o 0 *
      XF (eqAtG a) B (sl.map (ev2 M)) o := by
    rw [hT2, hz, zero_add, ev2_dot_range]
    exact Finset.sum_congr rfl fun o ho ↦ by
      rw [ev2_getDz hz, ev2_getDz hz, hte, hX,
        getD_range_map _ _ (show o < 8 by have := Finset.mem_range.mp ho; omega)]
  have hT3' : ev2 M T3 = ∑ l ∈ range 25, (eqKernelF ((ϱ.map (ev2 M)).drop 5)).getD (8 + l) 0 *
      laneFormF B (rotSumG (uS (sl.map (ev2 M))) (eqAtG a)) l := by
    rw [hT3, hz, zero_add, ev2_dot_range]
    exact Finset.sum_congr rfl fun l hl ↦ by
      rw [ev2_getDz hz, ev2_getDz hz, hte, hLS, getD_range_map _ _ (Finset.mem_range.mp hl)]
  rw [treeSum _ _ _ _ _ _ _ hϱs]
  simp only [hr, ha2, ha1, hT1', hT2', hT3', hcM, hmm, hcL, hl1, hcP, hp1, hrseg1, hrtop1, hϱtop1, hz,
    ev2_getDz hz]
  ring

theorem hs_spTotG {z one : C2} (hz0 : z.val M = 0) (hone : one.val M = 1) (ta bc sl : List C2)
    (a B : List E2) (hta : ta.map (ev2 M) = eqKernelF a) (hbc : bc.map (ev2 M) = B)
    (rseg : C2) (ϱ : List C2) (hϱ : ϱ.length = 10) :
    Hs c M (spTotG z one ta bc sl rseg ϱ) fun r ↦ ev2 M r =
      ∑ x ∈ range 64, spWt (ev2 M rseg) (linearTransposeF (prodWG (eqAtG a) B))
        ((ϱ.map (ev2 M)).drop 4) x * (sl.map (ev2 M)).getD x 0 := by
  have hz := ev2_of_zero hz0
  have hA : ∀ k, ev2 M (ta.getD k z) = eqAtG a k := fun k ↦ by rw [ev2_getDz hz, hta]; rfl
  have hϱs : ((ϱ.map (ev2 M)).drop 4).length = 6 := by simp [hϱ]
  unfold spTotG
  refine hs_bind (hs_rotTabsG hz sl ta _ hA) fun R hR ↦ ?_
  obtain ⟨-, -, h3⟩ := hR
  have hRs : ∀ k, ev2 M (R.2.2.getD (k % 64) z) = rotSumG (uS (sl.map (ev2 M))) (eqAtG a) k :=
    fun k ↦ by
      rw [ev2_getDz hz, h3, getD_range_map _ _ (Nat.mod_lt k (by norm_num : (64 : ℕ) > 0)),
        rotSum_mod']
  refine hs_bind (hsE_eqTab hz0 hone _) fun te hte ↦ ?_
  rw [List.map_drop] at hte
  refine hs_bind (hsE_mapB _ (laneFormF B (rotSumG (uS (sl.map (ev2 M))) (eqAtG a))) _ fun l _ ↦
      hs_mono (hs_laneFormG hz bc _ _ hRs l) fun r hr ↦ by rw [hr, hbc]) fun LS hLS ↦ ?_
  refine hs_bind (hsE_dot _ _) fun S0 hS0 ↦ hs_bind (hsE_dot _ _) fun S1 hS1 ↦
    hs_bind (hsE_one _) fun rseg1 hrseg1 ↦ hs_bind (hsE_mul _ _ _) fun a1 ha1 ↦
    hs_mono (hsE_mul _ _ _) fun r hr ↦ ?_
  have hS0' : ev2 M S0 = ∑ l ∈ range 25, (eqKernelF ((ϱ.map (ev2 M)).drop 4)).getD l 0 *
      laneFormF B (rotSumG (uS (sl.map (ev2 M))) (eqAtG a)) l := by
    rw [hS0, hz, zero_add, ev2_dot_range]
    exact Finset.sum_congr rfl fun l hl ↦ by
      rw [ev2_getDz hz, ev2_getDz hz, hte, hLS, getD_range_map _ _ (Finset.mem_range.mp hl)]
  have hS1' : ev2 M S1 = ∑ l ∈ range 25, (eqKernelF ((ϱ.map (ev2 M)).drop 4)).getD (25 + l) 0 *
      laneFormF B (rotSumG (uS (sl.map (ev2 M))) (eqAtG a)) l := by
    rw [hS1, hz, zero_add, ev2_dot_range]
    exact Finset.sum_congr rfl fun l hl ↦ by
      rw [ev2_getDz hz, ev2_getDz hz, hte, hLS, getD_range_map _ _ (Finset.mem_range.mp hl)]
  rw [spSum _ _ _ _ _ hϱs]
  simp only [hr, ha1, hS0', hS1', hrseg1, hz]
  ring

theorem slC_ev2 (R q : ℕ) : (slC R q).map (ev2 M) = scal M (q + 14 * R) 64 := by
  rw [slC, scal, List.map_map]
  rfl

/-! ## The tree's input end -/

/-- **The tree end gadget** on a claim with `lt` weights. -/
def treeEndCore (κ q : ℕ) (claim : ClaimC) (pos : List C2) (β : C2) (gate : Cell) :
    BM (List C2 × List C2 × List C2) :=
  g2Zero claim.value >>= fun z ↦ g2One z >>= fun one ↦
  wDataG z one pos β >>= fun wd ↦
  cwG z wd.1 wd.2 cPbits >>= fun cwp ↦ cwG z wd.1 wd.2 cLbits >>= fun cwl ↦
  vG κ z claim cwp cwl >>= fun v' ↦
  sc2 11 q v' >>= fun lv ↦
  mleG claim.mu (lv.1.take 4) >>= fun mf ↦
  treeTotG z one wd.1 wd.2 (slC 11 q) (claim.point.getD (κ - 4) z) (claim.point.getD (κ - 4 - 1) z)
    lv.1 >>= fun tot ↦
  g2Mul (mf.headD z) tot lv.2 >>= fun e ↦ g2Assert e gate >>= fun _ ↦
  pure (lv.1, lv.1.take 4 ++ claim.point.take (κ - 4 - 1) ++ [lv.1.getD 4 z] ++ lv.1.drop 5, slC 11 q)

/-- **The tree end generator** (`TreeEndHarStmt`'s `G`). -/
def treeEndG (κ q : ℕ) (claim : ClaimC) (gate : Cell) : BM (List C2 × List C2 × List C2) :=
  match claim.w with
  | .lt pos β => treeEndCore κ q claim pos β gate
  | .first _ => pure ([], [], [])

theorem treeEndCore_har {κ : ℕ} (q : ℕ) (claim : ClaimC) (pos : List C2) (β : C2) (gate : Cell)
    (hg : gate.val M = 1) (hw : claim.w = .lt pos β) (hpl : pos.length = 11) (cl : KClaim E2)
    (hrep : ClaimRep M claim cl) :
    HsA c M (treeEndCore κ q claim pos β gate) fun o ↦
      Runs M (layItems treeEndItems q) (treeEnd6 (κ - 4) cl)
        (fun en ↦ o.1.map (ev2 M) = en.ϱ ∧ o.2.1.map (ev2 M) = en.pt ∧ o.2.2.map (ev2 M) = en.s) := by
  obtain ⟨hv, hmu, hpoint, hwts⟩ := hrep
  rw [hw, wOf, batchW_eq (by rw [List.length_map, hpl])] at hwts
  unfold treeEndCore
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz0 ↦ ?_
  have hz := ev2_of_zero hz0
  refine hsA_bind (hsA_of_hs (hs_g2One z)) fun one hone ↦ ?_
  rw [hz0, add_zero] at hone
  refine hsA_bind (hsA_of_hs (hs_wDataG hz0 hone pos β)) fun wd hwd ↦ ?_
  obtain ⟨hta, hbc⟩ := hwd
  refine hsA_bind (hsA_of_hs (hs_cwG hz wd.1 wd.2 _ _ hta hbc cPbits (by simp [cPbits])))
    fun cwp hcwp ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_cwG hz wd.1 wd.2 _ _ hta hbc cLbits (by simp [cLbits])))
    fun cwl hcwl ↦ ?_
  rw [hwts] at hcwp hcwl
  refine hsA_bind (hsA_of_hs (hs_vG κ hz claim cl hv hmu hpoint cwp cwl hcwp hcwl)) fun v' hv' ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_and (sc2_runs (c := c) 2 (by norm_num) 11 q v') (hs_sc2 11 q v')))
    fun lv hlv ↦ ?_
  obtain ⟨hom, homs, -⟩ := hlv
  have hlen : lv.1.length = 11 := by rw [homs, List.length_map, sc2Ans_length]
  refine hsA_bind (hsA_of_hs (hs_mle hz claim.mu (lv.1.take 4))) fun mf hmf ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_treeTotG hz0 hone wd.1 wd.2 (slC 11 q) _ _ hta hbc _ _ lv.1 hlen))
    fun tot htot ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun e he ↦
    hsA_bind (hsA_g2Assert e gate hg) fun _ hE ↦ hsA_pure ?_
  have hchk := chk_of_assert he hE
  rw [hmf, htot, ev2_getDz hz, ev2_getDz hz, hpoint, hwts, slC_ev2, hmu, List.map_take] at hchk
  intro hpw evs hev
  rw [show layItems treeEndItems q = layItems (rep 11 (rnd 2 2)) q ++
      (layItems [.E 64] (q + 14 * 11) ++ []) by
    rw [treeEndItems, layItems_append, layEnd_repR', List.append_nil]] at hpw hev
  rw [hv'] at hom
  refine runs_bind hom (fun lvv hlvv ↦ runs_bind (runs_e2Reads' M 64 (q + 14 * 11)) fun s hs ↦
    runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ⟨?_, ?_, ?_⟩)
    hpw evs hev
  · rw [hlvv.1, hlvv.2, hs]
    exact hchk
  · exact hlvv.1.symm
  · simp only [List.map_append, List.map_take, List.map_drop, List.map_cons, List.map_nil, hpoint,
      ev2_getDz hz, hlvv.1]
  · exact (slC_ev2 11 q).trans hs.symm

/-- **The tree's input end re-executes `treeEnd6`** (FORMAT6 §6.2 row 10), its check included. -/
theorem treeEnd_har : TreeEndHarStmt treeEndG := by
  intro κ _ q claim gate c M hg _ hex cl hrep
  obtain ⟨pos, β, hw, hpl⟩ := hex
  have e : treeEndG κ q claim gate = treeEndCore κ q claim pos β gate := by
    simp only [treeEndG, hw]
  rw [e]
  exact treeEndCore_har q claim pos β gate hg hw hpl cl hrep

/-! ## The sponge's input end -/

/-- **The sponge end gadget** on a claim with `lt` weights. -/
def spEndCore (h q : ℕ) (claim : ClaimC) (pos : List C2) (β : C2) (gate : Cell) :
    BM (List C2 × List C2 × List C2) :=
  g2Zero claim.value >>= fun z ↦ g2One z >>= fun one ↦
  wDataG z one pos β >>= fun wd ↦
  sc2 10 q claim.value >>= fun lv ↦
  mleG claim.mu (lv.1.take 4) >>= fun mf ↦
  spTotG z one wd.1 wd.2 (slC 10 q) (claim.point.getD (h - 4) z) lv.1 >>= fun tot ↦
  g2Mul (mf.headD z) tot lv.2 >>= fun e ↦ g2Assert e gate >>= fun _ ↦
  pure (lv.1, lv.1.take 4 ++ claim.point.take (h - 4) ++ lv.1.drop 4, slC 10 q)

/-- **The sponge end generator** (`SpEndHarStmt`'s `G`). -/
def spEndG (h q : ℕ) (claim : ClaimC) (gate : Cell) : BM (List C2 × List C2 × List C2) :=
  match claim.w with
  | .lt pos β => spEndCore h q claim pos β gate
  | .first _ => pure ([], [], [])

theorem spEndCore_har {h : ℕ} (q : ℕ) (claim : ClaimC) (pos : List C2) (β : C2) (gate : Cell)
    (hg : gate.val M = 1) (hw : claim.w = .lt pos β) (hpl : pos.length = 11) (cl : KClaim E2)
    (hrep : ClaimRep M claim cl) :
    HsA c M (spEndCore h q claim pos β gate) fun o ↦
      Runs M (layItems spEndItems q) (spongeEnd6 (h - 4) cl)
        (fun en ↦ o.1.map (ev2 M) = en.ϱ ∧ o.2.1.map (ev2 M) = en.pt ∧ o.2.2.map (ev2 M) = en.s) := by
  obtain ⟨hv, hmu, hpoint, hwts⟩ := hrep
  rw [hw, wOf, batchW_eq (by rw [List.length_map, hpl])] at hwts
  unfold spEndCore
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz0 ↦ ?_
  have hz := ev2_of_zero hz0
  refine hsA_bind (hsA_of_hs (hs_g2One z)) fun one hone ↦ ?_
  rw [hz0, add_zero] at hone
  refine hsA_bind (hsA_of_hs (hs_wDataG hz0 hone pos β)) fun wd hwd ↦ ?_
  obtain ⟨hta, hbc⟩ := hwd
  refine hsA_bind (hsA_of_hs (hs_and (sc2_runs (c := c) 2 (by norm_num) 10 q claim.value)
    (hs_sc2 10 q claim.value))) fun lv hlv ↦ ?_
  obtain ⟨hom, homs, -⟩ := hlv
  have hlen : lv.1.length = 10 := by rw [homs, List.length_map, sc2Ans_length]
  refine hsA_bind (hsA_of_hs (hs_mle hz claim.mu (lv.1.take 4))) fun mf hmf ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_spTotG hz0 hone wd.1 wd.2 (slC 10 q) _ _ hta hbc _ lv.1 hlen))
    fun tot htot ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun e he ↦
    hsA_bind (hsA_g2Assert e gate hg) fun _ hE ↦ hsA_pure ?_
  have hchk := chk_of_assert he hE
  rw [hmf, htot, ev2_getDz hz, hpoint, hwts, slC_ev2, hmu, List.map_take] at hchk
  intro hpw evs hev
  rw [show layItems spEndItems q = layItems (rep 10 (rnd 2 2)) q ++
      (layItems [.E 64] (q + 14 * 10) ++ []) by
    rw [spEndItems, layItems_append, layEnd_repR', List.append_nil]] at hpw hev
  rw [hv] at hom
  refine runs_bind hom (fun lvv hlvv ↦ runs_bind (runs_e2Reads' M 64 (q + 14 * 10)) fun s hs ↦
    runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ⟨?_, ?_, ?_⟩)
    hpw evs hev
  · rw [hlvv.1, hlvv.2, hs]
    exact hchk
  · exact hlvv.1.symm
  · simp only [List.map_append, List.map_take, List.map_drop, hpoint, hlvv.1]
  · exact (slC_ev2 10 q).trans hs.symm

/-- **The sponge's input end re-executes `spongeEnd6`** (FORMAT6 §6.3), its check included. -/
theorem spEnd_har : SpEndHarStmt spEndG := by
  intro h _ q claim gate c M hg _ hex cl hrep
  obtain ⟨pos, β, hw, hpl⟩ := hex
  have e : spEndG h q claim gate = spEndCore h q claim pos β gate := by
    simp only [spEndG, hw]
  rw [e]
  exact spEndCore_har q claim pos β gate hg hw hpl cl hrep

end Lvm6.QK.En
