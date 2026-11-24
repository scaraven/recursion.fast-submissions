-- New for lvm6 (WP CD). The child's wiring sumcheck in the node circuit (`wire6`, CD-2): `γ`, the
-- 21 plain rounds (CB's `sc2`), the matrix and region values, and `virt(r_y)` from the child's
-- `PUB` cells (one region of `2^10` words, an `eq` table over 10 coordinates) and the `1` words.
import Lvm6QDRelay

/-!
# The wiring (generator and HAR)

* **`virt_eq`**: under `Ti.Ok` and `TyLayOk Ti`, `virtE Ti pw r_y = eq(r_y^{≥10}, pb / 2^10)·
  Σ_{j<2^10} eq(r_y^{<10}, j)·pw(pb + j) + Σ_{one regions R} eq(r_y^{≥log R}, base R / 2^{log R})`
  (no `QLT` region; a `1` region's inner sum is `1`).
* **`wire6 Ti pubC v a gate`**: `γ` at `a + 1`; the start `A + γB + γ²C`; `sc2` from `a + 10`;
  matrix values at `a + 304`, region values at `a + 312`; `virt` (`pubDot6`, `onesSum6`); the gated
  check `final = (v_A + γv_B + γ²(v_D + v_W))·(Σ rv + virt)`. **`wire6_har : WireHarStmt wire6`**.
-/

set_option autoImplicit false

namespace Lvm6.QD

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm.Typed Finset
open Lvm6 (Item rep rnd)
open Lvm6.QK
open Lvm6.Ty (TInst6 wireProgE virtE wBatchE wGE regSumW regSumT gGamma gWire)
open Lvm6.Mb (kG)

/-! ## `toE2` as a ring map -/

/-- `toE2` as a ring homomorphism. -/
def toE2Hom : FE2 →+* E2 where
  toFun := FE2.toE2
  map_one' := FE2.toE2_one
  map_mul' := FE2.fe2_mul_eq
  map_zero' := FE2.toE2_zero
  map_add' := FE2.toE2_add

theorem toE2_eqAtF : ∀ (pt : List FE2) (w : ℕ), FE2.toE2 (E2V.eqAtF pt w) = E2V.eqAtF (pt.map FE2.toE2) w
  | [], _ => by simp [E2V.eqAtF]
  | r :: rs, w => by
    rw [List.map_cons, E2V.eqAtF, E2V.eqAtF, FE2.fe2_mul_eq, toE2_eqAtF rs]
    split_ifs <;> simp

/-! ## Blocks of an aligned region -/

theorem eqAtF_block (ry : List E2) {b log i : ℕ} (hal : b % 2 ^ log = 0) (hi : i < 2 ^ log)
    (hlog : log ≤ ry.length) :
    E2V.eqAtF ry (b + i) = E2V.eqAtF (ry.take log) i * E2V.eqAtF (ry.drop log) (b / 2 ^ log) := by
  have htl : (ry.take log).length = log := by simp [hlog]
  conv_lhs => rw [← List.take_append_drop log ry]
  rw [eqAtF_append, htl, eqAtF_mod (ry.take log), htl]
  have h1 : (b + i) % 2 ^ log = i := by rw [Nat.add_mod, hal, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi]
  have h2 : (b + i) / 2 ^ log = b / 2 ^ log := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hal
    rw [hk, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi, add_zero,
      Nat.mul_div_cancel_left _ (by positivity)]
  rw [h1, h2]

theorem yregsSorted_fits : ∀ (l : List YReg), yregsSorted l = true → ∀ r ∈ l, r.base + 2 ^ r.log ≤ 2 ^ yVars
  | [], _, r, hr => by simp at hr
  | [x], h, r, hr => by
    simp only [yregsSorted, decide_eq_true_eq] at h
    simp only [List.mem_singleton] at hr
    exact hr ▸ h.2
  | x :: y :: l, h, r, hr => by
    simp only [yregsSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨-, h1⟩, h2⟩ := h
    have hy := yregsSorted_fits (y :: l) h2 y (List.mem_cons_self ..)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_trans h1 (le_trans (Nat.le_add_right _ _) hy)
    · exact yregsSorted_fits (y :: l) h2 r hr

theorem ok_log {Ti : TInst6} (hok : Ti.Ok) : ∀ r ∈ Ti.lay.yregs, r.log ≤ yVars := by
  intro r hr
  have h := hok.1
  simp only [Lay.Ok, Lay.okB, Bool.and_eq_true] at h
  have := yregsSorted_fits _ (by tauto) r hr
  have h2 : 2 ^ r.log ≤ 2 ^ yVars := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- A region's `eq` sum against `f`, split at the region's alignment. -/
theorem region_sum (ry : List E2) (hry : ry.length = yVars) (b log : ℕ) (hal : b % 2 ^ log = 0)
    (hlog : log ≤ yVars) (f : ℕ → E2) :
    ((List.range (2 ^ log)).map fun i ↦ E2V.eqAtF ry (b + i) * f (b + i)).sum =
      E2V.eqAtF (ry.drop log) (b / 2 ^ log) *
        ∑ j ∈ range (2 ^ log), E2V.eqAtF (ry.take log) j * f (b + j) := by
  rw [lsum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eqAtF_block ry hal (Finset.mem_range.mp hj) (by omega)]; ring

/-- The `1` regions. -/
def onesOf (Ti : TInst6) : List YReg := Ti.lay.yregs.filter fun r ↦ r.src == .one

/-- **`virt` under CD's layout.** -/
theorem virt_eq {Ti : TInst6} (hok : Ti.Ok) (hlay : TyLayOk Ti) (pw : ℕ → FK) (ry : List E2)
    (hry : ry.length = yVars) :
    virtE Ti pw ry = E2V.eqAtF (ry.drop 10) (pubBase Ti / 2 ^ 10) *
        ∑ j ∈ range (2 ^ 10), E2V.eqAtF (ry.take 10) j * kG (pw (pubBase Ti + j)) +
      ((onesOf Ti).map fun R ↦ E2V.eqAtF (ry.drop R.log) (R.base / 2 ^ R.log)).sum := by
  obtain ⟨-, hpub, hnq⟩ := hlay
  have hqlt : Ti.lay.yregs.filter (fun r ↦ r.src == .qlt) = [] := by
    rw [List.filter_eq_nil_iff]; intro r hr; simpa using hnq r hr
  have hmem : (⟨pubBase Ti, 10, .pub⟩ : YReg) ∈ Ti.lay.yregs := by
    have : (⟨pubBase Ti, 10, .pub⟩ : YReg) ∈ Ti.lay.yregs.filter (fun r ↦ r.src == .pub) := by
      rw [hpub]; exact List.mem_singleton_self _
    exact (List.mem_filter.mp this).1
  unfold virtE regSumT
  rw [regSumW_filter, regSumW_filter, regSumW_filter, hpub, hqlt]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hp := region_sum ry hry (pubBase Ti) 10 (ok_aligned hok _ hmem) (ok_log hok _ hmem)
    (fun y ↦ kG (pw y))
  refine congrArg₂ (· + ·) hp ?_
  rw [onesOf]
  refine congrArg List.sum (List.map_congr_left fun R hR ↦ ?_)
  have hR' := (List.mem_filter.mp hR).1
  have hs := region_sum ry hry R.base R.log (ok_aligned hok _ hR') (ok_log hok _ hR') (fun _ ↦ 1)
  simp only [mul_one] at hs ⊢
  have hl : (ry.take R.log).length = R.log := by simp [hry, ok_log hok _ hR']
  have h1 : ∑ j ∈ range (2 ^ R.log), E2V.eqAtF (ry.take R.log) j = 1 := by
    have := sum_eqAtF (ry.take R.log); rwa [hl] at this
  rw [hs, h1, mul_one]

/-! ## Gadgets -/

/-- `Σ_{j<2^10} eq(lo, j)·pub_j` (the `eq` table, then the dot with the `PUB` cells as `K` values). -/
def pubDot6 (z o : C2) (lo : List C2) (pc : ℕ → Cell) : BM C2 :=
  g2EqTab z [o] lo >>= fun tab ↦
    g2Dot z ((List.range (2 ^ 10)).map fun j ↦ (tab.getD j z, kC2 (pc j) z.re))

/-- `Σ_R eq(r_y^{≥log R}, base R / 2^{log R})` over the `1` regions. -/
def onesSum6 (z o : C2) (ry : List C2) : List YReg → BM C2
  | [] => pure z
  | R :: Rs => g2Sel z o (ry.drop R.log) (R.base / 2 ^ R.log) >>= fun s ↦
      onesSum6 z o ry Rs >>= fun t ↦ g2Add s t

theorem hs_onesSum6 {c : Ctx} {M : Mem} {z o : C2} (hz : z.val M = 0) (ho : o.val M = 1) (ry : List C2) :
    ∀ Rs : List YReg, Hs c M (onesSum6 z o ry Rs) (fun s ↦ ev2 M s =
      (Rs.map fun R ↦ E2V.eqAtF ((ry.map (ev2 M)).drop R.log) (R.base / 2 ^ R.log)).sum)
  | [] => hs_pure (by simp [ev2_of_zero hz])
  | R :: Rs => hs_bind (hs_g2Sel hz ho _ _) fun s hs ↦ hs_bind (hs_onesSum6 hz ho ry Rs) fun t ht ↦
      hs_mono (hs_g2Add _ _) fun r hr ↦ by
        rw [ev2_add hr, hs, ht, List.map_cons, List.sum_cons, List.map_drop]

theorem getD_map_val (M : Mem) (l : List C2) (z : C2) (j : ℕ) :
    (l.getD j z).val M = (l.map (C2.val M)).getD j (z.val M) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

theorem hs_pubDot6 {c : Ctx} {M : Mem} {z o : C2} (hz : z.val M = 0) (ho : o.val M = 1) (lo : List C2)
    (hlo : lo.length = 10) (pc : ℕ → Cell) :
    Hs c M (pubDot6 z o lo pc) (fun s ↦ ev2 M s =
      ∑ j ∈ range (2 ^ 10), E2V.eqAtF (lo.map (ev2 M)) j * kG ((pc j).val M).c₀) :=
  hs_bind (hs_g2EqTab hz [o] lo) fun tab htab ↦ hs_mono (hs_g2Dot z _) fun s hs ↦ by
    have hz' : (z.re.val M).c₀ = 0 := congrArg FE2.re hz
    have htab' : tab.map (C2.val M) = eqKernelF (lo.map (C2.val M)) := by
      rw [htab]; simp only [List.map_cons, List.map_nil, ho]; rfl
    rw [ev2, hs, hz, zero_add, List.map_map, lsum_range]
    change toE2Hom _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j < 2 ^ (lo.map (C2.val M)).length := by simpa [hlo] using Finset.mem_range.mp hj
    simp only [Function.comp_apply, map_mul]
    rw [getD_map_val, htab', hz, eqKernelF_getD, if_pos hj']
    simp only [toE2Hom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toE2_eqAtF, List.map_map]
    congr 1
    simp only [kG, kC2, C2.val, hz']; rfl

/-- **The wiring gadget.** -/
def wire6 (Ti : TInst6) (pubC : ℕ → Cell) (v : List C2) (a : ℕ) (gate : Cell) : BM WireOutC :=
  g2Zero (ld2 a) >>= fun z ↦ g2Const 1 (ld2 a) >>= fun o ↦
  g2Mul (ld2 (a + 1)) (ld2 (a + 1)) z >>= fun γ2 ↦
  g2Mul (ld2 (a + 1)) (v.getD 1 z) (v.getD 0 z) >>= fun t1 ↦ g2Mul γ2 (v.getD 2 z) t1 >>= fun st ↦
  sc2 yVars (a + 10) st >>= fun rf ↦
  let vs := (List.range 4).map fun i ↦ ld2 (a + 304 + 2 * i)
  let rv := (List.range 4).map fun i ↦ ld2 (a + 312 + 2 * i)
  g2Add (vs.getD 2 z) (vs.getD 3 z) >>= fun sDW ↦ g2Mul (ld2 (a + 1)) (vs.getD 1 z) (vs.getD 0 z) >>= fun t2 ↦
  g2Mul γ2 sDW t2 >>= fun wg ↦ g2Sum z rv >>= fun srv ↦
  g2Sel z o (rf.1.drop 10) (pubBase Ti / 2 ^ 10) >>= fun sel ↦
  pubDot6 z o (rf.1.take 10) (fun j ↦ pubC (pubBase Ti + j)) >>= fun pd ↦ g2Mul sel pd z >>= fun pv ↦
  onesSum6 z o rf.1 (onesOf Ti) >>= fun ones ↦ g2Add pv ones >>= fun virt ↦ g2Add srv virt >>= fun zt ↦
  g2Mul wg zt z >>= fun m ↦ g2Add rf.2 m >>= fun d ↦ g2Assert d gate >>= fun _ ↦ pure ⟨rf.1, vs, rv⟩

/-- **CD-2**: `wire6` re-executes the wiring. -/
theorem wire6_har : WireHarStmt wire6 := by
  intro Ti hok hlay pubC v hv a gate c M hg
  obtain ⟨A, B, C, rfl⟩ : ∃ A B C, v = [A, B, C] := by
    match v, hv with
    | [A, B, C], _ => exact ⟨A, B, C, rfl⟩
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Const 1 _)) fun o ho ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun γ2 hγ2 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t1 ht1 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun st hst ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_and (sc2_runs (c := c) gWire (by norm_num) yVars (a + 10) st)
    (hs_sc2 yVars (a + 10) st))) fun rf hrf2 ↦ ?_
  obtain ⟨hrf, hlen, -⟩ := hrf2
  have hrl : rf.1.length = yVars := by rw [hlen]; simp [sc2Ans]
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun sDW hsDW ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t2 ht2 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun wg hwg ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sum _ _)) fun srv hsrv ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sel hz ho _ _)) fun sel hsel ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_pubDot6 hz ho _ (by simp [hrl, yVars]) _)) fun pd hpd ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun pv hpv ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_onesSum6 hz ho _ _)) fun ones hones ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun virt hvirt ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun zt hzt ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun m hm ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun d hd ↦ ?_
  refine hsA_bind (hsA_g2Assert d gate hg) fun _ h0 ↦ hsA_pure ?_
  show Runs M (layItems wireItems a) _ _
  set γ := ev2 M (ld2 (a + 1))
  have hst' : ev2 M st = wBatchE γ ([A, B, C].map (ev2 M)) := by
    rw [ev2_mul hst, ev2_mul ht1, ev2_mul hγ2, ev2_of_zero hz]
    simp only [wBatchE, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    ring
  have hvirt' : ev2 M virt = virtE Ti (fun y ↦ ((pubC y).val M).c₀) (rf.1.map (ev2 M)) := by
    rw [virt_eq hok hlay _ _ (by simp [hrl]), ev2_add hvirt, ev2_mul hpv, ev2_of_zero hz, add_zero, hsel,
      hpd, hones, ← List.map_drop, ← List.map_take]
  have hfin : ev2 M rf.2 = wGE γ (((List.range 4).map fun i ↦ ld2 (a + 304 + 2 * i)).map (ev2 M)) *
      (sumF (((List.range 4).map fun i ↦ ld2 (a + 312 + 2 * i)).map (ev2 M)) +
        virtE Ti (fun y ↦ ((pubC y).val M).c₀) (rf.1.map (ev2 M))) := by
    rw [ev2_eq_of_add (hd.symm.trans h0), ev2_mul hm, ev2_of_zero hz, add_zero, ev2_add hzt, hvirt',
      ev2_mul hwg, ev2_mul ht2, ev2_add hsDW, ev2_mul hγ2, ev2_of_zero hz]
    congr 1
    · rw [show List.range 4 = [0, 1, 2, 3] from rfl]
      simp only [wGE, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
      ring
    · congr 1
      simp only [ev2, hsrv, hz, zero_add, sumF, toE2_sum, List.map_map]
      rw [List.sum_eq_foldl]; rfl
  have hl : layItems wireItems a = layItems [.G gGamma] a ++
      (layItems (rep yVars (rnd 2 gWire)) (a + 10) ++
        ((List.range 4).map (fun i ↦ LEv.e (a + 304 + 2 * i)) ++
          ((List.range 4).map (fun i ↦ LEv.e (a + 312 + 2 * i)) ++ []))) := by
    rw [wireItems, layItems_append, layItems_append, layEnd_append, layEnd_repR2]; rfl
  unfold wireProgE
  refine runs_bind' hl (l₁ := [_, _]) (runs_e2Sample M (by norm_num) a) fun g hg' ↦ ?_
  subst hg'
  rw [← hst']
  refine runs_bind' rfl hrf fun res hres ↦ ?_
  refine runs_bind' rfl (runs_e2Reads M 4 (a + 304)) fun vs hvs ↦ ?_
  refine runs_bind' (l₂ := []) rfl (runs_e2Reads M 4 (a + 312)) fun rv hrv ↦ ?_
  refine runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ⟨hres.1, ?_, ?_⟩
  · rw [hres.1, hres.2, hvs, hrv, hfin]; rfl
  · rw [hvs, scal, List.map_map]; rfl
  · rw [hrv, scal, List.map_map]; rfl

end Lvm6.QD
