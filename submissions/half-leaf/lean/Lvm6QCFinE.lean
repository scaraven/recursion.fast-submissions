-- New for lvm6 (WP CC8). The deployed final level's gadgets for CC-8: the row fold `fvE` by CCV's
-- value gadget with no high part (`valsGen … []`), the final polynomial `fpolyE` at the positions'
-- points (`fpGen`, from CCV's `W_i`/`Ŵ_i`/`X_s` chain), CC-3a's positions, and CC-8 at W1's
-- deployed final level (`finE2`, `fvE`, `chkE`) with only the weight cell left as a hypothesis.
import Lvm6QCFinW
import Lvm6QCVals

/-!
# The deployed final level (CC-8 at `finE2`)

* `highF_nil`, `fvE_eq_valsE`, `fvGen`, **`fvGen_ok`**: `ValsAt` for `fvE` (CCV's `valsEHar` at `hi = []`).
* `fpV`, `eval_fpolyE`: `fpolyE κ ℓ s` at `K(p)` is `Σ_{j<2^κ} s_j X_j(a) + Ŵ_κ(a)·Σ_{j<ℓ} s_{2^κ+j} X_j(a)`.
* `fpPre` (the class prelude: zero, one, constants `W_i(e_i)^{±1}` for `i < fpN`), `fpAt` (one
  instance per position, no constant inside), `fpGen`, **`fpGen_ok : FpAt (finE2 …) (fpGen κ ℓ)`**.
* **`finHarE`**: CC-8 at `finE2 κ ℓ h kq t c` with `posGen B`, `fvGen`, `fpGen`: for any weight
  gadget meeting `WAt Pre w`, `finGen` re-executes `finP … (fvE false h ℓ hh) (chkE gT κ) w σ`.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK

variable {c : Ctx} {M : Mem}

/-! ## The row fold -/

theorem highF_nil (κ ℓ : ℕ) : Whir.highF κ ℓ [] = 0 := by
  simp [Whir.highF]

theorem fvE_eq_valsE (z : Bool) (h ℓ κ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List (Whir.Rnd E2)) :
    Whir.fvE z h ℓ hh (t := t) rs = Whir.valsE z h ℓ κ hh rs [] := by
  funext ps rows k
  simp [Whir.fvE, Whir.valsE, highF_nil]

/-- **The final level's row fold**: CCV's value gadget with no high part. -/
def fvGen (h ℓ κ : ℕ) (rc : List RndC) (ps : List Cell) (rows : List (List (Option ℕ)))
    (gate : Cell) : BM (List C2) :=
  valsGen false h ℓ κ rc [] ps rows gate

theorem fvGen_ok (h ℓ κ : ℕ) (hh : h ≤ 64) {t : ℕ} : ∀ (c : Ctx) (M : Mem) (rc : List RndC)
    (rs : List (Whir.Rnd E2)), RndsRep M rc rs →
      ValsAt (t := t) c M (fun _ ↦ Whir.fvE false h ℓ hh rs) (fun _ ↦ fvGen h ℓ κ rc) := by
  intro c M rc rs hr hi ps rows gate hg
  refine hsA_mono (valsEHar false h ℓ κ hh t c M rc rs hr [] ps rows gate hg) fun cs hcs p hp ↦ ?_
  rw [hcs p hp, fvE_eq_valsE false h ℓ κ hh rs]
  rfl

/-! ## The final polynomial at a point -/

/-- The value of `fpolyE κ ℓ s` at `a`. -/
noncomputable def fpV (κ ℓ : ℕ) (s : List E2) (a : K) : E2 :=
  ((List.range (2 ^ κ)).map fun j ↦ s.getD j 0 * algebraMap K E2 (novelAt j a)).sum +
    algebraMap K E2 (normVanishingAt κ a) *
      ((List.range ℓ).map fun j ↦ s.getD (2 ^ κ + j) 0 * algebraMap K E2 (novelAt j a)).sum

theorem eval_novelF (j : ℕ) (a : K) :
    (Whir.novelF (F := E2) j).eval (algebraMap K E2 a) = algebraMap K E2 (novelAt j a) := by
  show ((novel j).map (algebraMap K E2)).eval _ = _
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, eval_novel]

theorem eval_fpolyE (κ ℓ : ℕ) (s : List E2) (a : K) :
    (Whir.fpolyE κ ℓ s Whir.lane0).eval (algebraMap K E2 a) = fpV κ ℓ s a := by
  have hm : (Whir.msgPolyF κ (fun u ↦ s.getD (bitsToNat u) 0)).eval (algebraMap K E2 a) =
      ((List.range (2 ^ κ)).map fun j ↦ s.getD j 0 * algebraMap K E2 (novelAt j a)).sum := by
    simp only [Whir.msgPolyF, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_finsetSum,
      Polynomial.eval_smul, smul_eq_mul]
    rw [← sum_range_list, ← Fin.sum_univ_eq_sum_range, ← (bitsEquiv κ).sum_comp]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [bitsEquiv_val, eval_novelF]
  have hd : ∀ j, (s.drop (2 ^ κ)).getD j 0 = s.getD (2 ^ κ + j) 0 := fun j ↦ by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  show (Whir.msgPolyF κ (fun u ↦ s.getD (bitsToNat u) 0) + Whir.highF κ ℓ (s.drop (2 ^ κ))).eval
    (algebraMap K E2 a) = _
  rw [Polynomial.eval_add, eval_highF, hm, fpV]
  simp only [hd]

/-! ## The final-polynomial gadget -/

/-- The number of `Ŵ_i`, `X_j` a position needs: `κ + 1`, `ℓ`, `2^κ`. -/
def fpN (κ ℓ : ℕ) : ℕ := max (max (κ + 1) ℓ) (2 ^ κ)

/-- **The class prelude**: a zero and a one (from the gate's cell), the constants `W_i(e_i)^{±1}`. -/
def fpPre (κ ℓ : ℕ) (gate : Cell) : BM (C2 × C2 × (List C2 × List C2)) :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦ wConsts z (fpN κ ℓ) >>= fun k ↦
    pure (z, one, k)

theorem hs_fpPre (κ ℓ : ℕ) (gate : Cell) :
    Hs c M (fpPre κ ℓ gate) fun e ↦ ev2 M e.1 = 0 ∧ ev2 M e.2.1 = 1 ∧
      ConstsOK M e.1 (fpN κ ℓ) e.2.2 :=
  hs_bind (hs_g2Zero _) fun z hz0 ↦ hs_bind (hs_g2Const 1 z) fun _ hone ↦
    hs_bind (hs_wConsts (ev2_zero hz0) _) fun _ hk ↦ hs_pure ⟨ev2_zero hz0, ev2_one' hone, hk⟩

/-- **The final polynomial at one position**, one instance (`pc` a `K` cell holding `a = K(p)`,
`sc` the scalars' cells): `Ŵ_κ(a)·Σ_{j<ℓ} s_{2^κ+j} X_j(a) + Σ_{j<2^κ} s_j X_j(a)`. -/
def fpAt (z one : C2) (k : List C2 × List C2) (ℓ κ : ℕ) (sc : List C2) (pc : Cell) : BM C2 :=
  vChain z k.1 (fpN κ ℓ - 1) 0 ⟨pc, z.re⟩ >>= fun ws ↦
  mapB (fun i ↦ nStep z (k.2.getD i z) (ws.getD i z)) (List.range (fpN κ ℓ)) >>= fun nws ↦
  mapB (novG z one nws) (List.range (fpN κ ℓ)) >>= fun novs ↦
  g2Dot z ((List.range ℓ).map fun j ↦ (sc.getD (2 ^ κ + j) z, novs.getD j z)) >>= fun d ↦
  g2Mul (nws.getD κ z) d z >>= fun hv ↦
  g2Dot hv ((List.range (2 ^ κ)).map fun j ↦ (sc.getD j z, novs.getD j z))

theorem hs_fpAt {z one : C2} (hz : ev2 M z = 0) (hone : ev2 M one = 1) (k : List C2 × List C2)
    (ℓ κ : ℕ) (hk : ConstsOK M z (fpN κ ℓ) k) (sc : List C2) (pc : Cell) :
    Hs c M (fpAt z one k ℓ κ sc pc) fun o ↦ ev2 M o = fpV κ ℓ (sc.map (ev2 M)) (kv M pc) := by
  have hzk := kv_re_zero hz
  have hx0 : ev2 M ⟨pc, z.re⟩ = algebraMap K E2 (vanishingAt 0 (kv M pc)) := by
    rw [ev2_mk, hzk, vanishingAt_zero_idx]
    rfl
  have hN : κ + 1 ≤ fpN κ ℓ ∧ ℓ ≤ fpN κ ℓ ∧ 2 ^ κ ≤ fpN κ ℓ := by
    unfold fpN
    omega
  have hn1 : 0 + (fpN κ ℓ - 1) ≤ fpN κ ℓ := by omega
  refine hs_bind (hs_vChain hz k.1 _ (fun i hi ↦ (hk i hi).1) (kv M pc) _ 0 _ hn1 hx0) fun ws hws ↦
    hs_bind (hs2_mapB _ (fun i ↦ algebraMap K E2 (normVanishingAt i (kv M pc))) _ fun i hi ↦
      hs_nStep hz i _ _ _ (hk i (List.mem_range.mp hi)).2 (by
        have := List.mem_range.mp hi
        rw [hws i (by omega), zero_add])) fun nws hnws ↦ ?_
  have hn : ∀ i < fpN κ ℓ, ev2 M (nws.getD i z) =
      algebraMap K E2 (normVanishingAt i (kv M pc)) := fun i hi ↦ by
    rw [ev2_getDz hnws hz, getD_range_map _ _ hi]
  refine hs_bind (hs2_mapB _ (fun s ↦ algebraMap K E2 (novelAt s (kv M pc))) _ fun s hs ↦
    hs_novG hz hone _ nws hn s (List.mem_range.mp hs)) fun novs hnovs ↦
    hs_bind (hs2_dot z _) fun d hd ↦ hs_bind (hs2_mul _ d z) fun hv hhv ↦
    hs_mono (hs2_dot hv _) fun o ho ↦ ?_
  have hnv : ∀ j < fpN κ ℓ, ev2 M (novs.getD j z) = algebraMap K E2 (novelAt j (kv M pc)) :=
    fun j hj ↦ by rw [ev2_getDz hnovs hz, getD_range_map _ _ hj]
  have hsc : ∀ j, ev2 M (sc.getD j z) = (sc.map (ev2 M)).getD j 0 := ev2_getDz (l := sc) rfl hz
  have e1 : (((List.range ℓ).map fun j ↦ (sc.getD (2 ^ κ + j) z, novs.getD j z)).map
      fun e ↦ ev2 M e.1 * ev2 M e.2) = (List.range ℓ).map fun j ↦
        (sc.map (ev2 M)).getD (2 ^ κ + j) 0 * algebraMap K E2 (novelAt j (kv M pc)) := by
    rw [List.map_map]
    refine List.map_congr_left fun j hj ↦ ?_
    simp only [Function.comp_apply]
    rw [hsc, hnv j (by have := List.mem_range.mp hj; omega)]
  have e2 : (((List.range (2 ^ κ)).map fun j ↦ (sc.getD j z, novs.getD j z)).map
      fun e ↦ ev2 M e.1 * ev2 M e.2) = (List.range (2 ^ κ)).map fun j ↦
        (sc.map (ev2 M)).getD j 0 * algebraMap K E2 (novelAt j (kv M pc)) := by
    rw [List.map_map]
    refine List.map_congr_left fun j hj ↦ ?_
    simp only [Function.comp_apply]
    rw [hsc, hnv j (by have := List.mem_range.mp hj; omega)]
  rw [ho, hhv, hd, e1, e2, hz, zero_add, add_zero, hn κ (by omega), fpV]
  ring

/-- **The deployed final-polynomial gadget**: the prelude, then one `fpAt` instance per position. -/
def fpGen (κ ℓ : ℕ) (sc : List C2) (ps : List Cell) (gate : Cell) : BM (List C2) :=
  fpPre κ ℓ gate >>= fun e ↦
    mapB (fun k ↦ fpAt e.1 e.2.1 e.2.2 ℓ κ sc (ps.getD k gate)) (List.range ps.length)

/-- **`FpAt` for the deployed final level.** -/
theorem fpGen_ok (κ ℓ h kq t cc : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64)
    (hc : 0 < cc) (hch : cc * h ≤ 128) (ht : t ≤ (kq + 1) * cc) :
    FpAt (Whir.finE2 κ ℓ h kq t cc hκ hℓ hℓ' hh hc hch ht) (fpGen κ ℓ) := by
  intro c M sc ps gate _
  refine hsA_of_hs (hs_bind (hs_fpPre κ ℓ gate) fun e he ↦ ?_)
  obtain ⟨hz, hone, hk⟩ := he
  refine hs_mono (hs2_mapB _ (fun k ↦ fpV κ ℓ (sc.map (ev2 M)) (kv M (ps.getD k gate))) _
    fun k _ ↦ hs_fpAt hz hone e.2.2 ℓ κ hk sc _) fun fs hfs p hp ↦ ?_
  have hlen : ps.length = (Whir.finE2 κ ℓ h kq t cc hκ hℓ hℓ' hh hc hch ht).t := by
    simpa [posOf] using congrArg List.length hp
  rw [hfs]
  apply List.ext_getElem
  · simp [hlen]
  intro k h1 _
  have hk : k < (Whir.finE2 κ ℓ h kq t cc hκ hℓ hℓ' hh hc hch ht).t := by simpa [hlen] using h1
  have hpk : kToNat (kv M ps[k]) = (p ⟨k, hk⟩ : ℕ) := by
    have e := congrArg (fun l ↦ l[k]?) hp
    simp only [posOf, List.getElem?_map, List.getElem?_eq_getElem (by omega : k < ps.length),
      List.getElem?_ofFn, Option.map_some] at e
    simp only [hk, ↓reduceDIte] at e
    exact Option.some.inj e
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by omega : k < ps.length)]
  show fpV κ ℓ _ (kv M ps[k]) =
    (Whir.fpolyE κ ℓ (sc.map (ev2 M)) Whir.lane0).eval (Whir.domE h hh (p ⟨k, hk⟩))
  rw [domE_apply, ← hpk, ofBits_kToNat, eval_fpolyE]

/-! ## The `Ŵ` gadget of the glue's query terms -/

/-- **`Ŵ_i(K(x))`, `i < n`**, at a position cell `x` (one instance per position): a zero from the
gate's cell, the class constants `W_i(e_i)^{±1}`, CCV's chain `W_i(a)` and `Ŵ_i(a)`. -/
def whGen (n : ℕ) (x gate : Cell) : BM (List C2) :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ wConsts z n >>= fun k ↦
    vChain z k.1 (n - 1) 0 ⟨x, z.re⟩ >>= fun ws ↦
      mapB (fun i ↦ nStep z (k.2.getD i z) (ws.getD i z)) (List.range n)

/-- **`WhAt` for the deployed `Ŵ` gadget.** -/
theorem whGen_ok (n : ℕ) : WhAt n (whGen n) := by
  intro c M x gate _
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz0 ↦ hs_bind (hs_wConsts (ev2_zero hz0) n)
    fun k hk ↦ ?_)
  have hz := ev2_zero (M := M) hz0
  have hx0 : ev2 M ⟨x, z.re⟩ = algebraMap K E2 (vanishingAt 0 (kv M x)) := by
    rw [ev2_mk, kv_re_zero hz, vanishingAt_zero_idx]
    rfl
  refine hs_bind (hs_vChain hz k.1 n (fun i hi ↦ (hk i hi).1) (kv M x) (n - 1) 0 _ (by omega) hx0)
    fun ws hws ↦ hs_mono (hs2_mapB _ (fun i ↦ algebraMap K E2 (normVanishingAt i (kv M x))) _
      fun i hi ↦ hs_nStep hz i _ _ _ (hk i (List.mem_range.mp hi)).2 (by
        have := List.mem_range.mp hi
        rw [hws i (by omega), zero_add])) fun r hr ↦ ?_
  rw [hr, ofBits_kToNat]

/-- **CC-8g at the deployed `Ŵ` gadget.** -/
theorem glueHarE (κ' ℓ' ko t h ℓ : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (w : Whir.WtE.Wt (0 + ℓ))
    (Pre : Mem → Prop) (wGp : List RndC → List C2 → Cell → BM C2) (hwok : Whir.wokE (ko + 1) ℓ w)
    (hwp : WAt Pre w wGp) (rcP : List RndC) (rs : List (Whir.Rnd E2)) (oc : TailOutC)
    (o : Whir.TailOut E2 ko t (2 ^ h)) (hl : rs.length = ℓ) :
    WAt (ℓ := ℓ') (fun M ↦ Pre M ∧ RndsRep M rcP rs ∧ TailRep M oc o)
      (Whir.wGlueE κ' ℓ' ko t h (Whir.wFolds Whir.WtE ℓ rs w) o)
      (glueG wGp (whGen (ko + 1)) rcP oc) :=
  glueHar κ' ℓ' ko t h ℓ hκ w Pre wGp _ hwok hwp (whGen_ok (ko + 1)) rcP rs oc o hl

/-! ## CC-8 at the deployed final level -/

/-- **CC-8 at `finE2`**: with CC-3a's position gadget, the row fold `fvGen` and `fpGen`, for any
weight gadget meeting `WAt Pre w` (the glue chain `glueG` over the levels, `Lvm6QCFinW`) with `w.1 = κ`, the final
level's generator re-executes `finP WtE chalE2 (finE2 …) g gq i ℓ (fvE false h ℓ hh) (chkE gT κ) w σ`
and on memories with `Pre` where `σc` holds `σ` the program returns `true`. -/
theorem finHarE (B κ ℓ h kq t cc : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64)
    (hc : 0 < cc) (hch : cc * h ≤ 128) (ht : t ≤ (kq + 1) * cc)
    (w : Whir.WtE.Wt (0 + ℓ)) (Pre : Mem → Prop) (wG : List RndC → List C2 → Cell → BM C2)
    (hw : WAt Pre w wG) (hwκ : w.1 = κ) (g gq gT i : ℕ) (hg : g ≤ 64) (hgq : gq ≤ 64) (hgT : gT ≤ 64)
    (lev : Level) (wdI a : ℕ) (σ : E2) (σc : C2) (gate : Cell) :
    HarO gate (finGen (2 ^ κ + ℓ) t (posGen B h cc kq t) (fun rc ↦ fvGen h ℓ κ rc) (fpGen κ ℓ) wG
        g gT κ ℓ lev wdI a σc gate)
      (Whir.finP Whir.WtE Whir.chalE2 (Whir.finE2 κ ℓ h kq t cc hκ hℓ hℓ' hh hc hch ht) g gq i ℓ
        (Whir.fvE false h ℓ hh) (Whir.chkE gT κ) w σ)
      (layFin (2 ^ κ + ℓ) kq t κ lev wdI g gq gT ℓ a)
      fun M _ out ↦ Pre M → ev2 M σc = σ → out = true :=
  finHar (Whir.finE2 κ ℓ h kq t cc hκ hℓ hℓ' hh hc hch ht) (Whir.fvE false h ℓ hh)
    (posGen B h cc kq t) (fun rc ↦ fvGen h ℓ κ rc) (fpGen κ ℓ) ℓ w Pre wG
    (posE2Har B h cc kq t hc ht hch hh) (fvGen_ok h ℓ κ hh) (fpGen_ok κ ℓ h kq t cc hκ hℓ hℓ' hh hc hch ht)
    hw g gq gT i κ hg hgq hgT hwκ lev wdI a σ σc gate

end Lvm6.QC
