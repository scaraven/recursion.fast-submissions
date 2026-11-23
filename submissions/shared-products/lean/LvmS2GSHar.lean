-- New for lvm2 σ_LEAF (SLF-C2, 2026-11-16): Q_arith at S2GS (`harithS20H`, SLF-STMT 7e's text at RE-FREEZE R2): the
-- kernels over a list of key-leaf starts (`hs_kernS`), the S2GS wire gadget (`wireGS_sound`), the front's phases over
-- the config (`front_phasesS`, `front_phasesUG`'s twin for `frontS`), `P20S`'s positions, front facts and plan facts,
-- V_S's S2GS decision from its phases, the pair lemmas and `harithL20`'s proof at `cfgS20`.
import LvmE2QAsmS
import LvmS2GLHar
import LvmS2GSPlan
import LvmS2GSFront
import LvmE2QInstS
import LvmS2GSHarT
import LvmS2GSGuardC

/-!
# Q_arith at S2GS (`harithS20H`) and its front

* **`hs_kernS`**: `hs_kernU` for `kernS` (the `cont` intervals `[1, B − 1]` and `[K + 1, K + 31]`, `K ∈ Ks`).
* **`wireGS_sound`**: `wireGU_sound` for `wireGS`.
* **`front_phasesS`**: `front_phasesUG` for `frontS` (the wire's `cont` intervals `(1, B − 1) :: ksKs p`'s).
* **`posS20`**, **`frontPF_P20S`**, **`ivsS20`**: `P20S`'s positions (one kernel walk of its own literals), front facts
  and `cont` intervals (`contIvS aSP`); **`passR_P20S`**, **`streamOk_P20S`**, **`hQS20`**: its plan and Q_link facts.
* **`core_of_phasesS`**, **`decideFSG_of`**: `decideFSG` accepts from its phases (`core_of_phasesL`, `decideFLG_of`).
* Pair lemmas at S2GS (`sigS_size`, `streamedS`, `hWS`, `rowWordsS`, `powOkS`, `childOkS` from `qsigNoSl_sound`,
  `posCellsS`, `vk_cellsS`, `phiS20_acc` at `accCS`), **`harithS20H`** (`harithL20`'s proof with `frontS`, `typedGS`,
  `pubOfWS` and `contIvS aSP`; Q_arith's pointer `p2S20H`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.E2V

variable {c : Ctx} {M : Mem}

/-! ## The kernels (`kernS`) -/

set_option maxHeartbeats 1000000 in
/-- **The kernels' values** (`kernS`): `hs_kernU`'s, with `K̃_ks(σ') = kksF` on `cont`'s intervals `[1, B − 1]` and
`[K + 1, K + 31]` for every `K ∈ Ks` at base `2^20`. -/
theorem hs_kernS {z one : C2} (hz : z.val M = 0) (ho : one.val M = 1) (rho mu σ mb lt : List C2) (t : ℕ)
    (hρ : rho.length = 16) (hμ : mu.length = 32) (hσ : σ.length = 20) (hmb : mb.map (C2.val M) = bitsF t 20)
    (ht : t < 2 ^ 20)
    (hlt : lt.map (C2.val M) = (List.range 33).map fun k => ((eqKernelF ((mb.take 5).map (C2.val M))).take k).sum)
    (B : ℕ) (Ks : List ℕ) (hB : B - 1 < 2 ^ 13) (hKs : ∀ K ∈ Ks, K + 31 < 2 ^ 13) :
    Hs c M (kernS z one rho mu σ mb lt B Ks) (fun k =>
      k.kch.val M = E2V.msEvalF (rho.map (C2.val M)) (mu.map (C2.val M)) (σ.map (C2.val M)) 0 t ∧
      k.kks.val M = Lvm.E2U.kksF ((1, B - 1) :: Ks.map fun K => (K + 1, K + 31)) (rho.map (C2.val M))
        (mu.map (C2.val M)) ((σ.map (C2.val M)).take 13) (2 ^ 20) ∧
      k.iks.val M = E2V.ikEvalP (rho.map (C2.val M)) (mu.map (C2.val M)) ((σ.map (C2.val M)).take 13) (2 ^ 20) ∧
      k.e'.val M = Lvm.E2U.eTailF 13 20 (σ.map (C2.val M))) := by
  unfold kernS
  rw [g2Ms_take]
  refine hs_bind (hs_g2Ms hz ho (rho.take (σ.length - 5)) mu σ mb lt t (by omega) (by simp [hρ, hσ]) hμ
    (by rw [hmb, hσ]) (by rw [hσ]; exact ht) hlt) fun ms hms => ?_
  refine hs_bind (hs_g2One _) fun r16 hr16 => hs_bind (hs_g2Mul _ _ _) fun kch hkch => ?_
  refine hs_bind (hs_g2Eq0 hz _ _) fun cTop hcTop => hs_bind (hs_g2EqTab hz [one] (σ.take 5)) fun e4 he4 => ?_
  refine hs_bind (hs_mapB_getDU _ (fun d v => v.val M = (e4.getD d default).val M *
      (mu.getD ((d + 1) % 32) default).val M) (fun d => hs_mono (hs_g2Mul _ _ _) fun v hv => by rw [hv, hz, add_zero])
      _) fun A ⟨hAl, hA⟩ => ?_
  refine hs_bind (hs_mapB_getDU _ (fun k q => q.1.val M = 1 + ((σ.getD (5 + k) default).val M +
      (rho.getD k default).val M + (σ.getD (5 + k) default).val M * (rho.getD k default).val M) ∧
      q.2.1.val M = (σ.getD (5 + k) default).val M * (rho.getD k default).val M ∧
      q.2.2.1.val M = (rho.getD k default).val M + (σ.getD (5 + k) default).val M * (rho.getD k default).val M ∧
      q.2.2.2.val M = (σ.getD (5 + k) default).val M + (σ.getD (5 + k) default).val M * (rho.getD k default).val M)
      (fun k => hs_msCoef hz _ _) _) fun cs ⟨hcsl, hcs⟩ => ?_
  rw [List.length_range] at hcsl
  -- the automaton's points: `σ'_{5…12}`, `ρ_{<8}`
  set as := ((σ.map (C2.val M)).take 13).drop 5 with has
  set rs := (rho.map (C2.val M)).take 8 with hrs
  have hasl : as.length = 8 := by simp [has, hσ]
  have hrsl : rs.length = 8 := by simp [hrs, hρ]
  have hc : ∀ i (hi : i < cs.length), (cs[i]).1.val M = 1 + (as.getD i 0 + rs.getD i 0 + as.getD i 0 * rs.getD i 0) ∧
      (cs[i]).2.1.val M = as.getD i 0 * rs.getD i 0 ∧
      (cs[i]).2.2.1.val M = rs.getD i 0 + as.getD i 0 * rs.getD i 0 ∧
      (cs[i]).2.2.2.val M = as.getD i 0 + as.getD i 0 * rs.getD i 0 := by
    intro i hi
    have h := hcs i (by simp; omega)
    simp only [List.getElem_range] at h
    have ea : as.getD i 0 = (σ.getD (5 + i) default).val M := by
      rw [getD_map_val σ (by omega), has, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        List.getElem?_take]
      rw [if_pos (by omega)]
    have er : rs.getD i 0 = (rho.getD i default).val M := by
      rw [getD_map_val rho (by omega), hrs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
        if_pos (by omega)]
    rw [ea, er, ← List.getD_eq_getElem cs default hi]
    exact h
  have hcB : ∀ u, u < 2 ^ 13 → u / 32 < 2 ^ cs.length := fun u hu => by rw [hcsl]; omega
  -- the shared values: `eq(σ_{<5}, ·)`, the `A_d`, the top factor
  have hσ' : ((σ.map (C2.val M)).take 13).length = 13 := by simp [hσ]
  have he4' : ∀ d < 32, (e4.getD d default).val M = E2V.eqAtF (((σ.map (C2.val M)).take 13).take 5) d := by
    intro d hd
    have e : e4.map (C2.val M) = eqKernelF ((σ.take 5).map (C2.val M)) := by
      rw [he4, List.map_cons, List.map_nil, ho]; rfl
    have he4l : e4.length = 32 := by
      have := congrArg List.length e
      simp only [List.length_map, eqKernelF_length, List.length_take, hσ] at this
      simpa using this
    rw [getD_map_val e4 (by omega), e, eqKernelF_getD, if_pos (by simp [hσ]; omega), List.take_take, List.map_take]
    rfl
  have hAv : ∀ d < 32, (A.getD d default).val M =
      E2V.eqAtF (((σ.map (C2.val M)).take 13).take 5) d * (mu.map (C2.val M)).getD ((d + 1) % 32) 0 := by
    intro d hd
    have h := hA d (by simpa using hd)
    simp only [List.getElem_range] at h
    rw [h, he4' d hd, getD_map_val mu (by rw [hμ]; omega)]
  have hcT : cTop.val M = E2V.eqAtF ((rho.map (C2.val M)).drop 8) (2 ^ 20 / 2 ^ 13) := by
    rw [hcTop, cTop_eq _ (by simp [hρ]), getD_map_val rho (by omega), List.map_take, List.map_drop]
  have hlo : ∀ u, u < 32 → ((List.range u).map fun d => (A.getD d default).val M).sum =
      ((List.range u).map fun d => E2V.eqAtF (((σ.map (C2.val M)).take 13).take 5) d *
        (mu.map (C2.val M)).getD ((d + 1) % 32) 0).sum := fun u hu =>
    congrArg _ (List.map_congr_left fun d hd => hAv d (by have := List.mem_range.mp hd; omega))
  have hhi : ∀ u, (((List.range 31).drop u).map fun d => (A.getD d default).val M).sum =
      (((List.range 31).drop u).map fun d => E2V.eqAtF (((σ.map (C2.val M)).take 13).take 5) d *
        (mu.map (C2.val M)).getD ((d + 1) % 32) 0).sum := fun u =>
    congrArg _ (List.map_congr_left fun d hd => hAv d (by
      have := List.mem_range.mp (List.mem_of_mem_drop hd); omega))
  -- one `MS` bound `u < 2^13`: `msConstU`'s value times the top factor is V's `msEvalF` at `u` (`E u`)
  obtain ⟨E, hEu⟩ : ∃ E : ℕ → FE2, ∀ u, E u =
      E2V.msEvalF (rho.map (C2.val M)) (mu.map (C2.val M)) ((σ.map (C2.val M)).take 13) (2 ^ 20) u := ⟨_, fun _ => rfl⟩
  have key : ∀ u, u < 2 ^ 13 → Hs c M (msConstU z one cs A u) (fun m => m.val M * cTop.val M = E u) :=
    fun u hu => hs_mono (hs_msConstU hz ho cs as rs A u (by omega) (by omega) hc (hcB _ hu)) fun m hm => by
      rw [hEu, hm, msEvalF_low _ _ _ hσ', hcT, hlo _ (Nat.mod_lt _ (by norm_num)), hhi, hAv 31 (by norm_num)]
      ring
  have hE0 : E 0 = 0 := by
    rw [hEu, msEvalF_low _ _ _ hσ', Nat.zero_div, Nat.zero_mod, (msTailF_zero _ _).1, (msTailF_zero _ _).2]
    simp
  -- the key-leaf intervals: `MS(K + 31) + MS(K)` for every `K`
  have hmap : ∀ Ks' : List ℕ, (∀ K ∈ Ks', K + 31 < 2 ^ 13) →
      Hs c M (mapB (fun K => msConstU z one cs A (K + 31) >>= fun a => msConstU z one cs A K >>= fun b =>
        pure [a, b]) Ks') (fun ms2 => (ms2.flatten.map (C2.val M)).sum * cTop.val M =
          ((Ks'.map fun K => (K + 1, K + 31)).map fun ab => E ab.2 - E (ab.1 - 1)).sum) := by
    intro Ks' hKs'
    induction Ks' with
    | nil => exact hs_pure (by simp)
    | cons K Ks' ih =>
      have hK := hKs' K List.mem_cons_self
      refine hs_bind (hs_bind (key (K + 31) hK) fun a ha => hs_bind (key K (by omega)) fun b hb =>
        hs_pure (P := fun r : List C2 => (r.map (C2.val M)).sum * cTop.val M = E (K + 31) + E K) ?_) fun r hr => ?_
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [add_mul, ha, hb]
      refine hs_bind (ih fun K' hK' => hKs' K' (List.mem_cons_of_mem _ hK')) fun rs hrs => hs_pure ?_
      rw [List.flatten_cons, List.map_append, List.sum_append, add_mul, hr, hrs]
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.add_sub_cancel, CharTwo.sub_eq_add]
  refine hs_bind (key (B - 1) hB) fun m1 hm1 => hs_bind (hmap Ks hKs) fun ms2 hms2 => ?_
  refine hs_bind (hs_g2Sum _ _) fun ms3 hms3 => hs_bind (hs_g2Mul _ _ _) fun kks hkks => ?_
  refine hs_bind (hs_g2Dot z _) fun dg hdg => ?_
  refine hs_bind (hs_mapB_getDU _ (fun k v => v.val M = 1 + ((rho.getD k default).val M +
      (σ.getD (5 + k) default).val M)) (fun k => hs_bind (hs_g2Add _ _) fun s hs =>
        hs_mono (hs_g2One _) fun v hv => by rw [hv, hs]) _) fun fs ⟨hfsl, hfs⟩ => ?_
  refine hs_bind (hs_g2Prod hz dg fs) fun ik0 hik0 => hs_bind (hs_g2Mul _ _ _) fun iks hiks => ?_
  refine hs_bind (hs_g2Eq0 hz one _) fun e' he' => hs_pure ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hkch, hms, hr16, hz, add_zero, msEvalF_top (rho.map (C2.val M)) (mu.map (C2.val M)) (σ.map (C2.val M))
      (by simp [hρ]) (by simp [hσ]),
      show σ.length - 5 = 15 by omega, List.map_take, getD_map_val rho (by omega)]
    ring
  · unfold Lvm.E2U.kksF
    rw [sumF_eq_sum, List.map_cons, List.sum_cons, hkks, hms3, hz, add_zero, add_mul, hm1, hms2]
    simp only [← hEu]
    rw [show 1 - 1 = 0 from rfl, hE0, sub_zero]
  · rw [hiks, hik0, hdg, hz, zero_add, add_zero, hcT]
    unfold E2V.ikEvalP
    rw [hσ', sumF_eq_sum, eqEvalF_prod _ _ (by simp [hρ, hσ])]
    congr 2
    · rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
      have := List.mem_range.mp hd
      simp only [Function.comp_apply]
      rw [he4' d this, getD_map_val mu (by omega)]
    · have hfv : fs.map (C2.val M) = (List.range 8).map fun k =>
          1 + ((rho.map (C2.val M)).getD k 0 + (σ.map (C2.val M)).getD (5 + k) 0) := by
        apply List.ext_getElem (by simp [hfsl])
        intro i h1 h2
        have hi9 : i < 8 := by simpa [hfsl] using h1
        have h := hfs i (by simpa [hfsl] using h1)
        simp only [List.getElem_range] at h
        simp only [List.getElem_map, List.getElem_range]
        rw [← getD_map_val rho (by omega), ← getD_map_val σ (by omega), ← h,
          ← List.getD_eq_getElem fs default (by simpa [hfsl] using h1)]
      rw [hfv, List.length_take, List.length_map, hρ, show min (13 - 5) 16 = 8 from rfl]
      refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
      have := List.mem_range.mp hk
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, show 13 - 5 = 8 from rfl,
        if_pos this, if_pos (show 5 + k < 13 by omega)]
      ring
  · rw [he', ho, one_mul, eqAtF_zero2]
    unfold Lvm.E2U.eTailF
    rw [prodF_eq, List.take_of_length_le (by simp [hσ] : (σ.map (C2.val M)).length ≤ 20), List.map_take,
      List.map_drop, List.take_of_length_le (by simp [hσ])]
    exact congrArg List.prod (List.map_congr_left fun x _ => by rw [CharTwo.sub_eq_add])

/-! ## The wire gadget at S2GS (`wireGS`) -/

set_option maxHeartbeats 2000000 in
/-- **The S2GS wire gadget is sound** (`wireGU_sound`'s twin; gate on; `P = 15`, `w = 20`): its points are the
stream's challenges; the wire sumcheck from `targetF` ends at `K̃_ch·g_D + e'·(K̃_ks·g_Y + Ĩ_ks·g_M)` (V's final
check); the slot sumchecks of `D`, `Y`, `M` end at their slot weights against the slices. `mb`'s cells hold `t`'s
bits (`t < 2^20`); `K̃_ks` is on `[1, B − 1]` and `[K + 1, K + 31]`, `K ∈ Ks`. -/
theorem wireGS_sound (qw : ℕ) (cv : ℕ → C2) (mb sb : List Cell) (B : ℕ) (Ks : List ℕ) (zk gate : Cell) (t : ℕ)
    (hzk : zk.val M = 0) (hg : gate.val M = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => kC2 b zk).map (C2.val M) = bitsF t 20) (ht : t < 2 ^ 20)
    (hB : B - 1 < 2 ^ 13) (hKs : ∀ K ∈ Ks, K + 31 < 2 ^ 13) :
    HsA c M (wireGS 15 20 qw cv mb sb B Ks zk gate) (fun o =>
      o.sigma = (sc2Ans 20 qw).map ld2 ∧ o.tauD = (sc2Ans 2 (wireLanesU 20 qw).slotD).map ld2 ∧
      o.tauY = (sc2Ans 5 (wireLanesU 20 qw).slotY).map ld2 ∧ o.tauM = (sc2Ans 5 (wireLanesU 20 qw).slotM).map ld2 ∧
      scFold2 (fun k => (ld2 k).val M) 20 qw (targetF M 15 cv ((sb.map fun b => kC2 b zk).map (C2.val M)) t) =
        E2V.msEvalF (cvRho M 15 cv) (cvMu M cv) (o.sigma.map (C2.val M)) 0 t * (ld2 (wireLanesU 20 qw).g3).val M +
        Lvm.E2U.eTailF 13 20 (o.sigma.map (C2.val M)) *
          (Lvm.E2U.kksF ((1, B - 1) :: Ks.map fun K => (K + 1, K + 31)) (cvRho M 15 cv) (cvMu M cv)
              ((o.sigma.map (C2.val M)).take 13) (2 ^ 20) * (ld2 ((wireLanesU 20 qw).g3 + 2)).val M +
            E2V.ikEvalP (cvRho M 15 cv) (cvMu M cv) ((o.sigma.map (C2.val M)).take 13) (2 ^ 20) *
              (ld2 ((wireLanesU 20 qw).g3 + 4)).val M) ∧
      scFold2 (fun k => (ld2 k).val M) 2 (wireLanesU 20 qw).slotD ((ld2 (wireLanesU 20 qw).g3).val M) =
        ((List.range 64).map fun zz => ((List.range 4).map fun ob =>
          (eqKernelF (o.tauD.map (C2.val M))).getD ob 0 * omegaF M 15 cv (8 + 64 * ob + zz)).sum *
            (ld2 ((wireLanesU 20 qw).slicesD + 2 * zz)).val M).sum ∧
      scFold2 (fun k => (ld2 k).val M) 5 (wireLanesU 20 qw).slotY ((ld2 ((wireLanesU 20 qw).g3 + 2)).val M) =
        ((List.range 64).map fun zz => slotWv (cvB M 15 cv) (eqKernelF (cvA M 15 cv)) (o.tauY.map (C2.val M)) 25 zz *
          (ld2 ((wireLanesU 20 qw).slicesY + 2 * zz)).val M).sum ∧
      scFold2 (fun k => (ld2 k).val M) 5 (wireLanesU 20 qw).slotM ((ld2 ((wireLanesU 20 qw).g3 + 4)).val M) =
        ((List.range 64).map fun zz => slotWv (cvB M 15 cv) (eqKernelF (cvA M 15 cv)) (o.tauM.map (C2.val M)) 17 zz *
          (ld2 ((wireLanesU 20 qw).slicesM + 2 * zz)).val M).sum) := by
  unfold wireGS
  refine hsA_bind (hsA_of_hs (hs_preWU cv _ _ t hmb ht (by simp [hsb]))) fun G hG => ?_
  obtain ⟨hz, ho, hom, heZ, hlt, htg⟩ := hG
  have heZl : G.eZ.length = 64 := by
    have := congrArg List.length heZ; rw [List.length_map, eqKernelF_length, cvA] at this; simpa using this
  refine hsA_bind (hsA_of_hs (hs_sc2 20 qw G.target)) fun sc ⟨hs1, hs2⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_kernS hz ho _ _ sc.1 _ G.lt t (by simp) (by simp) (by rw [hs1]; simp [sc2Ans])
    hmb ht hlt B Ks hB hKs)) fun k ⟨hkch, hkks, hiks, he'⟩ => ?_
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
  · have e1 : (List.map (C2.val M) ((List.range (15 + 1)).map fun i => cv (34 + i))) = cvRho M 15 cv := by
      rw [cvRho, List.map_map]; rfl
    have e2 : (List.map (C2.val M) ((List.range 32).map fun i => cv (1 + i))) = cvMu M cv := by
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

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

/-! ## The front's phases at S2GS (`frontS`) -/

section FrontS

open Lvm.Q2 Lvm.QShape

/-- `nStepRowsC` (proof help). -/
theorem nStepRowsC_eq : Lvm.QSig.nStepRowsC = 352 := Lvm.QSig.layC.2.2.2.2.2.2.2.2.2.1

/-- **The key-leaf starts fit the wire's kernel**: every `K ∈ ksKs p` has `K + 31 < 2^13` (`ksSplit p = 7680`). -/
theorem hKsS {p : Params} (hf : FrontPF p) : ∀ K ∈ ksKs p, K + 31 < 2 ^ 13 := by
  intro K hK
  simp only [ksKs, hf.ksSplit_eq, nStepRowsC_eq] at hK
  split at hK <;> simp at hK <;> omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`front_phasesS`** (`front_phasesUG` for `frontS`): the front's phases at `p = C.p` with `P20U`'s front facts
(`FrontPF`) and `cont`'s intervals `ivs` (`(1, B − 1)` and `(K + 1, K + 31)` for `K ∈ ksKs p`, `B` the sponge
blocks): from the front's rows and assertions (gate on), the proof-of-work answers (`powFrontU`), the three row
switches' words (the `rowAux` blocks on `tBu`), `n'`'s bits and range and the bits of `s'`, V_S's merged tape with the
wire runs from the tape's first item to the opening's, the front's claims stand for `frontItemsU`'s, and `mb` is
`n' − 1`'s selector. -/
theorem front_phasesS (C : QCfg) {p : Params} (hp : C.p = p) (hf : FrontPF p) (ivs : List (ℕ × ℕ))
    (hivs : (1, spongeBlocks p - 1) :: (ksKs p).map (fun K => (K + 1, K + 31)) = ivs) {c : Ctx} {M : Mem}
    {sig : ByteArray} {q : Ptr}
    (hS : Lvm.Q1.Streamed M sig (streamLanes p))
    (hTo : posOf p (phaseItem0 p .openMain) + 48 ≤ 8 * streamLanes p)
    (hg : M.k (pbB C) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFrontU p))
    (hrD : ∀ j < 128, M.k (tBu C 0 + j) = rowWordD (Lvm.Q2.slicesOf M (wlUG p).slicesD) j)
    (hrY : ∀ j < 128, M.k (tBu C 1 + j) = rowWordD (Lvm.Q2.slicesOf M (wlUG p).slicesY) j)
    (hrM : ∀ j < 128, M.k (tBu C 2 + j) = rowWordD (Lvm.Q2.slicesOf M (wlUG p).slicesM) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn C).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB C + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontS C) q) :
    ∃ tp : Lvm.E2U.TapeU Lvm.RowZ,
      Lvm.Har.PhaseAt (Lvm.E2L.tapeUDGc ivs Lvm.rowSwitchDR p pub.s pub.n) sig
        (posOf p (phaseItem0 p .tape)) (posOf p (phaseItem0 p .openMain)) tp ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontS C q).1.cs
        ((Lvm.E2U.frontItemsU Lvm.rowAccR p pub tp).flatMap Lvm.FItem.flat) ∧
      vs M (frontS C q).1.mb = selectorPoint (pub.n - 1) 20 := by
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨T, hTl⟩ : ∃ T, streamLanes p = T := ⟨_, rfl⟩
  rw [hTl] at hS hTo
  -- GOLF3-U: no `streamLanes p` fact left: every later `omega` listed it as an atom and the kernel evaluated the
  -- tally while checking each certificate (0.2–0.5 M heartbeats per `omega`)
  clear hTl
  have hgv : (kc (pbB C)).val M = 1 := by rw [Cell.val_K, hg, ofK_one]
  -- the positions
  obtain ⟨pR, pOut, p20, pQs, pW, pQw, pOp, -⟩ := hf.pos
  simp only [phaseLane] at pR pOut p20 pQs pW pQw
  simp only [wlUG, phaseLane, hf.logN] at hrD hrY hrM
  -- the proof of work, by phase
  simp only [powFrontU, getD_toArray, hf.logN, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hpow
  obtain ⟨hp3, hpW⟩ := powOkV_append hpow
  obtain ⟨hp2, hpT⟩ := powOkV_append hp3
  obtain ⟨hpR, hp20⟩ := powOkV_append hp2
  clear hpow hp3 hp2
  -- the front's gadgets
  obtain ⟨fo, hfo⟩ : ∃ fo, (frontS C q).1 = fo := ⟨_, rfl⟩
  rw [hfo]
  simp only [frontS, hp, getD_toArray, Lvm.Q1.tapeGadgetE2F_eq, hf.logN, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub] at h hfo
  obtain ⟨q1, hZ, h1, E⟩ := ok_bindE h
  clear h
  rw [E] at hfo
  rw [show (const .E 0 (kc 0) q).1 = ec q.e from rfl] at h1 hfo
  obtain ⟨q2, hO, h2, E⟩ := ok_bindE h1
  clear h1
  rw [E] at hfo
  rw [show (const .E 1 (kc 0) q1).1 = ec q1.e from rfl] at h2 hfo
  obtain ⟨q3, hZK, h3, E⟩ := ok_bindE h2
  clear h2
  rw [E] at hfo
  rw [show (const .K 0 (kc 0) q2).1 = kc q2.k from rfl] at h3 hfo
  obtain ⟨q4, hOK, h4, E⟩ := ok_bindE h3
  clear h3
  rw [E] at hfo
  rw [show (const .K 1 (kc 0) q3).1 = kc q3.k from rfl] at h4 hfo
  have hz : M.e q.e = 0 := (const_val hZ.1).trans ofK_zero
  have ho : M.e q1.e = 1 := (const_val hO.1).trans ofK_one
  have hzk : (kc q2.k).val M = 0 := (const_val hZK.1).trans ofK_zero
  have hok : M.k q3.k = 1 := congrArg FE.c₀ ((const_val hOK.1).trans ofK_one.symm)
  clear hZ hO hZK hOK
  obtain ⟨q5, hV, h5, E⟩ := ok_bindE h4
  clear h4
  rw [E] at hfo
  obtain ⟨q6, hT, h6, E⟩ := ok_bindE h5
  clear h5
  rw [E] at hfo
  obtain ⟨q7, hB, h7, E⟩ := ok_bindE h6
  clear h6
  rw [E] at hfo
  obtain ⟨q8, hW, h8, E⟩ := ok_bindE h7
  clear h7
  rw [E] at hfo
  obtain ⟨q9, hRD, h9, E⟩ := ok_bindE h8
  clear h8
  rw [E] at hfo
  obtain ⟨q10, hND, h10, E⟩ := ok_bindE h9
  clear h9
  rw [E] at hfo
  obtain ⟨q11, hRY, h11, E⟩ := ok_bindE h10
  clear h10
  rw [E] at hfo
  obtain ⟨q12, hNY, h12, E⟩ := ok_bindE h11
  clear h11
  rw [E] at hfo
  obtain ⟨q13, hRM, h13, E⟩ := ok_bindE h12
  clear h12
  rw [E] at hfo
  obtain ⟨q14, hNM, h14, E⟩ := ok_bindE h13
  clear h13
  rw [E] at hfo
  obtain ⟨q15, hME, -, E⟩ := ok_bindE h14
  clear h14
  rw [E] at hfo
  clear E
  -- names
  -- GOLF3-U: `generalize`, not `set`: as `let` values the positions were closed atoms of every later `omega`, which
  -- the kernel evaluated (the lanes' walk) while checking the certificates
  have hq0' : 8 * laneOf p (phaseItem0 p .tape + 2) = posOf p (phaseItem0 p .tape) + 120 := by
    have := pR 0 (by norm_num); simpa using this
  generalize posOf p (phaseItem0 p .tape) = Pt at *
  generalize posOf p (phaseItem0 p .wire) = Pw at *
  generalize posOf p (phaseItem0 p .openMain) = Pop at *
  generalize laneOf p (phaseItem0 p .tape + 45) = qs at *
  generalize laneOf p (phaseItem0 p .wire + 0) = qw at *
  generalize laneOf p (phaseItem0 p .tape + 41) = tOut at *
  generalize laneOf p (phaseItem0 p .tape + 43) = r43 at *
  generalize laneOf p (phaseItem0 p .tape + 2) = q0 at *
  have hri : ∀ i < 20, laneOf p (phaseItem0 p .tape + (2 + 2 * i)) = q0 + 10 * i := fun i hi => by
    have := pR i hi; omega
  have htE : qs + 49 ≤ Lvm.Q1.tapeEnd2 15 qs := by unfold Lvm.Q1.tapeEnd2 Lvm.Q1.tapeQ2; omega
  have hqwE : qw = Lvm.Q1.tapeEnd2 15 qs := by omega
  have hTw : qw + 1027 < T := by omega
  -- GOLF3-U: the tape's end as a variable too (as a closed `omega` atom the kernel evaluated `lay02 15`); the link kept
  -- as a `HEq`, which `omega` does not read
  generalize hE : Lvm.Q1.tapeEnd2 15 qs = E at *
  have hEh : HEq (Lvm.Q1.tapeEnd2 15 qs) E := heq_of_eq hE
  clear hE
  -- T1's values and the tape GKR
  set F : FCtx := ⟨ec q.e, ec q1.e, kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc q3.k, kc q2.k⟩, false⟩ with hF
  set r : List C2 := (List.range 20).map fun i => Lvm.Q1.laneC2 (laneOf p (phaseItem0 p .tape + (2 + 2 * i)))
    with hr
  set r20 := Lvm.Q1.laneC2 r43 with hr20
  set a : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 2 * l) with ha
  set bb : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 50 + 2 * l) with hbb
  have hz2v : F.z2.val M = 0 := by
    show (⟨((kc q2.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 0
    rw [hzk]; rfl
  have ho2v : F.o2.val M = 1 := by
    show (⟨((kc q3.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 1
    rw [Cell.val_K, hok, ofK_one, hzk]; rfl
  have hrl : r.length = 20 := by simp [hr]
  have hrv : r.map (C2.val M) = sampsG sig (Pt + 72) 20 := by
    rw [hr, List.map_map]
    unfold sampsG
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [hri i hi', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hr20v : r20.val M = fe2At sig (Pt + 2520) := by rw [hr20, Lvm.Q1.laneC2_val hS (by omega), p20]
  have hav : (List.range 25).map (fun l => (a.getD l default).val M) = readsE2 sig (Pt + 1672) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [ha, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hbv : (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672 + 16 * 25) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [hbb, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have habv : ((List.range 25).map fun l => (a.getD l default).val M) ++
      (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672) 50 := by
    rw [hav, hbv, show 50 = 25 + 25 from rfl, readsE2_add]
  have hV1 := hs_tOneU F hz2v ho2v r hrl r20 a bb q4 hV.1
  have hinst : (List.range (15 + 6)).map (fun i => ((r ++ [r20]).getD i default).val M) =
      sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)] := by
    rw [show 15 + 6 = (r ++ [r20]).length by simp [hrl], map_range_getD, List.map_append, hrv, List.map_singleton,
      hr20v]
  have hout : (List.range 25).map (fun l => ((tOneU F r r20 a bb q4).1.getD l default).val M) =
      Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50) := by
    rw [List.map_congr_left fun l hl => hV1 l (List.mem_range.mp hl), hrv, hr20v, habv]
    conv_rhs => unfold Lvm.E2U.t1ValsF
    exact List.map_congr_left fun l hl => by
      unfold Lvm.E2U.t1ValsF; exact getD_map_range0 _ (List.mem_range.mp hl)
  have TG := tapeGkr_phaseU hS (P := Pt) (qs := qs) pQs (by rw [eq_of_heq hEh]; omega) hT.1 hT.2 hgv hpT hinst hout
  obtain ⟨TG1, hR⟩ := TG
  set claimV := (tapeGkrD 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (Lvm.E2U.t1ValsF 20 13
    (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)) sig ⟨Pt + 2552, 0, true⟩).1
    with hclaimV
  set cv := (Lvm.Q1.tapeGadgetE2 15 qs (fun i => (r ++ [r20]).getD i default)
    (fun l => ((tOneU F r r20 a bb q4).1).getD l default) (kc (pbB C)) q5).1.cv with hcv
  -- `n' − 1`'s bits
  have hmbv := borrowK_vs (N := pub.n) (show M.k (kc q3.k).n = 1 from hok) (fun j hj => hnb j hj) hn1 hB.1
  have hmb := kC2_bits (m := 20) hzk hmbv
  -- the wire gadget
  have hsbl : (sbCells C).length = 256 := by simp [sbCells]
  have hBs : spongeBlocks p - 1 < 2 ^ 13 := hf.sb
  have hKs : ∀ K ∈ ksKs p, K + 31 < 2 ^ 13 := hKsS hf
  obtain ⟨wo, hwo, WS⟩ := hsA_out (wireGS_sound qw cv _ (sbCells C) (spongeBlocks p) (ksKs p)
    (kc q2.k) (kc (pbB C)) (pub.n - 1) hzk hgv hsbl hmb (by omega) hBs hKs) hW
  rw [wireLanesU_20] at WS
  dsimp only at WS
  obtain ⟨hs1, hd1, hy1, hm1, hfinW, hDW, hYW, hMW⟩ := WS
  have hpt : cvRho M 15 cv = claimV.point := hR.point
  have hmu : cvMu M cv = claimV.mu := hR.mu
  have hω : ∀ j < 1600, claimV.weights.getD j 0 = omegaF M 15 cv j := fun j hj => Lvm.Q1.rep2_lt_posF hR hj
  have htgt : targetF M 15 cv (((sbCells C).map fun b => kC2 b (kc q2.k)).map (C2.val M)) (pub.n - 1) =
      wireTargetDF (sBitsD pub.s) pub.n claimV := by
    rw [wireTargetDF_eq]
    exact targetF_eq 15 cv claimV pub.s pub.n _ hR.value.symm hmu.symm hpt.symm hω (sb_vals hzk pub.s hsb)
  have hσ : wo.sigma.map (C2.val M) = scPts sig Pw 20 := by rw [hs1]; exact sc2_vals hS pQw (by omega)
  have hτD : wo.tauD.map (C2.val M) = scPts sig (Pw + 2288) 2 := by rw [hd1]; exact sc2_vals hS (by omega) (by omega)
  have hτY : wo.tauY.map (C2.val M) = scPts sig (Pw + 4040) 5 := by rw [hy1]; exact sc2_vals hS (by omega) (by omega)
  have hτM : wo.tauM.map (C2.val M) = scPts sig (Pw + 6128) 5 := by rw [hm1]; exact sc2_vals hS (by omega) (by omega)
  have hg0 : (ld2 (qw + 280)).val M = fe2At sig (Pw + 2280) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg1 : (ld2 (qw + 280 + 2)).val M = fe2At sig (Pw + 2296) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg2 : (ld2 (qw + 280 + 4)).val M = fe2At sig (Pw + 2312) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hcont : (1, spongeBlocks p - 1) :: (ksKs p).map (fun K => (K + 1, K + 31)) = ivs := hivs
  have hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 qw (wireTargetDF (sBitsD pub.s) pub.n claimV) =
      E2V.msEvalF claimV.point claimV.mu (scPts sig Pw 20) 0 (pub.n - 1) * fe2At sig (Pw + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig Pw 20) *
          (Lvm.E2U.kksF ivs claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) *
              fe2At sig (Pw + 2296) +
            E2V.ikEvalP claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) * fe2At sig (Pw + 2312)) := by
    rw [← htgt, ← scFold2_ld2 hS (by omega), hfinW, hpt, hmu, hσ, hg0, hg1, hg2, hcont]
  have hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((Pw + 2288 + 40) / 8) (fe2At sig (Pw + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claimV.weights.toArray) (scPts sig (Pw + 2288) 2) z *
        (readsE2 sig (Pw + 2288 + 112 * 2) 64).getD z 0) := by
    rw [show (Pw + 2288 + 40) / 8 = qw + 286 by omega, ← hg0, ← scFold2_ld2 hS (by omega), hDW, E2V.sumF_eq_sum,
      dWA_eq]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτD, slotW_eq _ _ (by simp [scPts]) _ hω zz hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 4040 + 40) / 8) (fe2At sig (Pw + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claimV.weights) (scPts sig (Pw + 4040) 5) z *
        (readsE2 sig (Pw + 4040 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 4040 + 40) / 8 = qw + 505 by omega, ← hg1, ← scFold2_ld2 hS (by omega), hYW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτY, slotWF_yWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 6128 + 40) / 8) (fe2At sig (Pw + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claimV.weights) (scPts sig (Pw + 6128) 5) z *
        (readsE2 sig (Pw + 6128 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 6128 + 40) / 8 = qw + 766 by omega, ← hg2, ← scFold2_ld2 hS (by omega), hMW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτM, slotWF_mWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  obtain ⟨hpw, hpD, hpY, hpM⟩ := powW_of pQw hpW
  have WP := wireUDGc_phase (P := Pw) (q := qw) ivs p hf.logN hf.ksLog pub.s pub.n claimV pQw hpw hpD hpY hpM hfin hD
    hY hM
  have TG1' : Lvm.Har.PhaseAt (tapeGkrDF 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)))
      sig (Pt + 2552) Pw claimV := by rw [pW, ← eq_of_heq hEh]; exact TG1
  have hp20' : DM.powOKR E2V.gC1 (feAt sig (Pt + 2520)) = true := by
    have := hp20 _ List.mem_cons_self; rwa [p20] at this
  have TP := tapeUDGc_phase (P := Pt) (q0 := q0) ivs p hf.logN hf.ksLog pub.s pub.n hq0' hpR hp20' TG1' ⟨hn1, hn2⟩ WP
  rw [pOp]
  refine ⟨_, TP, ?_, ?_⟩
  · rw [← hfo]
    subst hwo
    simp only [wireLanesU_20] at hrD hrY hrM
    have hsD := slicesOf_reads hS (a := qw + 314) (P := Pw + 2288 + 112 * 2) (by omega) (by omega)
    have hsY := slicesOf_reads hS (a := qw + 575) (P := Pw + 4040 + 112 * 5) (by omega) (by omega)
    have hsM := slicesOf_reads hS (a := qw + 836) (P := Pw + 6128 + 112 * 5) (by omega) (by omega)
    rw [hsD] at hrD
    rw [hsY] at hrY
    rw [hsM] at hrM
    have hTD : (wireLanesU 20 qw).ringD + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTY : (wireLanesU 20 qw).ringY + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTM : (wireLanesU 20 qw).ringM + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    refine front_claimsUG hf (zc := zc) (b := b) (pub := pub) (F := F) (r := r) (a := a) (bb := bb)
      (sY := E2V.selPtF ((layout0 p).ks / 2 ^ (p.ksLog + 5)) (p.nuMain - (p.ksLog + 5)))
      (sM := E2V.selPtF ((layout0 p).s / 2 ^ p.nuRec) (p.nuMain - p.nuRec))
      (eqD := (rowG (wireLanesU 20 qw).ringD (tBu C 0) (ec q.e).n (ec q1.e).n q8).1.eqR.map (Cell.val M))
      (eqY := (rowG (wireLanesU 20 qw).ringY (tBu C 1) (ec q.e).n (ec q1.e).n q10).1.eqR.map (Cell.val M))
      (eqM := (rowG (wireLanesU 20 qw).ringM (tBu C 2) (ec q.e).n (ec q1.e).n q12).1.eqR.map (Cell.val M))
      hz2v ho2v ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hz ho ?_ hrl ?_ ?_ hrv.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hσ.symm hτD.symm ?_
      ?_ ?_ ?_ ?_ ?_ ?_ hh hsm hn1
    · intro x hx
      rw [hr] at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
    · intro l hl; rw [ha, getD_map_range _ (by omega)]; exact ⟨rfl, rfl⟩
    · intro l hl; rw [hbb, getD_map_range _ hl]; exact ⟨rfl, rfl⟩
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD l 0 = _
      rw [← habv, List.getD_append _ _ _ _ (by simp; omega), getD_map_range0 _ (by omega)]
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD (25 + l) 0 = _
      rw [← habv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, getD_map_range0 _ hl]
    · rw [hs1]; exact ld2_K _
    · rw [hs1]; simp [sc2Ans]
    · rw [hd1]; exact ld2_K _
    · rw [hd1]; simp [sc2Ans]
    · rw [hy1]; exact ld2_K _
    · rw [hy1]; simp [sc2Ans]
    · rw [hm1]; exact ld2_K _
    · rw [hm1]; simp [sc2Ans]
    · show ((rowSwitchDR _ _ sig ⟨Pw + 2288 + 112 * 2 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTD hRD.1 (by simp only [wireLanesU_20]; omega) _ _ hrD, hσ, hτD]
    · exact rowNuOk_of hS hz ho hTD hRD.1 hND.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 4040 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTY hRY.1 (by simp only [wireLanesU_20]; omega) _ _ hrY, hσ, hτY]
    · exact rowNuOk_of hS hz ho hTY hRY.1 hNY.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 6128 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTM hRM.1 (by simp only [wireLanesU_20]; omega) _ _ hrM, hσ, hτM]
    · exact rowNuOk_of hS hz ho hTM hRM.1 hNM.1
    · exact (mapB_add_vs (by rw [Cell.val_E, hz]) _ _ hME.1).trans (by rw [hmbv, selectorPoint_bits])
  · rw [← hfo]
    exact hmbv.trans (selectorPoint_bits _ _).symm

end FrontS

end Lvm.E2Q

/-! ## `P20S`'s literals (proof help: S2GU's phase literals without the phase `tables`, `P20S`'s own) -/

namespace Lvm

/-- **`phases P20S`**, phase by phase (S2GS's phases are S2GL's: S2GU's literals without the phase `tables`). -/
private def phasesS20 : List (Phase × List Item) :=
  [(.commit, ph20U_commit), (.bus, ph20U_bus), (.tape, ph20U_tape), (.wire, ph20U_wire),
   (.openMain, ph20U_openMain)]

set_option maxRecDepth 100000 in
/-- The phases at `P20S` are `phasesS20` (by `rfl` after the stage dispatch). -/
private theorem phases_P20S_lit : phases P20S = phasesS20 := by
  rw [phases_P20S]; rfl

/-- **`schedule P20S`**: the phase literals in order. -/
private def schedS20 : List Item := ph20U_commit ++ ph20U_bus ++ ph20U_tape ++ ph20U_wire ++ ph20U_openMain

/-- The schedule at `P20S` is `schedS20`. -/
private theorem schedule_P20S_lit : schedule P20S = schedS20 := by
  rw [schedule, phases_P20S_lit]
  simp only [phasesS20, schedS20, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- `P20S` with its WHIR levels written out. -/
private def P20SL : Params := { P20S with mainLevels := P20UL.mainLevels }

/-- `P20S` is `P20SL` (its levels are `P20`'s with the root row `46`, `P20_eq`). -/
private theorem P20S_eqL : P20S = P20SL := by
  have h : P20S.mainLevels = P20SL.mainLevels := by
    show withRow0 P20.mainLevels 46 = _
    rw [Lvm.Replay.P20_eq]; rfl
  show P20S = { P20S with mainLevels := P20SL.mainLevels }
  rw [← h]

end Lvm

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

/-! ## Positions at `P20S` -/

set_option maxRecDepth 100000 in
/-- The first items of `P20S`'s phases (proof help: one walk of the literal `phasesS20`). -/
private theorem phaseItem0_P20S : phaseItem0 P20S .commit = 0 ∧ phaseItem0 P20S .bus = 25 ∧
    phaseItem0 P20S .tape = 357 ∧ phaseItem0 P20S .wire = 2523 ∧ phaseItem0 P20S .openMain = 2644 := by
  simp only [phaseItem0, phases_P20S_lit]; decide +kernel

/-- The phases' suffixes at `P20S` from one another (proof help: `.wire` and `.openMain` from `.tape`'s suffix). -/
private theorem drop_chainS (l : List Nat) :
    l.drop 2644 = ((l.drop 357).drop 2166).drop 121 ∧ l.drop 2523 = (l.drop 357).drop 2166 := by
  constructor <;> simp only [List.drop_drop]

set_option maxRecDepth 200000 in
/-- **`P20S`'s positions** (`posL20`'s twin; one kernel evaluation of the schedule's lanes). -/
theorem posS20 : startByte P20S + nodeBytes * 2 ^ (P20S.level ⟨.main, 0⟩).cap = posOf P20S 1 ∧
    posOf P20S 1 + 40 = 8 * phaseLane P20S .commit 1 ∧
    phaseLane P20S .commit (P20S.nuMain + 1) = phaseLane P20S .commit 1 + 9 * P20S.nuMain ∧
    posOf P20S 1 + 72 * P20S.nuMain + 24 = typedPosF P20S ∧ busLanesB P20S = true ∧
    ((∀ i < 20, 8 * phaseLane P20S .tape (2 + 2 * i) = posOf P20S (phaseItem0 P20S .tape) + 120 + 80 * i) ∧
      8 * phaseLane P20S .tape 41 = posOf P20S (phaseItem0 P20S .tape) + 1712 ∧
      8 * phaseLane P20S .tape 43 = posOf P20S (phaseItem0 P20S .tape) + 2520 ∧
      8 * phaseLane P20S .tape 45 = posOf P20S (phaseItem0 P20S .tape) + 2600 ∧
      posOf P20S (phaseItem0 P20S .wire) = 8 * Lvm.Q1.tapeEnd2 15 (phaseLane P20S .tape 45) - 40 ∧
      8 * phaseLane P20S .wire 0 = posOf P20S (phaseItem0 P20S .wire) + 40 ∧
      posOf P20S (phaseItem0 P20S .openMain) = posOf P20S (phaseItem0 P20S .wire) + 8216 ∧
      posOf P20S (phaseItem0 P20S .tape) % 8 = 0) := by
  simp only [posOf_drop, phaseLane_drop, typedPosF, busLanesB, busL_drop, phaseItem0_P20S.1, phaseItem0_P20S.2.1,
    phaseItem0_P20S.2.2.1, phaseItem0_P20S.2.2.2.1, phaseItem0_P20S.2.2.2.2]
  rw [itemLanes, schedule_P20S_lit, P20S_eqL, (drop_chainS _).1, (drop_chainS _).2, itemLanesAux_eq_R]
  simp only [← dropLN_eq, ← getDLN_eq, iZR, iWR, iRR, getDLN_add]
  decide +kernel


theorem hbS : Lvm.Har.pos (RS.startH (headerBytesP P20S)) + nodeBytes * 2 ^ (P20S.level ⟨.main, 0⟩).cap =
    posOf P20S 1 := by
  rw [pos_startH]; exact posS20.1

theorem pinHPS : posOf P20S 1 + 40 = 8 * phaseLane P20S .commit 1 := posS20.2.1

theorem pinQaS : phaseLane P20S .commit (P20S.nuMain + 1) = phaseLane P20S .commit 1 + 9 * P20S.nuMain :=
  posS20.2.2.1

theorem pinEndS : posOf P20S 1 + 72 * P20S.nuMain + 24 = typedPosF P20S := posS20.2.2.2.1

theorem busLanesB_P20S : busLanesB P20S = true := posS20.2.2.2.2.1

/-- **`P20S`'s front facts** (`frontPF_P20L`'s twin; the sponge blocks from `sizes_P20S`). -/
theorem frontPF_P20S : FrontPF P20S :=
  ⟨rfl, rfl, rfl, rfl, rfl, by rw [sizes_P20S.1.2.2.2.2.1]; norm_num, posS20.2.2.2.2.2⟩

/-- **The wire's `cont` intervals at S2GS are V_S's** (`contIvS aSP`: the trace's, Q_sig's key leaf, the own key
leaf). -/
theorem ivsS20 : (1, spongeBlocks P20S - 1) :: (ksKs P20S).map (fun K => (K + 1, K + 31)) =
    Lvm.E2S.contIvS Lvm.E2S.aSP := by
  rw [sizes_P20S.1.2.2.2.2.1]
  simp only [ksKs, frontPF_P20S.ksSplit_eq, nStepRowsC_eq, show P20S.leafOut = true from rfl, if_true]
  rfl

end Lvm.E2Q

/-! ## The plan's facts at `P20S` -/

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- The cap entries at `P20S` and their lengths (the FS queries that absorb the caps; a probe evaluation of the
plan). -/
def tblS20 : List (ℕ × ℕ) := [(2, 8224), (973, 4176), (2392, 4176)]

set_option maxRecDepth 200000 in
/-- **The plan's facts at `P20S`** in one kernel evaluation (the walk over `schedS20` at `P20SL`; `Σ clen = 284,864`,
`Σ (40 + len) = 537,335`). -/
private theorem planFactsS :
    passR (capLk tblS20) 3618 284864 537335 (plan P20S) tblS20 0 0 0 = true ∧
      (PlanOk P20S ∧ (planAll P20S).2.i = 3618) ∧ qOkF P20S (lay cfgS20) = true :=
  planFacts_of schedule_P20S_lit P20S_eqL sizes_P20S.1.2.2.1 rfl (by decide +kernel)

/-- **The one decision at `P20S`.** -/
theorem passR_P20S : passR (capLk tblS20) 3618 284864 537335 (plan P20S) tblS20 0 0 0 = true :=
  planFactsS.1

/-- `PlanOk P20S` and the walk's last entry. -/
theorem planSt_P20S : PlanOk P20S ∧ (planAll P20S).2.i = 3618 :=
  planFactsS.2.1

/-- **Q_link's stream facts at `P20S`.** -/
theorem streamOk_P20S : StreamOk P20S := streamOk_ofR passR_P20S sizes_P20S.1.2.2.1

/-- Q_link's static checks at S2GS as `qOkF` (at S2GS's layout `lay cfgS20`; from `planFactsS`). -/
theorem qOkF_P20S : qOkF P20S (lay cfgS20) = true :=
  planFactsS.2.2

/-- **Q_link's static checks at S2GS.** -/
theorem hQS20 : QOk P20S (lay cfgS20) :=
  qOk_of streamOk_P20S rfl ((qOkF_eq _ _).symm.trans qOkF_P20S)

end Lvm.E2Q

/-! ## V_S's S2GS decision from its phases (`core_of_phasesL`, `decideFLG_of` at `decideProgSG`) -/

namespace Lvm.Har

open Lvm DM Lvm.E2T Lvm.E2U

private theorem bind_runS {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runS {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl
private theorem skip_runS (n : Nat) (sig : ByteArray) (s : RS) :
    skip n sig s = ((), { s with msg := s.msg + n }) := (skip_run' n sig s).trans rfl
private theorem read_runS (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) :=
  (read_run' sig s).trans rfl
private theorem stRunS {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

/-- **`decideProgSG` from its phases** (`core_of_phasesL`'s twin at S2GS: `pubOfWS`, `contIvS a`; the typed phases
end at the bus's point and decomposition; the opening is `dOpenF` on the typed claims, the three claims and the front's). -/
theorem core_of_phasesS (p pT : Params) (a : Nat) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P1 P2 P3 : Nat} {pin : BlockClaim} {acc : Acc} {ti : List FItem} {ζ : List FE} {bus : BusOut}
    {tp : TapeU RowZ}
    (hb : pos (RS.startH (headerBytesP p)) + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (Lvm.E2L.dTypedLG pT N (m3G N p) (Lvm.pubOfWS vk c sig) (typedItemsND N p)) sig P1 P2
      (acc, ti, ζ, bus))
    (htape : PhaseAt (Lvm.E2L.tapeUDGc (Lvm.E2S.contIvS a) rowSwitchDR p (Lvm.pubOfWS vk c sig).s
      (Lvm.pubOfWS vk c sig).n) sig P2 P3 tp)
    (hopen : ∀ s : RS, pos s = P3 → s.ok = true →
      let o := dOpenF p (TypedV.smallT p (Lvm.pubOfWS vk c sig)) pin
        (ti.flatMap FItem.flat ++ Lvm.E2L.linClaims p.nuMain ζ
            ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
            ((List.range 3).map (M3.mbValueN (M3.sumcheckTabs N.mbT) bus ζ)) ++
          (frontItemsU rowAccR p (Lvm.pubOfWS vk c sig) tp).flatMap FItem.flat) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, Lvm.E2S.decideProgSG p pT a N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧ s₉.ok = true ∧
      s₉.ent = sig.size ∧ s₉.msg = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : RS, RS.startH (headerBytesP p) = s₀ := ⟨_, rfl⟩
  have h₀ : s₀.ok = true := by rw [← hs₀]; rfl
  rw [hs₀] at hb ⊢
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = { s₀ with msg := s₀.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← hb, hs1]; simp only [pos]; omega
  obtain ⟨a1, a2, a3⟩ := hpin s1 e1 (by rw [hs1]; exact h₀)
  generalize hA : pinD p.nuMain sig s1 = AA at a1 a2 a3
  obtain ⟨av, s2⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨b1, b2, b3⟩ := htyped s2 a3 a2
  generalize hB : Lvm.E2L.dTypedLG pT N (m3G N p) (Lvm.pubOfWS vk c sig) (typedItemsND N p) sig s2 = BB at b1 b2 b3
  obtain ⟨bv, s3⟩ := BB
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s3 b3 b2
  generalize hC : Lvm.E2L.tapeUDGc (Lvm.E2S.contIvS a) rowSwitchDR p (Lvm.pubOfWS vk c sig).s (Lvm.pubOfWS vk c
      sig).n sig s3 = CC
    at c1 c2 c3
  obtain ⟨cv, s4⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨o1, o2, o3⟩ := hopen s4 c3 c2
  rw [← dOpenFFL_eq] at o1 o2 o3
  generalize hO : Lvm.E2L.dOpenFFL p (TypedV.smallT p (Lvm.pubOfWS vk c sig)) pin ti ζ
    ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
    ((List.range 3).map (M3.mbValueN (M3.sumcheckTabs N.mbT) bus ζ))
    (frontItemsU rowAccR p (Lvm.pubOfWS vk c sig) tp) sig s4 = OO at o1 o2 o3
  obtain ⟨ov, s5⟩ := OO
  simp only at o1 o2 o3
  refine ⟨s5, ?_, o1, o2, o3⟩
  unfold Lvm.E2S.decideProgSG
  simp only [bind_runS, read_runS, skip_runS, pure_runS]
  rw [← hs1, hA]
  simp only
  rw [hB]
  simp only
  rw [hC]
  simp only
  rw [Lvm.M3.mbValsF_eq, hO]

/-- **`decideFSG` accepts** when its run ends accepting with the accumulator `acc` and `Φ_Q` at `E2` holds at it. -/
theorem decideFSG_of (p pT : Params) (a : Nat) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, Lvm.E2S.decideProgSG p pT a N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phiT (acc.pt.map Lvm.e2OfFE) = Lvm.e2OfFE acc.y) :
    Lvm.E2S.decideFSG p pT a N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  have eD : @Lvm.E2S.decideFSG = @Lvm.E2S.decideFSG := rfl
  conv at eD => rhs; delta Lvm.E2S.decideFSG
  rw [eD]
  beta_reduce
  rw [DM.runOnH, stRunS, h1]
  simp only [h2, h3, h4, hphi, beq_self_eq_true, Bool.and_self]

end Lvm.Har

/-! ## Q_arith at S2GS (`harithL20`'s proof at `cfgS20`) -/

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU YqU MqU)
open Lvm.E2S (VSSX decideFSX THypS GoodTS)

/-- Q_arith's pointer at S2GS (after Q_link and `qsigSC`; `LvmS2GSStmtC`'s `p2S20`). -/
def p2S20H : Ptr :=
  let p1 := (⟨nK cfgS20, 0⟩ : Ptr).adv (qlink cfgS20.p (lay cfgS20) ⟨nK cfgS20, 0⟩).2
  p1.adv (qsigSC (sigIn cfgS20) (sigInLC cfgS20) p1).2

/-- **The front's inputs from the stream** (`frontIns` with Q_sig's `ChildOkS`). -/
theorem frontInsS {C : QCfg} {M : Mem} {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) (hT : 29 ≤ T)
    {o : SigOut} (hbits : SigBits (sigIn C) o M.k) (hch : ChildOkS (sigIn C) M.k)
    (hsb : Lvm.Q1.SBitsS M.k (sigIn C).hd (bsB C)) (accV : ℕ) (vk cL : Vector UInt8 32)
    (hln : (sigIn C).ln = 20) (hhd : (sigIn C).hd + 13 = nLane) :
    (∀ j < 20, (kc ((sigIn C).bn + 2 + j)).val M = bitE (pubOfA accV vk cL sig).n j) ∧
      (1 ≤ (pubOfA accV vk cL sig).n ∧ (pubOfA accV vk cL sig).n ≤ 2 ^ 20) ∧
      ∀ i < 256, M.k (bsB C + i) = if sBitsD (pubOfA accV vk cL sig).s i then 1 else 0 := by
  have hn : (pubOfA accV vk cL sig).n = (M.k nLane).val.toNat := pub_n hS hT vk cL
  refine ⟨fun j hj => ?_, ?_, sBitsD_of hsb ?_⟩
  · rw [hn, Cell.val_K]
    exact bitE_out1 (by (clear * - j C M sig T accV vk cL hj; omega)) (hhd ▸ hbits.n_bit j (show j ≤ (sigIn C).ln by
        (clear * - j C M sig T accV vk cL hln hj; omega)))
  · rw [hn, ← hhd, ← hln]
    exact ⟨hch.2.2.1, hch.2.2.2.1⟩
  · rw [show (pubOfA accV vk cL sig).s = (pubOf vk cL sig).s from rfl, pub_s hS hT vk cL]
    refine List.map_congr_left fun l _ => ?_
    rw [sLane_eq]
    rfl

section PairSH

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- The trace bytes of the child at S2GS have `hashedLen P20S` bytes. -/
theorem sigS_size (hL : LaneLink P20S (wsC qr)) : (traceBytesB (decode P20S (wsC qr))).size = hashedLen P20S := by
  rw [traceBytesB_decode streamOk_P20S hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams the child's trace at S2GS** (`streamed_child` at `cfgS20`). -/
theorem streamedS {M : Mem} (hst : ∀ j < 2 ^ (lay cfgS20).m, M.k ((lay cfgS20).sb + j) = laneK (wsC qr) j)
    (hL : LaneLink P20S (wsC qr)) : Lvm.Q1.Streamed M (traceBytesB (decode P20S (wsC qr))) (streamLanes P20S) := by
  have hh : hashedLen P20S = 537336 := sizes_P20S.1.2.2.1
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  exact Lvm.Har.streamed_child cfgS20 streamOk_P20S hL hst (T := streamLanes P20S)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgS20.p = P20S from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)

theorem hWS (S : NodeGS) (H : THypS TiS20) (hG : GoodTS TiS20 H x qm qr) :
    WiringRelX QS20 layS20 (zTX (NTS20.toN.instL Pub.hdrLanesT QS20 layS20) Lvm.pubXTS x qm qr) :=
  (wiringRelT_iff QS20 layS20 S.st.hlay _).mp hG.1.1.1.1

/-- **The three row switches' words at S2GS** (the `rowAux` blocks of `specQU` on `tBu cfgS20 i`). -/
theorem rowWordsS (S : NodeGS) (H : THypS TiS20) (hG : GoodTS TiS20 H x qm qr) :
    (∀ j < 128, (memTX TiS20 Lvm.pubXTS x qm qr).k (tBu cfgS20 0 + j) =
      rowWordD (Lvm.Q2.slicesOf (memTX TiS20 Lvm.pubXTS x qm qr) (wlUG P20S).slicesD) j) ∧
    (∀ j < 128, (memTX TiS20 Lvm.pubXTS x qm qr).k (tBu cfgS20 1 + j) =
      rowWordD (Lvm.Q2.slicesOf (memTX TiS20 Lvm.pubXTS x qm qr) (wlUG P20S).slicesY) j) ∧
    (∀ j < 128, (memTX TiS20 Lvm.pubXTS x qm qr).k (tBu cfgS20 2 + j) =
      rowWordD (Lvm.Q2.slicesOf (memTX TiS20 Lvm.pubXTS x qm qr) (wlUG P20S).slicesM) j) := by
  obtain ⟨f, hf⟩ := Lvm.QTyped.aux_mkLayD QS20 (specQU cfgS20 QS20 powS20) dintsS20
  have hmem : ∀ B, B ∈ Lvm.Q2.rowAuxL (f (specQ cfgS20 QS20).auxWords.length) (tBu cfgS20 0) (wlUG P20S).slicesD ++
      Lvm.Q2.rowAuxL (f ((specQ cfgS20 QS20).auxWords.length + 1)) (tBu cfgS20 1) (wlUG P20S).slicesY ++
      Lvm.Q2.rowAuxL (f ((specQ cfgS20 QS20).auxWords.length + 2)) (tBu cfgS20 2) (wlUG P20S).slicesM →
      B ∈ layS20.aux := fun B hB => by
    show B ∈ (mkLayD QS20 (specQU cfgS20 QS20 powS20) dintsS20).1.aux
    rw [hf]
    show B ∈ (specQ cfgS20 QS20).auxOf f ++ _ ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hB)
  have hone := zOf_one (NTS20.toN.instL Pub.hdrLanesT QS20 layS20) H.ok.2 Lvm.M3.lay26 (Lvm.pubXTS x) qm qr
  exact ⟨fun j hj => rowWords_of_aux S.st.hlay hone (hWS S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_left _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWS S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_right _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWS S H hG) (fun B hB => hmem B (List.mem_append_right _ hB)) hj⟩

/-- **V's proof-of-work checks at S2GS** (`powOk_of_blksU` at `cfgS20`). -/
theorem powOkS (S : NodeGS) (H : THypS TiS20) (hG : GoodTS TiS20 H x qm qr) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memTX TiS20 Lvm.pubXTS x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ powS20)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blksU cfgS20 (Q := QS20) (tl := layS20) (d := dintsS20) rfl S.st.hlay
    (zOf_one (NTS20.toN.instL Pub.hdrLanesT QS20 layS20) H.ok.2 Lvm.M3.lay26 (Lvm.pubXTS x) qm qr) (hWS S H hG)
    hS hL hpw

/-- **Q_sig's `ChildOkS` at S2GS** (`childOkL`'s twin: the first walk `qsigNoSl`, the `KS` facts from the merged
tape over `contIvS aSP`). -/
theorem childOkS (S : NodeGS) (H : THypS TiS20) {vk c : RecursionFast.Digest} (hok : okSL vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTS TiS20 H x qm qr ∧ SBlkU qm qr) :
    ChildOkS (sigIn cfgS20) (memTX TiS20 Lvm.pubXTS x qm qr).k := by
  have hone : (NTS20.toN.instL Pub.hdrLanesT QS20 layS20).src? layS20.one = some .one := H.ok.2
  obtain ⟨hH, hA⟩ := hholdsCS S Pub.hdrLanesT Lvm.pubXTS cfgU_S20 hone (hWS S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH' : QS20.Holds (memTX TiS20 Lvm.pubXTS x qm qr) := hH
  have hA' : QS20.Asserts (memTX TiS20 Lvm.pubXTS x qm qr) := hA
  rw [QS20_eq] at hH' hA'
  have P := parts_of_holdsS hH' hA'
  have h1 := (Lvm.Har.okb P.2.1).1
  have mp := inMapS20 S H vk c x qm qr hok hb hG
  have hk : ksSplit cfgS20.p = ksSplit P20 := by decide
  have hx : ∀ r < 449, ∀ l < 17, (memTX TiS20 Lvm.pubXTS x qm qr).k ((sigIn cfgS20).xs + 17 * r + l) =
      FK.ofBF64 (MqU qm (ksSplit P20 + r) l) := fun r hr l hl ↦ by rw [mp.xs r hr l hl, hk]
  have hy : ∀ r < 449, ∀ l < 4, (memTX TiS20 Lvm.pubXTS x qm qr).k ((sigIn cfgS20).ys + 4 * r + l) =
      FK.ofBF64 (YqU qm (ksSplit P20 + r) l) := fun r hr l hl ↦ by rw [mp.ys r hr l hl, hk]
  have hks := Lvm.E2U.sigKSin_of_GkL Lvm.E2S.contIvS_ok.1 Lvm.E2S.contIvS_ok.2.2.1 Lvm.E2S.contIvS_ok.2.2.2.1 hG.1.2
    hx (fun r hr l hl ↦ hy r (by omega) l hl)
    (fun t ht l hl ↦ by
      rw [show (sigIn cfgS20).yc + 4 * t + l = (sigIn cfgS20).ys + 4 * (430 + t) + l by
        show ysQ cfgS20 + 4 * 430 + 4 * t + l = ysQ cfgS20 + 4 * (430 + t) + l; ring, hy _ (by omega) l hl,
        Nat.add_assoc])
    (fun l hl ↦ by
      rw [show (sigIn cfgS20).yls + l = (sigIn cfgS20).ys + 4 * 447 + l from rfl, hy _ (by omega) l hl])
    (fun l hl ↦ by
      rw [show (sigIn cfgS20).yns + l = (sigIn cfgS20).ys + 4 * 448 + l from rfl, hy _ (by omega) l hl])
  exact (qsigNoSl_sound (by rw [show (sigIn cfgS20).ln = 20 from rfl]; omega) h1 mp.flag hks
    (hbitsCS S Pub.hdrLanesT Lvm.pubXTS rfl hone (hWS S H hG.1))
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

/-- **Q_link's position cells at S2GS** (`posCellsU`'s twin). -/
theorem posCellsS (S : NodeGS) (H : THypS TiS20) {vk c : RecursionFast.Digest} (hok : okSL vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTS TiS20 H x qm qr ∧ SBlkU qm qr) :
    ∀ k < (opens P20S).length, ((opens P20S).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20S).getD k default).L.t,
      (memTX TiS20 Lvm.pubXTS x qm qr).k (nK cfgS20 + posIdx P20S k j) =
        kOf (posL P20S (wsC qr) (((opens P20S).getD k default).pe + j / 8)
          (j % 8 * ((opens P20S).getD k default).L.height) ((opens P20S).getD k default).L.height) := by
  intro k hk hH j hj
  have hone : (NTS20.toN.instL Pub.hdrLanesT QS20 layS20).src? layS20.one = some .one := H.ok.2
  obtain ⟨hH', hA⟩ := hholdsCS S Pub.hdrLanesT Lvm.pubXTS cfgU_S20 hone (hWS S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH'' : QS20.Holds (memTX TiS20 Lvm.pubXTS x qm qr) := hH'
  have hA' : QS20.Asserts (memTX TiS20 Lvm.pubXTS x qm qr) := hA
  rw [QS20_eq] at hH'' hA'
  have P := parts_of_holdsS hH'' hA'
  have mp := inMapS20 S H vk c x qm qr hok hb hG
  have hp : cfgS20.p = P20S := rfl
  have hk' : k < (opens cfgS20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgS20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgS20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := posVal_onC (C := cfgS20) (outsOnCS S Pub.hdrLanesT Lvm.pubXTS hone (hWS S H hG.1))
    (by rw [hp]; exact streamOk_P20S) (by rw [hp]; exact hQS20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := qlink_pos (pt := p0 (nK cfgS20) 0) hQS20 P.1.1 hk hj
  exact hq.trans hv

/-- The current proof's `vk` cells at S2GS (`vk_cellsU` at `cfgS20`). -/
theorem vk_cellsS {M : Mem} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanesS P20S, M.k ((sigIn cfgS20).flag + j) = hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pbB cfgS20 + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pbB cfgS20 + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, show pbB cfgS20 = (sigIn cfgS20).flag from rfl, hpub _ (lt_of_lt_of_le (show 1 + i < 18 by
        omega) (by decide)),
      Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
  have hv : (Lvm.VEq.pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- **`Φ_Q` at `E2` holds at the folded accumulator at S2GS** (`phiU20_acc`'s twin). -/
theorem phiS20_acc (S : NodeGS) (hlin : Lvm.Typed.KT.linOkX cacheS20 = true) (H : THypS TiS20)
    (hG : GoodTS TiS20 H x qm qr) {M : Mem}
    (hpub : ∀ j < pubLanesS P20S, M.k ((sigIn cfgS20).flag + j) = hdrLane x j) :
    NTS20.phiT ((accCS M (pbB cfgS20)).pt.map Lvm.e2OfFE) = Lvm.e2OfFE (accCS M (pbB cfgS20)).y := by
  have hacc : Lvm.E2T.AccOkTT TiS20 (Lvm.pubXTS x) := hG.1.2
  have hn : pubLanesS P20S = 18 + 2 * (45 + 1) := by decide
  have hl : ∀ j < 46, (Lvm.Q2.ld2 (pbB cfgS20 + 18 + 2 * j)).val M =
      Lvm.e2OfFE (fe16At (Lvm.VEq.sigOfX x) (headerAt (hdrFixS + 16 * j))) := by
    intro j hj
    have hpb : (sigIn cfgS20).flag = pbB cfgS20 := rfl
    have e1 := hpub (18 + 2 * j) (by rw [hn]; omega)
    have e2 := hpub (18 + 2 * j + 1) (by rw [hn]; omega)
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (18 + 2 * j) = headerAt (hdrFixS + 16 * j) by
      simp only [headerAt, hdrFixS]; omega] at e1
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (18 + 2 * j + 1) = headerAt (hdrFixS + 16 * j) + 8 by
      simp only [headerAt, hdrFixS]; omega] at e2
    show (⟨(FE.ofK (M.k (pbB cfgS20 + 18 + 2 * j))).c₀, (FE.ofK (M.k (pbB cfgS20 + 18 + 2 * j + 1))).c₀⟩ : FE2) = _
    rw [Nat.add_assoc (pbB cfgS20), e1, Nat.add_assoc (pbB cfgS20) (18 + 2 * j), e2]
    rfl
  have hpt : (accCS M (pbB cfgS20)).pt.map Lvm.e2OfFE = (Lvm.pubXTS x).accIn.pt.map Lvm.e2OfFE := by
    simp only [accCS, Lvm.pubXTS, Lvm.pubOfWS, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    exact hl j (by omega)
  have hy : Lvm.e2OfFE (accCS M (pbB cfgS20)).y = Lvm.e2OfFE (Lvm.pubXTS x).accIn.y := by
    simp only [accCS, Lvm.pubXTS, Lvm.pubOfWS]
    exact hl Lvm.VEq.accVT (by decide)
  rw [hpt, hy]
  have hc : cacheS20 = Lvm.Typed.cacheWX QS20 layS20 := cacheWXF_eq QS20 layS20 S.st.hlay
  show Lvm.E2T.PhiQGC cacheS20 _ = _
  rw [hc, Lvm.E2T.PhiQGC, Lvm.Typed.KT.PhiQGC_eqW QS20 layS20 S.st.hlay S.st.cache (hc ▸ hlin) _
    (by rw [List.length_map]; exact H.acc x)]
  have hpt' : Lvm.E2T.accPtT (Lvm.pubXTS x) = ((Lvm.pubXTS x).accIn.pt.map Lvm.e2OfFE).map FE2.toE2 := by
    rw [Lvm.E2T.accPtT, List.map_map]; rfl
  have hy' : Lvm.E2T.accYT (Lvm.pubXTS x) = FE2.toE2 (Lvm.e2OfFE (Lvm.pubXTS x).accIn.y) := rfl
  have hof : ∀ z : FE2, Lvm.Typed.ofE2 (FE2.toE2 z) = z := fun _ => rfl
  rw [Lvm.E2T.AccOkTT, Lvm.Typed.PhiQT, hpt', hy', List.map_map] at hacc
  simp only [Function.comp_def, hof, List.map_id'] at hacc
  exact FE2.toE2_injective hacc

end PairSH

/-- The mini-bus's table rounds at S2GS lie within the bus's point (`T.mbR = 6 ≤ 12`, `mbLinG_ok`'s `hpt`). -/
theorem mbR_leS20 (S : NodeGS) : tdataS20.mbR ≤ P20S.busDepth := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgS20 frzS20) = mbTOf cfgS20 frzS20 := Lvm.Har.mbT_sumcheck cfgS20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨-, t2, -, -⟩ := Lvm.Har.tdataOf_mb cfgS20 frzS20
  show (Lvm.QTyped.tdataOf cfgS20 frzS20).mbR ≤ _
  rw [t2, ← hR, show cfgS20.p = P20S from rfl]
  decide

/-- **Q_arith is `V_S`'s decision at S2GS** (`harithL20`'s twin; SLF-STMT 7e's text at RE-FREEZE R2, closed in
`LvmS2GSStmtC` by this lemma): the program's segments after Q_sig on a good S2GS pair whose `qr` is `qm`'s stream
block. -/
theorem harithS20H (S : NodeGS) (hhar : harChkBS20 = true) (hlin : Lvm.Typed.KT.linOkX cacheS20 = true)
    (H : THypS TiS20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 →
      GoodTS TiS20 H x qm qr ∧ SBlkU qm qr →
      InMapMBS (spongeBlocks P20S) (pubLanesS P20S) cfgS20 (memTX TiS20 Lvm.pubXTS x qm qr) vk x qm qr →
      LaneLink P20S (wsC qr) → LinkOk P20S (decode P20S (wsC qr)) →
      Ok (ctxOf TiS20.Q) (memTX TiS20 Lvm.pubXTS x qm qr) qaS20 p2S20H →
      decideFSX NTS20 vk (hdrOf x).cL (traceBytesB (decode P20S (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  obtain ⟨sig, hsig⟩ : ∃ s, traceBytesB (decode P20S (wsC qr)) = s := ⟨_, rfl⟩
  rw [hsig]
  -- the program's three parts after Q_sig: the pin, the front, `qarithS`
  have hrun' : Lvm.QSig.Ok (ctxOf TiS20.Q) (memTX TiS20 Lvm.pubXTS x qm qr)
      (pinF cfgS20.p >>= fun pin ↦ frontS cfgS20 >>= fun o ↦ qarithS cfgS20 tdataS20 pin o)
      (p2S20H) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2S20H).adv
      (pinF cfgS20.p (p2S20H)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgS20.p (p2S20H)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontS cfgS20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontS cfgS20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkS20_sound hhar
  have hS : Lvm.Q1.Streamed (memTX TiS20 Lvm.pubXTS x qm qr) sig (streamLanes P20S) := hsig ▸ streamedS hin.stream hLL
  have hTl : streamLanes P20S = 67167 := sizes_P20S.1.2.2.2.1
  have hg : (memTX TiS20 Lvm.pubXTS x qm qr).k (pbB cfgS20) = 1 := hin.flag
  have hvk := vk_cellsS hin.pub (okSL_vk hok)
  -- `qarithS`: the constants
  unfold qarithS at hQa
  obtain ⟨hZ, hR⟩ := Lvm.Har.okb hQa
  have ez : (const .E 0 (kc 0) q2).1 = ec q2.e := rfl
  have hzv := (Lvm.Har.constE_val hZ.1).trans ofK_zero
  rw [ez] at hzv
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hO, hR⟩ := Lvm.Har.okb hR
  have eo : (const .E 1 (kc 0) ⟨q2.k, q2.e + 1⟩).1 = ec (q2.e + 1) := rfl
  have hov := (Lvm.Har.constE_val hO.1).trans ofK_one
  rw [eo] at hov
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hZK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, Lvm.Har.constK_adv] at hR
  obtain ⟨hOK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, Lvm.Har.constK_adv] at hR
  have hzkv : (kc q2.k).val (memTX TiS20 Lvm.pubXTS x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memTX TiS20 Lvm.pubXTS x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  -- the typed phases (`typed_phaseTS` at `P20S`), their claims, the shape cell
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hDd, hfix⟩ := miniS20 S
  have hpowA := powOkS S H hG.1 hS (L := powS20) (fun a ha => ha) hPW
  have hpowT : Lvm.Q1.PowOkV (feAt sig) (typedChalsT P20S) := fun a ha =>
    hpowA a (List.mem_append_right _ ha)
  have hpowF : Lvm.Q1.PowOkV (feAt sig) (powFrontU P20S) := fun a ha => hpowA a (List.mem_append_left _ ha)
  have hDL : tdataS20.mbD = P20.busDepth := by
    rw [show tdataS20.mbD = cfgS20.p.busDepth from hDd]
    rfl
  have htyped := typed_phaseTS P20S rfl rfl (c := ctxOf TiS20.Q) vk (hdrOf x).cL hS hg hvk (z := ec q2.e)
    (o := ec (q2.e + 1)) (zk := kc q2.k) (ok := kc (q2.k + 1)) rfl rfl hzv hov rfl rfl hzkv hokv htd P20 rfl hDL
    (Lvm.E2T.m3G NTS20 P20S) (busLanes_of busLanesB_P20S) hpowT (by rw [hTl] at hTT ⊢; exact hTT)
    (by rw [hTl]; decide) _ (by simp) hTy (fun _ => rfl) (Lvm.E2T.typedItemsND NTS20 P20S)
  rw [show cfgS20.p = P20S from rfl] at ht
  -- the typed gadget's shape and its three claims (7c at the bus's outputs, `mbLinG_ok`)
  have hpbE : Lvm.pubOfWS vk (hdrOf x).cL sig = Lvm.pubOfWS vk (hdrOf x).cL sig := rfl
  have hfxL : tdataS20.mbFix = mbFixOf cfgS20 := (Lvm.Har.tdataOf_mb cfgS20 frzS20).2.2.2
  have hsh := Lvm.Har.soundG_ok (typedGS_shape (c := ctxOf TiS20.Q) (M := memTX TiS20 Lvm.pubXTS x qm qr) tdataS20
      P20S (pbB cfgS20)
    (pubLanesS P20S) (ec q2.e) (ec (q2.e + 1)) (kc q2.k) (kc (q2.k + 1)) (hDd.trans rfl)
    (fun bc cs => cs.map (Lvm.Har.CClaim.val (memTX TiS20 Lvm.pubXTS x qm qr)) = (Lvm.M3.mbClaimsN CMain.nu20
        NTS20.toN.mbT
      ⟨Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.al, bc.be.val (memTX TiS20 Lvm.pubXTS x qm qr), bc.cnt.val
          (memTX TiS20 Lvm.pubXTS x qm qr),
        Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.pt, Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.vals, [0],
        Lvm.pubOfWS vk (hdrOf x).cL sig⟩).map (fun b => (Com.main, b)) ∧
      ∀ cc ∈ cs, cOkB (ec q2.e) cc = true ∧ cc.com = .main)
    (fun bc h1 h2 h3 h4 => by
      have hal2 : 2 ≤ (Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.al).length := by
        show 2 ≤ (bc.al.map _).length
        rw [List.length_map, h1]; decide
      have hA := mbLinG_sound' (c := ctxOf TiS20.Q) hzv hov rfl rfl NTS20.toN.mbT tdataS20 hsc hSs hfix H.lin bc
        ⟨Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.al, bc.be.val (memTX TiS20 Lvm.pubXTS x qm qr), bc.cnt.val
            (memTX TiS20 Lvm.pubXTS x qm qr),
          Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.pt, Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) bc.vals, [0],
          Lvm.pubOfWS vk (hdrOf x).cL sig⟩ rfl rfl rfl rfl hal2 h2 h3
        (by rw [S.mb]; exact mbT_slots cfgS20 frzS20.wordK _ _ hal2)
        (by rw [S.mb]; exact mbT_cnt cfgS20 frzS20.wordK _ _)
        (by rw [S.mb, hfxL]; exact mbFixOf_exact cfgS20 frzS20.wordK _ _)
      have hB := mbLinG_ok (c := ctxOf TiS20.Q) (M := memTX TiS20 Lvm.pubXTS x qm qr) (zc := ec q2.e) (z := ec q2.e)
        (o := ec (q2.e + 1)) (bc := bc) hTR (by rw [h4]; exact mbR_leS20 S)
      exact fun q hH hA' => ⟨hA q hH hA', hB q hH⟩)) hTy
  rw [ht] at hsh htyped
  obtain ⟨⟨⟨hry, hryK⟩, ⟨hrr, hrrK⟩, hvR, hrvK⟩, htab, hcs, hcok⟩ := hsh
  rw [hTE] at htyped
  have hle : typedPosF P20S ≤ typedEndL tdataS20 P20S := by
    have h1 := mbPT_leL tdataS20 P20S
    have h2 := (busLanes_of busLanesB_P20S).mb
    have h3 : mbPT P20S = 8 * busL P20S iMB - 40 := rfl
    omega
  -- the pin (`pin_phase`)
  have hnu : P20S.nuMain = 23 := rfl
  have hpb := pinHPS
  have hpe := pinEndS
  have hqa := pinQaS
  rw [hnu] at hpe hqa
  have epin : pinF cfgS20.p = Lvm.Q2.pinG 23 (phaseLane P20S .commit 1) (phaseLane P20S .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20S .commit 1) (phaseLane P20S .commit (23 + 1))
    (p2S20H)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 sig ⟨posOf P20S 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) zP) (aP.val (memTX TiS20 Lvm.pubXTS x qm
          qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs and its phases (`front_phasesS` at `cfgS20`, V_S's intervals `contIvS aSP`)
  have hT29 : 29 ≤ streamLanes P20S := by rw [hTl]; norm_num
  obtain ⟨hrD, hrY, hrM⟩ := rowWordsS S H hG.1
  have hch := childOkS S H hok hb hG
  have hone : (NTS20.toN.instL Pub.hdrLanesT QS20 layS20).src? layS20.one = some .one := H.ok.2
  have hon := outsOnCS S Pub.hdrLanesT Lvm.pubXTS hone (hWS S H hG.1)
  have hsb := sBits_onC hon
  obtain ⟨hnb, hn, hsbv⟩ := frontInsS hS hT29 (sigBits_ofC cfgS20 hon ⟨by decide, by decide⟩)
    hch hsb Lvm.VEq.accVT vk (hdrOf x).cL rfl rfl
  have hh : (Lvm.pubOfWS vk (hdrOf x).cL sig).h =
      (List.range 4).map fun l => (memTX TiS20 Lvm.pubXTS x qm qr).k (Lvm.Har.hLane l) := Lvm.Har.pub_h hS hT29 vk
          (hdrOf x).cL
  have hsmE : TypedV.smallT P20S (Lvm.pubOfWS vk (hdrOf x).cL sig) =
      decide ((Lvm.pubOfWS vk (hdrOf x).cL sig).n ≤ 2 ^ 18) := rfl
  obtain ⟨tp, htape, hfrel, hmbv⟩ := front_phasesS (p := P20S) cfgS20 rfl frontPF_P20S (Lvm.E2S.contIvS Lvm.E2S.aSP)
      ivsS20 hS hTO hg hpowF hrD hrY hrM
    (Lvm.pubOfWS vk (hdrOf x).cL sig) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20S (Lvm.pubOfWS vk (hdrOf x).cL sig))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK`
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hsK : sK.val (memTX TiS20 Lvm.pubXTS x qm qr) =
      if TypedV.smallT P20S (Lvm.pubOfWS vk (hdrOf x).cL sig) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one,
      add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memTX TiS20 Lvm.pubXTS x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, true⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memTX TiS20 Lvm.pubXTS x qm qr)).c₀, ((kc q2.k).val (memTX TiS20 Lvm.pubXTS x qm
        qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memTX TiS20 Lvm.pubXTS x qm qr)).c₀, ((kc q2.k).val (memTX TiS20 Lvm.pubXTS x qm
        qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memTX TiS20 Lvm.pubXTS x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memTX TiS20 Lvm.pubXTS x qm qr) zP) (aP.val (memTX TiS20 Lvm.pubXTS x qm
          qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases' (S2GT's halves, no table claims), the three claims (7c), then the front's
  have hz2 : (⟨kc q2.k, kc q2.k⟩ : C2).val (memTX TiS20 Lvm.pubXTS x qm qr) = 0 := by
    show (⟨((kc q2.k).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 0; rw [hzkv]; rfl
  have ho2 : (⟨kc (q2.k + 1), kc q2.k⟩ : C2).val (memTX TiS20 Lvm.pubXTS x qm qr) = 1 := by
    show (⟨((kc (q2.k + 1)).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 1; rw [hokv, hzkv]; rfl
  have hrelT := typed_relT (c := ctxOf TiS20.Q) (M := memTX TiS20 Lvm.pubXTS x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20S (Lvm.pubOfWS vk (hdrOf x).cL sig)) (N := NTS20) (p := P20S)
    (m := Lvm.E2T.m3G NTS20 P20S) (pub := Lvm.pubOfWS vk (hdrOf x).cL sig) (T := tdataS20)
    (sOff := (layout0 cfgS20.p).s) (t := t.1) (z := ec q2.e) hzv hz2 ⟨rfl, rfl⟩ ho2 ⟨rfl, rfl⟩ htd hTR rfl rfl rfl
    hry hryK hrr hrrK hvR hrvK (by rw [htab]; simp)
    (st := Lvm.M3.sumcheckTabs NTS20.mbT) (by rw [show NTS20.mbT = NTS20.toN.mbT from rfl, hsc]; exact hSs)
    (m3G_tableClaimsT _ _ _ _)
  have hlinR := lin_rel (M := memTX TiS20 Lvm.pubXTS x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20S (Lvm.pubOfWS vk (hdrOf x).cL sig)) (tabs := Lvm.M3.sumcheckTabs NTS20.mbT)
    (by rw [show NTS20.mbT = NTS20.toN.mbT from rfl, hsc]; exact hcs) (fun cc hc => (hcok cc hc).1)
  have hTC' := hTC.1
  unfold typedClaimsGL at hTC' htc
  obtain ⟨l, -, hl, -, hl1, -⟩ := ok_bindV hTC
  have htcE : tc = l ++ t.2.map Lvm.Q2.FClaim.e3 := by rw [← htc, bind_apply, hl]; rfl
  have hrl := hrelT q3 hl1.1
  rw [hl, htab] at hrl
  simp only [List.map_nil, m3G_tableClaimsT, Lvm.M3.tableClaimsR, List.zip_nil_right, Shape.zeroTails,
    List.map_nil, List.flatMap_nil, List.append_nil] at hrl
  have htrel := List.rel_append hrl hlinR
  beta_reduce at htrel
  rw [← htcE] at htrel
  have hrel := List.rel_append htrel hfrel
  -- the opening's static inputs
  have hopenU : posOf P20S (phaseItem0 P20S .openMain) =
      8 * (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOk (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)) (streamLanes P20S) =
      true := by
    rw [layOkF_pb P20S _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOk (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)) (memTX TiS20 Lvm.pubXTS
      x qm qr)
      sig 0 (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).levels
      ((cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20S (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).g
        (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).ood
        (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).levels
        ((cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).U + 15) 0 := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    rw [← hsig]
    exact posOk_ofG P20S cfgS20 rfl _ 0 (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL' streamOk_P20S hLL hQS20
      (posCellsS S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)) (memTX TiS20 Lvm.pubXTS x
      qm qr) 0
      (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    exact pw_onC hon hGR i (lt_of_lt_of_le hi hML)
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).g
      (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).ood
      (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).levels
      ((cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)).U + 15) = sig.size := by
    rw [← hsig, sigS_size hLL, stackEnd_cfgMainF]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgS20.p = P20S from rfl] at hOpen
  -- `core_of_phasesL`, the opening by `open_phase`
  refine Lvm.Har.decideFSG_of P20S P20 Lvm.E2S.aSP NTS20 vk (hdrOf x).cL sig ?_ (phiS20_acc S hlin H hG.1 hin.pub)
  refine Lvm.Har.core_of_phasesS P20S P20 Lvm.E2S.aSP NTS20 vk (hdrOf x).cL sig hbS hpin htyped htape ?_
  intro s hs hsok
  rw [Lvm.E2T.typedItemsND_flat]
  dsimp only
  rw [show (Lvm.E2T.m3G NTS20 P20S).busFinal = Lvm.M3.busFinalR (Lvm.M3.sumcheckTabs NTS20.mbT) from rfl,
    show P20S.nuMain = CMain.nu20 from rfl]
  have key := Lvm.Q2.open_phase P20S (cfgMainF P20S (Lvm.Har.posBase cfgS20) (Lvm.Har.pwBase cfgS20)) rfl rfl rfl
    rfl rfl hF pin hpt _ _ hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgS20)) hsK hS hlayO
    (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO hq7 hOpen s (hs.trans hopenU) hsok
  beta_reduce at key
  rw [hnu] at key
  dsimp only at key
  exact key

end Lvm.E2Q
