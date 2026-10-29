-- New for `flock-recursive` (BLUEPRINT A.9 `finLc`, A.10; stage S-G12′, S-G11 handover §7 item 1b).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessFrWalk
import FRSoundnessFrRndV
import FRSoundnessFrW0V
import FRSoundnessCoreAcc

/-!
# `finLc` (ii) on an accepted run: the lincheck's last claim is the per-kind sum

On every accepted run of `gen (sfFinals finP finPf)` whose `walkAB`, `rowW` and `eqZ` meet their
specifications, L2's last claim is `Σ_j vM_j · M̃_j(r_k)` (`lc_ii_run`). So neither the leaf's
`finLc` (ii) doom `RejLc2` nor the node's `RejLcN` holds on an accepted run (`accFront_rejLc2`,
**`accFront_rejLcN`**: `NodeL.front` for `nodeLF`, S-G11's item 4).

The registers `finLc` reads, on the log (`SkRun`):
* L2's challenges are `rkL` (`lc_rk`), Z3's first eight `rhiL` (`lc_rhi`), Z2's `λ` is `lamL`
  (`lc_lam`), L1's `α` is `alL` (`lc_alpha`), L3's eight values are `vL` (`lc_v`);
* L2's last claim register holds `rValF 69 es 13`, which is `clR2 … 14` (`lc_claimN`).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

theorem phStart_lc : phStart 4 = 13 ∧ phStart 7 = 68 ∧ phStart 9 = 97 := by
  simp only [phStart, fsStarts_eq]; decide

theorem mm6_ge8 (κ : Kind) : 8 ≤ mm 6 κ ∧ mm 6 κ ≤ 26 := by cases κ <;> decide

theorem val_eqv_f {a : F} {v : Val} (h : (Val.f a).eqv v = true) : v = .f a := by
  cases v <;> simp_all [Val.eqv]

section Views
variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- L2's challenges are `rkL`. -/
theorem lc_rk : lcRk fi R = rkL (fsOf tr items) := by
  have hl := chals_len (n := 8) (by rw [phases_length]; omega) rfl hfi phaseIx_vals.2.2.2.2.1
  apply List.ext_getElem (by simp [lcRk, rkL, rchs, hl])
  intro i h1 h2
  simp only [lcRk, List.length_map, hl] at h1
  have hv := (chalsF_view h (n := 8) (by rw [phases_length]; omega) rfl (by decide) (by norm_num) hfi
    phaseIx_vals.2.2.2.2.1 hR h1).2
  rw [frW0_starts.2.2.1] at hv
  simp only [lcRk, rkL, rchs, List.getElem_map, List.getElem_range]
  rw [← List.getD_eq_getElem _ 0]
  show (rd R _).toF = _
  rw [hv]; rfl

/-- Z3's first eight challenges are `rhiL`. -/
theorem lc_rhi : ptA 8 (lcRhi fi R) = rhiL (fsOf tr items) ∧ (lcRhi fi R).size = 8 := by
  have hl := chals_len (n := 5) (by rw [phases_length]; omega) rfl hfi phaseIx_vals.2.2.1
  refine ⟨funext fun i => ?_, by simp [lcRhi, hl]⟩
  have hv := (chalsF_view h (n := 5) (by rw [phases_length]; omega) rfl (by decide) (by norm_num) hfi
    phaseIx_vals.2.2.1 hR (j := i) (by omega)).2
  rw [frW0_starts.2.1] at hv
  have hm := mm6_ge8 (kindOf (fsOf tr items))
  simp only [ptA, lcRhi, rhiL, ptOf, rZ, rchs, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_take, List.getD_eq_getElem?_getD, List.getElem?_range,
    show (i : ℕ) < 8 from i.isLt, show (i : ℕ) < mm 6 (kindOf (fsOf tr items)) by omega, if_true,
    Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem?_getD] at hv
  rcases hc : (chals fi "Z3" 26)[(i : ℕ)]? with _ | x
  · rw [List.getElem?_eq_none_iff] at hc; omega
  · rw [hc, Option.getD_some] at hv
    simp only [Option.map_some, Option.getD_some, fv, hv]; rfl

/-- Z2's `λ` is `lamL`. -/
theorem lc_lam : fv R ((outsOf fi "Z2").headD 0) = lamL (fsOf tr items) ∧
    (outsOf fi "Z2").headD 0 < (#[] ++ y.1.toArray).size := by
  obtain ⟨b, hb, hlt, hv⟩ := uni_view h (n := 4) (by rw [phases_length]; omega) rfl (by decide)
  have he : (outsOf fi "Z2").headD 0 = b + 3 := by rw [outsOf, hfi, phaseIx_vals.2.1, hb]
  rw [he, phStart_lc.1] at *
  exact ⟨by rw [fv, hR.rd hlt, hv]; rfl, hlt⟩

/-- L1's `α` is `alL`. -/
theorem lc_alpha : fv R ((outsOf fi "L1").headD 0) = alL (fsOf tr items) ∧
    (outsOf fi "L1").headD 0 < (#[] ++ y.1.toArray).size := by
  obtain ⟨hlt, hv⟩ := oneR_view h (n := 7) (by rw [phases_length]; omega) rfl hfi
    phaseIx_vals.2.2.2.1 hR
  rw [phStart_lc.2.1] at hv
  exact ⟨by rw [fv, hv]; rfl, hlt⟩

/-- L2's last claim register holds `clR2 … 14`. -/
theorem lc_claimN (c0 : Log → Log → F) (L : Log) :
    rd R (claimN fi "L2") = .f (clR2 69 16 readF (fun d => chF d 0) c0 L (fsOf tr items) 14) ∧
      claimN fi "L2" < (#[] ++ y.1.toArray).size ∧ claim0 fi "L2" < (#[] ++ y.1.toArray).size := by
  obtain ⟨b, hout, hsz, -, hlast, -⟩ := roundsF2_view h (n := 8) (by rw [phases_length]; omega) rfl rfl
    (by decide) (by norm_num) (by cases κ <;> decide) (by norm_num)
  have ho : outsOf fi "L2" = (b + 2) :: (List.range 14).map (fun j => b + 13 * j + 6) ++
      [b + 13 * 14 + 2] := by rw [outsOf, hfi, phaseIx_vals.2.2.2.2.1, hout]
  have hN : claimN fi "L2" = b + 13 * 14 + 2 := by
    rw [claimN, ho, List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton]; simp
  have h0 : claim0 fi "L2" = b + 2 := by rw [claim0, ho, List.cons_append, List.headD_cons]
  rw [frW0_starts.2.2.1] at hlast
  refine ⟨?_, by rw [hN]; exact lt_of_lt_of_le (Nat.lt_succ_self _) hsz,
    by rw [h0]; exact lt_of_lt_of_le (by omega : b + 2 < b + 13 * 14 + 3) hsz⟩
  rw [hN, hR.rd (lt_of_lt_of_le (Nat.lt_succ_self _) hsz), hlast, ← rValF_eq_clR2 69 c0 L]

end Views

/-! ## L3's values -/

theorem lc_v {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2) :
    lcV ⟨vk, c, π⟩ = (List.range 8).map (vL es) := by
  have hm := msgAt_abs hq (n := 9) (by rw [phases_length]; omega) rfl (by norm_num)
  rw [phStart_lc.2.2] at hm
  unfold lcV
  rw [phaseIx_L3]
  refine List.map_congr_left fun i hi => ?_
  have hi8 := List.mem_range.1 hi
  rw [vL, hm, readF, bytesAt_extract_n _ (by omega), pe, absOff_eq (by decide), Nat.add_assoc]

/-! ## `finLc` (ii) on an accepted run -/

/-- **L2's last claim is the per-kind lincheck sum on every accepted run** (`finLc` (ii) through
the walk bridge, revision 3.16): for `walkAB`, `rowW`, `eqZ` at their specifications. -/
theorem lc_ii_run {impl : OpImpl}
    (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {vk c : Digest} {π : Proof} {k : Kind} {tr : Trace} (L : Log) (hk : FR.kindOf π = .snark k)
    (hsem : semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr items) 14 =
      ∑ j, vM (kindOf (fsOf tr items)) (fsOf tr items) j *
        mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rwL (fsOf tr items)) (alL (fsOf tr items)))
          (ptOf 14 (rkL (fsOf tr items))) := by
  obtain ⟨y, hy, hfl, hn, L₀, hRS, Rs, h0, hrest⟩ :=
    accept_chain impl k ⟨vk, c, π⟩ _ noAsk_sf hsem
  obtain ⟨hl, hq⟩ := fsQ_gen ⟨vk, c, π⟩ impl _ _ hsem
  have hS : SkRun impl k ⟨vk, c, π⟩ tr y := ⟨hy, hfl, hl, hq⟩
  have hkind : kindOf (fsOf tr items) = k := kindOf_fsQ hq hk
  have hpos := skel_pos hS
  set fi₀ : FinIn := ⟨skeleton.2.outs, [], #[]⟩
  have hext : ∀ j < (sfFinals finP finPf).rest.length, ExtA (Rs j) (Rs (j + 1)) := fun j hj => by
    obtain ⟨L, -, he⟩ := hrest j hj; rw [he]; exact ExtA.app _ _
  have h1 : 1 < (sfFinals finP finPf).rest.length := by rw [rest_eq]; simp
  have hE01 : ExtA (Rs 0) (Rs 1) := hext 0 (by omega)
  rw [h0] at hE01
  have hE1 : ExtA (#[] ++ y.1.toArray) (Rs 1) := (ExtA.app _ L₀).trans hE01
  obtain ⟨L1, hp1, -⟩ := hrest 1 h1
  rw [rest_get (by rw [rest_eq]; rfl : (sfFinals finP finPf).rest[1]? = some finLc)] at hp1
  rw [hn] at hRS
  have hl₀ := pureRun_len impl k ⟨vk, c, π⟩ _ _ [] L₀ true hRS
  suffices H : ∀ fi : FinIn, fi.outs = skeleton.2.outs →
      fi.zhat = (finRS fi₀ (#[] ++ y.1.toArray).size).2 →
      pureRun impl k ⟨vk, c, π⟩ (finLc fi (Rs 1).size).1 (Rs 1) [] = some (L1, true) →
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr items) 14 =
        ∑ j, vM (kindOf (fsOf tr items)) (fsOf tr items) j *
          mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rwL (fsOf tr items)) (alL (fsOf tr items)))
            (ptOf 14 (rkL (fsOf tr items))) from H _ rfl (by rw [← hn]; rfl) hp1
  intro fi hfi hzh hp
  have hzlt : fi.zhat.getD 1 0 < (Rs 1).size := by
    have hsz : ((#[] ++ y.1.toArray) ++ L₀.toArray).size =
        (#[] ++ y.1.toArray).size + opsOut (finRS fi₀ (#[] ++ y.1.toArray).size).1 := by
      simp [hl₀]; rfl
    refine lt_of_lt_of_le ?_ hE01.1
    rw [hzh, hsz]
    exact getD_lt_of (finRS_ex_lt fi₀ _) (Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)) 1
  have hsk : ∀ name, ∀ x ∈ outsOf fi name, x < (Rs 1).size := fun name x hx =>
    lt_of_lt_of_le (outsR_lt hS hfi name x hx) hE1.1
  obtain ⟨L', hL'⟩ := flag_finLc impl k ⟨vk, c, π⟩ fi (Rs 1) (by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((hx | hx) | hx | hx | hx | hx | hx | hx)
    · exact hsk "Z3" x (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take hx)))
    · exact hsk "L2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    · subst hx; exact headD_lt (hsk "L1") (lt_of_lt_of_le hpos hE1.1)
    · subst hx; exact headD_lt (hsk "L3β") (lt_of_lt_of_le hpos hE1.1)
    · subst hx; exact headD_lt (hsk "Z2") (lt_of_lt_of_le hpos hE1.1)
    · subst hx; exact headD_lt (hsk "L2") (lt_of_lt_of_le hpos hE1.1)
    · subst hx; exact getLastD_lt (hsk "L2") (lt_of_lt_of_le hpos hE1.1)
    · subst hx; exact hzlt)
  have hrel : relLc impl k ⟨vk, c, π⟩ fi (Rs 1) = true := pureRun_det hp hL'
  unfold relLc at hrel
  simp only [Bool.and_eq_true] at hrel
  have h3 := val_eqv_f hrel.2
  rw [(lc_claimN hS hfi hE1 (fun _ es => c0L es) L).1, Val.f.injEq] at h3
  rw [h3]
  -- the bridge
  obtain ⟨hlam, -⟩ := lc_lam hS hfi hE1
  obtain ⟨hal, -⟩ := lc_alpha hS hfi hE1
  obtain ⟨hrhi, hrhi8⟩ := lc_rhi hS hfi hE1
  have hrk := lc_rk hS hfi hE1
  have hv := lc_v (π := π) hq
  have hrkl : (lcRk fi (Rs 1)).length = 14 := by rw [hrk]; simp [rkL, rchs]
  have hb := lc_bridge hW hR hZ k (v := lcV ⟨vk, c, π⟩) (by simp [lcV]) (lcVf k ⟨vk, c, π⟩)
    (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (fv (Rs 1) ((outsOf fi "L1").headD 0)) (lcRhi fi (Rs 1))
    hrhi8 (lcRk fi (Rs 1)) hrkl
  simp only at hb
  have hlhs : lcWalk impl k ⟨vk, c, π⟩ fi (Rs 1) + (lcFree impl k ⟨vk, c, π⟩ fi (Rs 1) +
      fv (Rs 1) ((outsOf fi "L1").headD 0) * lcFree impl k ⟨vk, c, π⟩ fi (Rs 1)) =
      (impl.walkAB (maskRows (lcWts k (lcV ⟨vk, c, π⟩)).toArray
          (impl.rowW (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (lcRhi fi (Rs 1))))
          (eqTab (lcRk fi (Rs 1)).toArray)).1 +
        fv (Rs 1) ((outsOf fi "L1").headD 0) * (impl.walkAB (maskRows (lcWts k (lcV ⟨vk, c, π⟩)).toArray
          (impl.rowW (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (lcRhi fi (Rs 1))))
          (eqTab (lcRk fi (Rs 1)).toArray)).2 +
        (lcVf k ⟨vk, c, π⟩ * (dotAcc 0 (impl.eqZ (fv (Rs 1) ((outsOf fi "Z2").headD 0)) 0)
            (eqTab ((lcRk fi (Rs 1)).take 6).toArray) 64 *
          eqPoint (lcRhi fi (Rs 1)) ((lcRk fi (Rs 1)).drop 6).toArray) +
         fv (Rs 1) ((outsOf fi "L1").headD 0) * (lcVf k ⟨vk, c, π⟩ *
          (dotAcc 0 (impl.eqZ (fv (Rs 1) ((outsOf fi "Z2").headD 0)) 0)
            (eqTab ((lcRk fi (Rs 1)).take 6).toArray) 64 *
          eqPoint (lcRhi fi (Rs 1)) ((lcRk fi (Rs 1)).drop 6).toArray))) := by
    simp only [lcWalk, lcFree, lcRk, lcWts, List.map_take, List.map_drop]
  rw [hlhs, hb, hlam, hal, hrhi, hrk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lcWts_vM k (by simp [lcV]) _ (by simp only [lcVf]; split <;> simp [lcV]), hkind, hv]
  simp only [vM]
  split
  · split
    · rfl
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp only [List.getElem_map, List.getElem_range]; rfl
  · split
    · rw [List.getD_eq_getElem _ _ (by simp)]; simp only [List.getElem_map, List.getElem_range]; rfl
    · rfl

/-! ## The front's Lc checks on accepted runs -/

/-- **A check holds on every accepted run's chain of a proof of kind `k`** (`AccFront` with the
proof's kind byte: `hAcc_of_fin(R)` calls its `hFront` only under `FR.kindOf π = .snark k`; the
log's kind `kindOf es` is the program's `k` only then, `kindOf_fsQ`). -/
def AccFrontK (impl : OpImpl) (vk : Digest) (R : Log → Log → Prop) : Prop :=
  ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
    π.size = piSize → FR.kindOf π = .snark k →
    semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
    (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
    ¬ R L (entriesOf L (pathOf L j))

/-- `AccFront` gives `AccFrontK` (one more hypothesis). -/
theorem accFrontK_of {impl : OpImpl} {vk : Digest} {R : Log → Log → Prop} (h : AccFront impl vk R) :
    AccFrontK impl vk R := fun k c π L tr j hb hπ _ hsem hin hci heq => h k c π L tr j hb hπ hsem hin hci heq

section Lc
variable {impl : OpImpl}
    (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
include hW hR hZ

/-- **The node's `finLc` (ii) on accepted runs** (`NodeL.front` for `nodeLF`, S-G11's item 4). -/
theorem accFrontK_rejLcN (vk : Digest) : AccFrontK impl vk RejLcN := by
  intro k c π L tr j _ _ hk hsem _ _ heq h
  rw [heq] at h
  exact h.2.2 (lc_ii_run hW hR hZ L hk hsem)

/-- **The leaf's `finLc` (ii) on accepted runs** (`RejF`'s `RejLc2` disjunct). -/
theorem accFrontK_rejLc2 (vk : Digest) : AccFrontK impl vk (RejLc2 zlmFR) := by
  intro k c π L tr j _ _ hk hsem _ _ heq h
  rw [heq] at h
  exact h.2.2 (lc_ii_run hW hR hZ L hk hsem)

end Lc

theorem specC_rowW (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    (specC fin lRows κs₀).rowW = rowWS := by dsimp only [specC, specCWith]
theorem specC_eqZ (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    (specC fin lRows κs₀).eqZ = eqZS := by dsimp only [specC, specCWith]
theorem specC_walkAB (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (rw cw : Array F) :
    (specC fin lRows κs₀).walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw) := rfl

/-- **`implC`'s ops meet the Lc specifications**, so `RejLcN` holds on no accepted run of the
entry's verifier. -/
theorem accFrontK_rejLcN_C (κs₀ : F) (vk : Digest) :
    AccFrontK (implC (finC finPf) Layout.lRows κs₀) vk RejLcN := by
  obtain ⟨-, -, hZ, -, -, -, hW, -, -, -, -, -, -, -, -, hR, -⟩ :=
    implC_meets (finC finPf) Layout.lRows κs₀
  rw [specC_rowW] at hR; rw [specC_eqZ] at hZ; simp only [specC_walkAB] at hW
  exact accFrontK_rejLcN hW hR hZ vk

theorem accFrontK_rejLc2_C (κs₀ : F) (vk : Digest) :
    AccFrontK (implC (finC finPf) Layout.lRows κs₀) vk (RejLc2 zlmFR) := by
  obtain ⟨-, -, hZ, -, -, -, hW, -, -, -, -, -, -, -, -, hR, -⟩ :=
    implC_meets (finC finPf) Layout.lRows κs₀
  rw [specC_rowW] at hR; rw [specC_eqZ] at hZ; simp only [specC_walkAB] at hW
  exact accFrontK_rejLc2 hW hR hZ vk

/-! ## Controls -/

/-- (+) `AccFrontK` holds for the empty check. -/
theorem accFrontK_false (impl : OpImpl) (vk : Digest) : AccFrontK impl vk fun _ _ => False :=
  accFrontK_of (accFront_false impl vk)

/-- (−) `AccFrontK` is not vacuous: the check "always" fails it on any accepted run (here: it is
refuted outright, since every chain satisfies `True`). -/
theorem not_accFrontK_true (impl : OpImpl) (vk : Digest) {k : Kind} {c : Digest} {π : Proof}
    {L tr : Log} {j : ℕ} (hb : ¬ Bad L) (hπ : π.size = piSize) (hk : FR.kindOf π = .snark k)
    (hsem : semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true)
    (hin : ∀ e ∈ tr, e ∈ L) (hci : IsChain L j) (heq : entriesOf L (pathOf L j) = fsOf tr items) :
    ¬ AccFrontK impl vk fun _ _ => True := fun h => h k c π L tr j hb hπ hk hsem hin hci heq trivial

end FR.Snd
