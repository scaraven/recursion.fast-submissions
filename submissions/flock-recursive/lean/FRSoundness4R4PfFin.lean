-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`, `relPf`; track R4h). The 3.x
-- templates are the `enc`/`fin` cases of `FRSoundnessAccLog.finLog_of_run`, `fhVal_mle`, `padV_eq`,
-- `finV_zero`, `pfRefs_lt`.
import FRSoundness4R4PfFlag

/-!
# `FinRest4.fin` from INT-8's `finPf`, and `FinRest4.enc`'s zero tail

On an accepted run's fields (field 11), `flag_gFinPf4` gives **`relPf4`** (`relPf4_of_fields`).
Its parts at the spec:

* `claimN(Pf)` is `clR2 pfStart … 7` (`pf_view4`);
* **`finHat4_eq`**: `final̂(sf) = mleN 7 finalAt (pfPt es)` (`fhVal4_eq`, `eqTab_getD`, `finalAt_eq4`);
* **`padV4_eq`**: the kind's pad is `Π_{mLog ≤ v < 7} (1 − ρ_v)` (characteristic 2);
* **`tail_zero4`**: the kind's tail flag makes the final message zero beyond `2^mLog` (π's
  elements), which is `enc4_of_fields`' hypothesis.

**`fin4_of_fields`** is `FinRest4.fin` given `Ŵ₄(P₄) = wHatL W₀ L es 4` (`hW`: the level steps and
`Ŵ₀(P₀)`, handover).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## Registers -/

section Refs
variable {fi : FinIn} {N : ℕ} (hN : 0 < N) (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < N)
include hN hO

theorem gSRegs_lt (S : Seq) (i : ℕ) : ∀ x ∈ gSRegs S fi i, x < N :=
  sub_lt (lvOuts_lt hN hO i 0) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem gTailRegs_lt (S : Seq) (m k : ℕ) : ∀ x ∈ gTailRegs S fi m k, x < N := by
  intro x hx
  rw [gTailRegs, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨j, -, hx⟩ | hx
  · exact gSRegs_lt hN hO S j x (List.mem_of_mem_drop hx)
  · exact chals_lt hN hO "Pf" S.pf x (List.mem_of_mem_take hx)

theorem gP0Regs_lt (S : Seq) (m : ℕ) : ∀ x ∈ gP0Regs S fi m, x < N := by
  intro x hx
  rw [gP0Regs, List.mem_append] at hx
  rcases hx with hx | hx
  · exact gSRegs_lt hN hO S 0 x hx
  · exact gTailRegs_lt hN hO S m 1 x hx

/-- **`gPfPts` reads only the skeleton's registers** (3.x's `pfPts_lt`, every family). -/
theorem gPfPts_lt (P : FinP) : ∀ s ∈ gPfPts P fi, ∀ p ∈ s, ∀ x ∈ p.regs, x < N := by
  have hz : ∀ m, ∀ p ∈ zSrc fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app
    (by simpa [List.map_map] using srcs_c (N := N) ((List.ofFn pinnedRho).drop 1) K.ofF)
    (srcs_f (sub_lt (coordsR_lt hN hO "Z1") fun _ hx => List.mem_of_mem_take hx))
  have hlc : ∀ m, ∀ p ∈ gLcSrc P.S fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app
    (srcs_f (sub_lt (chals_lt hN hO "L2" 14) fun _ hx => List.mem_of_mem_drop hx))
    (srcs_f (sub_lt (chals_lt hN hO "Z3" P.S.z3) fun _ hx =>
      List.mem_of_mem_take (List.mem_of_mem_drop hx)))
  have hsh : ∀ m, ∀ p ∈ gShSrc P.S fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app (srcs_app
    (srcs_f (sub_lt (chals_lt hN hO "S2" P.S.s2) fun _ hx =>
      List.mem_of_mem_drop (List.mem_of_mem_take hx)))
    (by
      intro p hp x hx
      rw [List.eq_of_mem_replicate hp] at hx; simp [PtSrc.regs] at hx))
    (srcs_f (sub_lt (chals_lt hN hO "S2" P.S.s2) fun _ hx => List.mem_of_mem_take hx))
  have htl : ∀ m, ∀ s ∈ (List.range 4).map (fun k => (gTailRegs P.S fi m (k + 1)).map PtSrc.k),
      ∀ p ∈ s, ∀ x ∈ p.regs, x < N := fun m s hs => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hs; exact srcs_k (gTailRegs_lt hN hO P.S m (k + 1))
  intro s hs
  simp only [gPfPts, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((((((((((rfl | ⟨m, -, rfl⟩) | rfl) | ⟨m, -, rfl⟩) | rfl) | ⟨m, -, rfl⟩) |
    ⟨e, -, rfl⟩) | hs) | ⟨m, -, hs⟩) | rfl) | ⟨m, -, rfl⟩)
  · exact hz _
  · exact hz m
  · exact hlc _
  · exact hlc m
  · exact hsh _
  · exact hsh m
  · exact srcs_f (chals_lt hN hO "E4" e)
  · exact htl _ s (List.mem_map.2 hs)
  · exact htl m s (List.mem_map.2 hs)
  · exact srcs_k (gP0Regs_lt hN hO P.S _)
  · exact srcs_k (gP0Regs_lt hN hO P.S m)

theorem gPfPts_ok (P : FinP) : ∀ s ∈ gPfPts P fi, ∀ x ∈ s, x.Ok N := by
  intro s hs x hx
  have h := gPfPts_lt hN hO P s hs x hx
  cases x with
  | f y => exact h y (by simp [PtSrc.regs])
  | k y => exact h y (by simp [PtSrc.regs])
  | c v => trivial

theorem lvRefs_lt4 : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < N := by
  intro k _ x hx
  simp only [lvRefs, List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hx) | hx
  · exact headD_lt (sRegs_lt hN hO k) hN
  · exact kcOf_lt hN hO _ x hx
  · exact ysOf_lt hN hO _ x hx

end Refs

theorem rest_gFinPf (P : FinP) :
    (finalsOf P).rest[11]'(by rw [rest_finalsOf_length]; omega) = fun fi b => gFinPf P fi b := by
  simp only [Finals.rest, finalsOf, show 11 = 5 + 1 + 1 + 1 + 1 + 1 + 1 from rfl,
    List.getElem_cons_succ, List.nil_append, List.cons_append]
  rw [List.getElem_append_right (by simp [nLevels])]
  simp [nLevels]

/-! ## The flag on an accepted run -/

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **`finPf`'s relation on an accepted run's fields** (field 11). -/
theorem relPf4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) (hck : P.ck = true)
    (hnc : 0 < P.nc) (hnf : 0 < P.fams.length)
    (hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length) :
    relPf4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P = true := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩
  have hE := hF.ext 11 (by omega)
  have hpos := hF.pos (k := 11) (by omega)
  have hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < (Rs 11).size := fun n x hx =>
    lt_of_lt_of_le (skeleton4_out_lt p hF.sk.ref n x hx) hE.1
  obtain ⟨-, Lk, hLk, -, -⟩ := hF.fld 11 (by omega)
  rw [rest_gFinPf P] at hLk
  simp only at hLk
  rw [gFinPf_reloc P hck] at hLk
  obtain ⟨L', hL'⟩ := flag_gFinPf4 impl p.tix inp (Rs 11) P hPS hnc hnf fi hpos hO
    (gPfPts_ok hpos hO P) hix (lvRefs_lt4 hpos hO)
  exact pureRun_det hLk hL'

end Acc

/-! ## The parts at the spec -/

theorem fhVal4_eq (S : Seq) (inp : Input) (E : Array K) : ∀ (cs : List ℕ) (A : K),
    fhVal4 S inp E cs A = A + (cs.map fun c => finV4 S inp c * E.getD c 0).sum
  | [], A => by simp [fhVal4]
  | c :: cs, A => by rw [fhVal4, fhVal4_eq S inp E cs, List.map_cons, List.sum_cons, add_assoc]

/-- `final̂` over `seq4`'s final elements at `sf` (3.x's `fhVal_mle`). -/
theorem fhVal4_mle (inp : Input) (sf : Array K) (hs : sf.size = 7) :
    fhVal4 seq4 inp (eqTab sf) (List.range (2 ^ seq4.pf)) 0 = mleN 7 (finV4 seq4 inp) (fun v => sf.getD v 0) := by
  rw [fhVal4_eq, zero_add, mleN, mle, ← List.sum_toFinset _ (List.nodup_range), seq4_pf]
  · rw [List.toFinset_range, ← Fin.sum_univ_eq_sum_range]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [eqTab_getD sf (by rw [hs]; exact u.2), eq_cube, mul_comm, hs]
    congr 1

theorem list_prod_range (g : ℕ → K) : ∀ k, ((List.range k).map g).prod = ∏ i ∈ range k, g i
  | 0 => by simp
  | k + 1 => by rw [List.range_succ, List.map_append, List.prod_append, list_prod_range g k, prod_range_succ]; simp

/-- **The kind's pad at Pf's challenges** (characteristic 2: `1 + x = 1 − x`). -/
theorem padF4_eq (sfv : ℕ → K) (m : ℕ) :
    padF4 sfv 7 m = ∏ v ∈ Ico (m - 25) 7, (1 - sfv v) := by
  have h1 : ∀ x : K, 1 + x = 1 - x := fun x => by rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [padF4, list_prod_range, prod_Ico_eq_prod_range]
  exact prod_congr rfl fun i _ => h1 _

/-- **The kind's tail flag zeroes the final message beyond `2^(t − 25)`** (3.x's `finV_zero`). -/
theorem tail_zero4 {inp : Input} {P : FinP} {κ : Kind} (h : tailOk4 P κ inp = true) (hS : P.S = seq4)
    {t : ℕ} (ht : t ∈ P.tails) (hm : P.kv.m κ = t) :
    ∀ c, 2 ^ (t - 25) ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0 := by
  intro c hc1 hc2
  have hz := (List.all_eq_true.1 h) t ht
  simp only [hm, decide_true, Bool.not_true, Bool.false_or] at hz
  rw [hS] at hz
  have hz' := allZero_mem hz
  have hle : 2 ^ (t - 25) ≤ 2 ^ 7 := le_trans hc1 hc2.le
  have hb : bytesAt inp.π (fieldOffOf seq4 fFinal + 32 * c) 32 = Vector.replicate 32 0 := by
    refine Vector.ext fun k hk => ?_
    rw [getElem_bytesAt _ _ _ _ hk, Vector.getElem_replicate]
    by_cases hlt : fieldOffOf seq4 fFinal + 32 * c + k < inp.π.size
    · refine hz' _ ?_
      rw [tailBytes4, toList_extract, seq4_pf]
      set o := fieldOffOf seq4 fFinal
      have hoff : o + 32 * c + k = o + 2 ^ (t - 25) * 32 + (32 * c - 2 ^ (t - 25) * 32 + k) := by omega
      rw [hoff] at hlt ⊢
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      refine List.mem_iff_getElem.2 ⟨32 * c - 2 ^ (t - 25) * 32 + k, ?_, ?_⟩
      · simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
        generalize 2 ^ (t - 25) = A at hc1 hle hlt ⊢
        refine lt_min ?_ (by omega)
        rw [Nat.add_sub_cancel_left]; norm_num at hc2 hle ⊢; omega
      · simp
    · rw [List.getD_eq_default _ _ (by simpa using not_lt.1 hlt)]
  rw [finV4, hb]; decide

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **`final̂(sf)` on the run is `mleN 7 finalAt (pfPt es)`**. -/
theorem finHat4_eq (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) {k : ℕ} (hk : k ≤ 12) (ex : Array (List Reg)) :
    finHat4 inp ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ (Rs k) P =
      mleN 7 (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.pfPt (fsOf tr (itemsOf seq4))) := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩
  have hE := hF.ext k hk
  obtain ⟨hpv, hpl, -, -, hpo, -⟩ := pf_view4 hF.sk (fi := fi) rfl
  have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
    unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  rw [finHat4, hPS, fhVal4_mle _ _ (by simp [seq4_pf, hpl])]
  unfold mleN
  have e1 : (fun u : Fin (2 ^ 7) => finV4 seq4 inp u) = fun u : Fin (2 ^ 7) => T4.finalAt (fsOf tr (itemsOf seq4)) u := by
    funext u; exact (finalAt_eq4 hF.sk u.2).symm
  have e2 : (fun v : Fin 7 => (((chals fi "Pf" seq4.pf).map fun x => (rd (Rs k) x).toK).toArray).getD v 0) =
      T4.pfPt (fsOf tr (itemsOf seq4)) := by
    funext v
    have hv := v.2
    rw [seq4_pf]
    have hmem : (chals fi "Pf" 7)[v.val]'(by rw [hpl]; exact hv) ∈ outsOf fi "Pf" := hch _ (List.getElem_mem _)
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [hpl]; exact hv : (v : ℕ) < _), Option.map_some, Option.getD_some]
    have := hpv v hv
    rw [List.getD_eq_getElem _ _ (by rw [hpl]; exact hv)] at this
    rw [hE.rd (hpo _ hmem), this]; rfl
  rw [e1, e2]

/-- **`FinRest4.fin`** on the fields, given `Ŵ₄(P₄)` at the spec (`hW`) and the kind's pad family
(`hpad`: `m*` with no pad, or the family `m` of the chain's kind). -/
theorem fin4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) (hck : P.ck = true)
    (hnc : 0 < P.nc) (hnf : 0 < P.fams.length)
    (hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length)
    (hpad : (P.kv.selA p.tix = true ∧ (kindOfC (fsOf tr (itemsOf seq4))).m = 32) ∨
      (P.kv.selA p.tix = false ∧ P.fams.getD (famI P p.tix) 0 = (kindOfC (fsOf tr (itemsOf seq4))).m))
    {W₀ : Log → Log → ℕ → K} {L : Log}
    (hW : wV4 impl p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) (c₀ : Log → Log → K) :
    clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L (fsOf tr (itemsOf seq4)) 7 =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4 *
        (∏ v ∈ Ico (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4) 7, (1 - T4.pfP (fsOf tr (itemsOf seq4)) v)) *
          mleN 7 (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.pfPt (fsOf tr (itemsOf seq4))) := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩
  have hE := hF.ext 11 (by omega)
  have hpos0 := skel_pos4 hF.sk
  have hrel := relPf4_of_fields hF hPS hck hnc hnf hix
  obtain ⟨hpv, hpl, -, hpN, hpo, -⟩ := pf_view4 hF.sk (fi := fi) rfl
  simp only [relPf4, Bool.and_eq_true] at hrel
  have h1 := hrel.1
  rw [hE.rd (x := claimN fi "Pf") (getLastD_lt hpo hpos0), hpN, eqv_k] at h1
  have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
    unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  have hsf : ∀ v < 7, sfv4 fi (Rs 11) P v = T4.pfP (fsOf tr (itemsOf seq4)) v := fun v hv => by
    have hlt : v < (chals fi "Pf" 7).length := by rw [hpl]; exact hv
    rw [sfv4, hPS, seq4_pf, hE.rd (hpo _ (hch _ (by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _))), hpv v hv]; rfl
  have hpadv : padV4 p.tix fi (Rs 11) P = ∏ v ∈ Ico (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4) 7,
      (1 - T4.pfP (fsOf tr (itemsOf seq4)) v) := by
    rw [padV4, mLog4_eq]
    rcases hpad with ⟨hA, hm⟩ | ⟨hA, hm⟩
    · rw [if_pos hA, hm]; simp
    · rw [if_neg (by simp [hA]), hm, hPS, seq4_pf, padF4_eq]
      have := CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))
      refine prod_congr rfl fun v hv => ?_
      rw [hsf v (mem_Ico.1 hv).2]
  rw [hW, hpadv, finHat4_eq hF hPS (k := 11) (by omega) (Ex 11)] at h1
  rw [show clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L (fsOf tr (itemsOf seq4)) 7 =
    rVal T4.pfStart (fsOf tr (itemsOf seq4)) 6 from rfl, h1]

/-- **`enc`'s zero tail from `finPf`'s tail flag** (the kind's `m` is `m*`, or one of the tails). -/
theorem hz_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) (hck : P.ck = true)
    (hnc : 0 < P.nc) (hnf : 0 < P.fams.length)
    (hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length)
    (hmk : P.kv.m p.tix = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (htl : (kindOfC (fsOf tr (itemsOf seq4))).m < 32 → (kindOfC (fsOf tr (itemsOf seq4))).m ∈ P.tails) :
    ∀ c, 2 ^ T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4 ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0 := by
  intro c hc1 hc2
  have hrel := relPf4_of_fields hF hPS hck hnc hnf hix
  simp only [relPf4, Bool.and_eq_true] at hrel
  rw [mLog4_eq] at hc1
  rcases Nat.lt_or_ge (kindOfC (fsOf tr (itemsOf seq4))).m 32 with h | h
  · exact tail_zero4 hrel.2 hPS (htl h) hmk c hc1 hc2
  · have := CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))
    have h7 : (kindOfC (fsOf tr (itemsOf seq4))).m - 25 = 7 := by omega
    rw [h7] at hc1; omega

end Acc

end FR.Snd.R4
