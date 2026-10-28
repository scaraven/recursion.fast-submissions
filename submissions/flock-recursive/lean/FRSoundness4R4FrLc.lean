-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finLc` (ii), A.10 L3; stage R4e).
import FRSoundness4R4FrZ
import FRSoundnessFrLc

/-!
# L2's last claim on an accepted run (P4a's `RejLc2`, `RejLcN`)

3.x's `lc_ii_run` at `gen4`: `relLc4` (ii) on the fields (**`relLc4_of_fields`**) through the views
(L2's last claim from its head `c0L`, `λ`, `α`, `r′_hi`, `r_k`, L3's values `vL`), and 3.x's walk
bridge `lc_bridge` with `walkAB`, `rowW`, `eqZ` at their specifications (parameters `hW hR hZ`, as
3.x's): **`lc_ii4`**, L2's last claim is `Σ_j v′_j M̃_j(r_k)`, `v′` the kind-masked values
(P4a's `vM`). **`not_rejLc_seg4`**, **`not_rejLc_node4`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **`finLc`'s relation on the fields of an accepted run** (field 1, file `Rs 1`). -/
theorem relLc4_of_fields {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relLc4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ (Rs 1) P = true := by
  obtain ⟨-, L1, hL1, -, -⟩ := hF.fld 1 (by decide)
  rw [rest_gFinLc] at hL1
  obtain ⟨L', hL'⟩ := flag_gFinLc impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ (Rs 1) P
    (hin_Lc (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide)))
  exact pureRun_det hL1 hL'

/-- L3's values on the log are the program's reads. -/
theorem lcV4_eq {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {P : FinP} (hP : P.S = seq4) :
    lcV4 inp P = (List.range 8).map (vL (fsOf tr (itemsOf seq4))) := by
  unfold lcV4
  rw [phaseIx_L3, hP]
  refine List.map_congr_left fun i hi => ?_
  have hi8 := List.mem_range.1 hi
  rw [vL, msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_front.2 (by omega), pe4, Nat.add_assoc]

/-- **L2's last claim on the fields of an accepted run** (3.x's `lc_ii_run` at `gen4`): for
`walkAB`, `rowW`, `eqZ` at their specifications and a kind flag the finals and the chain agree on,
it is the per-kind lincheck sum. -/
theorem lc_ii4 (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
    (hPS : P.S = seq4) (hnode : P.kv.node p.tix = p.tix.isNode)
    (hκ : (kindOfC (fsOf tr (itemsOf seq4))).isNode = p.tix.isNode)
    (M : P4a.ZLM4) (hA : M.Ak = zlmFR.Ak) (hB : M.Bk = zlmFR.Bk) (L : Log) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr (itemsOf seq4)) 14 =
      ∑ j, P4a.vM (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) j *
        mle (linM (M.Ak j) (M.Bk j) (P4a.rwL (fsOf tr (itemsOf seq4))) (alL (fsOf tr (itemsOf seq4))))
          (ptOf 14 (rkL (fsOf tr (itemsOf seq4)))) := by
  have hrel := relLc4_of_fields hF
  simp only [relLc4, Bool.and_eq_true, hPS] at hrel
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 1 (by decide)
  have hS := hF.sk
  -- L2's head and last claims
  have hc0 := val_eqv_f4 hrel.1.1
  have h3 := val_eqv_f4 hrel.2
  obtain ⟨hn8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) rfl
  obtain ⟨hn7, e7⟩ := ph4 (n := 7) (x := ("L1", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hα⟩ := one_name_view4 hS hfi hE hn7 (by rw [e7]) phaseIx_vals.2.2.2.1
  rw [show phStart4 7 = 68 by rw [phStart4, fsStarts4_eq]; rfl] at hα
  obtain ⟨hcl, -, -, hlt, hlast⟩ := roundsF2_view4 hS hn8 (by rw [e8]) L
  rw [(outsOf_skel hfi "L2").2.1, phaseIx4_rounds.2.2.1] at hc0
  rw [← hE.rd hcl, hc0] at hlast
  obtain ⟨hN, -⟩ := hlast _ rfl
  rw [e8, (realRounds_vals _ _).2.2.2.2.2, Nat.min_self,
    show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hN
  rw [(outsOf_skel hfi "L2").2.2, phaseIx4_rounds.2.2.1, hE.rd hlt, hN, Val.f.injEq] at h3
  have hc0L : pe4 seq4 inp fZend 0 + fv (Rs 1) ((outsOf fi "L1").headD 0) * pe4 seq4 inp fZend 16 =
      c0L es := by
    have hm := fsMsgs4_front.1
    rw [hα, c0L, alL, vZ, vZ, msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num),
      msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num)]
    rfl
  rw [clR2_c0_eq (c0' := fun _ _ => pe4 seq4 inp fZend 0 +
    fv (Rs 1) ((outsOf fi "L1").headD 0) * pe4 seq4 inp fZend 16) hc0L.symm, h3]
  -- the views
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, hlam, -⟩ := uni_view4 hS hn4 (by rw [e4])
  have hlm : fv (Rs 1) ((outsOf fi "Z2").headD 0) = lamL es := by
    rw [(outsOf_skel hfi "Z2").1, phaseIx4_rounds.1, hout, List.headD_cons]
    have hlt' := (hF.sk_lt (k := 1) (by decide) (Ex 1) "Z2")
    show (rd (Rs 1) _).toF = _
    rw [hE.rd (by
      have := skeleton4_out_lt p hS.ref 4 (b + (if p.d.node = true then 0 else 1) + 3)
        (by rw [hout]; simp)
      exact this), hlam, show phStart4 4 + 1 = 14 by rw [phStart4, fsStarts4_eq]; rfl]
    rfl
  obtain ⟨hn5, e5⟩ := ph4 (n := 5) (x := ("Z3", Sh.rounds fZ3 seq4.z3 3 false)) rfl
  have hz8 := chals_view4 hS hfi hE hn5 (by rw [e5]) phaseIx4_rounds.2.1 (a := 8) (by rw [seq4_eq]; decide)
  rw [show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hz8
  have htk : (chals fi "Z3" P.S.z3).take 8 = chals fi "Z3" 8 := by
    rw [hPS]
    rw [chals, chals, List.take_take, Nat.min_eq_left (by rw [seq4_eq]; decide)]
  have hrhi : lcRhi4 fi (Rs 1) P = (rchs 15 es 8).toArray := by
    rw [lcRhi4, htk, hz8]
  have hrhi8 : (lcRhi4 fi (Rs 1) P).size = 8 := by rw [hrhi]; simp [rchs]
  have hκm := CKind.m_mem (kindOfC es)
  have hrhiL : ptA 8 (lcRhi4 fi (Rs 1) P) = P4a.rhiL es := by
    rw [hrhi, ptA_toArray]
    funext i
    simp only [P4a.rhiL, P4a.rZ, ptOf, rchs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range i.isLt, List.getElem?_range (show i.val < P4a.mC 6 (kindOfC es) by
        unfold P4a.mC; omega)]
  have hch := chals_view4 hS hfi hE hn8 (by rw [e8]) phaseIx4_rounds.2.2.1 (a := 14) le_rfl
  rw [show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hch
  have hrk : lcRk fi (Rs 1) = rkL es := by rw [lcRk, hch]; rfl
  have hv := lcV4_eq hS hPS
  have hv8 : (lcV4 inp P).length = 8 := by simp [lcV4]
  have hrkl : (lcRk fi (Rs 1)).length = 14 := by rw [hrk]; simp [rkL, rchs]
  have hb := lc_bridge hW hR hZ p.tix (v := lcV4 inp P) hv8 (lcVf4 p.tix inp P)
    (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (fv (Rs 1) ((outsOf fi "L1").headD 0)) (lcRhi4 fi (Rs 1) P)
    hrhi8 (lcRk fi (Rs 1)) hrkl
  simp only at hb
  have hlhs : lcWalk4 impl p.tix inp fi (Rs 1) P + (lcFree4 impl p.tix inp fi (Rs 1) P +
      fv (Rs 1) ((outsOf fi "L1").headD 0) * lcFree4 impl p.tix inp fi (Rs 1) P) =
      (impl.walkAB (maskRows (lcWts p.tix (lcV4 inp P)).toArray
          (impl.rowW (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (lcRhi4 fi (Rs 1) P)))
          (eqTab (lcRk fi (Rs 1)).toArray)).1 +
        fv (Rs 1) ((outsOf fi "L1").headD 0) * (impl.walkAB (maskRows (lcWts p.tix (lcV4 inp P)).toArray
          (impl.rowW (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (lcRhi4 fi (Rs 1) P)))
          (eqTab (lcRk fi (Rs 1)).toArray)).2 +
        (lcVf4 p.tix inp P * (dotAcc 0 (impl.eqZ (fv (Rs 1) ((outsOf fi "Z2").headD 0)) 0)
            (eqTab ((lcRk fi (Rs 1)).take 6).toArray) 64 *
          eqPoint (lcRhi4 fi (Rs 1) P) ((lcRk fi (Rs 1)).drop 6).toArray) +
         fv (Rs 1) ((outsOf fi "L1").headD 0) * (lcVf4 p.tix inp P *
          (dotAcc 0 (impl.eqZ (fv (Rs 1) ((outsOf fi "Z2").headD 0)) 0)
            (eqTab ((lcRk fi (Rs 1)).take 6).toArray) 64 *
          eqPoint (lcRhi4 fi (Rs 1) P) ((lcRk fi (Rs 1)).drop 6).toArray))) := by
    simp only [lcWalk4, lcFree4, lcRk, lcWts, List.map_take, List.map_drop, hnode]
  rw [hlhs, hb, hlm, hα, hrhiL, hrk, hA, hB]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lcWts_vM p.tix hv8 _ (by simp only [lcVf4, hnode]; split <;> simp [lcV4]), hv]
  simp only [P4a.vM, hκ]
  split
  · split
    · rfl
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp only [List.getElem_map, List.getElem_range]; rfl
  · split
    · rw [List.getD_eq_getElem _ _ (by simp)]; simp only [List.getElem_map, List.getElem_range]; rfl
    · rfl

/-- **`RejLc2`, `RejLcN` never hold on an accepted segment run** (`walkAB`, `rowW`, `eqZ` at their
specifications; `M` a `zlm4`). -/
theorem not_rejLc_seg4 (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {σ : SegKind} {tr : Trace} (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejLc2 (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) ∧
      ¬ P4a.RejLcN (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have e := lc_ii4 hW hR hZ hF rfl rfl (by rw [kindOfC_seg4 hF.sk]; rfl) (P4a.zlm4 indN etN) rfl rfl L
  exact ⟨fun ⟨_, _, hne⟩ => hne e, fun ⟨_, _, hne⟩ => hne e⟩

/-- **… nor on an accepted node run.** -/
theorem not_rejLc_node4 (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {ν : NodeKind} {cells : List ℕ} {tr : Trace} (indN : NodeKind → Fin 9 → ℕ → F)
    (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejLc2 (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) ∧
      ¬ P4a.RejLcN (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have e := lc_ii4 hW hR hZ hF rfl rfl (by rw [kindOfC_node4 hF.sk]; rfl) (P4a.zlm4 indN etN) rfl rfl L
  exact ⟨fun ⟨_, _, hne⟩ => hne e, fun ⟨_, _, hne⟩ => hne e⟩

end FR.Snd.R4
