-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS`/`finB′`, §5.4; track R4g). The 3.x
-- template is `FRSoundnessFrRun`'s `start_run` (`rsV_eq`, `vkL_fsQ`, `stL_fsQ`).
import FRSoundness4R4Tail

/-!
# `FinRest4.start`: P1.0's first claim is the front's `c₀L4` on an accepted `gen4` run

`finB′`'s relation `relB4` says `ι v* = ` P1.0's first claim, with `v*` (`vStar4`) read on the
registers: `finRS`'s `v_RS` export (the `zhat` register `nRS`), B′'s `κ′` and the public values
(`vk`, the statement's `c₁`, `c₂`, read from π). On an accepted run every one of them is the log's:

* **`rsV4_zh`**: the `zhat nRS` register holds `rsV4` (`exec_gFinRS`'s third conjunct);
* **`rsV4_eq`**: `rsV4 = vRSL4` (RS1's `r″`, `κ` by `rs1_val4`; RS0's slices by `msg_abs4` at 326;
  `phiRS` at its specification `phiRSS`, a new op parameter `hphi`, which `Meets` gives:
  `phiRS_segC`, `phiRS_nodeC`);
* `kp = kpL4` (B′ at 331, `one_name_view4`); **`pubH4_eq`**: `pubH4 = pubHL` (`vkL_eq4` by
  `seedQ4`, `stL_eq4` by `stmt_msg4`).

**`start4_of_fields`** puts them together with P1.0's first claim (`p1_view4`);
**`start4_seg`**, **`start4_node`**: on an accepted run of the kind's program.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-! ## The public values on the log -/

section Pub
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
include h

/-- **The seed's `vk` on the log is the input's.** -/
theorem vkL_eq4 : vkL (fsOf tr (itemsOf seq4)) = inp.vk := by
  unfold vkL
  rw [seedQ4 h]
  refine Vector.ext fun k hk => ?_
  rw [getElem_bytesAt _ _ _ _ hk, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]),
    show 7 + k - tagSeed.length = k by simp [tagSeed],
    List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
    Vector.getElem_toList]

/-- **The statement's digests on the log are π's** (bytes `1`, `33` of the `stmt` field). -/
theorem stL_eq4 :
    stL (fsOf tr (itemsOf seq4)) 0 = bytesAt inp.π (fieldOffOf seq4 fStmt + 1) 32 ∧
      stL (fsOf tr (itemsOf seq4)) 1 = bytesAt inp.π (fieldOffOf seq4 fStmt + 33) 32 := by
  rw [fieldOff_hdr_stmt4.2]
  exact ⟨by rw [stL, stmt_msg4 h]; exact bytesAt_extract_of_le inp.π (by norm_num),
    by rw [stL, stmt_msg4 h]; exact bytesAt_extract_of_le inp.π (by norm_num)⟩

/-- **`pubH` at `P` is the log's `pubHL`** (`P.S = seq4`). -/
theorem pubH4_eq {P : FinP} (hPS : P.S = seq4) (kp : F) :
    pubH4 inp P kp = pubHL (fsOf tr (itemsOf seq4)) kp := by
  obtain ⟨h0, h1⟩ := stL_eq4 h
  simp only [pubH4, pubHL, hPS, h0, h1, vkL_eq4 h]

end Pub

/-! ## `v_RS` -/

section RS
variable {tr : Trace} {y : List Val × List Bool × Trace}

/-- **RS1's coordinates by name** are `rsCoL4` (`coordAt es 326`). -/
theorem rs1_val4 (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {q : ℕ} (hq : q < 8) :
    fv R ((coordsR fi "RS1").getD q 0) = P4b.rsCoL4 (fsOf tr (itemsOf seq4)) q := by
  obtain ⟨hn24, e24⟩ := ph4 (n := 24) (x := ("RS1", Sh.squeezes 4 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 h hfi hR hn24 (by rw [e24]) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (a := 8) (by norm_num)
  rw [show phStart4 24 = 327 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  obtain ⟨hlen, hget⟩ := take_map_getElem hco
  rw [List.getD_eq_getElem _ _ (by omega), hget q (by omega) hq, P4b.rsCoL4, coordAt]

/-- **`finRS`'s `v_RS` export** holds `rsV4` on the skeleton's file. -/
theorem rsV4_zh {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    fv (Rs 0) (zh.getD nRS 0) =
      rsV4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray) P := by
  obtain ⟨L₀, hL₀, h0⟩ := hF.rs
  obtain ⟨L, hL, -, hv⟩ := exec_gFinRS impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
    (#[] ++ y.1.toArray) P (hin_RS (fun name x hx => outsOf_lt4 hF.sk [] #[] name x hx)
      (skel_pos4 hF.sk) _ P)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hL₀.symm.trans hL))
  rw [h0, hF.zh_eq]
  exact hv

/-- **`v_RS` on the skeleton's registers is `vRSL4`** (`phiRS` at its specification; the finals'
node flag is the chain's kind's). -/
theorem rsV4_eq (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a)
    (h : SkRun4 impl p inp tr y) {P : FinP} (hPS : P.S = seq4)
    (hnode : P.kv.node p.tix = (kindOfC (fsOf tr (itemsOf seq4))).isNode) :
    rsV4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray) P =
      P4b.vRSL4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) := by
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
  have hR := extA_refl (#[] ++ y.1.toArray)
  have hpt : ptF (#[] ++ y.1.toArray) (rsFsRegs fi) = (P4b.rsRL4 es).toArray := by
    simp only [ptF, rsFsRegs, P4b.rsRL4, List.map_map]
    exact congrArg List.toArray (List.map_congr_left fun q hq =>
      rs1_val4 h (fi := fi) rfl hR (by simp at hq; omega))
  have hT : ∀ j < 4, rsTv4 impl inp fi (#[] ++ y.1.toArray) P j = P4b.rsTvL4 es j := by
    intro j hj
    simp only [rsTv4, P4b.rsTvL4]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [hpt, hphi _ _ (by simp [P4b.rsRL4]), phiRSS, List.toList_toArray, P4b.sliceL4,
      msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_ends.2.2.2 (by simp only [rsOff]; omega), sv4, hPS]
  unfold rsV4 P4b.vRSL4 P4b.rsKL4
  rw [hT 0 (by norm_num), hT 1 (by norm_num), hT 2 (by norm_num), hT 3 (by norm_num),
    rs1_val4 h (fi := fi) rfl hR (show 7 < 8 by norm_num), hnode]

end RS

/-! ## `finB′` on the fields -/

theorem rest_gFinB' (P : FinP) :
    (finalsOf P).rest[5]'(by rw [rest_finalsOf_length]; decide) = gFinB' P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

/-- **`FinRest4.start` on the fields**: P1.0's first claim is `c₀L4 = ι v*` (`relB4` with every
input of `v*` the log's). -/
theorem start4_of_fields (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a)
    {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
    (hPS : P.S = seq4) (hnode : P.kv.node p.tix = (kindOfC (fsOf tr (itemsOf seq4))).isNode)
    (hrsv : P4b.nRsv (kindOfC (fsOf tr (itemsOf seq4))) = if (P.rsvOps && P.rsv) = true then rsvN else 0)
    (L : Log) :
    rSum (T4.p1Start 0) (fsOf tr (itemsOf seq4)) 0 = P4b.c₀L4 L (fsOf tr (itemsOf seq4)) := by
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 5⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 5 (by decide)
  have hpos := hF.pos (k := 5) (by decide)
  obtain ⟨-, L5, hL5, -, -⟩ := hF.fld 5 (by decide)
  rw [rest_gFinB'] at hL5
  obtain ⟨hn25, e25⟩ := ph4 (n := 25) (x := ("B'", Sh.squeezes 1 .one)) (by rw [seq4_eq]; rfl)
  obtain ⟨hk1, hk2⟩ := one_name_view4 hF.sk hfi hE hn25 (by rw [e25])
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hc0 : claim0 fi "P1" < (Rs 5).size := headD_lt (hF.sk_lt (by decide) _ "P1") hpos
  have hin1 : (outsOf fi "B'").headD 0 < (Rs 5).size := lt_of_lt_of_le hk1 hE.1
  have hin2 : fi.zhat.getD nRS 0 < (Rs 5).size := getD_lt hpos (hF.zlt' (by decide)) _
  have hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < (Rs 5).size := by
    obtain ⟨hs4, L4, hL4, he4, hx4⟩ := hF.fld 4 (by decide)
    rw [rest_gFinE] at hL4 hx4
    have hl4 := pureRun_len impl p.tix inp _ _ [] _ _ hL4
    rw [List.length_nil, Nat.zero_add] at hl4
    have hfx : fi.ex.getD exE [] = (gFinE P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩ (Rs 4).size).2 := by
      rw [show fi.ex = Ex 5 from rfl, hx4, exE, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs4,
        if_pos rfl, Option.getD_some]
    rw [hfx]
    exact gFinE_ex_lt P _ he4 hl4
  obtain ⟨L', hL', -⟩ := flag_gFinB' (impl := impl) (κ := p.tix) (inp := inp) (fi := fi) (r := Rs 5)
    (P := P) (List.forall_mem_cons.2 ⟨hin1, List.forall_mem_cons.2 ⟨hin2,
      List.forall_mem_cons.2 ⟨hc0, fun _ h => absurd h List.not_mem_nil⟩⟩⟩) hex
  have h1 := val_eqv_k (pureRun_det hL5 hL')
  obtain ⟨b, hout, -, h0, -, hlt, -⟩ := p1_view4 hF.sk hfi (i := 0) (by norm_num)
  have hlt0 : p1Claim0 fi 0 < (#[] ++ y.1.toArray).size := by
    rw [p1Claim0, hout, List.cons_append, List.headD_cons]
    exact hlt _ (by rw [hout, List.cons_append]; exact List.mem_cons_self ..)
  have he : p1Claim0 fi 0 = claim0 fi "P1" := by
    simp only [p1Claim0, claim0, lvOuts, outsOf, Nat.mul_zero, Nat.add_zero]
  rw [← he, hE.rd hlt0, h0] at h1
  rw [P4b.c₀L4, Val.k.inj h1, K.smulF_one]
  refine congrArg (algebraMap F K) ?_
  have hz : fv (Rs 5) (fi.zhat.getD nRS 0) = P4b.vRSL4 (kindOfC es) es := by
    rw [show fi.zhat = zh from rfl, hF.fv_zh (by decide), rsV4_zh hF, rsV4_eq hphi hF.sk hPS hnode]
  have hv0 : vStar4o p.tix inp fi (Rs 5) P = P4b.vRSL4 (kindOfC es) es +
      if (kindOfC es).isNode then P4b.kpL4 es * P4b.kpL4 es * pubHL es (P4b.kpL4 es) else 0 := by
    simp only [vStar4o, hz, hk2, hnode, pubH4_eq hF.sk hPS, P4b.kpL4,
      show phStart4 25 = 331 by rw [phStart4, fsStarts4_eq]; rfl]
    rfl
  have hkp : fv (Rs 5) ((outsOf fi "B'").headD 0) = P4b.kpL4 es := by
    rw [hk2, P4b.kpL4, show phStart4 25 = 331 by rw [phStart4, fsStarts4_eq]; rfl]
  simp only [vStar4, P4b.vStarL4]
  by_cases hc : (P.rsvOps && P.rsv) = true
  · have h60 : P4b.nRsv (kindOfC es) = 60 := by rw [hrsv, if_pos hc]; rfl
    have hnd : (kindOfC es).isNode = true := by
      cases hk : kindOfC es with
      | node ν => rfl
      | seg σ => rw [hk] at h60; simp [P4b.nRsv] at h60
    have hro : P.rsvOps = true := by simp only [Bool.and_eq_true] at hc; exact hc.1
    rw [if_pos hc, hv0, if_pos hnd, if_pos hnd, P4b.rsvHL, h60, hkp]
    have hs : ∀ i ∈ Finset.range rsvN, P4b.kpL4 es ^ i * fv (Rs 5) (((fi.ex.getD exE []).drop 1).getD i 0) =
        P4b.kpL4 es ^ i * P4b.rsvV es i := fun i hi => by
      rw [Finset.mem_range] at hi
      rw [show fi.ex = Ex 5 from rfl, rsvEx_of_fields hF i hi hro, P4b.rsvV,
        child_vals4 hF.sk (show i < 60 from hi), hPS]
    rw [Finset.sum_congr rfl hs]
    simp only [rsvN]; ring
  · have h0 : P4b.nRsv (kindOfC es) = 0 := by rw [hrsv, if_neg hc]
    rw [if_neg hc, hv0, P4b.rsvHL, h0]
    split_ifs <;> simp

/-! ## On an accepted run of the kind's program -/

/-- **`FinRest4.start` for a segment** (`phiRS` at its specification). -/
theorem start4_seg (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a) {σ : SegKind} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    rSum (T4.p1Start 0) (fsOf tr (itemsOf seq4)) 0 = P4b.c₀L4 L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  exact start4_of_fields hphi hF rfl (by rw [kindOfC_acc_seg h]; rfl) (by rw [kindOfC_acc_seg h]; rfl) L

/-- **`FinRest4.start` for a node.** -/
theorem start4_node (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a) {ν : NodeKind}
    {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    rSum (T4.p1Start 0) (fsOf tr (itemsOf seq4)) 0 = P4b.c₀L4 L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  exact start4_of_fields hphi hF rfl (by rw [kindOfC_acc_node h]; rfl)
    (by rw [kindOfC_acc_node h]; cases ν <;> rfl) L

/-! ## The op parameter `hphi` (controls) -/

/-- (+) **The concrete segment ops meet `hphi`** (`implSegC_meets`). -/
theorem phiRS_segC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    ∀ r a, r.size = 7 → (implSeg (implC fin lRows κs₀)).phiRS r a = phiRSS r a := fun r a hr => by
  rw [(implSegC_meets fin lRows κs₀).2.2.2.2.2.1 r a hr]
  simp only [specSeg, Impl.specC, Impl.specCWith]

/-- (+) **… and the node's** (`implN4T` over 3.x's ops). -/
theorem phiRS_nodeC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) :
    ∀ r a, r.size = 7 → (NI4T.implN4T (fun _ => implC fin lRows κs₀) ν).phiRS r a = phiRSS r a :=
  fun r a hr => by
    have hm : (NI4T.implN4T (fun _ => implC fin lRows κs₀) ν).Meets
        (NI4.specN4 (fun _ => specC fin lRows κs₀) ν) := NI4T.implN4T_meets ν (implC_meets fin lRows κs₀)
    rw [hm.2.2.2.2.2.1 r a hr]
    simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]

end FR.Snd.R4
